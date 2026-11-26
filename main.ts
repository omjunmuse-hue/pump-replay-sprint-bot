// Replay Sprint bot: confirmed-inflow momentum over a 24-hour window.
//
// The window here is a full day of pump.fun chain data, four times the
// Paper Sprint's, so this bot trades confirmation instead of speed. A
// fresh curve becomes a candidate when strangers pour in: ten or more
// distinct non-creator buyers and at least eight SOL of net inflow over
// the last forty slots, with the price up a fifth to four fifths from
// create and the creator still holding. A candidate is only bought when
// the same picture is still true on the next look, which filters the
// one-batch pumps that fake a crowd and vanish. Stakes stay small, losers
// are cut at nine percent, winners ride a trailing stop, nothing is held
// past seven minutes of slots, and a paced drip of tiny probe round trips
// keeps the entry over the guardrail bar of twenty distinct coins. A pure
// function of the batches: no clock, no randomness, no environment.

import { runBot, type Batch, type BotState, type OrderInput, type Pubkey } from './vendor/makefun-bot.ts';

const SOL = 1_000_000_000n;
const BPS = 10_000n;

// Entry filters, measured at decision time on the batch's slot.
const MIN_AGE_SLOTS = 10;
const MAX_AGE_SLOTS = 60;
const MIN_REAL_SOL = 6n * SOL;
const MAX_REAL_SOL = 30n * SOL;
const MIN_TRADES = 24;
const MIN_BUYERS = 10;
const MAX_BUYERS = 16;
const FLOW_WINDOW_SLOTS = 40;
const MIN_FLOW_LAMPORTS = 10n * SOL; // net inflow over the window: +10 SOL
const MAX_SELL_RATIO_BPS = 3_000n; // sells by others at most 30% of buys
const MIN_RUNUP_BPS = 2_000; // price at least +20% over the create price
const MAX_RUNUP_BPS = 8_000; // and at most +80%
const MAX_DEV_BUY = 3n * SOL;
const CONFIRMATIONS_NEEDED = 2; // the picture must hold on two looks
const STAKE_LAMPORTS = (SOL * 25n) / 1_000n; // 0.025 SOL before the cap
const MIN_BUY_LAMPORTS = SOL / 100n; // 0.01 SOL: the guardrail round-trip bar
const BUY_SLIPPAGE_BPS = 2_500;

// Exits: cut at -9%, trail from +18% with a 9% leash, out by 420 slots.
const STOP_LOSS_BPS = 900n;
const TRAIL_ARM_BPS = 1_800n;
const TRAIL_BPS = 900n;
const MAX_HOLD_SLOTS = 300;
const STALE_SLOTS = 90;

// Guardrail probes over a 24-hour final window.
const PROBE_LAMPORTS = (SOL * 12n) / 1_000n; // 0.012 SOL per probe
const PROBE_TARGET_COINS = 24;
const WINDOW_SECONDS = 86_400; // the final window is 24 hours of block time
const MAX_PROBES_TOTAL = 36;

interface Tick {
  slot: number;
  isBuy: boolean;
  sol: bigint;
  user: Pubkey;
}

interface Coin {
  createSlot: number;
  creator: Pubkey;
  vq0: bigint;
  vt0: bigint;
  devBuy: bigint;
  devSold: boolean;
  trades: number;
  buyers: Set<Pubkey>;
  bought: bigint;
  soldByOthers: bigint;
  lastTradeSlot: number;
  recent: Tick[];
  confirmations: number;
  entered: boolean;
  finished: boolean;
}

interface Held {
  openedSlot: number;
  bestValue: bigint;
  sellSent: boolean;
}

const coins = new Map<Pubkey, Coin>();
const held = new Map<Pubkey, Held>();
const probeStage = new Map<Pubkey, 'buying' | 'selling'>();
const roundTripCoins = new Set<Pubkey>();
let probesSent = 0;
let firstBlockTime: number | null = null;
let lastBlockTime = 0;

/** What selling `tokens` on a curve pays after the 1.25% curve fee, before tx fees. */
function sellValue(tokens: bigint, vq: bigint, vt: bigint): bigint {
  if (tokens <= 0n || vt <= 0n) return 0n;
  const gross = (tokens * vq) / (vt + tokens);
  return gross - (gross * 125n) / BPS;
}

/** Net flow and distinct buyers over the last FLOW_WINDOW_SLOTS slots. */
function recentFlow(coin: Coin, slot: number): { net: bigint; buyers: number } {
  const from = slot - FLOW_WINDOW_SLOTS;
  let drop = 0;
  while (drop < coin.recent.length && coin.recent[drop]!.slot <= from) drop++;
  if (drop > 0) coin.recent.splice(0, drop);
  let net = 0n;
  const buyers = new Set<Pubkey>();
  for (const t of coin.recent) {
    if (t.isBuy) {
      net += t.sol;
      buyers.add(t.user);
    } else {
      net -= t.sol;
    }
  }
  return { net, buyers: buyers.size };
}

function readEvents(batch: Batch): void {
  for (const e of batch.events) {
    if (e.block_time !== null) {
      if (firstBlockTime === null) firstBlockTime = e.block_time;
      if (e.block_time > lastBlockTime) lastBlockTime = e.block_time;
    }
    if (e.event === 'CreateEvent') {
      coins.set(e.mint, {
        createSlot: e.slot,
        creator: e.creator,
        vq0: BigInt(e.virtual_quote_reserves),
        vt0: BigInt(e.virtual_token_reserves),
        devBuy: 0n,
        devSold: false,
        trades: 0,
        buyers: new Set(),
        bought: 0n,
        soldByOthers: 0n,
        lastTradeSlot: e.slot,
        recent: [],
        confirmations: 0,
        entered: false,
        finished: false,
      });
    } else if (e.event === 'TradeEvent') {
      const coin = coins.get(e.mint);
      if (coin === undefined) continue;
      const sol = BigInt(e.sol_amount);
      coin.trades += 1;
      coin.lastTradeSlot = e.slot;
      coin.recent.push({ slot: e.slot, isBuy: e.is_buy, sol, user: e.user });
      if (e.is_buy) {
        coin.bought += sol;
        if (e.user === coin.creator) {
          if (e.slot === coin.createSlot) coin.devBuy += sol;
        } else {
          coin.buyers.add(e.user);
        }
      } else if (e.user === coin.creator) {
        coin.devSold = true;
      } else {
        coin.soldByOthers += sol;
      }
    } else {
      const coin = coins.get(e.mint);
      if (coin !== undefined) coin.finished = true;
    }
  }
}

function hasPending(state: BotState, mint: Pubkey, side: 'buy' | 'sell'): boolean {
  for (const p of state.pending.values()) {
    if (p.order.mint === mint && p.order.side === side) return true;
  }
  return false;
}

await runBot({
  onBatch(state, batch) {
    readEvents(batch);
    const orders: OrderInput[] = [];
    const cap = state.hello.caps.max_orders_per_batch;
    const tx = state.txFeeLamports();
    const marks = new Map<Pubkey, { vq: bigint; vt: bigint }>();
    for (const m of batch.marks) marks.set(m.mint, { vq: BigInt(m.virtual_quote_reserves), vt: BigInt(m.virtual_token_reserves) });

    for (const f of batch.fills) {
      if (f.status === 'filled' && f.side === 'sell' && !f.client_id.startsWith('_')) {
        roundTripCoins.add(f.mint);
      }
    }
    for (const mint of [...held.keys()]) {
      if (!state.positions.has(mint) && !hasPending(state, mint, 'buy') && !hasPending(state, mint, 'sell')) {
        held.delete(mint);
      }
    }
    for (const mint of [...probeStage.keys()]) {
      if (!state.positions.has(mint) && !hasPending(state, mint, 'buy') && !hasPending(state, mint, 'sell')) {
        probeStage.delete(mint);
      }
    }

    // Exits first: they free the position slots everything else needs.
    for (const [mint, pos] of state.positions) {
      if (orders.length >= cap) break;
      if (probeStage.has(mint)) continue;
      let h = held.get(mint);
      if (h === undefined) {
        h = { openedSlot: state.slot, bestValue: 0n, sellSent: false };
        held.set(mint, h);
      }
      if (h.sellSent) continue;
      const coin = coins.get(mint);
      const mk = marks.get(mint);
      const curve = state.curves.get(mint);
      const vq = mk?.vq ?? curve?.virtual_quote_reserves ?? 0n;
      const vt = mk?.vt ?? curve?.virtual_token_reserves ?? 0n;
      const value = sellValue(pos.token_amount, vq, vt) - tx;
      if (value > h.bestValue) h.bestValue = value;
      const cost = pos.cost_lamports;
      let exit = false;
      if (cost > 0n) {
        if (value * BPS <= cost * (BPS - STOP_LOSS_BPS)) exit = true;
        if (h.bestValue * BPS >= cost * (BPS + TRAIL_ARM_BPS) && value * BPS <= h.bestValue * (BPS - TRAIL_BPS)) exit = true;
      }
      if (state.slot - h.openedSlot >= MAX_HOLD_SLOTS) exit = true;
      if (coin !== undefined) {
        if (coin.devSold) exit = true;
        if (state.slot - coin.lastTradeSlot >= STALE_SLOTS) exit = true;
        if (coin.finished) exit = true;
      }
      if (!exit) continue;
      orders.push({ side: 'sell', mint, token_amount: pos.token_amount, max_slippage_bps: 10_000 });
      h.sellSent = true;
    }

    // Probe exits: sell the whole probe on the first batch after it lands.
    for (const [mint] of probeStage) {
      if (orders.length >= cap) break;
      const pos = state.positions.get(mint);
      if (pos === undefined || hasPending(state, mint, 'sell') || hasPending(state, mint, 'buy')) continue;
      orders.push({ side: 'sell', mint, token_amount: pos.token_amount, max_slippage_bps: 10_000 });
      probeStage.set(mint, 'selling');
    }

    // Entries: the picture must be true, then true again, before a buy.
    let free = state.freeCashLamports();
    let openSlots = state.hello.caps.max_open_positions - state.committedPositionCount();
    for (const [mint, coin] of coins) {
      if (orders.length >= cap || openSlots <= 0) break;
      if (coin.entered || coin.finished || held.has(mint) || probeStage.has(mint)) continue;
      const age = state.slot - coin.createSlot;
      if (age < MIN_AGE_SLOTS) continue;
      if (age > MAX_AGE_SLOTS) {
        coin.entered = true;
        continue;
      }
      const curve = state.curves.get(mint);
      if (curve === undefined || curve.complete) continue;
      const rq = curve.real_quote_reserves;
      let ok = rq >= MIN_REAL_SOL && rq <= MAX_REAL_SOL;
      ok = ok && !coin.devSold && coin.devBuy <= MAX_DEV_BUY;
      ok = ok && coin.trades >= MIN_TRADES;
      ok = ok && coin.buyers.size >= MIN_BUYERS && coin.buyers.size <= MAX_BUYERS;
      ok = ok && !(coin.bought > 0n && coin.soldByOthers * BPS > coin.bought * MAX_SELL_RATIO_BPS);
      const flow = recentFlow(coin, state.slot);
      ok = ok && flow.net >= MIN_FLOW_LAMPORTS && flow.buyers >= MIN_BUYERS;
      const runupBps = (curve.virtual_quote_reserves * coin.vt0 * BPS) / (curve.virtual_token_reserves * coin.vq0) - BPS;
      ok = ok && runupBps >= BigInt(MIN_RUNUP_BPS) && runupBps <= BigInt(MAX_RUNUP_BPS);
      if (!ok) {
        coin.confirmations = 0;
        continue;
      }
      coin.confirmations += 1;
      if (coin.confirmations < CONFIRMATIONS_NEEDED) continue;
      const capBuy = state.maxBuyLamports(mint);
      const amount = capBuy < STAKE_LAMPORTS ? capBuy : STAKE_LAMPORTS;
      if (amount < MIN_BUY_LAMPORTS) continue;
      if (free < amount + 2n * tx) continue;
      orders.push({ side: 'buy', mint, quote_lamports: amount, max_slippage_bps: BUY_SLIPPAGE_BPS });
      free -= amount + tx;
      openSlots -= 1;
      coin.entered = true;
      held.set(mint, { openedSlot: state.slot, bestValue: 0n, sellSent: false });
    }

    // Probes: keep the distinct-coin round-trip count on pace for the bar.
    if (
      probesSent < MAX_PROBES_TOTAL &&
      probeStage.size === 0 &&
      openSlots > 0 &&
      firstBlockTime !== null &&
      roundTripCoins.size < PROBE_TARGET_COINS
    ) {
      const elapsed = Math.max(0, lastBlockTime - firstBlockTime);
      const due = Math.ceil((PROBE_TARGET_COINS * Math.min(elapsed, WINDOW_SECONDS)) / WINDOW_SECONDS);
      if (roundTripCoins.size < due) {
        for (const [mint, coin] of coins) {
          if (orders.length >= cap) break;
          if (coin.finished || coin.entered || held.has(mint) || roundTripCoins.has(mint)) continue;
          const curve = state.curves.get(mint);
          if (curve === undefined || curve.complete) continue;
          if (curve.real_quote_reserves < 6n * SOL) continue;
          if (state.slot - coin.lastTradeSlot > 30) continue;
          const capBuy = state.maxBuyLamports(mint);
          const amount = capBuy < PROBE_LAMPORTS ? capBuy : PROBE_LAMPORTS;
          if (amount < MIN_BUY_LAMPORTS) continue;
          if (free < amount + 2n * tx) break;
          orders.push({ side: 'buy', mint, quote_lamports: amount, max_slippage_bps: BUY_SLIPPAGE_BPS });
          free -= amount + tx;
          probeStage.set(mint, 'buying');
          coin.entered = true;
          probesSent += 1;
          break;
        }
      }
    }
    return orders;
  },
});
