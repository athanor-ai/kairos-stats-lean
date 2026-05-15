//! # pythia-hft-orderbook
//!
//! Verified limit order book with price-time priority invariants.
//!
//! ## Lean specifications
//!
//! - `Pythia.Finance.HFT.OrderBook`: base invariants (sorted, FIFO,
//!   tick quantization, spread non-negativity)
//! - `Pythia.Finance.HFT.OrderBookStrong`: strengthened theorems
//!   (fill-improves-or-matches-mid, narrow-spread-reduces,
//!   tick-aligned-spread-pos)
//!
//! ## Performance
//!
//! - Sorted insert: O(n) worst case, O(1) amortized for in-order flow
//! - Best bid/ask: O(1) via cached top-of-book
//! - Cancel: O(n) by order ID scan (O(1) with HashMap index)

use std::cmp::Ordering;

/// An order in the book.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Order {
    pub id: u64,
    pub price: i64,
    pub qty: u64,
    pub seqno: u64,
    pub side: Side,
}

/// Order side.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Side {
    Bid,
    Ask,
}

/// A fill produced by the matching engine.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Fill {
    pub price: i64,
    pub qty: u64,
    pub maker_id: u64,
    pub taker_id: u64,
}

/// Limit order book with price-time priority.
///
/// # Lean theorem: `bidSorted`
/// Bids are sorted descending by price, FIFO within same price.
///
/// # Lean theorem: `spread_nonneg`
/// `best_ask - best_bid >= 0` (no crossed book).
#[derive(Debug, Default)]
pub struct OrderBook {
    bids: Vec<Order>,
    asks: Vec<Order>,
    next_seqno: u64,
    tick_size: i64,
}

impl OrderBook {
    pub fn new(tick_size: i64) -> Self {
        assert!(tick_size > 0, "tick size must be positive");
        Self {
            bids: Vec::new(),
            asks: Vec::new(),
            next_seqno: 0,
            tick_size,
        }
    }

    /// Best bid price, or None if no bids.
    pub fn best_bid(&self) -> Option<i64> {
        self.bids.first().map(|o| o.price)
    }

    /// Best ask price, or None if no asks.
    pub fn best_ask(&self) -> Option<i64> {
        self.asks.first().map(|o| o.price)
    }

    /// Spread = best_ask - best_bid. None if either side is empty.
    ///
    /// # Lean theorem: `spread_nonneg`
    /// `bid ≤ ask → 0 ≤ ask - bid`
    pub fn spread(&self) -> Option<i64> {
        match (self.best_bid(), self.best_ask()) {
            (Some(bid), Some(ask)) => Some(ask - bid),
            _ => None,
        }
    }

    /// Mid price = (bid + ask) / 2.
    ///
    /// # Lean theorem: `mid_between_bid_ask`
    /// `bid ≤ (bid + ask) / 2 ∧ (bid + ask) / 2 ≤ ask`
    pub fn mid_price(&self) -> Option<i64> {
        match (self.best_bid(), self.best_ask()) {
            (Some(bid), Some(ask)) => Some((bid + ask) / 2),
            _ => None,
        }
    }

    /// Insert an order. Returns fills if the order crosses the book.
    ///
    /// # Lean theorem: `best_bid_ge_second`
    /// After insert, the book remains sorted by price-time priority.
    ///
    /// # Lean theorem: `tick_size_gap`
    /// All prices are multiples of tick_size.
    pub fn insert(&mut self, id: u64, price: i64, qty: u64, side: Side) -> Vec<Fill> {
        assert!(price % self.tick_size == 0, "price must be tick-aligned");
        assert!(qty > 0, "quantity must be positive");

        let seqno = self.next_seqno;
        self.next_seqno += 1;

        let mut remaining_qty = qty;
        let mut fills = Vec::new();

        match side {
            Side::Bid => {
                // Match against asks (ascending price)
                while remaining_qty > 0 {
                    if let Some(best_ask) = self.asks.first() {
                        if price >= best_ask.price {
                            let fill_qty = remaining_qty.min(best_ask.qty);
                            let fill_price = best_ask.price; // passive price
                            fills.push(Fill {
                                price: fill_price,
                                qty: fill_qty,
                                maker_id: best_ask.id,
                                taker_id: id,
                            });
                            remaining_qty -= fill_qty;
                            if fill_qty >= self.asks[0].qty {
                                self.asks.remove(0);
                            } else {
                                self.asks[0].qty -= fill_qty;
                            }
                        } else {
                            break;
                        }
                    } else {
                        break;
                    }
                }
                // Rest on book
                if remaining_qty > 0 {
                    let order = Order { id, price, qty: remaining_qty, seqno, side };
                    let pos = self.bids.partition_point(|o| {
                        o.price > price || (o.price == price && o.seqno < seqno)
                    });
                    self.bids.insert(pos, order);
                }
            }
            Side::Ask => {
                // Match against bids (descending price)
                while remaining_qty > 0 {
                    if let Some(best_bid) = self.bids.first() {
                        if price <= best_bid.price {
                            let fill_qty = remaining_qty.min(best_bid.qty);
                            let fill_price = best_bid.price; // passive price
                            fills.push(Fill {
                                price: fill_price,
                                qty: fill_qty,
                                maker_id: best_bid.id,
                                taker_id: id,
                            });
                            remaining_qty -= fill_qty;
                            if fill_qty >= self.bids[0].qty {
                                self.bids.remove(0);
                            } else {
                                self.bids[0].qty -= fill_qty;
                            }
                        } else {
                            break;
                        }
                    } else {
                        break;
                    }
                }
                if remaining_qty > 0 {
                    let order = Order { id, price, qty: remaining_qty, seqno, side };
                    let pos = self.asks.partition_point(|o| {
                        o.price < price || (o.price == price && o.seqno < seqno)
                    });
                    self.asks.insert(pos, order);
                }
            }
        }

        fills
    }

    /// Cancel an order by ID. Returns true if found and removed.
    pub fn cancel(&mut self, order_id: u64) -> bool {
        if let Some(pos) = self.bids.iter().position(|o| o.id == order_id) {
            self.bids.remove(pos);
            return true;
        }
        if let Some(pos) = self.asks.iter().position(|o| o.id == order_id) {
            self.asks.remove(pos);
            return true;
        }
        false
    }

    /// Check that bids are sorted (descending price, FIFO within level).
    ///
    /// # Lean theorem: `bidSorted`
    pub fn is_bid_sorted(&self) -> bool {
        self.bids.windows(2).all(|w| {
            w[0].price > w[1].price || (w[0].price == w[1].price && w[0].seqno < w[1].seqno)
        })
    }

    /// Check that asks are sorted (ascending price, FIFO within level).
    pub fn is_ask_sorted(&self) -> bool {
        self.asks.windows(2).all(|w| {
            w[0].price < w[1].price || (w[0].price == w[1].price && w[0].seqno < w[1].seqno)
        })
    }

    /// Check no-cross invariant.
    ///
    /// # Lean theorem: `no_cross`
    pub fn is_uncrossed(&self) -> bool {
        match (self.best_bid(), self.best_ask()) {
            (Some(bid), Some(ask)) => bid < ask,
            _ => true,
        }
    }

    pub fn bid_count(&self) -> usize { self.bids.len() }
    pub fn ask_count(&self) -> usize { self.asks.len() }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_book() {
        let book = OrderBook::new(1);
        assert_eq!(book.best_bid(), None);
        assert_eq!(book.best_ask(), None);
        assert_eq!(book.spread(), None);
        assert!(book.is_uncrossed());
    }

    #[test]
    fn test_insert_bid_ask_no_cross() {
        let mut book = OrderBook::new(1);
        book.insert(1, 100, 10, Side::Bid);
        book.insert(2, 102, 10, Side::Ask);
        assert_eq!(book.best_bid(), Some(100));
        assert_eq!(book.best_ask(), Some(102));
        assert_eq!(book.spread(), Some(2));
        assert!(book.is_uncrossed());
        assert!(book.is_bid_sorted());
        assert!(book.is_ask_sorted());
    }

    #[test]
    fn test_crossing_order_fills() {
        let mut book = OrderBook::new(1);
        book.insert(1, 100, 10, Side::Ask);
        let fills = book.insert(2, 100, 5, Side::Bid);
        assert_eq!(fills.len(), 1);
        assert_eq!(fills[0].price, 100);
        assert_eq!(fills[0].qty, 5);
        assert_eq!(fills[0].maker_id, 1);
        assert_eq!(fills[0].taker_id, 2);
    }

    #[test]
    fn test_price_time_priority() {
        let mut book = OrderBook::new(1);
        book.insert(1, 100, 10, Side::Bid);
        book.insert(2, 100, 10, Side::Bid); // same price, later
        book.insert(3, 101, 10, Side::Bid); // better price
        assert_eq!(book.best_bid(), Some(101));
        assert!(book.is_bid_sorted());
    }

    #[test]
    fn test_cancel() {
        let mut book = OrderBook::new(1);
        book.insert(1, 100, 10, Side::Bid);
        assert!(book.cancel(1));
        assert_eq!(book.best_bid(), None);
        assert!(!book.cancel(999)); // not found
    }

    #[test]
    fn test_tick_alignment() {
        let book = OrderBook::new(5);
        // This would panic:
        // book.insert(1, 101, 10, Side::Bid);
        let mut book = OrderBook::new(5);
        book.insert(1, 100, 10, Side::Bid);
        book.insert(2, 105, 10, Side::Ask);
        assert_eq!(book.spread(), Some(5));
    }

    #[test]
    fn test_partial_fill() {
        let mut book = OrderBook::new(1);
        book.insert(1, 100, 10, Side::Ask);
        let fills = book.insert(2, 100, 3, Side::Bid);
        assert_eq!(fills.len(), 1);
        assert_eq!(fills[0].qty, 3);
        assert_eq!(book.ask_count(), 1); // residual remains
    }
}
