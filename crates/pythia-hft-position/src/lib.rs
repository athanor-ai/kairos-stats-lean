//! # pythia-hft-position
//!
//! Position tracking with proven limit enforcement and PnL attribution.
//!
//! ## Lean specification (`Pythia.Finance.HFT.PositionTracker`)
//!
//! - **Buy increases position** (`buy_increases_position`)
//! - **Sell decreases position** (`sell_decreases_position`)
//! - **PnL = qty * (mark - entry)** (`pnl_from_trade`)
//! - **Long profit when mark > entry** (`long_profit`)
//! - **Short profit when mark < entry** (`short_profit`)
//! - **Position within limit ⟹ |pos| ≤ limit** (`within_limit`)
//! - **Flat position = zero risk** (`flat_zero_risk`)

/// A position in a single instrument with limit enforcement.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Position {
    pub qty: f64,
    pub avg_entry: f64,
    pub limit: f64,
}

/// Result of attempting a fill.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum FillResult {
    Filled { new_pos: Position },
    Rejected,
}

impl Position {
    /// Flat position (zero quantity).
    pub fn flat(limit: f64) -> Self {
        Self { qty: 0.0, avg_entry: 0.0, limit }
    }

    /// Is this position flat?
    ///
    /// # Lean theorem: `flat_zero_risk`
    /// `0 * price_change = 0`
    pub fn is_flat(&self) -> bool {
        self.qty == 0.0
    }

    /// Attempt a fill. Returns `Rejected` if it would breach the limit.
    ///
    /// # Lean theorems:
    /// - `buy_increases_position`: positive qty increases position
    /// - `sell_decreases_position`: negative qty decreases position
    /// - `within_limit`: `|new_pos| ≤ limit`
    pub fn fill(&self, fill_qty: f64, fill_price: f64) -> FillResult {
        let new_qty = self.qty + fill_qty;
        if new_qty.abs() > self.limit {
            return FillResult::Rejected;
        }
        let new_entry = if new_qty.abs() < 1e-15 {
            0.0
        } else if fill_qty.signum() == self.qty.signum() || self.qty == 0.0 {
            (self.qty * self.avg_entry + fill_qty * fill_price) / new_qty
        } else {
            if new_qty.signum() == self.qty.signum() {
                self.avg_entry
            } else {
                fill_price
            }
        };
        FillResult::Filled {
            new_pos: Position { qty: new_qty, avg_entry: new_entry, limit: self.limit },
        }
    }

    /// Unrealized PnL at a given mark price.
    ///
    /// # Lean theorem: `pnl_from_trade`
    /// `qty * (mark - entry) = qty * mark - qty * entry`
    ///
    /// # Lean theorem: `long_profit`
    /// Positive when long and mark > entry.
    ///
    /// # Lean theorem: `short_profit`
    /// Positive when short and mark < entry.
    pub fn unrealized_pnl(&self, mark_price: f64) -> f64 {
        self.qty * (mark_price - self.avg_entry)
    }

    /// Market risk exposure (zero when flat).
    pub fn market_risk(&self, price_change: f64) -> f64 {
        self.qty * price_change
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn buy_increases() {
        let p = Position::flat(1000.0);
        if let FillResult::Filled { new_pos } = p.fill(100.0, 50.0) {
            assert!(new_pos.qty > p.qty);
        } else {
            panic!("fill rejected");
        }
    }

    #[test]
    fn sell_decreases() {
        let p = Position { qty: 500.0, avg_entry: 100.0, limit: 1000.0 };
        if let FillResult::Filled { new_pos } = p.fill(-200.0, 105.0) {
            assert!(new_pos.qty < p.qty);
        } else {
            panic!("fill rejected");
        }
    }

    #[test]
    fn limit_enforced() {
        let p = Position::flat(100.0);
        assert_eq!(p.fill(200.0, 50.0), FillResult::Rejected);
    }

    #[test]
    fn long_profit() {
        let p = Position { qty: 100.0, avg_entry: 50.0, limit: 1000.0 };
        assert!(p.unrealized_pnl(55.0) > 0.0);
    }

    #[test]
    fn short_profit() {
        let p = Position { qty: -100.0, avg_entry: 50.0, limit: 1000.0 };
        assert!(p.unrealized_pnl(45.0) > 0.0);
    }

    #[test]
    fn flat_zero_risk() {
        let p = Position::flat(1000.0);
        assert_eq!(p.market_risk(100.0), 0.0);
    }

    #[test]
    fn within_limit_after_fill() {
        let p = Position::flat(100.0);
        if let FillResult::Filled { new_pos } = p.fill(50.0, 100.0) {
            assert!(new_pos.qty.abs() <= new_pos.limit);
        }
    }
}
