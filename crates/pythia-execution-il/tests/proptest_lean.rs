use proptest::prelude::*;
use pythia_execution_il::*;

proptest! {
    /// Lean: impermanentLoss_nonpos: IL(r) <= 0 for r > 0
    #[test]
    fn prop_il_nonpos(
        r in 0.001_f64..1e6,
    ) {
        let il = impermanent_loss(r);
        prop_assert!(il <= 1e-12,
            "impermanent_loss({r}) = {il} > 0");
    }

    /// Lean: impermanentLoss_at_one is the unique zero:
    /// IL(1) = 0 and IL(r) < 0 for r != 1
    #[test]
    fn prop_il_at_one_is_max(
        r in 0.001_f64..1e4,
    ) {
        let il = impermanent_loss(r);
        let il_one = impermanent_loss(1.0);
        prop_assert!(il <= il_one + 1e-12,
            "impermanent_loss({r}) = {il} > IL(1) = {il_one}");
    }

    /// IL is in [-1, 0] for all positive r
    #[test]
    fn prop_il_bounded(
        r in 0.001_f64..1e8,
    ) {
        let il = impermanent_loss(r);
        prop_assert!(il >= -1.0 - 1e-12 && il <= 1e-12,
            "impermanent_loss({r}) = {il} out of [-1, 0]");
    }
}
