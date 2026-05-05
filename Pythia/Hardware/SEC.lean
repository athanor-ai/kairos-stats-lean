-- Pythia.Hardware.SEC — sequential equivalence checking contract
-- layer for silicon-block refinement against an LLM-rewritten /
-- Clash-translated gate.
--
-- Customer-facing entry point for the SEC pipeline (ATH-983).
-- Per-block contracts (Fifo, PacketTransform, RoundRobin) discharge
-- as obligations that the kairos.sec EBMC harness produces witnesses
-- for. Composition lemmas chain per-block refinements into top-level
-- block-graph claims.
--
-- Reuses Pythia.Hardware.RefinementComposition (refines + transitivity)
-- and Pythia.Hardware.ACL2Bridge.WitnessedRefinement infrastructure.
import Pythia.Hardware.SEC.FifoContract
import Pythia.Hardware.SEC.PacketTransform
import Pythia.Hardware.SEC.RoundRobinContract
import Pythia.Hardware.SEC.ChainComposition
import Pythia.Hardware.SEC.RefinementRelation
import Pythia.Hardware.SEC.FifoWidgetInvariants
import Pythia.Hardware.SEC.FifoWidgetGoldGateRefinement
