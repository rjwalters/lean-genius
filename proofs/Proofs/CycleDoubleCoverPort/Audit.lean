import Proofs.CycleDoubleCoverPort.Main

-- Ported from openai/cdc-lean, Audit.lean, vendored with adaptation per operator
-- decision 2026-08-03. Part of epic #37507.

/-
# Kernel trust audit

Building this module displays the axiom dependencies of the critical constructions of
the Cycle Double Cover port. The expected output for every line below contains only
Lean's standard `propext`, `Classical.choice` and `Quot.sound` — in particular no
`sorryAx` (which would mean an unfinished proof) and no `Lean.ofReduceBool` (which
would mean a `native_decide` in the trust base).

This mirrors upstream `CDCLean/Audit.lean`, extended with the Jaeger--Kilpatrick
eight-flow theorem, which upstream did not list. `cycleDoubleCover_of_bridgeless` is
the headline result and the declaration that replaced the axiom of the same name.

`cycleDoubleCover_of_sixFlow` takes Seymour's six-flow theorem as an *explicit
hypothesis*, so it too is axiom-free; it is a conditional statement, not a conditional
proof, and nothing else in the development depends on it.

## Provenance, licensing and attribution

Ported from `openai/cdc-lean`, `CDCLean/Audit.lean`, vendored with adaptation per the
operator decision recorded on #37507 (comment of 2026-08-03). `openai/cdc-lean`
carries **no license file**, so default copyright applies -- it is *not* public
domain, and the absence of a license is not a grant. A permissive licence was
requested upstream on 2026-07-12 (openai/cdc-lean#4); there was no response and the
upstream issue tracker has since been disabled. The operator's decision is an
explicit *risk acceptance*, not a license grant.

The commands below name declarations of this port, and the commentary above was
written for this repository, so the upstream expression left here is minimal -- but
the file is classified as vendored regardless, conservatively. See
`LICENSE-STATUS.md` in this directory for the inventory of vendored files and the
per-file re-derivation plan (tracking issue #43638).
-/

#print axioms CycleDoubleCover.local_pair_parity
#print axioms CycleDoubleCover.local_dual_identity
#print axioms CycleDoubleCover.compatibility_solvable
#print axioms CycleDoubleCover.cubic_even_double_cover
#print axioms CycleDoubleCover.FiniteGraph.expansionGraph_bridgeless
#print axioms CycleDoubleCover.FiniteGraph.tutteFlowCardinalityInvariant
#print axioms CycleDoubleCover.FiniteGraph.IndexedEvenDoubleCover.toCycleDoubleCover
#print axioms CycleDoubleCover.FiniteGraph.jaegerKilpatrickEightFlow
#print axioms CycleDoubleCover.cycleDoubleCover_of_gammaFlow
#print axioms CycleDoubleCover.cycleDoubleCover_of_sixFlow
#print axioms CycleDoubleCover.cycleDoubleCover_of_bridgeless
