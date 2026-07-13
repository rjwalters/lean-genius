# Current State

**Phase**: ORIENT
**Since**: 2026-06-14 (S1, researcher-3)
**Iteration**: 2
**Last Updated**: 2026-06-15 (researcher-6, **S2 ORIENT** — master-status re-confirm + map-API gap sharpened + obstruction cert)

## Problem

**OQ-04-OQ-01**: Can `JordanHolderLattice (Subgroup G)` be contributed upstream
to Mathlib? The parent entry `abel-ruffini-galois-extensions-oq-04` formalizes
the Jordan-Hölder theorem for finite groups by instantiating
`JordanHolderLattice (Subgroup G)`, which is an explicit Mathlib TODO.

## S2 ORIENT (2026-06-15, researcher-6) — build-free; Docker down

**OQ still OPEN at master.** The `Order/JordanHolder.lean` TODO/NOTE block (L51-68)
is present at both the repo pin `v4.26.0` and current master (master grew 420→454
LOC, now under `@[expose] public section`; the TODO text is unchanged). No
`JordanHolderLattice (Subgroup G)` instance has landed (`search/code` → only the
TODO mention + `nolints.json`); no `ModularLattice` instance either. The OQ does
not auto-close.

**Map-API gap sharpened (knowledge.md Insight 4).** The TODO's second ask — "an API
for mapping composition series across homomorphisms" — has its generic *carrier*
already upstream: `RelSeries.map (p) (f : r.Hom s)` (`Order/RelSeries.lean:372`, at
pin AND master). The missing piece is the group-specific `RelSeries.Hom` builder:
the naive `Subgroup.map φ` is **not** an `IsMaxNorm`-preserving hom because maximal-
normality is not stable under images with nontrivial kernel. Witnessed durably in
the cert (`C4 ↠ C2`: covering `{e} ◁ ⟨g²⟩` collapses to `{e} ◁ {e}`). So the API
must restrict φ (injective) or route quotient steps through the second iso theorem.

**Cert extended.** `verify_jordan_holder_lattice.py` adds `check_map_obstruction()`
(C4→C2 quotient); full script still exits 0 — V4/C6/S3/D4 A1·A2 PASS + obstruction
PASS. No Lean built (Docker down; this is ORIENT, no ACT artifact).

## S1 ORIENT verdict (build-free; Docker down)

**The instance is already PROVED locally (0 sorries, 0 axioms). The Mathlib TODO
is OPEN at master, but it is a PACKAGING/design problem (global-instance
diamonds), NOT a provability gap. Upstreaming is feasible as a *non-global,
namespaced* instance, mirroring how Mathlib already handles modules.**

### Local state (this repo)
`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ04.lean` (234 lines, **0 sorries,
0 `axiom` declarations**) provides:
- `instJordanHolderLatticeSubgroup : JordanHolderLattice (Subgroup G)` with
  `IsMaximal := IsMaxNorm` (maximal *normal* subgroup), and full proofs of the
  two non-trivial fields:
  - `sup_eq_of_isMaximal` (A1) — via `subgroupOf_sup` + maximality.
  - `isMaximal_inf_left_of_isMaximal_sup` (A2) — via element-wise `Subgroup.mem_sup`.
- `jordan_holder_subgroups` / `jordan_holder_finite_groups` (from
  `CompositionSeries.jordan_holder`).

### Mathlib master status (surveyed 2026-06-14, `Mathlib/Order/JordanHolder.lean`)
- TODO (L51-68) is **still present**: "Provide instances of `JordanHolderLattice`
  for subgroups... It is not entirely clear how this should be done. Possibly
  there should be no global instances..." The concern is concrete: a future
  `JordanHolderLattice` instance for `ModularLattice` would **clash** with the
  module instance (different `Iso`), so "at least one of these instances should
  not be a global instance."
- NOTE (L68): the existing **module** instance is
  `JordanHolderModule.instJordanHolderLattice` — a *scoped, non-global*
  instance in its own namespace, NOT routed through `ModularLattice`.

### Upstreaming recommendation
Package the subgroup instance the SAME way the module instance is packaged:
a non-global `instance` inside a dedicated namespace (e.g.
`JordanHolderSubgroup`) rather than the current global
`noncomputable instance`. This sidesteps the diamond the TODO worries about and
matches the precedent the Mathlib NOTE points to. Remaining upstream API work
flagged by the TODO: "an API for mapping composition series across
homomorphisms" (independent of this instance).

### Numerical cert (durable, `verify_jordan_holder_lattice.py`)
Brute-force subgroup-lattice check of A1 and A2 (under `IsMaxNorm`) on concrete
groups — a regression oracle for the Lean instance:
- V4 (Klein, 3 maximal subgroups): A1 6/6, A2 6/6.
- C6: A1 2/2, A2 2/2.  S3 (only A3 maximal-normal): vacuous, consistent.
- D4 (order 8, non-abelian): A1 18/18, A2 18/18.
All PASS.

## Next action
ACT here is not new mathematics — it is an upstream Mathlib PR (re-namespace the
instance + the composition-series-map API the TODO requests). Docker-gated for
build verification of the re-namespaced instance. Re-check the TODO at master on
future cycles; if someone lands the subgroup instance upstream, this OQ closes.
