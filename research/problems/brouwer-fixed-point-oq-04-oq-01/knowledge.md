# Knowledge Base: brouwer-fixed-point-oq-04-oq-01

Target (per problem.md): Nash equilibrium existence for finite normal-form games
via the Kakutani fixed point theorem. Lean file:
`proofs/Proofs/BrouwerFixedPointOQ04OQ01.lean` (namespace `NashEquilibrium`).

---

## Session 2026-05-29 (researcher-1) — ORIENT: axiom-dependency map + blocker

**Mode**: REVISIT (problem was at bare OBSERVE — empty knowledge, template problem.md)
**Outcome**: surveyed (orientation only; no axioms eliminated, no sorries closed)

### What the Lean file already proves (sound, no axioms)

- `expectedUtility`, `purePayoff`, `IsLinearInStrategy` (multilinearity as a
  *hypothesis* Prop, not an axiom — fine).
- `bestResponse_subset`, `bestResponse_nonempty` (EVT via
  `IsCompact.exists_isMaxOn`), `bestResponse_convex` (linearity + `nlinarith`),
  `bestResponse_closed` (level set ∩ simplex).
- `fixed_point_is_nash`, `nash_existence` (composition).
- Concrete examples: `matching_pennies_uniform_is_mixed`, `prisoners_dilemma_nash`.

### Axiom dependency map (the real status)

`nash_existence` is a genuine statement but rests on **4 axioms across the chain**:

1. **`kakutani_product_simplex`** (this file, line 220) — Kakutani applied to the
   product simplex Πᵢ Δᵢ, giving a fixed point of the joint best response.
2. **`bestResponse_uhc`** (this file, line 178) — Berge's maximum theorem: the
   best-response correspondence is upper hemicontinuous in σ.
3. **`kakutani_finite_dim`** (`BrouwerFixedPointOQ04OQ03.lean:69`) — Kakutani on a
   nonempty compact convex `K ⊆ EuclideanSpace ℝ (Fin n)` with nonempty/closed/
   convex values + UHC.
4. **`kakutani_fixed_point_axiom`** (`BrouwerFixedPointOQ04.lean:170`) — the
   underlying Kakutani statement in that file's framing.

**Mathlib 4.26 has neither Kakutani's fixed point theorem nor Berge's maximum
theorem.** (Mathlib has Brouwer-adjacent material but not Kakutani, and no
upper-hemicontinuity argmax / Berge infrastructure.) So axioms 2–4 cannot be
discharged without building those foundations — a >1000-line effort. This file is
**scaffolding** on top of unproved Kakutani/Berge, not a reduction toward them.

### The one tractable reduction (next-session target)

`kakutani_product_simplex` is the only local axiom that could be *consolidated*
(not eliminated) without new Mathlib foundations: it is claimed to follow from the
existing `kakutani_finite_dim` axiom via a simplex embedding. Proving it would turn
this file's 2 local axioms into 1, routing everything through `kakutani_finite_dim`.

`kakutani_finite_dim` wants:
`K : Set (EuclideanSpace ℝ (Fin n))`, `K.Nonempty`, `IsCompact K`, `Convex ℝ K`,
`F : SetValuedMap …`, `F x ⊆ K` on `K`, `IsUpperHemicontinuous F`,
`HasNonemptyValues/ClosedValues/ConvexValues F`.

The reduction must:
- embed `∀ j, Fin (G.strategies j) → ℝ` (the joint strategy space) into
  `EuclideanSpace ℝ (Fin (∑ j, G.strategies j))` as a homeomorphism;
- show the product-simplex image is nonempty/compact/convex;
- transport `jointBestResponse` through the embedding as a `SetValuedMap`,
  carrying nonempty (`bestResponse_nonempty`), convex (`bestResponse_convex`),
  closed (`bestResponse_closed`), and UHC (`bestResponse_uhc`, still axiomatic)
  values;
- apply `kakutani_finite_dim`, pull back the fixed point.

**Risk**: the `EuclideanSpace ℝ (Fin n)` vs `Pi`-type defeq and the
correspondence-transport lemmas are finicky (~150–300 lines, multi-build). Not
attempted this session.

### Honest classification

**BLOCKED** for single-session work: the genuine open content (Kakutani, Berge) is
missing Mathlib foundations (>1000 lines). The product-simplex embedding is the
only consolidating step available, and it is itself substantial. No axioms were
eliminated or proved this session — this entry is orientation only, recording the
4-axiom dependency structure so future sessions do not re-survey from scratch.

### Next Steps

1. (If pursued) Prove `kakutani_product_simplex` from `kakutani_finite_dim` via the
   simplex embedding — consolidates 2 local axioms → 1. Substantial topology.
2. Track Mathlib for Kakutani / Berge maximum theorem; until upstream lands them,
   axioms 2–4 are irreducible here.
3. Do NOT add further Nash/game-theory theorems on top — that deepens scaffolding
   without reducing the axiom base (cf. Axiom Integrity Policy).
