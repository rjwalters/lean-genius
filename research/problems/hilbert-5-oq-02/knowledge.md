# hilbert-5-oq-02 — Knowledge

**Open question (parent `hilbert-5`, OQ-02):** *Can the formalization be extended
with actual Lie algebra infrastructure from Mathlib to state the exponential map
properties?*

## Approach (researcher-1, 2026-06-23)

The parent entry `hilbert-5` states the Gleason–Montgomery–Zippin solution of
Hilbert's 5th problem at the level of **axiomatized** deep theorems
(no-small-subgroups, Montgomery–Zippin, von Neumann) — these are out of reach of
present-day Mathlib and should stay axioms. Rather than pile new content on those
axioms, OQ-02 is answered by formalizing the **genuine, verifiable** machinery
that sits underneath the Lie correspondence, using real Mathlib infrastructure:

- **Lie bracket** of an associative algebra `⁅X,Y⁆ = X·Y − Y·X`
  (`Mathlib.Algebra.Lie.OfAssociative`, `LieRing.of_associative_ring_bracket`);
- **Exponential map** of a real Banach algebra `NormedSpace.exp ℝ : 𝔸 → 𝔸`
  (`Mathlib.Analysis.Normed.Algebra.Exponential`).

The exponential map is the concrete bridge from the Lie algebra to the Lie group:
`X` is an infinitesimal generator and `t ↦ exp(t·X)` is the one-parameter
subgroup it generates.

## Deliverable

`proofs/Proofs/Hilbert5OQ02.lean` (namespace `Hilbert5OQ02`, 123 lines, 8
theorems, 1 definition, 0 sorries, **0 axioms**, no `native_decide`), parametric
in any real Banach algebra `[NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]`:

- `commute_of_lie_eq_zero`, `lie_eq_zero_of_commute`, `lie_eq_zero_iff_commute`
  — `⁅X,Y⁆ = 0 ↔ Commute X Y`.
- `exp_add_of_lie_eq_zero` — `⁅X,Y⁆ = 0 ⇒ exp(X+Y) = exp X · exp Y`.
- `oneParam X t := exp ℝ (t • X)` with `oneParam_zero`, `oneParam_add`
  (`γ(s+t) = γ(s)·γ(t)`), `oneParam_neg_mul` (`γ(−t)·γ(t) = 1`), `oneParam_commute`
  (abelian image) — the one-parameter-subgroup homomorphism laws.

Gallery entry: `src/data/proofs/hilbert-5-oq-02/` (meta.json + annotations.json),
status `verified`, badge `mathlib`. Registered in `proofs/Proofs.lean`.

## Build status — VERIFIED

Kernel-verified clean: 0 errors, 0 linter warnings, and `#print axioms` reports
every theorem depends only on `[propext, Classical.choice, Quot.sound]` (the
foundational axioms that do not count) — **0 real axioms, no native_decide**.

The shared docker daemon was down during this session, so verification used the
host fallback documented by the auditor role: from `proofs/`,
`LAKE_UNSAFE=1 ./bin/lake env lean Proofs/Hilbert5OQ02.lean` (single-file
elaboration against the prebuilt Mathlib 4.26.0 oleans, with a `ulimit -v` cap —
no `lake build`). All lemma names were confirmed present in Mathlib 4.26.0
(`NormedSpace.exp_zero`, `exp_add_of_commute`, `LieRing.of_associative_ring_bracket`,
`Commute.smul_left/smul_right`, `neg_add_cancel`).

## Follow-up open questions (generated)

1. Prove `HasDerivAt (fun t => exp (t·X)) X 0` — the derivative of the
   one-parameter subgroup at 0 recovers the generator, tying it to the tangent
   space.
2. Formalize the first-order Baker–Campbell–Hausdorff term
   `exp X · exp Y = exp(X + Y + ½⁅X,Y⁆ + …)`, making the bracket's role in
   non-commuting exponentiation explicit.
