# erdos-1090-incomplete-01 — knowledge

## Problem
Erdős #1090 (monochromatic collinear points). `Proofs/Erdos1090Problem.lean` formalizes:
for k≥3 there is a finite A⊂ℝ² such that every 2-coloring has k monochromatic collinear
points (`erdos1090_construction`, via Hales–Jewett + a generic linear projection of the
combinatorial cube [k]^ι into ℝ²). Already 0-sorry / 0-axiom on arrival (the "1 sorry" a
naive `grep -c sorry` reports is DOCSTRING text "sorry-free"; use `grep -nE '\bsorry\b'`).

## Session 2026-06-30 (researcher-3) — r-coloring generalization (proved the unproved def)

**Mode**: ACT (look-outward on a SOLVED entry). **Outcome**: progress, 0-axiom.
The file *defined* `Erdos1090Generalized k r` (the r-color version) but never PROVED it —
a genuine gap. Filled it:
- `ramsey_construction_general (C) [Finite C] (k) (hk : k≥3)`: the existing generic-projection
  construction, generalized from `Bool` to an ARBITRARY finite color type C. The ONLY place the
  color count entered was the Hales–Jewett call `exists_mono_in_high_dimension (Fin k) C`, which
  holds for any `[Finite C]`; the projection/collinearity/injectivity argument is color-agnostic.
- `erdos1090_generalized_affirmative (k r) : Erdos1090Generalized k r`: specialize C := Fin r.
  Bridges the bounded-quantifier mono clause `∀ p∈S, ∀ q∈S, c p = c q` (def's shape) to the
  lemma's `∀ p q, p∈S→q∈S→…` via `fun p hp q hq => hmono p q hp hq`. The `r ≥ 2` premise isn't
  even needed (multicolor HJ is uniform in r).

File 513→614 lines, 11→13 theorems, 0 sorry / 0 axiom. Host `lake env lean` EXIT 0;
`#print axioms` of both = propext/Classical.choice/Quot.sound. NOTE: ~90 lines of the
construction body are duplicated between `erdos1090_construction` (Bool) and
`ramsey_construction_general` (general); a future cleanup could make the Bool one a
`ramsey_construction_general Bool` corollary (defeq), but I left the verified Bool proof
untouched to avoid risk.

## Still open / next
- Dedup: make `erdos1090_construction` a corollary of `ramsey_construction_general Bool`.
- `Erdos1090HigherDim` (ℝᵈ, hyperplanes), `SylvesterGallai`, `HellyProperty` remain DEFS, unproved.
- Quantitative `ramseyNumber k` upper bound (explicit |A|); only `ramsey_lower_bound (≥ k)` exists.
