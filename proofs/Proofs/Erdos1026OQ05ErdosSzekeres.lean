/-
# erdos-1026-oq-05 (Erdős–Szekeres companion): the product bound `n ≤ LIS · LDS`

`Erdos1026OQ05IncreasingIdentity.lean` proves the exact Mirsky/Dilworth min–max identity
`minIncreasingParts seq = LDS seq` for a sequence of distinct reals, and constructs the explicit
witnessing decomposition `mirskyIncreasingDecomposition` — a covering of all `n` indices by exactly
`LDS seq` strictly-*increasing* parts.

This file extracts the classical **Erdős–Szekeres product bound** as a structural consequence of
that covering:

    n ≤ LIS seq · LDS seq                              (`card_le_LIS_mul_LDS`)

for a sequence of distinct reals. The derivation is the textbook counting argument, but phrased
entirely in the gallery's own `LIS`/`LDS`/decomposition language:

* **Cell-counting for increasing decompositions** (`incrDecomposition_numParts_lower_bound`): the
  increasing analogue of the committed `monotonicDecomposition_numParts_lower_bound`. The parts'
  index maps assemble into a surjection from the disjoint union of the parts onto `Fin n`, so
  `n ≤ ∑ (part lengths)`; every part is strictly increasing, hence has length `≤ LIS seq`, and
  summing this constant over the `numParts` parts gives `n ≤ numParts · LIS seq`.

* **Product bound**: apply the cell count to `mirskyIncreasingDecomposition`, whose part count is
  exactly `LDS seq`. This charges each of the `LDS seq` increasing parts its `LIS seq` budget:
  `n ≤ LDS seq · LIS seq`.

From the product bound the classical Erdős–Szekeres pigeonhole theorem follows by contradiction:

    r · s < n  ⟹  r < LIS seq  ∨  s < LDS seq        (`erdos_szekeres`)

and, specialising `r = s = k`, any sequence of more than `k²` distinct reals carries a strictly
monotone subsequence of length `> k` (`exists_long_monotone`, `lt_max_LIS_LDS`).

Mathlib has its own `Theorems100.erdos_szekeres`; the point here is a *self-contained* derivation
from this entry's Mirsky covering identity, giving the product/pigeonhole form directly in the
`LIS`/`LDS` vocabulary the rest of the OQ-05 development uses (distinctness is genuinely required:
a constant sequence has `LIS = LDS = 1` yet arbitrary length).

No axioms, no sorries.
-/

import Mathlib
import Proofs.Erdos1026OQ05IncreasingIdentity

open Finset

namespace Erdos1026OQ05ErdosSzekeres

open Erdos1026OQ05 Erdos1026OQ05IncreasingIdentity

variable {n : ℕ}

/-! ## Cell-counting for increasing decompositions -/

/-- **Increasing cell count.** The increasing analogue of the committed
`monotonicDecomposition_numParts_lower_bound`: every decomposition of a length-`n` sequence into
strictly-increasing parts satisfies `n ≤ numParts · LIS seq`.

Because each part is *increasing* (not merely monotone) it can only be as long as `LIS seq`, so this
charges each part the sharper `LIS` budget rather than `max (LIS, LDS)`.

Proof: the parts' index maps package into one map `g` out of the disjoint union
`Σ i, Fin (length of part i)`; the covering condition says `g` is surjective, so
`n = |Fin n| ≤ Σ i, (length of part i)`. Each length is `≤ LIS seq`, and summing the constant over
the `numParts` parts gives the claim. -/
theorem incrDecomposition_numParts_lower_bound
    (seq : RealSeq n) (D : IncreasingDecomposition n seq) :
    n ≤ D.numParts * LIS seq := by
  classical
  -- The parts' index maps, packaged as one map out of the disjoint union of the parts.
  let g : (Σ i : Fin D.numParts, Fin (D.parts i).1) → Fin n :=
    fun p => (D.parts p.1).2.indices p.2
  -- Covering says this map is surjective.
  have hsurj : Function.Surjective g := by
    intro k
    obtain ⟨i, m, hm, hk⟩ := D.covering k
    exact ⟨⟨i, ⟨m, hm⟩⟩, hk⟩
  -- Hence `n = |Fin n| ≤ |Σ i, Fin (part i length)| = Σ i, (part i length)`.
  have hcard : Fintype.card (Fin n)
      ≤ Fintype.card (Σ i : Fin D.numParts, Fin (D.parts i).1) :=
    Fintype.card_le_of_surjective g hsurj
  rw [Fintype.card_fin, Fintype.card_sigma] at hcard
  simp only [Fintype.card_fin] at hcard
  refine hcard.trans ?_
  -- Each part is strictly increasing, so its length is at most `LIS seq`.
  calc ∑ i, (D.parts i).1
      ≤ ∑ _i : Fin D.numParts, LIS seq :=
        Finset.sum_le_sum (fun i _ => len_le_LIS_of_increasing (D.increasing i))
    _ = D.numParts * LIS seq := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-! ## The Erdős–Szekeres product bound -/

/-- **Erdős–Szekeres product bound.** For a sequence of distinct reals,
`n ≤ LIS seq · LDS seq`.

Proof: the Mirsky increasing decomposition covers all `n` indices with exactly `LDS seq`
strictly-increasing parts, and `incrDecomposition_numParts_lower_bound` charges each part its `LIS`
budget, giving `n ≤ LDS seq · LIS seq`. -/
theorem card_le_LIS_mul_LDS (seq : RealSeq n) (hinj : Function.Injective seq) :
    n ≤ LIS seq * LDS seq := by
  -- `(mirskyIncreasingDecomposition seq hinj).numParts` is `LDS seq` definitionally.
  have h : n ≤ LDS seq * LIS seq :=
    incrDecomposition_numParts_lower_bound seq (mirskyIncreasingDecomposition seq hinj)
  rwa [mul_comm] at h

/-! ## The classical pigeonhole theorem and its monotone-run corollary -/

/-- **Erdős–Szekeres theorem (product / pigeonhole form).** For a sequence of distinct reals, if
`r · s < n` then either the longest strictly-increasing subsequence has length `> r`, or the longest
strictly-decreasing subsequence has length `> s`.

Contrapositive of the product bound: `LIS ≤ r` and `LDS ≤ s` would force
`n ≤ LIS · LDS ≤ r · s < n`. -/
theorem erdos_szekeres (seq : RealSeq n) (hinj : Function.Injective seq)
    {r s : ℕ} (h : r * s < n) : r < LIS seq ∨ s < LDS seq := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  -- h1 : LIS seq ≤ r, h2 : LDS seq ≤ s
  have hchain : n ≤ r * s :=
    (card_le_LIS_mul_LDS seq hinj).trans (Nat.mul_le_mul h1 h2)
  exact absurd hchain (not_le.mpr h)

/-- Any sequence of more than `k²` distinct reals carries a strictly monotone subsequence of length
`> k`: `k < LIS seq ∨ k < LDS seq`. The `r = s = k` specialisation of `erdos_szekeres`. -/
theorem exists_long_monotone (seq : RealSeq n) (hinj : Function.Injective seq)
    {k : ℕ} (h : k * k < n) : k < LIS seq ∨ k < LDS seq :=
  erdos_szekeres seq hinj h

/-- Packaged form: more than `k²` distinct reals force the *longest* monotone run (of either type) to
exceed `k`, i.e. `k < max (LIS seq) (LDS seq)`. -/
theorem lt_max_LIS_LDS (seq : RealSeq n) (hinj : Function.Injective seq)
    {k : ℕ} (h : k * k < n) : k < max (LIS seq) (LDS seq) := by
  rcases exists_long_monotone seq hinj h with h' | h'
  · exact lt_of_lt_of_le h' (le_max_left _ _)
  · exact lt_of_lt_of_le h' (le_max_right _ _)

/-! ## Canonical (sharp-threshold) form

The `erdos_szekeres` lemma above is stated in the strict `r · s < n` form (`LIS > r` or
`LDS > s`). The recognizable textbook statement of the theorem instead pins the *exact*
Erdős–Szekeres threshold: **any sequence of `(r-1)(s-1) + 1` distinct reals contains a
strictly increasing subsequence of length `r` or a strictly decreasing subsequence of
length `s`.** The number `(r-1)(s-1) + 1` is the sharp one — the block construction of
length `(r-1)(s-1)` with `LIS = r-1`, `LDS = s-1` shows no smaller threshold works.

This is the same counting content as `erdos_szekeres`, restated at the canonical
threshold; it is derived, not re-proved. -/

/-- **Erdős–Szekeres theorem (canonical threshold form).** For a sequence of distinct
reals of length `n`, if `(r-1)(s-1) < n` (equivalently `n ≥ (r-1)(s-1) + 1`) then there is
a strictly increasing subsequence of length `r` or a strictly decreasing subsequence of
length `s`: `r ≤ LIS seq ∨ s ≤ LDS seq`.

This is the textbook statement with the sharp Erdős–Szekeres number `(r-1)(s-1)+1`; it
follows from the strict form `erdos_szekeres` applied at `(r-1, s-1)`, converting each
`· - 1 < ·` to `· ≤ ·` (valid for all `r, s : ℕ`, including the degenerate `r = 0` or
`s = 0`). -/
theorem erdos_szekeres_threshold (seq : RealSeq n) (hinj : Function.Injective seq)
    {r s : ℕ} (h : (r - 1) * (s - 1) < n) : r ≤ LIS seq ∨ s ≤ LDS seq := by
  rcases erdos_szekeres seq hinj h with h' | h'
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

end Erdos1026OQ05ErdosSzekeres
