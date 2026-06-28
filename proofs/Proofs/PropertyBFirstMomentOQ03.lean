/-
  OQ-03: Non-uniform sharpening of the first-moment Property B criterion

  Parent `PropertyBFirstMoment.lean` proves Erdős 1963 for *uniform* hypergraphs:
  a `k`-uniform family with `< 2^(k-1)` edges has Property B (is 2-colorable).
  That bound only uses the edge *count*. This file sharpens the same first-moment
  argument to **arbitrary edge sizes**: the genuine Erdős criterion

      ∑_{e ∈ E} 2^(1-|e|) < 1   ⟹   E has Property B,

  stated over the natural numbers (no division) as `2 · ∑_{e} 2^(n-|e|) < 2^n`,
  where `n = |V|`. Large edges contribute geometrically less, so a family with
  many large edges and few small ones is 2-colorable even when its raw edge count
  far exceeds `2^(k-1)` for the smallest edge size `k`. The uniform theorem is the
  special case `|e| = k` (proved here as a corollary, confirming the refinement is
  faithful).

  This is the **sharp form of the first-moment lower bound**. It is NOT the
  Radhakrishnan–Srinivasan bound `m(k) = Ω(2^k · √(k/log k))` that OQ-03 ultimately
  targets: that extra `√(k/log k)` factor requires a *random recoloring* (alteration)
  argument — a second round that repairs the monochromatic edges left by the first —
  which is beyond the single-round first moment formalized here. See the knowledge
  base for the recoloring roadmap and tractability assessment.

  Status: 0 sorries, 0 axioms.
-/
import Proofs.PropertyBFirstMoment

namespace ProbMethod.PropertyB

open Finset BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Non-uniform first-moment criterion for Property B.** A finite edge family `E`
of nonempty edges (each of size `≤ n = |V|`) is 2-colorable as soon as the weighted
edge sum satisfies `2 · ∑_{e ∈ E} 2^(n - |e|) < 2^n` — equivalently `∑_e 2^(1-|e|) < 1`.

The proof is the parent's first moment over the `2^n` uniform 2-colorings, now without
the uniformity assumption: the total `(coloring, monochromatic edge)` incidence count is
`∑_{e} 2 · 2^(n-|e|)` (each edge `e` is monochromatic under exactly `2 · 2^(n-|e|)`
colorings, by `card_mono`), and when that is `< 2^n` the first moment principle
(`exists_zero_of_sum_lt_card`) hands back a coloring with no monochromatic edge. -/
theorem property_b_of_weighted_first_moment
    (E : Finset (Finset V))
    (hne : ∀ e ∈ E, e.Nonempty)
    (hsmall : 2 * ∑ e ∈ E, 2 ^ (Fintype.card V - e.card) < 2 ^ Fintype.card V) :
    ∃ c : V → Bool, ∀ e ∈ E, ¬ Mono e c := by
  -- ∑_c (#monochromatic edges under c) = ∑_e 2·2^(n-|e|)
  have hsum :
      (∑ c : V → Bool, (E.filter (fun e => Mono e c)).card)
        = ∑ e ∈ E, 2 * 2 ^ (Fintype.card V - e.card) := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro e he
    rw [← Finset.card_filter, card_mono e (hne e he)]
  have hcard : (univ : Finset (V → Bool)).card = 2 ^ Fintype.card V := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
  -- strict inequality: incidence sum < number of colorings
  have hlt :
      (∑ c : V → Bool, (E.filter (fun e => Mono e c)).card)
        < (univ : Finset (V → Bool)).card := by
    rw [hsum, hcard, ← Finset.mul_sum]
    exact hsmall
  -- first moment principle yields a coloring with zero monochromatic edges
  obtain ⟨c, -, hc⟩ := exists_zero_of_sum_lt_card hlt
  refine ⟨c, ?_⟩
  have hempty : E.filter (fun e => Mono e c) = ∅ := Finset.card_eq_zero.mp hc
  intro e he
  exact (Finset.filter_eq_empty_iff.mp hempty) he

/-- **The uniform Erdős bound is the special case.** Re-deriving `property_b_two_colorable`
(`k`-uniform, `< 2^(k-1)` edges) from the non-uniform criterion: with every `|e| = k` the
weighted sum collapses to `|E| · 2^(n-k)`, and `|E| < 2^(k-1)` is exactly
`2 · |E| · 2^(n-k) < 2^n`. This confirms the refinement faithfully extends the parent. -/
theorem property_b_two_colorable_of_uniform
    (E : Finset (Finset V)) (k : ℕ) (hk : 1 ≤ k)
    (huniform : ∀ e ∈ E, e.card = k)
    (hsmall : E.card < 2 ^ (k - 1)) :
    ∃ c : V → Bool, ∀ e ∈ E, ¬ Mono e c := by
  rcases E.eq_empty_or_nonempty with hE | hE
  · exact ⟨fun _ => true, by simp [hE]⟩
  obtain ⟨e₀, he₀⟩ := hE
  have hkn : k ≤ Fintype.card V := by
    have hle : e₀.card ≤ Fintype.card V := by
      rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ e₀)
    rw [huniform e₀ he₀] at hle; exact hle
  apply property_b_of_weighted_first_moment E
  · intro e he; exact Finset.card_pos.mp (by rw [huniform e he]; omega)
  · -- 2 · ∑_e 2^(n-k) = 2 · |E| · 2^(n-k) < 2^n
    have hsumc : (∑ e ∈ E, 2 ^ (Fintype.card V - e.card))
        = E.card * 2 ^ (Fintype.card V - k) := by
      rw [Finset.sum_congr rfl (fun e he => by rw [huniform e he]),
        Finset.sum_const, smul_eq_mul]
    rw [hsumc]
    have e1 : (2 : ℕ) ^ Fintype.card V = 2 ^ k * 2 ^ (Fintype.card V - k) := by
      rw [← pow_add]; congr 1; omega
    have ekey : E.card * 2 < 2 ^ k := by
      have e2 : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
        conv_lhs => rw [show k = 1 + (k - 1) by omega]
        rw [pow_add, pow_one]
      rw [e2]; omega
    calc 2 * (E.card * 2 ^ (Fintype.card V - k))
          = (E.card * 2) * 2 ^ (Fintype.card V - k) := by ring
      _ < 2 ^ k * 2 ^ (Fintype.card V - k) :=
          (Nat.mul_lt_mul_right (pow_pos (by norm_num) _)).mpr ekey
      _ = 2 ^ Fintype.card V := e1.symm

/-- **Worked example where non-uniformity is essential.** Over `V = Fin 3` the family
`{{0,1}, {0,1,2}}` mixes a size-2 and a size-3 edge. The weighted sum is
`2^(3-2) + 2^(3-3) = 2 + 1 = 3`, and `2 · 3 = 6 < 8 = 2^3`, so the criterion certifies a
proper 2-coloring. (The uniform theorem does not apply directly — the edges have different
sizes.) -/
theorem mixed_example_two_colorable :
    ∃ c : Fin 3 → Bool, ∀ e ∈ ({{0, 1}, {0, 1, 2}} : Finset (Finset (Fin 3))),
      ¬ Mono e c := by
  apply property_b_of_weighted_first_moment
  · decide
  · decide

end ProbMethod.PropertyB
