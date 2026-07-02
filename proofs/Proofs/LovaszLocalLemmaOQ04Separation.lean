import Proofs.LovaszLocalLemma

/-
# Lovász Local Lemma OQ-04: asymmetric strictly beats the symmetric threshold

`LovaszLocalLemmaOQ04.lean` shows the asymmetric LLL beats the *union bound*
(`asymLLL_beats_union_bound`) and that distinct weights are genuinely needed
(`asymLLL_asymmetric_weights`). This file sharpens the comparison against the
stronger baseline — the **symmetric** LLL threshold `lllThreshold d = T(d)` from
the parent, which requires every event probability `≤ T(d)` at max degree `d`.

**Result.** There is a two-event, mutually-dependent instance (max degree `d = 1`,
so `T(1) = 1/4`) that satisfies the asymmetric hypothesis with a **positive
avoidance product**, yet whose event `0` has probability `2/5 > 1/4 = T(1)`. Hence
the symmetric LLL (`symmetric_lll_complete` at `d = 1`) does **not** apply, while
the asymmetric LLL does: asymmetric LLL is *strictly stronger* than symmetric LLL
at the same maximum degree, not merely stronger than the union bound.

The mechanism is exactly the asymmetry: putting a small weight `x_1 = 1/10` on the
low-probability event frees the high-probability event to carry weight
`x_0 = 1/2`, admitting `prob_0 ≤ (1/2)(1 - 1/10) = 9/20`, far above the symmetric
cap `1/4`.
-/

namespace ProbMethod.LovaszLocal.OQ04

open ProbMethod.LovaszLocal

/-- The asymmetric LLL hypothesis (restated from `LovaszLocalLemmaOQ04.lean` so this
file depends only on the parent): every weight lies in `[0,1)`, and
`prob i ≤ x i · ∏_{j ∈ adj i} (1 - x j)`. -/
def AsymLLL (n : ℕ) (prob x : Fin n → ℚ) (adj : Fin n → Finset (Fin n)) : Prop :=
  (∀ i, 0 ≤ x i ∧ x i < 1) ∧
  (∀ i, prob i ≤ x i * (adj i).prod (fun j => 1 - x j))

/-- **Asymmetric LLL strictly beats the symmetric threshold.** A max-degree-1,
two-event mutually-dependent instance where the asymmetric hypothesis holds with a
positive avoidance product, but event `0`'s probability `2/5` exceeds the symmetric
threshold `T(1) = 1/4`, so `symmetric_lll_complete 2 1` cannot be invoked. -/
theorem asymLLL_beats_symmetric_threshold :
    AsymLLL 2 ![2 / 5, 1 / 20] ![1 / 2, 1 / 10] ![{1}, {0}]
      ∧ HasMaxDegree 2 ![{1}, {0}] 1
      ∧ 0 < ∏ i, (1 - (![1 / 2, 1 / 10] : Fin 2 → ℚ) i)
      ∧ ¬ (∀ i, (![2 / 5, 1 / 20] : Fin 2 → ℚ) i ≤ lllThreshold 1) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · -- weights in [0,1)
    intro i; fin_cases i <;> norm_num
  · -- prob i ≤ x i · ∏_{j ∈ adj i} (1 - x j)
    intro i; fin_cases i <;> simp [Finset.prod_singleton] <;> norm_num
  · -- max degree 1
    intro i; fin_cases i <;> simp
  · -- avoidance product positive
    simp [Fin.prod_univ_two]; norm_num
  · -- symmetric threshold is exceeded at event 0
    intro hall
    have h0 := hall 0
    rw [lllThreshold_one] at h0
    norm_num at h0

end ProbMethod.LovaszLocal.OQ04
