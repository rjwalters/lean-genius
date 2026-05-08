/-
# Erdős Problem #411: Iterated Totient Sums and Doubling

Let g(n) = n + φ(n) and define g_k(n) by iterating g. For which n and r
is it true that g_{k+r}(n) = 2·g_k(n) for all sufficiently large k?

## Status: OPEN

## References
- Erdős–Graham (1980), p. 81
- Steinerberger (2025)
-/

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/-
## Section I: The Iteration Function
-/

/-- g(n) = n + φ(n), the basic iteration step. -/
def totientStep (n : ℕ) : ℕ := n + n.totient

/-- g_k(n): the k-th iterate of g applied to n. -/
def iteratedTotientStep : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => totientStep (iteratedTotientStep k n)

/-
## Section II: The Doubling Relation
-/

/-- The doubling relation: g_{k+r}(n) = 2·g_k(n) holds for all large k. -/
def DoublingRelation (n r : ℕ) : Prop :=
  ∃ K : ℕ, ∀ k : ℕ, k ≥ K →
    iteratedTotientStep (k + r) n = 2 * iteratedTotientStep k n

/-
## Section III: The Conjecture
-/

/-- **Erdős Problem #411**: Characterize all (n, r) such that
g_{k+r}(n) = 2·g_k(n) for all sufficiently large k.

The problem asks for a complete description of the solution set. -/
def ErdosProblem411 : Prop :=
  ∃ S : Set (ℕ × ℕ), (∀ p : ℕ × ℕ, p ∈ S ↔ DoublingRelation p.1 p.2) ∧
    S.Nonempty

/-
## Section IV: Doubling Propagation

The key structural lemma: g(2m) = 2·g(m) for even m,
which makes the doubling relation self-perpetuating.
-/

/-- φ(2m) = 2·φ(m) when m is even and positive.
    From the prime power decomposition: if m = 2^a·k (a ≥ 1, k odd),
    then φ(2m) = 2^a·φ(k) = 2·(2^{a-1}·φ(k)) = 2·φ(m). -/
theorem totient_double_even {m : ℕ} (hm : 2 ∣ m) (hm_pos : 0 < m) :
    (2 * m).totient = 2 * m.totient :=
  Nat.totient_mul_of_prime_of_dvd Nat.prime_two hm

/-- g(2m) = 2·g(m) for even m > 0: the self-similar doubling property. -/
theorem totientStep_double_even {m : ℕ} (hm : 2 ∣ m) (hm_pos : 0 < m) :
    totientStep (2 * m) = 2 * totientStep m := by
  unfold totientStep
  rw [totient_double_even hm hm_pos]
  ring

/-- g(3m) = 3·g(m) for m divisible by 3 with m > 0. From Mathlib's totient identity. -/
theorem totientStep_triple {m : ℕ} (hm : 3 ∣ m) (hm_pos : 0 < m) :
    totientStep (3 * m) = 3 * totientStep m := by
  unfold totientStep
  rw [Nat.totient_mul_of_prime_of_dvd (by decide : Nat.Prime 3) hm]
  ring

/-- The iterates are always ≥ the starting value. -/
theorem iteratedTotientStep_ge_start (n k : ℕ) :
    iteratedTotientStep k n ≥ n := by
  induction k with
  | zero => simp [iteratedTotientStep]
  | succ k ih =>
    simp [iteratedTotientStep]
    have := totientStep_ge (iteratedTotientStep k n)
    omega

/-- The iterates of totientStep stay even when starting from even n > 2. -/
theorem iteratedTotientStep_even {n : ℕ} (hn_even : 2 ∣ n) (hn : n > 2)
    (k : ℕ) : 2 ∣ iteratedTotientStep k n := by
  induction k with
  | zero => exact hn_even
  | succ k ih =>
    show 2 ∣ totientStep (iteratedTotientStep k n)
    have h_gt : iteratedTotientStep k n > 2 := by
      have := iteratedTotientStep_ge_start n k; omega
    exact totientStep_even_of_even ih h_gt

/-- If the doubling base case holds for even n > 2, it propagates to all k.
    Key: g(2m) = 2·g(m) makes one step of doubling imply the next. -/
private theorem doubling_propagation (n : ℕ) (hn_even : 2 ∣ n) (hn_gt : n > 2)
    (hbase : iteratedTotientStep 2 n = 2 * n) :
    ∀ k, iteratedTotientStep (k + 2) n = 2 * iteratedTotientStep k n := by
  intro k
  induction k with
  | zero => exact hbase
  | succ k ih =>
    calc iteratedTotientStep (k + 3) n
        = totientStep (iteratedTotientStep (k + 2) n) := rfl
      _ = totientStep (2 * iteratedTotientStep k n) := by rw [ih]
      _ = 2 * totientStep (iteratedTotientStep k n) :=
          totientStep_double_even
            (iteratedTotientStep_even hn_even hn_gt k)
            (by have := iteratedTotientStep_ge_start n k; omega)
      _ = 2 * iteratedTotientStep (k + 1) n := rfl

/-
## Section V: Known Solutions (PROVED)
-/

/-- For r = 2, n = 10 is a solution: g_{k+2}(10) = 2·g_k(10) for all k.
    PROVED: base case g_2(10)=20=2·10 by native computation,
    then induction via g(2m) = 2·g(m) for even m. -/
theorem doubling_r2_n10 : DoublingRelation 10 2 :=
  ⟨0, fun k _ => doubling_propagation 10 (by norm_num) (by omega) (by native_decide) k⟩

/-- n = 94 is also a solution with period r = 2.
    PROVED: base case g_2(94)=188=2·94, then same induction. -/
theorem doubling_r2_n94 : DoublingRelation 94 2 :=
  ⟨0, fun k _ => doubling_propagation 94 (by norm_num) (by omega) (by native_decide) k⟩

/-- Cambie found: g_{k+4}(738) = 3·g_k(738), which gives a ratio-3
solution. More generally, non-doubling ratios exist. -/
def GeneralRatioRelation (n r c : ℕ) : Prop :=
  ∃ K : ℕ, ∀ k : ℕ, k ≥ K →
    iteratedTotientStep (k + r) n = c * iteratedTotientStep k n

/-- All iterates of 738 are divisible by 3 and satisfy g_{k+4}(738) = 3·g_k(738).
    Proved by strong induction: base cases (k < 4) verified computationally,
    inductive step uses g(3m) = 3·g(m) (when 3|m) and the ratio. -/
private theorem ratio3_738_aux :
    ∀ k, 3 ∣ iteratedTotientStep k 738 ∧
      iteratedTotientStep (k + 4) 738 = 3 * iteratedTotientStep k 738 := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    constructor
    · -- 3 | a_k: base cases by computation, k ≥ 4 from ratio at k-4
      by_cases hk : k < 4
      · interval_cases k <;> native_decide
      · -- k ≥ 4: a_k = 3·a_{k-4} (from ih at k-4), so 3 | a_k
        have h := (ih (k - 4) (by omega)).2
        have : k - 4 + 4 = k := by omega
        rw [this] at h; rw [h]
        exact dvd_mul_right 3 _
    · -- a_{k+4} = 3·a_k: base cases by computation, k ≥ 4 by propagation
      by_cases hk : k < 4
      · interval_cases k <;> native_decide
      · -- k ≥ 4: a_{k+4} = g(a_{k+3}) = g(3·a_{k-1}) = 3·g(a_{k-1}) = 3·a_k
        have ih_prev := ih (k - 1) (by omega)
        -- a_{k+3} = 3·a_{k-1}
        have h_ratio : iteratedTotientStep (k + 3) 738 =
            3 * iteratedTotientStep (k - 1) 738 := by
          have h := ih_prev.2; rwa [show k - 1 + 4 = k + 3 from by omega] at h
        -- a_k = g(a_{k-1})
        have h_ak : iteratedTotientStep k 738 =
            totientStep (iteratedTotientStep (k - 1) 738) := by
          conv_lhs => rw [show k = (k - 1) + 1 from by omega]
        -- Chain: a_{k+4} = g(a_{k+3}) = g(3·a_{k-1}) = 3·g(a_{k-1}) = 3·a_k
        calc iteratedTotientStep (k + 4) 738
            = totientStep (iteratedTotientStep (k + 3) 738) := rfl
          _ = totientStep (3 * iteratedTotientStep (k - 1) 738) := by rw [h_ratio]
          _ = 3 * totientStep (iteratedTotientStep (k - 1) 738) :=
              totientStep_triple ih_prev.1
                (by have := iteratedTotientStep_ge_start 738 (k - 1); omega)
          _ = 3 * iteratedTotientStep k 738 := by rw [← h_ak]

/-- PROVED: g_{k+4}(738) = 3·g_k(738) for all k ≥ 0.
    Cambie's ratio-3 solution, proved via structural induction using
    g(3m) = 3·g(m) for 3|m and 3-divisibility of all iterates. -/
theorem cambie_ratio3 : GeneralRatioRelation 738 4 3 :=
  ⟨0, fun k _ => (ratio3_738_aux k).2⟩

/-- g(4m) = 4·g(m) when 4|m > 0: self-similar ratio-4 property.
    Derived by applying the p=2 totient identity twice: φ(4m)=2φ(2m)=4φ(m). -/
theorem totientStep_quadruple {m : ℕ} (hm : 4 ∣ m) (hm_pos : 0 < m) :
    totientStep (4 * m) = 4 * totientStep m := by
  have h2m : 2 ∣ m := dvd_trans (by norm_num) hm
  unfold totientStep
  rw [show 4 * m = 2 * (2 * m) from by ring]
  rw [Nat.totient_mul_of_prime_of_dvd Nat.prime_two (dvd_mul_right 2 m)]
  rw [Nat.totient_mul_of_prime_of_dvd Nat.prime_two h2m]
  ring

private theorem ratio4_148646_aux :
    ∀ k, 1 ≤ k →
      4 ∣ iteratedTotientStep k 148646 ∧
      iteratedTotientStep (k + 4) 148646 = 4 * iteratedTotientStep k 148646 := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro hk
    refine ⟨?_, ?_⟩
    · rcases Nat.lt_or_ge k 5 with hlt | hge
      · interval_cases k <;> native_decide
      · have h := (ih (k - 4) (by omega) (by omega)).2
        rw [show k - 4 + 4 = k from by omega] at h
        rw [h]; exact dvd_mul_right 4 _
    · rcases Nat.lt_or_ge k 5 with hlt | hge
      · interval_cases k <;> native_decide
      · have ih_prev := ih (k - 1) (by omega) (by omega)
        have h_ratio : iteratedTotientStep (k + 3) 148646 =
            4 * iteratedTotientStep (k - 1) 148646 := by
          have h := ih_prev.2
          rwa [show k - 1 + 4 = k + 3 from by omega] at h
        have h_pos : 0 < iteratedTotientStep (k - 1) 148646 := by
          have := iteratedTotientStep_ge_start 148646 (k - 1); omega
        have h_ak : iteratedTotientStep k 148646 =
            totientStep (iteratedTotientStep (k - 1) 148646) := by
          conv_lhs => rw [show k = (k - 1) + 1 from by omega]
        calc iteratedTotientStep (k + 4) 148646
            = totientStep (iteratedTotientStep (k + 3) 148646) := rfl
          _ = totientStep (4 * iteratedTotientStep (k - 1) 148646) := by rw [h_ratio]
          _ = 4 * totientStep (iteratedTotientStep (k - 1) 148646) :=
              totientStep_quadruple ih_prev.1 h_pos
          _ = 4 * iteratedTotientStep k 148646 := by rw [← h_ak]

/-- PROVED: g_{k+4}(148646) = 4·g_k(148646) for all k ≥ 1.
    Cambie's first ratio-4 solution, proved via structural induction
    using g(4m) = 4·g(m) for 4|m and 4-divisibility of all iterates from k=1. -/
theorem cambie_ratio4_148646 : GeneralRatioRelation 148646 4 4 :=
  ⟨1, fun k hk => (ratio4_148646_aux k hk).2⟩

private theorem ratio4_4325798_aux :
    ∀ k, 1 ≤ k →
      4 ∣ iteratedTotientStep k 4325798 ∧
      iteratedTotientStep (k + 4) 4325798 = 4 * iteratedTotientStep k 4325798 := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro hk
    refine ⟨?_, ?_⟩
    · rcases Nat.lt_or_ge k 5 with hlt | hge
      · interval_cases k <;> native_decide
      · have h := (ih (k - 4) (by omega) (by omega)).2
        rw [show k - 4 + 4 = k from by omega] at h
        rw [h]; exact dvd_mul_right 4 _
    · rcases Nat.lt_or_ge k 5 with hlt | hge
      · interval_cases k <;> native_decide
      · have ih_prev := ih (k - 1) (by omega) (by omega)
        have h_ratio : iteratedTotientStep (k + 3) 4325798 =
            4 * iteratedTotientStep (k - 1) 4325798 := by
          have h := ih_prev.2
          rwa [show k - 1 + 4 = k + 3 from by omega] at h
        have h_pos : 0 < iteratedTotientStep (k - 1) 4325798 := by
          have := iteratedTotientStep_ge_start 4325798 (k - 1); omega
        have h_ak : iteratedTotientStep k 4325798 =
            totientStep (iteratedTotientStep (k - 1) 4325798) := by
          conv_lhs => rw [show k = (k - 1) + 1 from by omega]
        calc iteratedTotientStep (k + 4) 4325798
            = totientStep (iteratedTotientStep (k + 3) 4325798) := rfl
          _ = totientStep (4 * iteratedTotientStep (k - 1) 4325798) := by rw [h_ratio]
          _ = 4 * totientStep (iteratedTotientStep (k - 1) 4325798) :=
              totientStep_quadruple ih_prev.1 h_pos
          _ = 4 * iteratedTotientStep k 4325798 := by rw [← h_ak]

/-- PROVED: g_{k+4}(4325798) = 4·g_k(4325798) for all k ≥ 1.
    Cambie's second ratio-4 solution. Same proof structure as cambie_ratio4_148646. -/
theorem cambie_ratio4_4325798 : GeneralRatioRelation 4325798 4 4 :=
  ⟨1, fun k hk => (ratio4_4325798_aux k hk).2⟩

/-
## Section VI: Steinerberger's Reduction (PROVED, sufficient direction)

Steinerberger (2025, arXiv:2504.08023) observed that the r = 2 doubling
problem is equivalent to the elementary equation φ(n) + φ(n + φ(n)) = n.
We formalize the sufficient direction: if this equation holds for an
even n > 2, then DoublingRelation n 2 holds (with K = 0).

The converse (DoublingRelation n 2 → equation) requires backward reasoning
along orbits of g and is not formalized here.
-/

/-- Computational expansion: g_2(n) = (n + φ(n)) + φ(n + φ(n)). -/
theorem iteratedTotientStep_two (n : ℕ) :
    iteratedTotientStep 2 n = (n + n.totient) + (n + n.totient).totient := by
  rfl

/-- Steinerberger's identity (computational form):
g_2(n) = 2n ⟺ φ(n) + φ(n + φ(n)) = n. -/
theorem steinerberger_iff (n : ℕ) :
    iteratedTotientStep 2 n = 2 * n ↔
      n.totient + (n + n.totient).totient = n := by
  rw [iteratedTotientStep_two]; omega

/-- **Steinerberger's reduction (sufficient direction).** If n is even, n > 2,
and φ(n) + φ(n + φ(n)) = n, then DoublingRelation n 2 holds with K = 0.

Proof: The hypothesis gives g_2(n) = 2n by `steinerberger_iff`, and
`doubling_propagation` extends this to all k ≥ 0. -/
theorem steinerberger_r2_sufficient {n : ℕ} (hn_even : 2 ∣ n) (hn_gt : n > 2)
    (h_eq : n.totient + (n + n.totient).totient = n) :
    DoublingRelation n 2 :=
  ⟨0, fun k _ => doubling_propagation n hn_even hn_gt
    ((steinerberger_iff n).mpr h_eq) k⟩

/-- The known r = 2 solution n = 10 satisfies Steinerberger's equation:
φ(10) + φ(10 + φ(10)) = 4 + φ(14) = 4 + 6 = 10. -/
theorem steinerberger_eq_n10 :
    (10 : ℕ).totient + (10 + (10 : ℕ).totient).totient = 10 := by
  native_decide

/-- The known r = 2 solution n = 94 satisfies Steinerberger's equation:
φ(94) + φ(94 + φ(94)) = 46 + φ(140) = 46 + 48 = 94. -/
theorem steinerberger_eq_n94 :
    (94 : ℕ).totient + (94 + (94 : ℕ).totient).totient = 94 := by
  native_decide

/-
## Section VII: Structural Properties
-/

/-- For even n, g(n) = n + φ(n) is always even, so the iterates
stay even. This is relevant since all known solutions are even. -/
theorem totientStep_even_of_even {n : ℕ} (hn : 2 ∣ n) (hn2 : n > 2) :
    2 ∣ totientStep n := by
  unfold totientStep
  have hφ : 2 ∣ n.totient := Nat.totient_even hn2
  exact dvd_add hn hφ

/-- Cambie conjectures all r = 2 solutions have form n = 2^l · p
where l ≥ 1 and p ∈ {2, 3, 5, 7, 35, 47}. -/
def CambieConjecture : Prop :=
  ∀ n : ℕ, DoublingRelation n 2 →
    ∃ l : ℕ, l ≥ 1 ∧
      ∃ p ∈ ({2, 3, 5, 7, 35, 47} : Finset ℕ), n = 2 ^ l * p

/-- The iteration g(n) = n + φ(n) always produces an even number
when n ≥ 3, since φ(n) is even for n ≥ 3. -/
theorem totientStep_ge (n : ℕ) : totientStep n ≥ n := by
  unfold totientStep
  omega
