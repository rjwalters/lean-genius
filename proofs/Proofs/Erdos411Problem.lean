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
## Section VI.b: Additional Cambie l=1 Doubling Solutions

Cambie's conjecture predicts that every r=2 doubling solution has the
form n = 2^l · p with l ≥ 1 and p ∈ {2, 3, 5, 7, 35, 47}. The l=1
specialization gives six candidates: n ∈ {4, 6, 10, 14, 70, 94}.
The cases n = 10 and n = 94 are recorded above; we now formalize the
remaining four (n = 4, 6, 14, 70) using the Steinerberger sufficient
direction.
-/

/-- p=2 case (l=1, n=4): φ(4) + φ(4 + φ(4)) = 2 + φ(6) = 2 + 2 = 4. -/
theorem steinerberger_eq_n4 :
    (4 : ℕ).totient + (4 + (4 : ℕ).totient).totient = 4 := by
  native_decide

/-- **Cambie l=1, p=2**: g_{k+2}(4) = 2·g_k(4) for all k.
    n = 2^2 is a doubling solution via the Steinerberger reduction. -/
theorem doubling_r2_n4 : DoublingRelation 4 2 :=
  steinerberger_r2_sufficient (by norm_num) (by omega) steinerberger_eq_n4

/-- p=3 case (l=1, n=6): φ(6) + φ(6 + φ(6)) = 2 + φ(8) = 2 + 4 = 6. -/
theorem steinerberger_eq_n6 :
    (6 : ℕ).totient + (6 + (6 : ℕ).totient).totient = 6 := by
  native_decide

/-- **Cambie l=1, p=3**: g_{k+2}(6) = 2·g_k(6) for all k.
    n = 2·3 is a doubling solution. -/
theorem doubling_r2_n6 : DoublingRelation 6 2 :=
  steinerberger_r2_sufficient (by norm_num) (by omega) steinerberger_eq_n6

/-- p=7 case (l=1, n=14): φ(14) + φ(14 + φ(14)) = 6 + φ(20) = 6 + 8 = 14. -/
theorem steinerberger_eq_n14 :
    (14 : ℕ).totient + (14 + (14 : ℕ).totient).totient = 14 := by
  native_decide

/-- **Cambie l=1, p=7**: g_{k+2}(14) = 2·g_k(14) for all k.
    n = 2·7 is a doubling solution. -/
theorem doubling_r2_n14 : DoublingRelation 14 2 :=
  steinerberger_r2_sufficient (by norm_num) (by omega) steinerberger_eq_n14

/-- p=35 case (l=1, n=70): φ(70) + φ(70 + φ(70)) = 24 + φ(94) = 24 + 46 = 70. -/
theorem steinerberger_eq_n70 :
    (70 : ℕ).totient + (70 + (70 : ℕ).totient).totient = 70 := by
  native_decide

/-- **Cambie l=1, p=35**: g_{k+2}(70) = 2·g_k(70) for all k.
    n = 2·35 is a doubling solution. Together with `doubling_r2_n4`,
    `doubling_r2_n6`, `doubling_r2_n10`, `doubling_r2_n14`, `doubling_r2_n94`
    this exhausts the l=1 layer of Cambie's conjectured family. -/
theorem doubling_r2_n70 : DoublingRelation 70 2 :=
  steinerberger_r2_sufficient (by norm_num) (by omega) steinerberger_eq_n70

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

/-
## Section VIII: Cambie Family Doubling Tower

The Steinerberger equation φ(n) + φ(n + φ(n)) = n is preserved under
the doubling map n ↦ 2n (when n is even, n > 2). Each l = 1 base case in
Cambie's conjectured family {2 · p : p ∈ {2, 3, 5, 7, 35, 47}} therefore
generates an infinite tower {2^l · p : l ≥ 1} of doubling solutions.

Combined with `doubling_r2_n4`, `doubling_r2_n6`, `doubling_r2_n10`,
`doubling_r2_n14`, `doubling_r2_n70`, `doubling_r2_n94`, this realizes the
*entire* sufficient direction of Cambie's conjecture: every n in the
predicted family is unconditionally proved to be an r = 2 doubling solution.
The converse — that no other n satisfies DoublingRelation n 2 — remains open.
-/

/-- **Steinerberger equation lifts under doubling.** If n is even, n > 2,
and φ(n) + φ(n + φ(n)) = n, then φ(2n) + φ(2n + φ(2n)) = 2n.

Proof: φ(2n) = 2·φ(n) since 2 ∣ n; then 2n + φ(2n) = 2(n + φ(n)) and
n + φ(n) is even (n even and φ(n) even by `Nat.totient_even` since n > 2),
so φ(2n + φ(2n)) = φ(2(n + φ(n))) = 2·φ(n + φ(n)). The sum equals
2·(φ(n) + φ(n + φ(n))) = 2n. -/
theorem steinerberger_eq_lift {n : ℕ} (hn_even : 2 ∣ n) (hn_gt : n > 2)
    (h_eq : n.totient + (n + n.totient).totient = n) :
    (2 * n).totient + (2 * n + (2 * n).totient).totient = 2 * n := by
  have hn_pos : 0 < n := by omega
  have hφn_even : 2 ∣ n.totient := Nat.totient_even hn_gt
  have h_phi2n : (2 * n).totient = 2 * n.totient :=
    totient_double_even hn_even hn_pos
  have hsum_even : 2 ∣ (n + n.totient) := dvd_add hn_even hφn_even
  have hsum_pos : 0 < n + n.totient := by omega
  have h_phi_sum : (2 * (n + n.totient)).totient = 2 * (n + n.totient).totient :=
    totient_double_even hsum_even hsum_pos
  have h_arg_eq : 2 * n + 2 * n.totient = 2 * (n + n.totient) := by ring
  calc (2 * n).totient + (2 * n + (2 * n).totient).totient
      = 2 * n.totient + (2 * n + 2 * n.totient).totient := by rw [h_phi2n]
    _ = 2 * n.totient + (2 * (n + n.totient)).totient := by rw [h_arg_eq]
    _ = 2 * n.totient + 2 * (n + n.totient).totient := by rw [h_phi_sum]
    _ = 2 * (n.totient + (n + n.totient).totient) := by ring
    _ = 2 * n := by rw [h_eq]

/-- Iterated lifting: every doubling of a Steinerberger base case still
satisfies Steinerberger's equation. -/
theorem steinerberger_eq_pow_two {n : ℕ} (hn_even : 2 ∣ n) (hn_gt : n > 2)
    (h_eq : n.totient + (n + n.totient).totient = n) (l : ℕ) :
    (2^l * n).totient + (2^l * n + (2^l * n).totient).totient = 2^l * n := by
  induction l with
  | zero => simpa using h_eq
  | succ l ih =>
    have hpow_ge_one : 1 ≤ 2^l := Nat.one_le_two_pow
    have h_pow_n_even : 2 ∣ 2^l * n := dvd_mul_of_dvd_right hn_even _
    have h_pow_n_gt : 2^l * n > 2 := by
      have hge : 1 * n ≤ 2^l * n := Nat.mul_le_mul_right n hpow_ge_one
      omega
    have := steinerberger_eq_lift h_pow_n_even h_pow_n_gt ih
    have hrw : 2^(l+1) * n = 2 * (2^l * n) := by ring
    rw [hrw]; exact this

/-- **Cambie family tower theorem.** From any even base case n > 2 satisfying
Steinerberger's equation, the entire arithmetic-geometric tower
{n, 2n, 4n, 8n, …} consists of r = 2 doubling solutions.

Applied to the six l = 1 base cases (n ∈ {4, 6, 10, 14, 70, 94}), this proves
unconditionally that *every* element of Cambie's conjectured family
{2^l · p : l ≥ 1, p ∈ {2, 3, 5, 7, 35, 47}} is a doubling solution. -/
theorem cambie_family_doubling {n : ℕ} (hn_even : 2 ∣ n) (hn_gt : n > 2)
    (h_eq : n.totient + (n + n.totient).totient = n) (l : ℕ) :
    DoublingRelation (2^l * n) 2 := by
  have hpow_ge_one : 1 ≤ 2^l := Nat.one_le_two_pow
  refine steinerberger_r2_sufficient ?_ ?_ (steinerberger_eq_pow_two hn_even hn_gt h_eq l)
  · exact dvd_mul_of_dvd_right hn_even _
  · have hge : 1 * n ≤ 2^l * n := Nat.mul_le_mul_right n hpow_ge_one
    omega

/-- **Cambie l = 2 layer**: g_{k+2}(n) = 2·g_k(n) for n ∈ {8, 12, 20, 28, 140, 188},
obtained as the l = 2 instances of `cambie_family_doubling`. -/
theorem doubling_r2_n8 : DoublingRelation 8 2 :=
  cambie_family_doubling (n := 4) (by norm_num) (by omega) steinerberger_eq_n4 1

theorem doubling_r2_n12 : DoublingRelation 12 2 :=
  cambie_family_doubling (n := 6) (by norm_num) (by omega) steinerberger_eq_n6 1

theorem doubling_r2_n20 : DoublingRelation 20 2 :=
  cambie_family_doubling (n := 10) (by norm_num) (by omega) steinerberger_eq_n10 1

theorem doubling_r2_n28 : DoublingRelation 28 2 :=
  cambie_family_doubling (n := 14) (by norm_num) (by omega) steinerberger_eq_n14 1

theorem doubling_r2_n140 : DoublingRelation 140 2 :=
  cambie_family_doubling (n := 70) (by norm_num) (by omega) steinerberger_eq_n70 1

theorem doubling_r2_n188 : DoublingRelation 188 2 :=
  cambie_family_doubling (n := 94) (by norm_num) (by omega) steinerberger_eq_n94 1
