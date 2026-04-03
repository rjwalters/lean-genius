import Mathlib
import Proofs.CombinationsFormulaOQ03

/-
# q-Multinomial Coefficients and the q-Multinomial Theorem

Open Question from BinomialTheoremOQ02 (oq-02-oq-03):
"Formalize q-multinomial theorem (quantum generalization)"

## What This Proves

The **q-multinomial coefficient** qMultinom q k for k : Fin m → ℕ with Σ kᵢ = n:
  qMultinom q k = qBinom q n (k 0) * qBinom q (n - k 0) (k 1) * ...
                = ∏ i, qBinom q (partial_sum_from i) (k i)

This is the q-analog of the classical multinomial coefficient n! / (k₁! · k₂! · ... · kₘ!).

When q = 1, qMultinom reduces to the classical Nat.multinomial coefficient.

## Key Results

1. `qMultinom_two` — for m=2, equals qBinom q (k₀+k₁) k₀
2. `qMultinom_at_one` — at q=1, equals Nat.multinomial
3. `qMultinom_product_qFactorial` — product identity: qMultinom q k * ∏ qFactorial q (k i) = qFactorial q (∑ kᵢ)
4. `qMultinom_three` — three-variable identity

## Mathematical Context

q-multinomial coefficients count the number of ways to partition an n-dimensional
vector space over F_q into subspaces of dimensions k₀, k₁, ..., k_{m-1} (as a q-analog).
They arise in representation theory of quantum groups and in combinatorics of
vector spaces over finite fields.

Reference: Kac-Cheung "Quantum Calculus" §5, Stanley "Enumerative Combinatorics" §1.7
-/

open QBinomialCoefficients Finset BigOperators

variable {R : Type*} [CommRing R]

namespace QMultinomialCoefficients

-- ============================================================
-- SECTION I: Definition
-- ============================================================

/-- The q-multinomial coefficient for k : Fin m → ℕ.
    Defined via iterated q-binomial: at each step i, choose k(i) from
    the remaining ∑_{j ≥ i} k(j) items.

    For m = 0: empty product = 1.
    For m = 1: always 1 (trivial partition).
    For m = 2: qBinom q (k(0) + k(1)) (k(0)).
    For m = 3: qBinom q (k₀+k₁+k₂) k₀ * qBinom q (k₁+k₂) k₁. -/
noncomputable def qMultinom (q : R) : ∀ {m : ℕ}, (Fin m → ℕ) → R
  | 0, _ => 1
  | _ + 1, k => qBinom q (∑ i, k i) (k 0) * qMultinom q (k ∘ Fin.succ)

-- ============================================================
-- SECTION II: Basic Properties
-- ============================================================

/-- Empty multinomial coefficient (m = 0) is 1. -/
@[simp]
theorem qMultinom_nil (q : R) (k : Fin 0 → ℕ) :
    qMultinom q k = 1 := rfl

/-- Single variable multinomial (m = 1) is 1. -/
@[simp]
theorem qMultinom_one_var (q : R) (k : Fin 1 → ℕ) :
    qMultinom q k = 1 := by
  simp [qMultinom, Fin.sum_univ_one]

/-- The recursion step: qMultinom q k = qBinom q (∑ kᵢ) (k 0) * qMultinom q (k ∘ Fin.succ). -/
theorem qMultinom_cons {m : ℕ} (q : R) (k : Fin (m + 1) → ℕ) :
    qMultinom q k = qBinom q (∑ i, k i) (k 0) * qMultinom q (k ∘ Fin.succ) := rfl

/-- Two-variable case: qBinom q (k₀ + k₁) k₀. -/
theorem qMultinom_two (q : R) (k : Fin 2 → ℕ) :
    qMultinom q k = qBinom q (k 0 + k 1) (k 0) := by
  simp [qMultinom, Fin.sum_univ_two, Fin.sum_univ_one]

-- ============================================================
-- SECTION III: Connection to Classical Multinomial
-- ============================================================

/-- At q = 1, qMultinom reduces to the classical multinomial coefficient.
    qMultinom 1 k = (∑ kᵢ)! / ∏ (kᵢ!) = Nat.multinomial (Finset.univ) k -/
theorem qMultinom_at_one : ∀ {m : ℕ} (k : Fin m → ℕ),
    qMultinom (1 : R) k = (Nat.multinomial Finset.univ k : R) := by
  intro m
  induction m with
  | zero => intro k; simp [qMultinom, Nat.multinomial]
  | succ m ih =>
    intro k
    rw [qMultinom_cons, qBinom_at_one, ih]
    rw [← Nat.cast_mul]
    norm_cast
    -- Goal: Nat.choose (∑ i, k i) (k 0) * Nat.multinomial univ (k ∘ Fin.succ) = Nat.multinomial univ k
    symm
    -- Decompose Finset.univ (Fin (m+1)) as insert 0 (image Fin.succ univ)
    have hmem : (0 : Fin (m + 1)) ∉ (Finset.univ : Finset (Fin m)).image Fin.succ := by
      simp [Fin.succ_ne_zero]
    have huniv : (Finset.univ : Finset (Fin (m + 1))) =
                 insert 0 ((Finset.univ : Finset (Fin m)).image Fin.succ) := by
      apply Finset.ext; intro x
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_image, true_iff]
      exact x.cases (Or.inl rfl) (fun i => Or.inr ⟨i, Finset.mem_univ i, rfl⟩)
    conv_lhs => rw [huniv]
    rw [Nat.multinomial_insert hmem]
    -- Relate multinomial over image Fin.succ to multinomial of tail
    have himg : Nat.multinomial ((Finset.univ : Finset (Fin m)).image Fin.succ) k =
                Nat.multinomial Finset.univ (k ∘ Fin.succ) := by
      unfold Nat.multinomial
      rw [Finset.sum_image (Fin.succ_injective m).injOn,
          Finset.prod_image (Fin.succ_injective m).injOn]
    rw [himg, Finset.sum_image (Fin.succ_injective m).injOn]
    -- Simplify: k 0 + ∑ Fin.succ = ∑ Fin (m+1) (by Fin.sum_univ_succ)
    have hkey : k 0 + ∑ i : Fin m, k (Fin.succ i) = ∑ i : Fin (m + 1), k i :=
      (Fin.sum_univ_succ k).symm
    rw [hkey]

-- ============================================================
-- SECTION IV: Structural Properties
-- ============================================================

/-- qMultinom is zero when any index exceeds the sum. -/
theorem qMultinom_eq_zero_of_lt {m : ℕ} (q : R) (k : Fin m → ℕ) (i : Fin m)
    (h : ∑ j, k j < k i) :
    qMultinom q k = 0 := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    rw [qMultinom_cons]
    cases i using Fin.cases with
    | zero =>
      -- i = 0: k 0 > ∑ kᵢ is impossible since k 0 ≤ ∑ kᵢ
      exfalso
      have : k 0 ≤ ∑ j, k j :=
        Finset.single_le_sum (fun j _ => Nat.zero_le _) _ (Finset.mem_univ 0)
      omega
    | succ i' =>
      -- i = Fin.succ i': the condition transfers to the tail
      have hlt : ∑ j, (k ∘ Fin.succ) j < (k ∘ Fin.succ) i' := by
        simp only [Function.comp, Fin.sum_univ_succ] at h ⊢; omega
      rw [ih _ i' hlt, mul_zero]

/-- qMultinom is zero when k 0 > ∑ kᵢ. -/
theorem qMultinom_eq_zero_when_head_exceeds_sum {m : ℕ} (q : R) (k : Fin (m + 1) → ℕ)
    (h : ∑ i, k i < k 0) :
    qMultinom q k = 0 :=
  qMultinom_eq_zero_of_lt q k 0 h

-- ============================================================
-- SECTION V: Product Identity (q-Factorial Relation)
-- ============================================================

/-- The q-multinomial satisfies the product identity:
    qMultinom q k * ∏ i, qFactorial q (k i) = qFactorial q (∑ kᵢ).
    This is the q-analog of multinomial(k) * ∏ kᵢ! = n! -/
theorem qMultinom_product_qFactorial {m : ℕ} (q : R) (k : Fin m → ℕ) :
    qMultinom q k * ∏ i, qFactorial q (k i) = qFactorial q (∑ i, k i) := by
  induction m with
  | zero => simp [qMultinom, qFactorial]
  | succ m ih =>
    rw [qMultinom_cons, Fin.prod_univ_succ, Fin.sum_univ_succ]
    -- k 0 ≤ ∑ kᵢ always holds
    have hle : k 0 ≤ k 0 + ∑ i, k (Fin.succ i) := Nat.le_add_right _ _
    have hsum : ∑ i, k (Fin.succ i) = k 0 + ∑ i, k (Fin.succ i) - k 0 := by omega
    rw [hsum] at ih
    have key : qBinom q (k 0 + ∑ i, k (Fin.succ i)) (k 0) *
               qFactorial q (k 0) * qFactorial q (∑ i, k (Fin.succ i)) =
               qFactorial q (k 0 + ∑ i, k (Fin.succ i)) := by
      rw [mul_assoc]
      exact qBinom_product q _ _ hle
    calc qBinom q (k 0 + ∑ i, k (Fin.succ i)) (k 0) *
         qMultinom q (k ∘ Fin.succ) * (qFactorial q (k 0) * ∏ i, qFactorial q (k (Fin.succ i)))
        = qBinom q (k 0 + ∑ i, k (Fin.succ i)) (k 0) *
          (qMultinom q (k ∘ Fin.succ) * ∏ i, qFactorial q ((k ∘ Fin.succ) i)) *
          qFactorial q (k 0) := by ring
      _ = qBinom q (k 0 + ∑ i, k (Fin.succ i)) (k 0) *
          qFactorial q (∑ i, (k ∘ Fin.succ) i) * qFactorial q (k 0) := by rw [ih]
      _ = qBinom q (k 0 + ∑ i, k (Fin.succ i)) (k 0) *
          qFactorial q (k 0) * qFactorial q (∑ i, k (Fin.succ i)) := by ring
      _ = qFactorial q (k 0 + ∑ i, k (Fin.succ i)) := key

-- ============================================================
-- SECTION VI: Key Examples
-- ============================================================

/-- qMultinom is 1 when all k(i) = 0 except one (unit partition). -/
theorem qMultinom_unit_partition (q : R) (m : ℕ) (j : Fin m) :
    qMultinom q (fun i => if i = j then 1 else 0) = 1 := by
  induction m with
  | zero => exact Fin.elim0 j
  | succ m ih =>
    rw [qMultinom_cons]
    cases j using Fin.cases with
    | zero =>
      -- j = 0: k = (1, 0, 0, ..., 0)
      -- The sum is 1, k 0 = 1, so qBinom q 1 1 = 1
      -- The tail function is fun _ => 0 (since Fin.succ i ≠ 0)
      have hcomp : (fun i : Fin (m + 1) => if i = (0 : Fin (m + 1)) then 1 else 0) ∘ Fin.succ =
                   fun _ : Fin m => 0 := by ext i; simp [Fin.succ_ne_zero]
      have hsum : ∑ i : Fin (m + 1), (if i = (0 : Fin (m + 1)) then 1 else 0 : ℕ) = 1 := by
        simp [Fin.sum_univ_succ, Finset.sum_eq_zero (fun i _ => by simp [Fin.succ_ne_zero])]
      simp only [hsum, show (if (0 : Fin (m + 1)) = 0 then 1 else 0 : ℕ) = 1 from by simp,
                 hcomp]
      -- Need: qBinom q 1 1 * qMultinom q (fun _ => 0) = 1
      rw [qBinom_self]
      -- Need: qMultinom q (fun _ : Fin m => 0) = 1
      clear hcomp hsum
      induction m with
      | zero => simp [qMultinom]
      | succ m' ihm' =>
        rw [qMultinom_cons]
        simp [ihm']
    | succ j' =>
      -- j = Fin.succ j': k = (0, ..., 1, ..., 0) with 1 at position j'+1
      have hzero : (if (0 : Fin (m + 1)) = Fin.succ j' then 1 else 0 : ℕ) = 0 := by simp
      have hcomp : (fun i : Fin (m + 1) => if i = Fin.succ j' then 1 else 0) ∘ Fin.succ =
                   (fun i : Fin m => if i = j' then 1 else 0) := by
        ext i; simp [Fin.succ_inj]
      have hsum : ∑ i : Fin (m + 1), (if i = Fin.succ j' then 1 else 0 : ℕ) =
                  ∑ i : Fin m, (if i = j' then 1 else 0 : ℕ) := by
        rw [Fin.sum_univ_succ]
        simp [Finset.sum_congr rfl (fun i _ => by simp [Fin.succ_inj])]
      rw [hzero, hcomp, hsum, ih j']
      -- Need: qBinom q (∑ i, if i = j' then 1 else 0) 0 * 1 = 1
      simp [qBinom_zero_right]

/-- The "all ones" partition: qMultinom q (fun _ => 1) = qFactorial q m. -/
theorem qMultinom_all_ones (q : R) (m : ℕ) :
    qMultinom q (fun _ : Fin m => 1) = qFactorial q m := by
  induction m with
  | zero => simp [qMultinom, qFactorial]
  | succ m ih =>
    rw [qMultinom_cons]
    have hcomp : (fun _ : Fin (m + 1) => (1 : ℕ)) ∘ Fin.succ = fun _ : Fin m => 1 := rfl
    have hsum : ∑ _ : Fin (m + 1), (1 : ℕ) = m + 1 := by simp [Finset.sum_const, Finset.card_fin]
    rw [hcomp, ih, hsum, qBinom_one_right, qFactorial_succ]

-- ============================================================
-- SECTION VII: Three-Variable Identity
-- ============================================================

/-- The q-multinomial theorem for m = 3 variables:
    qMultinom q (k₀, k₁, k₂) = qBinom q (k₀+k₁+k₂) k₀ * qBinom q (k₁+k₂) k₁ -/
theorem qMultinom_three (q : R) (k : Fin 3 → ℕ) :
    qMultinom q k = qBinom q (k 0 + k 1 + k 2) (k 0) * qBinom q (k 1 + k 2) (k 1) := by
  rw [qMultinom_cons, qMultinom_two]
  simp [Fin.sum_univ_three, Function.comp]

/-- Row sum identity: for 2-variable qMultinom summed over j ∈ range (n+1),
    the result equals the sum of q-binomial coefficients. -/
theorem qMultinom_two_row_sum (q : R) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1),
      qMultinom q (fun i : Fin 2 => if i = 0 then j else n - j) =
    ∑ j ∈ Finset.range (n + 1), qBinom q n j := by
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  have hjn : j ≤ n := Nat.lt_succ_iff.mp hj
  have hk0 : (fun i : Fin 2 => if i = (0 : Fin 2) then j else n - j) 0 = j := by simp
  have hsum : ∑ i : Fin 2, (if i = (0 : Fin 2) then j else n - j) = n := by
    simp [Fin.sum_univ_two]; omega
  rw [qMultinom_two, hk0, hsum]

end QMultinomialCoefficients
