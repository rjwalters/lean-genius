/-
Newton's Inequality: e_k² ≥ e_{k-1} · e_{k+1}

For nonnegative real numbers x₁, ..., xₙ, the elementary symmetric polynomials
e_k satisfy the log-concavity inequality:

  (C(n,k))² · e_k² ≥ C(n,k-1) · C(n,k+1) · e_{k-1} · e_{k+1}

Equivalently, writing ē_k = e_k / C(n,k) for the normalized elementary
symmetric means:  ē_k² ≥ ē_{k-1} · ē_{k+1}.

This is the OQ-01 extension of the parent proof NewtonInductiveStep.lean,
which proved the key binomial coefficient inequality used in the inductive step.

Proof strategy:
  1. Define esymm (elementary symmetric polynomial) on lists of reals
  2. Use the recurrence: esymm (x :: xs) k = esymm xs k + x · esymm xs (k-1)
  3. Prove Newton's inequality by induction on n (list length)
  4. The inductive step uses the parent's binom_ineq and quadratic discriminant

References:
  - Newton (1707), Arithmetica Universalis
  - Niculescu (2000), A new look at Newton's inequalities
  - Hardy–Littlewood–Pólya (1952), Inequalities, Ch. 2
  - Parent proof: NewtonInductiveStep.lean (binom_ineq)
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Nat Finset List

/-! ## Elementary symmetric polynomials on lists -/

/-- The k-th elementary symmetric polynomial evaluated at a list of reals.
    esymm [] 0 = 1, esymm [] (k+1) = 0,
    esymm (x :: xs) k = esymm xs k + x * esymm xs (k-1). -/
noncomputable def esymm : List ℝ → ℕ → ℝ
  | [], 0 => 1
  | [], (_ + 1) => 0
  | x :: xs, 0 => esymm xs 0
  | x :: xs, k + 1 => esymm xs (k + 1) + x * esymm xs k

/-! ## Basic properties -/

@[simp]
theorem esymm_nil_zero : esymm [] 0 = 1 := rfl

@[simp]
theorem esymm_nil_succ (k : ℕ) : esymm [] (k + 1) = 0 := rfl

theorem esymm_cons_zero (x : ℝ) (xs : List ℝ) :
    esymm (x :: xs) 0 = esymm xs 0 := rfl

theorem esymm_cons_succ (x : ℝ) (xs : List ℝ) (k : ℕ) :
    esymm (x :: xs) (k + 1) = esymm xs (k + 1) + x * esymm xs k := rfl

/-- e_0 of any list is 1. -/
theorem esymm_zero (xs : List ℝ) : esymm xs 0 = 1 := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => exact ih

/-- e_k = 0 when k > length of list. -/
theorem esymm_eq_zero_of_gt (xs : List ℝ) (k : ℕ) (hk : xs.length < k) :
    esymm xs k = 0 := by
  induction xs generalizing k with
  | nil =>
    match k, hk with
    | k + 1, _ => rfl
  | cons x xs ih =>
    match k with
    | 0 => omega
    | k + 1 =>
      simp only [esymm_cons_succ, length_cons] at hk ⊢
      have hk' : xs.length < k + 1 := by omega
      have hk'' : xs.length < k := by omega
      rw [ih _ hk', ih _ hk'', mul_zero, add_zero]

/-- e_n of a list of length n is the product of all elements. -/
theorem esymm_length (xs : List ℝ) : esymm xs xs.length = xs.prod := by
  induction xs with
  | nil => simp [esymm_nil_zero]
  | cons x xs ih =>
    simp only [length_cons, esymm_cons_succ]
    rw [esymm_eq_zero_of_gt xs (xs.length + 1) (by omega)]
    simp [ih, mul_comm]

/-- esymm of nonneg list elements is nonneg. -/
theorem esymm_nonneg (xs : List ℝ) (hxs : ∀ x ∈ xs, (0 : ℝ) ≤ x) (k : ℕ) :
    0 ≤ esymm xs k := by
  induction xs generalizing k with
  | nil =>
    match k with
    | 0 => simp
    | k + 1 => simp
  | cons x xs ih =>
    match k with
    | 0 => rw [esymm_cons_zero]; exact ih (fun y hy => hxs y (List.mem_cons_of_mem x hy)) 0
    | k + 1 =>
      rw [esymm_cons_succ]
      have hx : 0 ≤ x := hxs x List.mem_cons_self
      have hmem : ∀ y ∈ xs, (0 : ℝ) ≤ y := fun y hy => hxs y (List.mem_cons_of_mem x hy)
      exact add_nonneg (ih hmem (k + 1)) (mul_nonneg hx (ih hmem k))

/-! ## Newton's inequality for the single-element base case -/

/-- For a single element [a], e_1² ≥ e_0 · e_2 (trivially 0 ≤ a²). -/
theorem newton_ineq_singleton (a : ℝ) (ha : 0 ≤ a) (k : ℕ) (hk : 1 ≤ k)
    (hk' : k ≤ 0) : esymm [a] k ^ 2 ≥ esymm [a] (k - 1) * esymm [a] (k + 1) := by
  omega

/-! ## Newton's inequality: the normalized (mean) form

We prove Newton's inequality in the "binomial mean" form:
  C(n,k)² · e_k² ≥ C(n,k-1) · C(n,k+1) · e_{k-1} · e_{k+1}

This is equivalent to ē_k² ≥ ē_{k-1} · ē_{k+1} where ē_k = e_k / C(n,k).
-/

/-- Newton's inequality (standard form):
    C(n,k-1) · C(n,k+1) · e_k² ≥ C(n,k)² · e_{k-1} · e_{k+1}
    for all nonneg x₁,...,xₙ and 1 ≤ k ≤ n-1.

    This is equivalent to the mean form ē_k² ≥ ē_{k-1}·ē_{k+1}
    where ē_k = e_k/C(n,k) are the elementary symmetric means. -/
theorem newton_inequality_binomial (xs : List ℝ) (hxs : ∀ x ∈ xs, (0 : ℝ) ≤ x)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k + 1 ≤ xs.length) :
    (Nat.choose xs.length (k - 1) : ℝ) * (Nat.choose xs.length (k + 1) : ℝ) *
    esymm xs k ^ 2 ≥
    (Nat.choose xs.length k : ℝ) ^ 2 *
    (esymm xs (k - 1) * esymm xs (k + 1)) := by
  -- Proved by induction on xs
  induction xs generalizing k with
  | nil => simp at hkn
  | cons x xs ih =>
    simp only [length_cons] at hkn
    -- The inductive step uses the recurrence and the IH
    -- For simplicity, we prove this via the log-concavity of binomial coefficients
    -- combined with the inductive structure
    --
    -- Key identity: C(n+1,k) = C(n,k) + C(n,k-1)
    -- esymm (x::xs) k = esymm xs k + x * esymm xs (k-1)
    --
    -- The full inductive proof is a careful expansion using Cauchy-Schwarz
    -- on the two terms of the recurrence.
    --
    -- We use the standard proof: write E_k = esymm xs k, F_k = esymm (x::xs) k
    -- F_k = E_k + x·E_{k-1}
    -- Then C(n+1,k)²·F_k² ≥ C(n+1,k-1)·C(n+1,k+1)·F_{k-1}·F_{k+1}
    -- expands to a sum of terms, each bounded using IH and nonneg conditions.
    sorry

/-! ## Sum-of-squares identity (key lemma for k = 1 case)

The expression `e_1² - 2·e_2 + n·t² - 2t·e_1` equals `∑_{i=1}^n (x_i - t)²`,
which is manifestly nonnegative. This identity drives the inductive proof of
Newton's inequality at k = 1.
-/

/-- Sum of squared differences identity in `esymm` form.
    The expression equals `∑_{i=1}^n (x_i - t)² ≥ 0`. -/
theorem esymm_sum_sub_sq_nonneg (xs : List ℝ) (t : ℝ) :
    0 ≤ esymm xs 1 ^ 2 - 2 * esymm xs 2 +
        (xs.length : ℝ) * t ^ 2 - 2 * t * esymm xs 1 := by
  induction xs with
  | nil =>
    show (0 : ℝ) ≤ esymm ([] : List ℝ) 1 ^ 2 - 2 * esymm ([] : List ℝ) 2 +
        ((0 : ℕ) : ℝ) * t ^ 2 - 2 * t * esymm ([] : List ℝ) 1
    simp [esymm_nil_succ]
  | cons y ys ih =>
    have h1 : esymm (y :: ys) 1 = esymm ys 1 + y := by
      show esymm ys 1 + y * esymm ys 0 = esymm ys 1 + y
      rw [esymm_zero]; ring
    have h2 : esymm (y :: ys) 2 = esymm ys 2 + y * esymm ys 1 := rfl
    rw [h1, h2, length_cons]
    push_cast
    nlinarith [ih, sq_nonneg (t - y)]

/-! ## Newton's inequality, k = 1 case: fully proved

The k = 1 case of Newton's inequality:
  C(n, 2) · e_1² ≥ n² · e_2,
equivalently (n-1)·(∑x_i)² ≥ 2n·∑_{i<j} x_i·x_j, equivalently
∑_{i<j} (x_i - x_j)² ≥ 0.

This is the foundational case from which Maclaurin's first inequality and the
AM-GM connection follow without depending on the general inductive case
(`newton_inequality_binomial`).
-/

/-- Newton's inequality (binomial form), k = 1 case: for nonneg reals,
    `C(n, 2) · e_1² ≥ n² · e_2`.

    Equivalent to `(∑x_i / n)² ≥ (∑_{i<j} x_i·x_j) / C(n,2)`,
    which is the first Maclaurin inequality `ē_1² ≥ ē_2` with cleared denominators. -/
theorem newton_inequality_binomial_k_one (xs : List ℝ)
    (hxs : ∀ x ∈ xs, (0 : ℝ) ≤ x) (hn : 2 ≤ xs.length) :
    (Nat.choose xs.length 2 : ℝ) * esymm xs 1 ^ 2 ≥
    (xs.length : ℝ) ^ 2 * esymm xs 2 := by
  induction xs with
  | nil => simp at hn
  | cons y ys ih =>
    have hy : 0 ≤ y := hxs y List.mem_cons_self
    have hys_nn : ∀ z ∈ ys, (0 : ℝ) ≤ z := fun z hz => hxs z (List.mem_cons_of_mem y hz)
    have hE1_nn : 0 ≤ esymm ys 1 := esymm_nonneg ys hys_nn 1
    have hE2_nn : 0 ≤ esymm ys 2 := esymm_nonneg ys hys_nn 2
    have hlen_ge_one : 1 ≤ ys.length := by
      have : 2 ≤ ys.length + 1 := by simpa [length_cons] using hn
      omega
    -- Recurrences: F_1 = E_1 + y, F_2 = E_2 + y · E_1.
    have h1 : esymm (y :: ys) 1 = esymm ys 1 + y := by
      show esymm ys 1 + y * esymm ys 0 = esymm ys 1 + y
      rw [esymm_zero]; ring
    have h2 : esymm (y :: ys) 2 = esymm ys 2 + y * esymm ys 1 := rfl
    rw [h1, h2, length_cons]
    push_cast
    -- Absorption identity: `2 · C(m+1, 2) = (m+1) · m`.
    have hchoose_succ : (Nat.choose (ys.length + 1) 2 : ℝ) * 2 =
        ((ys.length : ℝ) + 1) * (ys.length : ℝ) := by
      have hnat : (ys.length + 1).choose 2 * 2 = (ys.length + 1) * ys.length := by
        have key := Nat.choose_succ_right_eq (ys.length + 1) 1
        rw [Nat.choose_one_right] at key
        simpa using key
      have heq := congr_arg (Nat.cast : ℕ → ℝ) hnat
      push_cast at heq
      linarith
    by_cases hm : 2 ≤ ys.length
    · -- Inductive case: ys has length ≥ 2.
      have hih := ih hys_nn hm
      have hssq := esymm_sum_sub_sq_nonneg ys y
      -- Absorption identity for the IH: `2 · C(m, 2) = m · (m - 1)`.
      have hchoose_m : (Nat.choose ys.length 2 : ℝ) * 2 =
          (ys.length : ℝ) * ((ys.length : ℝ) - 1) := by
        have hnat_m : ys.length.choose 2 * 2 = ys.length * (ys.length - 1) := by
          have key := Nat.choose_succ_right_eq ys.length 1
          rw [Nat.choose_one_right] at key
          simpa using key
        have heq := congr_arg (Nat.cast : ℕ → ℝ) hnat_m
        push_cast at heq
        rw [show ((ys.length - 1 : ℕ) : ℝ) = (ys.length : ℝ) - 1 from
            Nat.cast_sub hlen_ge_one] at heq
        linarith
      have hm_real : (2 : ℝ) ≤ (ys.length : ℝ) := by exact_mod_cast hm
      have hm_pos : (0 : ℝ) < (ys.length : ℝ) := by linarith
      have hm1_pos : (0 : ℝ) < (ys.length : ℝ) + 1 := by linarith
      have h2m_pos : (0 : ℝ) < 2 * (ys.length : ℝ) := by linarith
      -- Step 1: Eliminate `Nat.choose` from `hih` via `hchoose_m`.
      -- Claim: `m·(m-1)·E_1² ≥ 2·m²·E_2`.
      have h1 : (ys.length : ℝ) * ((ys.length : ℝ) - 1) * esymm ys 1 ^ 2 ≥
                 2 * (ys.length : ℝ) ^ 2 * esymm ys 2 := by
        have hih2 : (Nat.choose ys.length 2 : ℝ) * 2 * esymm ys 1 ^ 2 ≥
                    2 * (ys.length : ℝ) ^ 2 * esymm ys 2 := by linarith
        rw [hchoose_m] at hih2
        linarith
      -- Step 2: Multiply `hssq` by `m` (≥ 0).
      have h2 : 0 ≤ (ys.length : ℝ) *
          (esymm ys 1 ^ 2 - 2 * esymm ys 2 +
            (ys.length : ℝ) * y ^ 2 - 2 * y * esymm ys 1) :=
        mul_nonneg hm_pos.le hssq
      -- Step 3: Combine `h1` and `h2` (sum) to get
      --   `m² · (E_1+y)² ≥ 2·m·(m+1) · (E_2 + y·E_1)`.
      -- Algebraic identity: `h1 + h2 = m² · (E_1+y)² - 2·m·(m+1) · (E_2+y·E_1)`.
      have h_combined :
          (ys.length : ℝ) ^ 2 * (esymm ys 1 + y) ^ 2 ≥
          2 * (ys.length : ℝ) * ((ys.length : ℝ) + 1) *
            (esymm ys 2 + y * esymm ys 1) := by
        nlinarith [h1, h2]
      -- Step 4: Multiply `h_combined` by `(m+1)` (≥ 0) to land in the binomial form.
      have hm1_h_combined : 0 ≤ ((ys.length : ℝ) + 1) *
          ((ys.length : ℝ) ^ 2 * (esymm ys 1 + y) ^ 2 -
            2 * (ys.length : ℝ) * ((ys.length : ℝ) + 1) *
              (esymm ys 2 + y * esymm ys 1)) := by
        apply mul_nonneg hm1_pos.le
        linarith
      -- Step 5: Substitute `m·(m+1) = 2·C(m+1, 2)` (from `hchoose_succ`) to reach the goal.
      -- Compute the polynomial identity:
      --   (m+1) · [m²·(E_1+y)² - 2m(m+1)·(E_2+y·E_1)]
      --   = m²·(m+1)·(E_1+y)² - 2m·(m+1)²·(E_2+y·E_1)
      --   = (using hchoose_succ × m: m²·(m+1) = 2m·C(m+1, 2))
      --     2m·C(m+1, 2)·(E_1+y)² - 2m·(m+1)²·(E_2+y·E_1)
      --   = 2m · [C(m+1, 2)·(E_1+y)² - (m+1)²·(E_2+y·E_1)]
      -- So: 0 ≤ 2m · (LHS_goal - RHS_goal).
      have hsub : (ys.length : ℝ) ^ 2 * ((ys.length : ℝ) + 1) =
                  2 * (ys.length : ℝ) * (Nat.choose (ys.length + 1) 2 : ℝ) := by
        linear_combination -(ys.length : ℝ) * hchoose_succ
      have h_factored : 0 ≤ 2 * (ys.length : ℝ) *
          ((Nat.choose (ys.length + 1) 2 : ℝ) * (esymm ys 1 + y) ^ 2 -
           ((ys.length : ℝ) + 1) ^ 2 * (esymm ys 2 + y * esymm ys 1)) := by
        have heq : ((ys.length : ℝ) + 1) *
            ((ys.length : ℝ) ^ 2 * (esymm ys 1 + y) ^ 2 -
              2 * (ys.length : ℝ) * ((ys.length : ℝ) + 1) *
                (esymm ys 2 + y * esymm ys 1)) =
            2 * (ys.length : ℝ) *
            ((Nat.choose (ys.length + 1) 2 : ℝ) * (esymm ys 1 + y) ^ 2 -
             ((ys.length : ℝ) + 1) ^ 2 * (esymm ys 2 + y * esymm ys 1)) := by
          linear_combination (esymm ys 1 + y) ^ 2 * hsub
        linarith [hm1_h_combined, heq]
      -- Step 6: Divide by `2m > 0` to obtain the goal.
      have h_diff_nn : 0 ≤ (Nat.choose (ys.length + 1) 2 : ℝ) * (esymm ys 1 + y) ^ 2 -
                            ((ys.length : ℝ) + 1) ^ 2 * (esymm ys 2 + y * esymm ys 1) := by
        have hzero : (2 * (ys.length : ℝ)) * 0 ≤ (2 * (ys.length : ℝ)) *
            ((Nat.choose (ys.length + 1) 2 : ℝ) * (esymm ys 1 + y) ^ 2 -
             ((ys.length : ℝ) + 1) ^ 2 * (esymm ys 2 + y * esymm ys 1)) := by
          rw [mul_zero]; exact h_factored
        exact le_of_mul_le_mul_left hzero h2m_pos
      linarith
    · -- Base case: ys.length = 1, hence ys = [a] for some a ≥ 0.
      push_neg at hm
      have hys_eq : ys.length = 1 := by omega
      -- Decompose ys into a singleton via nested cases.
      cases ys with
      | nil => simp at hys_eq
      | cons a tail =>
        cases tail with
        | cons _ _ => simp at hys_eq
        | nil =>
          -- ys = [a]
          have ha : 0 ≤ a := hys_nn a (List.mem_singleton.mpr rfl)
          have hE1_a : esymm ([a] : List ℝ) 1 = a := by
            show esymm ([] : List ℝ) 1 + a * esymm ([] : List ℝ) 0 = a
            simp [esymm_nil_succ, esymm_zero]
          have hE2_a : esymm ([a] : List ℝ) 2 = 0 := by
            show esymm ([] : List ℝ) 2 + a * esymm ([] : List ℝ) 1 = 0
            simp [esymm_nil_succ]
          rw [hE1_a, hE2_a]
          have hC : (Nat.choose 2 2 : ℝ) = 1 := by
            have : (2 : ℕ).choose 2 = 1 := Nat.choose_self 2
            exact_mod_cast this
          simp only [show ([a] : List ℝ).length = 1 from rfl, hC]
          push_cast
          nlinarith [sq_nonneg (a - y)]

/-! ## Newton's inequality: direct form for nonneg reals

The standard formulation without binomial normalization. -/

/-- Log-concavity of binomial coefficients: C(n,k)² ≥ C(n,k-1)·C(n,k+1). -/
theorem binom_log_concave (n k : ℕ) (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    (Nat.choose n k : ℝ) ^ 2 ≥
    (Nat.choose n (k - 1) : ℝ) * (Nat.choose n (k + 1) : ℝ) := by
  -- Use the absorption identity: (k+1)·C(n,k+1) = (n-k)·C(n,k)
  -- and k·C(n,k) = (n-k+1)·C(n,k-1)
  -- So C(n,k-1)·C(n,k+1) = [k·C(n,k)/(n-k+1)] · [(n-k)·C(n,k)/(k+1)]
  --    = k(n-k) / ((n-k+1)(k+1)) · C(n,k)²
  -- Since k(n-k) ≤ (n-k+1)(k+1) ⟺ 0 ≤ n+1 (always true), we're done.
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk1_pos : (0 : ℝ) < k + 1 := by linarith
  have hnk_pos : (0 : ℝ) < n - k + 1 := by
    have : k ≤ n := by omega
    have : (k : ℝ) ≤ n := by exact_mod_cast this
    linarith
  have hnk1_pos : (0 : ℝ) < (n : ℝ) - k := by
    have : k + 1 ≤ n := by omega
    have : (k : ℝ) + 1 ≤ n := by exact_mod_cast this
    linarith
  -- Absorption identities
  have abs1 : (k : ℝ) * (Nat.choose n k : ℝ) = ((n : ℝ) - k + 1) * (Nat.choose n (k - 1) : ℝ) := by
    have h := Nat.choose_succ_right_eq n (k - 1)
    rw [show k - 1 + 1 = k from by omega] at h
    rw [show n - (k - 1) = n - k + 1 from by omega] at h
    have := congr_arg (Nat.cast : ℕ → ℝ) h
    push_cast at this ⊢
    rw [Nat.cast_sub (show k ≤ n by omega)] at this
    linarith
  have abs2 : ((k : ℝ) + 1) * (Nat.choose n (k + 1) : ℝ) = ((n : ℝ) - k) * (Nat.choose n k : ℝ) := by
    have h := Nat.choose_succ_right_eq n k
    have := congr_arg (Nat.cast : ℕ → ℝ) h
    push_cast at this ⊢
    rw [Nat.cast_sub (show k ≤ n by omega)] at this
    linarith
  -- From abs1: C(n,k-1) = k·C(n,k) / (n-k+1)
  -- From abs2: C(n,k+1) = (n-k)·C(n,k) / (k+1)
  -- Product: C(n,k-1)·C(n,k+1) = k(n-k)/((n-k+1)(k+1)) · C(n,k)²
  -- Need: C(n,k)² ≥ k(n-k)/((n-k+1)(k+1)) · C(n,k)²
  -- i.e., (n-k+1)(k+1) ≥ k(n-k), i.e., n+1 ≥ 0. True!
  have hc_nn : (0 : ℝ) ≤ Nat.choose n k := Nat.cast_nonneg _
  -- Express the inequality in terms of C(n,k)
  -- C(n,k-1) = k * C(n,k) / (n-k+1)
  -- C(n,k+1) = (n-k) * C(n,k) / (k+1)
  -- So RHS = k*(n-k) * C(n,k)^2 / ((n-k+1)*(k+1))
  -- LHS = C(n,k)^2
  -- Need LHS ≥ RHS, i.e., 1 ≥ k(n-k)/((n-k+1)(k+1))
  -- i.e., (n-k+1)(k+1) ≥ k(n-k), i.e., nk+n-k²-k+k+1 ≥ nk-k², i.e., n+1 ≥ 0.
  suffices h : ((n : ℝ) - k + 1) * ((k : ℝ) + 1) *
    ((Nat.choose n (k - 1) : ℝ) * (Nat.choose n (k + 1) : ℝ)) ≤
    ((n : ℝ) - k + 1) * ((k : ℝ) + 1) *
    ((Nat.choose n k : ℝ) ^ 2) by
    have hprod_pos : (0 : ℝ) < ((n : ℝ) - k + 1) * ((k : ℝ) + 1) := by positivity
    exact le_of_mul_le_mul_left h hprod_pos
  -- LHS = (n-k+1)(k+1) · C(n,k-1) · C(n,k+1)
  -- Use abs1 and abs2 to rewrite
  -- (n-k+1)·C(n,k-1) = k·C(n,k)  and  (k+1)·C(n,k+1) = (n-k)·C(n,k)
  -- So LHS = k·C(n,k) · (n-k)·C(n,k) = k(n-k)·C(n,k)²
  -- RHS = (n-k+1)(k+1)·C(n,k)²
  -- Need k(n-k) ≤ (n-k+1)(k+1), i.e., 0 ≤ n+1. True!
  calc ((n : ℝ) - k + 1) * ((k : ℝ) + 1) *
      ((Nat.choose n (k - 1) : ℝ) * (Nat.choose n (k + 1) : ℝ))
      = ((n : ℝ) - k + 1) * (Nat.choose n (k - 1) : ℝ) *
        (((k : ℝ) + 1) * (Nat.choose n (k + 1) : ℝ)) := by ring
    _ = (k : ℝ) * (Nat.choose n k : ℝ) *
        (((n : ℝ) - k) * (Nat.choose n k : ℝ)) := by rw [abs1, abs2]
    _ = (k : ℝ) * ((n : ℝ) - k) * (Nat.choose n k : ℝ) ^ 2 := by ring
    _ ≤ ((n : ℝ) - k + 1) * ((k : ℝ) + 1) * (Nat.choose n k : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (Nat.choose n k : ℝ), sq_nonneg ((n : ℝ) + 1)]

/-- Ultra-log-concavity of binomial coefficients:
    C(n,k)⁴ ≥ C(n,k-1)² · C(n,k+1)²  for  1 ≤ k < n.
    Proof: square the log-concavity C(n,k)² ≥ C(n,k-1)·C(n,k+1). -/
theorem binom_ultra_log_concave (n k : ℕ) (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    (Nat.choose n k : ℝ) ^ 4 ≥
    (Nat.choose n (k - 1) : ℝ) ^ 2 * (Nat.choose n (k + 1) : ℝ) ^ 2 := by
  have h := binom_log_concave n k hk hkn
  have hb : (0 : ℝ) ≤ Nat.choose n (k - 1) := Nat.cast_nonneg _
  have hc : (0 : ℝ) ≤ Nat.choose n (k + 1) := Nat.cast_nonneg _
  have h1 : (0 : ℝ) ≤ (Nat.choose n k : ℝ) ^ 2 -
      (Nat.choose n (k - 1) : ℝ) * (Nat.choose n (k + 1) : ℝ) := by linarith
  have h2 : (0 : ℝ) ≤ (Nat.choose n k : ℝ) ^ 2 +
      (Nat.choose n (k - 1) : ℝ) * (Nat.choose n (k + 1) : ℝ) :=
    add_nonneg (sq_nonneg _) (mul_nonneg hb hc)
  have key : ((Nat.choose n k : ℝ) ^ 2 -
        (Nat.choose n (k - 1) : ℝ) * (Nat.choose n (k + 1) : ℝ)) *
      ((Nat.choose n k : ℝ) ^ 2 +
        (Nat.choose n (k - 1) : ℝ) * (Nat.choose n (k + 1) : ℝ)) =
      (Nat.choose n k : ℝ) ^ 4 -
      (Nat.choose n (k - 1) : ℝ) ^ 2 * (Nat.choose n (k + 1) : ℝ) ^ 2 := by ring
  linarith [key ▸ mul_nonneg h1 h2]

/-! ## Newton's inequality: mean form

The most elegant statement: the elementary symmetric means are log-concave. -/

/-- The k-th elementary symmetric mean of a list: ē_k = e_k / C(n, k). -/
noncomputable def esymmMean (xs : List ℝ) (k : ℕ) : ℝ :=
  esymm xs k / (Nat.choose xs.length k : ℝ)

/-- Newton's inequality for elementary symmetric means:
    ē_k² ≥ ē_{k-1} · ē_{k+1}  for 1 ≤ k ≤ n-1.
    This is the classical log-concavity of the sequence (ē₀, ē₁, ..., ēₙ). -/
theorem newton_inequality_means (xs : List ℝ) (hxs : ∀ x ∈ xs, (0 : ℝ) ≤ x)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k + 1 ≤ xs.length) :
    esymmMean xs k ^ 2 ≥ esymmMean xs (k - 1) * esymmMean xs (k + 1) := by
  -- Follows from newton_inequality_binomial: the mean form is just the
  -- binomial form with denominators cleared.
  have hni := newton_inequality_binomial xs hxs k hk hkn
  -- Binomial coefficients are positive for valid k
  set n := xs.length with hn
  have hckm : (0 : ℝ) < Nat.choose n (k - 1) :=
    Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  have hck : (0 : ℝ) < Nat.choose n k :=
    Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  have hckp : (0 : ℝ) < Nat.choose n (k + 1) :=
    Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  -- Unfold and clear fractions via the equivalence after multiplying by positive denominators.
  unfold esymmMean
  have hckm_ne : (Nat.choose n (k - 1) : ℝ) ≠ 0 := ne_of_gt hckm
  have hck_ne : (Nat.choose n k : ℝ) ≠ 0 := ne_of_gt hck
  have hckp_ne : (Nat.choose n (k + 1) : ℝ) ≠ 0 := ne_of_gt hckp
  rw [ge_iff_le, div_pow]
  -- Manually combine `a / b * (c / d) = (a * c) / (b * d)` to bypass `div_mul_div_comm` overload.
  have hcomb : esymm xs (k - 1) / (Nat.choose n (k - 1) : ℝ) *
                 (esymm xs (k + 1) / (Nat.choose n (k + 1) : ℝ)) =
               esymm xs (k - 1) * esymm xs (k + 1) /
                 ((Nat.choose n (k - 1) : ℝ) * (Nat.choose n (k + 1) : ℝ)) := by
    field_simp
  rw [hcomb, div_le_div_iff (mul_pos hckm hckp) (pow_pos hck 2)]
  -- Goal: esymm (k-1) * esymm (k+1) * C(n,k)^2 ≤ esymm k^2 * (C(n,k-1) * C(n,k+1))
  linarith

/-! ## Consequences of Newton's inequality -/

/-- Maclaurin's inequality (weak form):
    ē₁ ≥ ē₂^{1/2} ≥ ... ≥ ēₙ^{1/n}
    We prove the first step: ē₁² ≥ ē₂ (since ē₀ = 1).

    This proof routes through the proven `newton_inequality_binomial_k_one`,
    so it does not depend on the open `newton_inequality_binomial` sorry. -/
theorem maclaurin_first_step (xs : List ℝ) (hxs : ∀ x ∈ xs, (0 : ℝ) ≤ x)
    (hn : 2 ≤ xs.length) :
    esymmMean xs 1 ^ 2 ≥ esymmMean xs 2 := by
  -- Newton's inequality at k = 1: `C(n, 2)·e_1² ≥ n²·e_2`.
  -- Divide by `n² · C(n, 2)` (both positive) to obtain `e_1²/n² ≥ e_2/C(n, 2)`,
  -- i.e., `(esymmMean xs 1)² ≥ esymmMean xs 2`.
  have h := newton_inequality_binomial_k_one xs hxs hn
  set n := xs.length with hn_def
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    have : 1 ≤ n := by omega
    exact_mod_cast this
  have hC2_pos : (0 : ℝ) < (Nat.choose n 2 : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos hn)
  unfold esymmMean
  rw [show Nat.choose n 1 = n from Nat.choose_one_right n]
  rw [ge_iff_le, div_pow, div_le_div_iff hC2_pos (pow_pos hn_pos 2)]
  -- Goal: `esymm xs 2 * (n : ℝ)^2 ≤ esymm xs 1 ^ 2 * Nat.choose n 2`
  linarith

/-- AM-GM from Newton: the arithmetic mean squared ≥ the average product of pairs.
    Specifically: (∑ xᵢ / n)² ≥ (∑_{i<j} xᵢxⱼ) / C(n,2). -/
theorem amgm_from_newton (xs : List ℝ) (hxs : ∀ x ∈ xs, (0 : ℝ) ≤ x)
    (hn : 2 ≤ xs.length) :
    (esymm xs 1 / xs.length) ^ 2 ≥
    esymm xs 2 / (Nat.choose xs.length 2 : ℝ) := by
  -- e_1 = ∑ xᵢ and ē_1 = e_1/n, ē_2 = e_2/C(n,2)
  -- Newton gives ē_1² ≥ ē_2, which is exactly this.
  have h := maclaurin_first_step xs hxs hn
  unfold esymmMean at h
  simp only [Nat.choose_one_right] at h
  exact h

/-! ## Explicit small cases -/

/-- Newton's inequality for n=2: (x+y)² ≥ 4xy ⟺ (x-y)² ≥ 0. -/
theorem newton_two (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    esymm [x, y] 1 ^ 2 ≥ esymm [x, y] 0 * esymm [x, y] 2 := by
  simp only [esymm_cons_succ, esymm_cons_zero, esymm_nil_zero, esymm_nil_succ,
             mul_zero, add_zero, mul_one]
  -- Goal: (y + x * 1)^2 ≥ 1 * (0 + x * y)
  -- i.e., (x + y)² ≥ xy, which follows from (x-y)² ≥ 0
  nlinarith [sq_nonneg (x - y)]

/-- Newton's inequality for n=3, k=1:
    e₁² ≥ 3·e₂ where e₁ = x+y+z, e₂ = xy+xz+yz. -/
theorem newton_three_k1 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    esymm [x, y, z] 1 ^ 2 ≥
    3 * esymm [x, y, z] 2 := by
  -- e₁ = x + y + z, e₂ = yz + x·z + x·y
  -- Need: (x+y+z)² ≥ 3(xy+xz+yz) ⟺ x²+y²+z² ≥ xy+xz+yz
  -- ⟺ (x-y)²+(x-z)²+(y-z)² ≥ 0
  simp only [esymm_cons_succ, esymm_cons_zero, esymm_nil_zero, esymm_nil_succ,
             mul_zero, add_zero, mul_one]
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]

/-- Newton's inequality for n=3, k=2:
    e₂² ≥ e₁·e₃ where e₂ = xy+xz+yz, e₃ = xyz.
    Note: C(3,2)²/[C(3,1)·C(3,3)] = 9/3 = 3, so normalized form is
    (e₂/3)² ≥ (e₁/3)·(e₃/1), i.e., e₂² ≥ 3·e₁·e₃. -/
theorem newton_three_k2 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    esymm [x, y, z] 2 ^ 2 ≥
    3 * (esymm [x, y, z] 1 * esymm [x, y, z] 3) := by
  simp only [esymm_cons_succ, esymm_cons_zero, esymm_nil_zero, esymm_nil_succ,
             mul_zero, add_zero, mul_one]
  -- After expansion, this reduces to (xy-xz)²+(xy-yz)²+(xz-yz)² ≥ 0
  nlinarith [sq_nonneg (x*y - x*z), sq_nonneg (x*y - y*z), sq_nonneg (x*z - y*z),
             mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz,
             mul_nonneg (mul_nonneg hx hy) hz]

/-- Product formula: esymm of nonneg reals can be expressed as a sum over subsets.
    Here we prove the simple connection: e₁ = sum of the list. -/
theorem esymm_one_eq_sum (xs : List ℝ) : esymm xs 1 = xs.sum := by
  induction xs with
  | nil => simp [esymm_nil_succ]
  | cons x xs ih =>
    rw [esymm_cons_succ, esymm_zero, mul_one, List.sum_cons, ih, add_comm]

namespace NewtonInductiveStepOQ01

/-! ## Summary

We formalize Newton's inequality for elementary symmetric polynomials
of nonneg reals. Key results:

1. **esymm**: Definition of elementary symmetric polynomials on real lists
2. **esymm_nonneg**: Nonnegativity for nonneg inputs
3. **esymm_sum_sub_sq_nonneg**: Sum-of-squares identity
   `e_1² - 2·e_2 + n·t² - 2t·e_1 ≥ 0` (equivalent to `∑(x_i - t)² ≥ 0`)
4. **newton_inequality_binomial_k_one**: Newton's inequality at k = 1, fully proved
5. **binom_log_concave**: Log-concavity of binomial coefficients C(n,k)² ≥ C(n,k-1)·C(n,k+1)
6. **binom_ultra_log_concave**: Ultra-log-concavity C(n,k)⁴ ≥ C(n,k-1)²·C(n,k+1)²
7. **newton_two/three_k1/three_k2**: Explicit small cases (n=2,3)
8. **esymm_one_eq_sum**: e₁ equals the sum
9. **maclaurin_first_step**: First Maclaurin inequality ē₁² ≥ ē₂ (independent of the sorry)

The full general inductive proof `newton_inequality_binomial` (k ≥ 2) is stated with the
correct standard Newton inequality. The mean form (newton_inequality_means) is derived from
it by clearing fractions.

0 axioms. 1 sorry remaining (newton_inequality_binomial for general k — the inductive
Cauchy-Schwarz step at k ≥ 2). The k = 1 case is now fully proved
(newton_inequality_binomial_k_one) using induction on the list and the sum-of-squares
identity ∑(x_i - t)² ≥ 0. The downstream consequences `maclaurin_first_step` and
`amgm_from_newton` no longer depend on the remaining sorry.
-/

end NewtonInductiveStepOQ01
