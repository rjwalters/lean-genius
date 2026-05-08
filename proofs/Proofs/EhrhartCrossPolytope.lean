/-
  Ehrhart Polynomial of the Cross-Polytope: Axiom-Free First-Principles Proof
  (ehrhart-cube-proven-oq-02)

  The d-dimensional cross-polytope (hyperoctahedron):
    B_d = {x ∈ ℝᵈ : ‖x‖₁ ≤ 1}

  has Ehrhart polynomial L(B_d, n) = Σ_{k=0}^d 2^k · C(d,k) · C(n,k),
  which counts integer lattice points in n·B_d = {x ∈ ℤᵈ : Σ|xᵢ| ≤ n}.

  Proved WITHOUT the general Ehrhart existence theorem axiom, using only:
  - Pascal's rule: C(d+1,k+1) = C(d,k) + C(d,k+1)
  - Hockey-stick: Σ_{m<n} C(m,k) = C(n,k+1)
  - Finset sum algebra

  This extends EhrhartCubeProven.lean and EhrhartSimplexProven.lean to
  a third polytope family, answering ehrhart-cube-proven OQ-02:
  "Can Ehrhart polynomials for polytopes with known formulas be proved
   from first principles without the general existence theorem?"

  Main results (12 theorems, axiom-free, 0 sorries):
  1. crossEhrhart_d0          — L(B_0,n) = 1
  2. crossEhrhart_n0          — L(B_d,0) = 1
  3. crossEhrhart_d1          — L(B_1,n) = 2n+1
  4. crossEhrhart_d2          — L(B_2,n) = 2n²+2n+1 [proved by recursion]
  5. crossEhrhart_pos          — L(B_d,n) ≥ 1
  6. crossEhrhart_mono         — L(B_d,n) ≤ L(B_d,n+1)
  7. sum_choose_range          — hockey-stick Σ C(m,k) = C(n,k+1)
  8. sum_shift_hockey          — sum interchange using hockey-stick
  9. crossEhrhart_expand       — key algebraic expansion (Pascal split)
  10. crossEhrhart_succ_d      — geometric recursion: L(B_{d+1},n) = L(B_d,n) + 2·Σ L(B_d,m)
  11. crossEhrhart_is_poly     — polynomial identification via descPochhammer
  12. crossBall_card           — geometric meaning: |crossBall d n| = crossEhrhart d n
                                  (S6 closure, 2026-05-08, via Finset slicing)
-/
import Mathlib

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

open Finset Nat

namespace EhrhartCrossPolytope

-- ============================================================
-- PART I: The Ehrhart Formula
-- ============================================================

/-- **Ehrhart formula for the d-dimensional cross-polytope (hyperoctahedron)**:
    L(B_d, n) = Σ_{k=0}^d 2^k · C(d,k) · C(n,k)

    Counts lattice points in n·B_d = {x : Fin d → ℤ | Σ |xᵢ| ≤ n}.
    Also called the **central Delannoy formula**; see OEIS A001850 for d=2. -/
def crossEhrhart (d n : ℕ) : ℕ :=
  ∑ k ∈ range (d + 1), 2 ^ k * Nat.choose d k * Nat.choose n k

-- ============================================================
-- PART II: Base Cases
-- ============================================================

/-- B_0 is a single point; lattice count is always 1. -/
theorem crossEhrhart_d0 (n : ℕ) : crossEhrhart 0 n = 1 := by
  simp [crossEhrhart]

/-- At dilation 0, only the origin lies in n·B_d.
    C(0,k) = 0 for k ≥ 1, so only the k=0 term survives. -/
theorem crossEhrhart_n0 (d : ℕ) : crossEhrhart d 0 = 1 := by
  simp only [crossEhrhart]
  have hkey : ∑ k ∈ range (d + 1), 2 ^ k * Nat.choose d k * Nat.choose 0 k =
      2 ^ 0 * Nat.choose d 0 * Nat.choose 0 0 :=
    Finset.sum_eq_single 0
      (fun k _ hk => by
        rcases k with _ | k
        · exact absurd rfl hk
        · simp [Nat.choose_eq_zero_of_lt (Nat.succ_pos k)])
      (fun h => absurd (Finset.mem_range.mpr (Nat.succ_pos d)) h)
  rw [hkey]; simp

/-- B_1 = [-1,1]: dilation n gives {-n,...,n}, so 2n+1 lattice points. -/
theorem crossEhrhart_d1 (n : ℕ) : crossEhrhart 1 n = 2 * n + 1 := by
  simp [crossEhrhart, sum_range_succ, Nat.choose_one_right]; ring

-- Spot checks (concrete verification, proved by computation)
example : crossEhrhart 1 3 = 7 := by native_decide
example : crossEhrhart 2 1 = 5 := by native_decide
example : crossEhrhart 2 2 = 13 := by native_decide
example : crossEhrhart 3 1 = 7 := by native_decide

-- ============================================================
-- PART III: Structural Properties
-- ============================================================

/-- The formula is at least 1 (origin always counts). -/
theorem crossEhrhart_pos (d n : ℕ) : 1 ≤ crossEhrhart d n := by
  simp only [crossEhrhart]
  calc 1 = 2 ^ 0 * Nat.choose d 0 * Nat.choose n 0 := by simp
    _ ≤ ∑ k ∈ range (d + 1), 2 ^ k * Nat.choose d k * Nat.choose n k :=
        Finset.single_le_sum (fun k _ => Nat.zero_le (2^k * Nat.choose d k * Nat.choose n k))
          (Finset.mem_range.mpr (Nat.succ_pos d))

/-- Monotone in the dilation parameter: more dilation, more lattice points. -/
theorem crossEhrhart_mono (d n : ℕ) : crossEhrhart d n ≤ crossEhrhart d (n + 1) := by
  simp only [crossEhrhart]
  apply Finset.sum_le_sum
  intro k _
  gcongr
  omega

-- ============================================================
-- PART IV: Hockey-Stick Identity
-- ============================================================

/-- **Hockey-stick identity**: Σ_{m=0}^{n-1} C(m,k) = C(n,k+1).

    Proved by induction: the step uses Pascal's rule
    C(n+1,k+1) = C(n,k) + C(n,k+1). -/
lemma sum_choose_range (n k : ℕ) :
    ∑ m ∈ range n, Nat.choose m k = Nat.choose n (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    linarith [Nat.choose_succ_succ n k]

/-- **Sum interchange**: converts Σ_k 2^k·C(d,k)·C(n,k+1) to Σ_{m<n} Σ_k 2^k·C(d,k)·C(m,k).

    Key step: hockey-stick replaces C(n,k+1) = Σ_{m<n} C(m,k), then
    the double sum is commuted. -/
lemma sum_shift_hockey (d n : ℕ) :
    ∑ k ∈ range (d + 1), 2 ^ k * Nat.choose d k * Nat.choose n (k + 1) =
    ∑ m ∈ range n, ∑ k ∈ range (d + 1), 2 ^ k * Nat.choose d k * Nat.choose m k := by
  conv_lhs =>
    arg 2; ext k
    rw [show 2 ^ k * Nat.choose d k * Nat.choose n (k + 1) =
        ∑ m ∈ range n, (2 ^ k * Nat.choose d k * Nat.choose m k)
        from by rw [← sum_choose_range]; rw [Finset.mul_sum]]
  rw [Finset.sum_comm]

-- ============================================================
-- PART V: Key Algebraic Lemma
-- ============================================================

/-- **Key algebraic expansion**: L(B_{d+1},n) = L(B_d,n) + 2·Σ_k 2^k·C(d,k)·C(n,k+1).

    Proof strategy:
    1. Extract k=0 from the (d+1)-sum using sum_range_succ'.
    2. Apply Pascal C(d+1,k+1) = C(d,k) + C(d,k+1) to each term.
    3. Separate: 2·Σ 2^k·C(d,k)·C(n,k+1) + 2·Σ 2^k·C(d,k+1)·C(n,k+1).
    4. Show the last sum equals (crossEhrhart d n - 1)/2 using sum_range_succ'.
    5. Combine: 1 + 2A + (crossEhrhart d n - 1) = crossEhrhart d n + 2A. -/
theorem crossEhrhart_expand (d n : ℕ) :
    crossEhrhart (d + 1) n = crossEhrhart d n +
    2 * ∑ k ∈ range (d + 1), 2 ^ k * Nat.choose d k * Nat.choose n (k + 1) := by
  simp only [crossEhrhart]
  -- Extract k=0 from LHS: ∑_{k<d+2} f(k) = f(0) + ∑_{k<d+1} f(k+1)
  rw [sum_range_succ' (f := fun k => 2^k * Nat.choose (d+1) k * Nat.choose n k)]
  -- f(0) = 2^0 * C(d+1,0) * C(n,0) = 1
  simp only [pow_zero, one_mul, Nat.choose_zero_right]
  -- Apply Pascal: C(d+1,k+1) = C(d,k) + C(d,k+1)
  rw [show ∑ k ∈ range (d + 1), 2 ^ (k + 1) * Nat.choose (d + 1) (k + 1) * Nat.choose n (k + 1) =
      ∑ k ∈ range (d + 1), 2 ^ (k + 1) * (Nat.choose d k + Nat.choose d (k + 1)) * Nat.choose n (k + 1)
      from by
        apply Finset.sum_congr rfl
        intro k _
        rw [Nat.choose_succ_succ d k]]
  -- Factor out 2 and distribute over addition
  rw [show ∑ k ∈ range (d + 1), 2 ^ (k + 1) * (Nat.choose d k + Nat.choose d (k + 1)) * Nat.choose n (k + 1) =
      2 * ∑ k ∈ range (d + 1), 2 ^ k * Nat.choose d k * Nat.choose n (k + 1) +
      2 * ∑ k ∈ range (d + 1), 2 ^ k * Nat.choose d (k + 1) * Nat.choose n (k + 1)
      from by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _; ring]
  -- Key: Σ 2^k·C(d,k)·C(n,k) = 1 + 2·Σ 2^k·C(d,k+1)·C(n,k+1)
  -- Proof: extract k=0 from Σ 2^k·C(d,k)·C(n,k) and use C(d,d+1)=0 for the last term
  have key : ∑ k ∈ range (d + 1), 2 ^ k * Nat.choose d k * Nat.choose n k =
      1 + 2 * ∑ k ∈ range (d + 1), 2 ^ k * Nat.choose d (k + 1) * Nat.choose n (k + 1) := by
    rw [sum_range_succ' (f := fun k => 2 ^ k * Nat.choose d k * Nat.choose n k)]
    simp only [pow_zero, one_mul, Nat.choose_zero_right]
    -- Drop k=d term from RHS sum (it's 0 since C(d,d+1) = 0)
    conv_rhs =>
      rw [show ∑ k ∈ range (d + 1), 2 ^ k * Nat.choose d (k + 1) * Nat.choose n (k + 1) =
          ∑ k ∈ range d, 2 ^ k * Nat.choose d (k + 1) * Nat.choose n (k + 1)
          from by
            rw [sum_range_succ]
            simp [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self d)]]
    rw [Finset.mul_sum]
    have heq : ∑ k ∈ range d, 2 ^ (k + 1) * Nat.choose d (k + 1) * Nat.choose n (k + 1) =
        ∑ k ∈ range d, 2 * (2 ^ k * Nat.choose d (k + 1) * Nat.choose n (k + 1)) := by
      apply Finset.sum_congr rfl; intro k _; ring
    linarith [heq]
  linarith [key]

-- ============================================================
-- PART VI: Main Geometric Recursion
-- ============================================================

/-- **Geometric recursion**: slicing B_{d+1} along the last coordinate.

    For x_{d+1} = 0: contributes |{x ∈ ℤᵈ : Σ|xᵢ| ≤ n}| = L(B_d,n).
    For x_{d+1} = ±j (j = 1,...,n): each contributes L(B_d, n-j).
    Summing: L(B_{d+1},n) = L(B_d,n) + 2·Σ_{j=1}^n L(B_d,n-j)
                           = L(B_d,n) + 2·Σ_{m=0}^{n-1} L(B_d,m). -/
theorem crossEhrhart_succ_d (d n : ℕ) :
    crossEhrhart (d + 1) n =
    crossEhrhart d n + 2 * ∑ m ∈ range n, crossEhrhart d m := by
  rw [crossEhrhart_expand]
  have hshift : ∑ k ∈ range (d + 1), 2 ^ k * Nat.choose d k * Nat.choose n (k + 1) =
      ∑ m ∈ range n, crossEhrhart d m := by
    rw [sum_shift_hockey]
    apply Finset.sum_congr rfl
    intro m _
    simp [crossEhrhart]
  linarith [hshift]

-- ============================================================
-- PART VIb: Low-Dimensional Formulas (proved using recursion)
-- ============================================================

/-- B_2 = diamond (square at 45°): L(B_2,n) = 2n²+2n+1.
    Proved by induction: each step adds L(B_1,n+1) + L(B_1,n) = (2n+3)+(2n+1) = 4n+4. -/
theorem crossEhrhart_d2 (n : ℕ) : crossEhrhart 2 n = 2 * n ^ 2 + 2 * n + 1 := by
  induction n with
  | zero => simp [crossEhrhart_n0]
  | succ n ih =>
    have hrec : crossEhrhart 2 (n + 1) =
        crossEhrhart 2 n + crossEhrhart 1 (n + 1) + crossEhrhart 1 n := by
      rw [crossEhrhart_succ_d 1 (n + 1), crossEhrhart_succ_d 1 n, sum_range_succ]
      ring
    rw [hrec, ih, crossEhrhart_d1, crossEhrhart_d1]; ring

-- More spot checks (rely on crossEhrhart_succ_d being proved)
example : crossEhrhart 2 3 = 25 := by native_decide
example : crossEhrhart 3 2 = 25 := by native_decide
example : crossEhrhart 3 3 = 63 := by native_decide
example : crossEhrhart 3 4 = 129 := by native_decide

-- ============================================================
-- PART VII: Ehrhart Polynomial Identification
-- ============================================================

-- Helper: natDegree of `descPochhammer ℚ k` is at most `k`.
private lemma natDegree_descPochhammer_le (k : ℕ) :
    (Polynomial.descPochhammer ℚ k).natDegree ≤ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Polynomial.descPochhammer_succ_right]
    refine le_trans Polynomial.natDegree_mul_le ?_
    have h1 : (Polynomial.X - ((k : ℕ) : Polynomial ℚ)).natDegree ≤ 1 := by
      refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
      simp
    omega

-- Helper: `(descPochhammer ℚ k).eval (n : ℚ) = ↑(n.descFactorial k)`.
private lemma eval_descPochhammer_natCast (k n : ℕ) :
    (Polynomial.descPochhammer ℚ k).eval ((n : ℕ) : ℚ) =
      ((n.descFactorial k : ℕ) : ℚ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Polynomial.descPochhammer_succ_right]
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
               Polynomial.eval_natCast, ih]
    rcases le_or_lt k n with hkn | hkn
    · -- k ≤ n: descFactorial unfolds nicely
      rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub hkn]
      ring
    · -- k > n: both descFactorial values vanish
      have hzero_at : ∀ m, n.descFactorial (n + 1 + m) = 0 := by
        intro m
        induction m with
        | zero =>
          show n.descFactorial (n + 1) = 0
          rw [Nat.descFactorial_succ, Nat.sub_self, zero_mul]
        | succ m ihm =>
          rw [show n + 1 + (m + 1) = (n + 1 + m) + 1 from by omega,
              Nat.descFactorial_succ, ihm, mul_zero]
      have hk_zero : n.descFactorial k = 0 := by
        obtain ⟨m, hm⟩ : ∃ m, k = n + 1 + m := ⟨k - (n + 1), by omega⟩
        rw [hm]; exact hzero_at m
      have hk1_zero : n.descFactorial (k + 1) = 0 := by
        rw [Nat.descFactorial_succ, hk_zero, mul_zero]
      rw [hk_zero, hk1_zero]
      simp

/-- **The formula is a polynomial of degree ≤ d in n** (over ℚ).

    Each term 2^k · C(d,k) · C(n,k) is a polynomial of degree k in n,
    with C(n,k) = n(n-1)···(n-k+1)/k! a polynomial of degree k.
    So the sum is a polynomial of degree d.

    The construction is
    `P = Σ_{k=0}^d C ((2^k · C(d,k))/k!) · descPochhammer ℚ k`.
    Each summand has natDegree ≤ k ≤ d. Evaluation at `(n : ℚ)` uses
    `descPochhammer ℚ k`.eval = `descFactorial = k! · C(n,k)`, with
    the `k!` cancelling against the coefficient denominator. -/
theorem crossEhrhart_is_poly (d : ℕ) :
    ∃ (P : Polynomial ℚ), P.natDegree ≤ d ∧
    ∀ n : ℕ, P.eval (n : ℚ) = (crossEhrhart d n : ℚ) := by
  refine ⟨∑ k ∈ range (d + 1),
    Polynomial.C ((2 ^ k : ℚ) * (Nat.choose d k : ℚ) / (k.factorial : ℚ)) *
      Polynomial.descPochhammer ℚ k, ?_, ?_⟩
  · -- natDegree ≤ d
    refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
    apply Finset.sup_le
    intro k hk
    refine le_trans Polynomial.natDegree_mul_le ?_
    rw [Polynomial.natDegree_C, zero_add]
    have hk_le : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    exact le_trans (natDegree_descPochhammer_le k) hk_le
  · -- eval property at every Nat n
    intro n
    rw [Polynomial.eval_finset_sum, crossEhrhart, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Polynomial.eval_mul, Polynomial.eval_C, eval_descPochhammer_natCast,
        Nat.descFactorial_eq_factorial_mul_choose]
    have hk_ne : (k.factorial : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero k
    push_cast
    field_simp [hk_ne]
    ring

-- ============================================================
-- PART VIII: Connection to Lattice Points
-- ============================================================

/-- **Lattice point model**: encode n·B_d via coordinates in {0,...,2n}
    with 0 ≡ -n, n ≡ 0, 2n ≡ n (centered at n). -/
def crossBall (d n : ℕ) : Finset (Fin d → Fin (2 * n + 1)) :=
  Finset.univ.filter fun x =>
    ∑ i, (if (x i).val ≤ n then n - (x i).val else (x i).val - n) ≤ n

/-- The "centered weight" `(if a ≤ n then n - a else a - n)` of a Nat `a` relative
    to center `n` is at most `M` iff `a` lies in the interval `[n - M, n + M]`. -/
private lemma cweight_le_iff (n a M : ℕ) :
    (if a ≤ n then n - a else a - n) ≤ M ↔ n - M ≤ a ∧ a ≤ n + M := by
  by_cases h : a ≤ n
  · rw [if_pos h]; omega
  · push_neg at h; rw [if_neg (not_le.mpr h)]; omega

/-- "Translate" the centered weight: when `M ≤ n` and `a ∈ [n - M, n + M]`,
    the weight at center `n` of `a` equals the weight at center `M` of `a - (n - M)`. -/
private lemma cweight_translate (n M a : ℕ) (hM : M ≤ n)
    (h_lo : n - M ≤ a) (h_hi : a ≤ n + M) :
    (if a ≤ n then n - a else a - n) =
    (if a - (n - M) ≤ M then M - (a - (n - M)) else a - (n - M) - M) := by
  by_cases h : a ≤ n
  · rw [if_pos h, if_pos (by omega)]; omega
  · push_neg at h
    rw [if_neg (not_le.mpr h), if_neg (by push_neg; omega)]
    omega

/-- If the sum of centered weights at center `n` is at most `M`, then each
    individual term is at most `M`. (Each summand is non-negative.) -/
private lemma cweight_sum_individual {d n M : ℕ}
    (y : Fin d → Fin (2 * n + 1))
    (hsum : ∑ i, (if (y i).val ≤ n then n - (y i).val else (y i).val - n) ≤ M)
    (j : Fin d) :
    (if (y j).val ≤ n then n - (y j).val else (y j).val - n) ≤ M :=
  (Finset.single_le_sum
    (f := fun i => if (y i).val ≤ n then n - (y i).val else (y i).val - n)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans hsum

/-- Range corollary: a sum-of-cweights bound at center `n` with budget `M ≤ n`
    forces each `(y j).val` into the interval `[n - M, n + M]`. -/
private lemma cweight_sum_range {d n M : ℕ} (hM : M ≤ n)
    (y : Fin d → Fin (2 * n + 1))
    (hsum : ∑ i, (if (y i).val ≤ n then n - (y i).val else (y i).val - n) ≤ M)
    (j : Fin d) :
    n - M ≤ (y j).val ∧ (y j).val ≤ n + M :=
  (cweight_le_iff n (y j).val M).mp (cweight_sum_individual y hsum j)

/-- **Fiber bijection**: when `M ≤ n`, the set of `y : Fin d → Fin (2n+1)` whose
    centered-weight sum at `n` is at most `M` is in bijection with `crossBall d M`,
    via the translation `yᵢ ↦ ⟨(yᵢ).val - (n - M), _⟩`.

    This is the key counting lemma for the slicing decomposition: each fiber of
    `crossBall (d+1) n` over the last coordinate is in bijection with `crossBall d M`
    for the appropriate `M`. -/
private lemma fiber_card_eq_crossBall_card (d n M : ℕ) (hM : M ≤ n) :
    (Finset.univ.filter
      fun y : Fin d → Fin (2 * n + 1) =>
        ∑ i, (if (y i).val ≤ n then n - (y i).val else (y i).val - n) ≤ M).card =
    (crossBall d M).card := by
  apply Finset.card_bij'
    -- Forward: y ↦ z where z idx := (y idx).val - (n - M).
    (fun y hy idx =>
      ⟨(y idx).val - (n - M), by
        have hsum :
            ∑ i, (if (y i).val ≤ n then n - (y i).val else (y i).val - n) ≤ M := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
          exact hy
        obtain ⟨h_lo, h_hi⟩ := cweight_sum_range hM y hsum idx
        omega⟩)
    -- Backward: z ↦ y' where y' idx := (z idx).val + (n - M).
    (fun z _ idx =>
      ⟨(z idx).val + (n - M), by
        have hcoord : (z idx).val < 2 * M + 1 := (z idx).is_lt
        omega⟩)
    -- (1) Forward image lies in `crossBall d M`.
    (by
      intro y hy
      have hsum :
          ∑ i, (if (y i).val ≤ n then n - (y i).val else (y i).val - n) ≤ M := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        exact hy
      simp only [crossBall, Finset.mem_filter, Finset.mem_univ, true_and]
      have heq :
          ∑ i, (if ((y i).val - (n - M)) ≤ M
                  then M - ((y i).val - (n - M))
                  else ((y i).val - (n - M)) - M) =
          ∑ i, (if (y i).val ≤ n then n - (y i).val else (y i).val - n) := by
        apply Finset.sum_congr rfl
        intro i _
        obtain ⟨h_lo, h_hi⟩ := cweight_sum_range hM y hsum i
        exact (cweight_translate n M (y i).val hM h_lo h_hi).symm
      show ∑ i, (if ((y i).val - (n - M)) ≤ M
                  then M - ((y i).val - (n - M))
                  else ((y i).val - (n - M)) - M) ≤ M
      rw [heq]; exact hsum)
    -- (2) Backward image lies in the filter set.
    (by
      intro z hz
      have hzsum :
          ∑ i, (if (z i).val ≤ M then M - (z i).val else (z i).val - M) ≤ M := by
        simp only [crossBall, Finset.mem_filter, Finset.mem_univ, true_and] at hz
        exact hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have heq :
          ∑ i, (if ((z i).val + (n - M)) ≤ n
                  then n - ((z i).val + (n - M))
                  else ((z i).val + (n - M)) - n) =
          ∑ i, (if (z i).val ≤ M then M - (z i).val else (z i).val - M) := by
        apply Finset.sum_congr rfl
        intro i _
        have h_lo : n - M ≤ (z i).val + (n - M) := Nat.le_add_left _ _
        have h_hi : (z i).val + (n - M) ≤ n + M := by
          have hzlt : (z i).val < 2 * M + 1 := (z i).is_lt
          omega
        have hstep := cweight_translate n M ((z i).val + (n - M)) hM h_lo h_hi
        have hsubadd : (z i).val + (n - M) - (n - M) = (z i).val := by omega
        rw [hstep, hsubadd]
      show ∑ i, (if ((z i).val + (n - M)) ≤ n
                  then n - ((z i).val + (n - M))
                  else ((z i).val + (n - M)) - n) ≤ M
      rw [heq]; exact hzsum)
    -- (3) Left inverse: backward ∘ forward = id.
    (by
      intro y hy
      have hsum :
          ∑ i, (if (y i).val ≤ n then n - (y i).val else (y i).val - n) ≤ M := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        exact hy
      funext idx
      apply Fin.ext
      show (y idx).val - (n - M) + (n - M) = (y idx).val
      obtain ⟨h_lo, _⟩ := cweight_sum_range hM y hsum idx
      omega)
    -- (4) Right inverse: forward ∘ backward = id.
    (by
      intro z _
      funext idx
      apply Fin.ext
      show (z idx).val + (n - M) - (n - M) = (z idx).val
      omega)

-- ============================================================
-- PART VIII.b: Slicing Decomposition (S6, 2026-05-08)
-- ============================================================

/-- **Per-fiber cardinality**: for `j : Fin (2n+1)`, the fiber of `crossBall (d+1) n`
    over the last coordinate (i.e. `{y | y(last d) = j}`) has the same cardinality
    as `crossBall d M_j`, where `M_j := if j ≤ n then j else 2n - j` is the "budget"
    available to the remaining `d` coordinates.

    The bijection is `Fin.init` (drop last coord) on the forward side and
    `Fin.snoc · j` (append `j` as last coord) on the backward side.

    Key arithmetic identity: `cweight(j, n) + M_j = n`, so the constraint on the
    initial `d` coordinates is exactly "centered weight sum at center `n` ≤ M_j",
    which is the LHS filter set of `fiber_card_eq_crossBall_card`. -/
private lemma crossBall_succ_d_fiber_card (d n : ℕ) (j : Fin (2 * n + 1)) :
    ((crossBall (d + 1) n).filter (fun y => y (Fin.last d) = j)).card =
    (crossBall d (if j.val ≤ n then j.val else 2 * n - j.val)).card := by
  set Mj : ℕ := if j.val ≤ n then j.val else 2 * n - j.val with hMj_def
  -- Mj ≤ n in both branches.
  have hMj_le : Mj ≤ n := by
    by_cases h : j.val ≤ n
    · simp only [hMj_def, if_pos h]; exact h
    · push_neg at h
      have hjlt : j.val < 2 * n + 1 := j.isLt
      simp only [hMj_def, if_neg (not_le.mpr h)]
      omega
  -- Key identity: cweight(j, n) + Mj = n.
  have hcw_plus_Mj :
      (if j.val ≤ n then n - j.val else j.val - n) + Mj = n := by
    by_cases h : j.val ≤ n
    · rw [if_pos h]
      simp only [hMj_def, if_pos h]
      omega
    · push_neg at h
      rw [if_neg (not_le.mpr h)]
      simp only [hMj_def, if_neg (not_le.mpr h)]
      have hjlt : j.val < 2 * n + 1 := j.isLt
      omega
  -- Bridge to the previously-proved fiber bijection.
  rw [← fiber_card_eq_crossBall_card d n Mj hMj_le]
  -- Now: bijection between the fiber and the cweight-≤-Mj filter on Fin d → Fin (2n+1).
  -- Forward: y ↦ Fin.init y; Backward: z ↦ Fin.snoc z j.
  apply Finset.card_bij'
    (fun y _ => Fin.init y)
    (fun z _ => Fin.snoc z j)
    -- (1) Forward image lies in the cweight-≤-Mj filter.
    (by
      intro y hy
      simp only [crossBall, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      obtain ⟨hsum, hlast⟩ := hy
      -- Split Σ over Fin (d+1) into init part + last term.
      rw [Fin.sum_univ_castSucc] at hsum
      rw [hlast] at hsum
      -- hsum : Σᵢ cweight(y i.castSucc, n) + cweight(j, n) ≤ n.
      -- Goal: Σᵢ cweight((Fin.init y) i, n) ≤ Mj.
      -- (Fin.init y) i = y i.castSucc by definition (rfl).
      change ∑ i, (if (y i.castSucc).val ≤ n then n - (y i.castSucc).val
                    else (y i.castSucc).val - n) ≤ Mj
      omega)
    -- (2) Backward image lies in the original fiber.
    (by
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      simp only [crossBall, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, Fin.snoc_last⟩
      -- Σ over Fin (d+1) splits into castSucc part + last.
      rw [Fin.sum_univ_castSucc]
      -- castSucc part rewrites via Fin.snoc_castSucc.
      have hcs : ∀ i,
          (if ((Fin.snoc z j) i.castSucc : Fin (2 * n + 1)).val ≤ n
              then n - ((Fin.snoc z j) i.castSucc : Fin (2 * n + 1)).val
              else ((Fin.snoc z j) i.castSucc : Fin (2 * n + 1)).val - n)
          = (if (z i).val ≤ n then n - (z i).val else (z i).val - n) := by
        intro i; rw [Fin.snoc_castSucc]
      have hlast :
          (if ((Fin.snoc z j) (Fin.last d) : Fin (2 * n + 1)).val ≤ n
              then n - ((Fin.snoc z j) (Fin.last d) : Fin (2 * n + 1)).val
              else ((Fin.snoc z j) (Fin.last d) : Fin (2 * n + 1)).val - n)
          = (if j.val ≤ n then n - j.val else j.val - n) := by
        rw [Fin.snoc_last]
      rw [Finset.sum_congr rfl (fun i _ => hcs i), hlast]
      -- Goal: Σᵢ cweight(z i, n) + cweight(j, n) ≤ n.
      -- Have hz : Σᵢ cweight(z i, n) ≤ Mj, and cweight(j, n) + Mj = n.
      omega)
    -- (3) Left inverse: snoc (init y) j = y when y(last d) = j.
    (by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      obtain ⟨_, hlast⟩ := hy
      rw [← hlast]
      exact Fin.snoc_init_self y)
    -- (4) Right inverse: init (snoc z j) = z.
    (by
      intro z _
      exact Fin.init_snoc)

/-- **Step A — Slicing identity**: the cardinality of `crossBall (d+1) n` equals
    the sum over `j : Fin (2n+1)` of the cardinality of `crossBall d M_j`, where
    `M_j = if j ≤ n then j else 2n - j` is the budget after fixing the last coord.

    Proof: `Finset.card_eq_sum_card_fiberwise` projects on the last coordinate
    via `fun y => y (Fin.last d) : Fin (d+1) → Fin (2n+1) → Fin (2n+1)`; each
    fiber has card `(crossBall d M_j).card` by `crossBall_succ_d_fiber_card`. -/
private lemma crossBall_succ_d_slice (d n : ℕ) :
    (crossBall (d + 1) n).card =
    ∑ j : Fin (2 * n + 1),
      (crossBall d (if j.val ≤ n then j.val else 2 * n - j.val)).card := by
  -- Project on the last coordinate (lands in `Finset.univ` trivially).
  have hMapsTo :
      ((crossBall (d + 1) n : Finset _) : Set (Fin (d + 1) → Fin (2 * n + 1))).MapsTo
        (fun y => y (Fin.last d))
        ((Finset.univ : Finset (Fin (2 * n + 1))) : Set _) :=
    fun _ _ => by simp
  rw [Finset.card_eq_sum_card_fiberwise hMapsTo]
  apply Finset.sum_congr rfl
  intro j _
  exact crossBall_succ_d_fiber_card d n j

/-- **Step B — Sum reorganization**: the sum over `j : Fin (2n+1)` of
    `(crossBall d M_j).card` collapses (via the j ↔ 2n - j pairing) to
    `(crossBall d n).card + 2 * Σ m ∈ range n, (crossBall d m).card`.

    Proof: convert to `∑ k ∈ range (2n+1)`, split as
    `range (n+1) ⊔ Ico (n+1) (2n+1)`. The low half (k ≤ n) gives M_k = k;
    the high half (k > n) gives M_k = 2n - k, and reindexing m := 2n - k
    sends `Ico (n+1) (2n+1)` bijectively to `range n`. The low half splits
    further as `range n ⊔ {n}`; combining yields the stated identity. -/
private lemma sum_crossBall_pair (d n : ℕ) :
    ∑ j : Fin (2 * n + 1),
        (crossBall d (if j.val ≤ n then j.val else 2 * n - j.val)).card =
    (crossBall d n).card + 2 * ∑ m ∈ Finset.range n, (crossBall d m).card := by
  -- Step B.1: convert ∑ j : Fin (2n+1) into ∑ k ∈ range (2n+1).
  rw [show
      (∑ j : Fin (2 * n + 1),
          (crossBall d (if j.val ≤ n then j.val else 2 * n - j.val)).card)
        =
      ∑ k ∈ Finset.range (2 * n + 1),
          (crossBall d (if k ≤ n then k else 2 * n - k)).card from
    Fin.sum_univ_eq_sum_range
      (fun k => (crossBall d (if k ≤ n then k else 2 * n - k)).card) (2 * n + 1)]
  -- Step B.2: split range (2n+1) = range (n+1) ⊔ Ico (n+1) (2n+1).
  have hsplit :
      Finset.range (2 * n + 1) =
        Finset.range (n + 1) ∪ Finset.Ico (n + 1) (2 * n + 1) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have hdisj : Disjoint (Finset.range (n + 1)) (Finset.Ico (n + 1) (2 * n + 1)) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    rw [Finset.mem_range] at hk1
    rw [Finset.mem_Ico] at hk2
    omega
  rw [hsplit, Finset.sum_union hdisj]
  -- Step B.3: simplify the if on each piece.
  -- Low piece (k ∈ range (n+1)): k ≤ n so M_k = k.
  rw [show
      (∑ k ∈ Finset.range (n + 1),
          (crossBall d (if k ≤ n then k else 2 * n - k)).card)
        = ∑ k ∈ Finset.range (n + 1), (crossBall d k).card from
    Finset.sum_congr rfl (fun k hk => by
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      simp only [if_pos hkn])]
  -- High piece (k ∈ Ico (n+1) (2n+1)): k > n so M_k = 2n - k.
  rw [show
      (∑ k ∈ Finset.Ico (n + 1) (2 * n + 1),
          (crossBall d (if k ≤ n then k else 2 * n - k)).card)
        = ∑ k ∈ Finset.Ico (n + 1) (2 * n + 1), (crossBall d (2 * n - k)).card from
    Finset.sum_congr rfl (fun k hk => by
      have ⟨h1, _⟩ := Finset.mem_Ico.mp hk
      have hk_gt : ¬ k ≤ n := by omega
      simp only [if_neg hk_gt])]
  -- Step B.4: reindex high piece by m := 2n - k. Bijection Ico (n+1) (2n+1) ↔ range n.
  rw [show
      (∑ k ∈ Finset.Ico (n + 1) (2 * n + 1), (crossBall d (2 * n - k)).card)
        = ∑ m ∈ Finset.range n, (crossBall d m).card from by
    apply Finset.sum_nbij' (fun k => 2 * n - k) (fun m => 2 * n - m)
    · intro k hk
      have ⟨h1, h2⟩ := Finset.mem_Ico.mp hk
      simp only [Finset.mem_range]; omega
    · intro m hm
      have hm := Finset.mem_range.mp hm
      simp only [Finset.mem_Ico]; omega
    · intro k hk
      have ⟨h1, h2⟩ := Finset.mem_Ico.mp hk
      omega
    · intro m hm
      have hm := Finset.mem_range.mp hm
      omega
    · intro k _; rfl]
  -- Step B.5: combine. Low piece = ∑ m ∈ range n + (crossBall d n).card.
  rw [Finset.sum_range_succ]
  ring

/-- **Main geometric theorem**: the cross-polytope lattice count equals crossEhrhart d n.

    Proof (S6 closure, 2026-05-08): induction on `d` with `n` generalized.
    - Base `d = 0`: `crossBall 0 n` is a singleton (the empty function), so
      `card = 1 = crossEhrhart 0 n`.
    - Step: combine three pieces:
      * `crossBall_succ_d_slice` slices `crossBall (d+1) n` over the last coord;
      * `sum_crossBall_pair` collapses the resulting sum via the j ↔ 2n-j pairing;
      * `crossEhrhart_succ_d` closes the recursion under the IH.

    Closes the final `sorry` in this file. -/
theorem crossBall_card (d n : ℕ) : (crossBall d n).card = crossEhrhart d n := by
  induction d generalizing n with
  | zero =>
    -- crossBall 0 n = singleton {empty function}, card = 1 = crossEhrhart 0 n
    simp [crossBall, crossEhrhart]
  | succ d ih =>
    rw [crossBall_succ_d_slice, sum_crossBall_pair, ih n]
    rw [show
        (∑ m ∈ Finset.range n, (crossBall d m).card)
          = ∑ m ∈ Finset.range n, crossEhrhart d m from
      Finset.sum_congr rfl (fun m _ => ih m)]
    rw [← crossEhrhart_succ_d]

-- ============================================================
-- PART IX: Summary and Exports
-- ============================================================

/-
## Key Lemma Dependency Graph

    sum_choose_range (hockey-stick)
             |
    sum_shift_hockey (sum interchange)
             |
    crossEhrhart_expand (Pascal split: LHS = RHS + 2·shifted_sum)
             |
    crossEhrhart_succ_d (main geometric recursion)

## Comparison with Cube and Simplex

    Polytope    Formula              Lean model
    ─────────────────────────────────────────────
    Cube B_d    (n+1)^d             Fin d → Fin(n+1)
    Simplex Δ^d C(n+d,d)            Sym (Fin(d+1)) n
    Cross B_d   Σ 2^k C(d,k) C(n,k) (new — Finset slicing)

## Open Questions Generated

1. Can the crossBall_card theorem be proved without sorry,
   using Finset.card_biUnion and the slicing decomposition?

2. Does the formula Σ_k 2^k C(d,k) C(n,k) equal the central
   Delannoy number D(d,n) for all d,n? (Yes: Delannoy numbers
   count lattice paths; cross-polytope is the lattice path polytope.)

3. Can the formula be extended to half-integer dilations,
   giving a quasipolynomial for the rational cross-polytope?
-/

#check crossEhrhart_d0
#check crossEhrhart_d1
#check crossEhrhart_d2
#check sum_choose_range
#check sum_shift_hockey
#check crossEhrhart_expand
#check crossEhrhart_succ_d
#check crossEhrhart_is_poly

end EhrhartCrossPolytope
