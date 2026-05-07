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

  Main results (10 theorems, 3 sorries):
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

  Sorries (3):
  - crossEhrhart_is_poly: polynomial identification (Lean polynomial API)
  - crossBall_card base d=0: Finset card of empty-domain functions
  - crossBall_card step: Finset slicing decomposition
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

/-- Falling binomial coefficient polynomial: evaluates to C(n, k) at every n : ℕ. -/
private noncomputable def fallBinomPoly (k : ℕ) : Polynomial ℚ :=
  (1 / Nat.factorial k : ℚ) • ∏ i ∈ Finset.range k, (Polynomial.X - Polynomial.C (i : ℚ))

/-- For k ≤ n, the product ∏_{i<k} (n - i : ℚ) equals descFactorial n k. -/
private lemma prod_range_sub_eq_descFact (n : ℕ) :
    ∀ k : ℕ, k ≤ n → ∏ i ∈ Finset.range k, ((n : ℚ) - (i : ℚ)) = (n.descFactorial k : ℚ) := by
  intro k
  induction k with
  | zero => simp [Nat.descFactorial]
  | succ k ihk =>
    intro h
    have hk : k ≤ n := Nat.le_of_succ_le h
    rw [Finset.prod_range_succ, ihk hk, Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub hk]
    ring

/-- fallBinomPoly k evaluates to C(n, k) at every natural number n. -/
private lemma fallBinomPoly_eval (n k : ℕ) :
    (fallBinomPoly k).eval (n : ℚ) = (Nat.choose n k : ℚ) := by
  simp only [fallBinomPoly, Polynomial.eval_smul, Polynomial.eval_prod,
             Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, smul_eq_mul]
  rcases le_or_lt k n with hkn | hnk
  · rw [prod_range_sub_eq_descFact n k hkn, Nat.descFactorial_eq_factorial_mul_choose]
    have hfact : (Nat.factorial k : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    push_cast
    field_simp [hfact]
  · have hn_mem : n ∈ Finset.range k := Finset.mem_range.mpr hnk
    have hzero : ∏ i ∈ Finset.range k, ((n : ℚ) - (i : ℚ)) = 0 :=
      Finset.prod_eq_zero hn_mem (by ring)
    rw [hzero, mul_zero, Nat.choose_eq_zero_of_lt hnk, Nat.cast_zero]

/-- fallBinomPoly k has degree ≤ k. -/
private lemma fallBinomPoly_natDegree_le (k : ℕ) :
    (fallBinomPoly k).natDegree ≤ k := by
  unfold fallBinomPoly
  apply le_trans (Polynomial.natDegree_smul_le _ _)
  apply le_trans Polynomial.natDegree_prod_le
  apply le_trans (Finset.sum_le_sum
    (fun i _ => le_of_eq (Polynomial.natDegree_X_sub_C (i : ℚ))))
  simp [Finset.sum_const, Finset.card_range]

/-- **The formula is a polynomial of degree ≤ d in n** (over ℚ).

    Explicit polynomial: Σ_{k≤d} (2^k·C(d,k)/k!) · X·(X-1)···(X-k+1)
    Each factor C(n,k) = X·(X-1)···(X-k+1)/k! is a polynomial of degree k,
    so the sum has degree exactly d. -/
theorem crossEhrhart_is_poly (d : ℕ) :
    ∃ (P : Polynomial ℚ), P.natDegree ≤ d ∧
    ∀ n : ℕ, P.eval (n : ℚ) = (crossEhrhart d n : ℚ) := by
  use ∑ k ∈ Finset.range (d + 1),
        Polynomial.C (2 ^ k * Nat.choose d k : ℚ) * fallBinomPoly k
  refine ⟨?_, ?_⟩
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro k hk
    have hkd : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    apply le_trans Polynomial.natDegree_mul_le
    apply le_trans (Nat.add_le_add
        (le_of_eq (Polynomial.natDegree_C _)) (fallBinomPoly_natDegree_le k))
    omega
  · intro n
    simp only [crossEhrhart, Polynomial.eval_finset_sum, Polynomial.eval_mul,
              Polynomial.eval_C, fallBinomPoly_eval]
    push_cast
    apply Finset.sum_congr rfl
    intro k _; ring

-- ============================================================
-- PART VIII: Connection to Lattice Points
-- ============================================================

/-- **Lattice point model**: encode n·B_d via coordinates in {0,...,2n}
    with 0 ≡ -n, n ≡ 0, 2n ≡ n (centered at n). -/
def crossBall (d n : ℕ) : Finset (Fin d → Fin (2 * n + 1)) :=
  Finset.univ.filter fun x =>
    ∑ i, (if (x i).val ≤ n then n - (x i).val else (x i).val - n) ≤ n

-- Generalized ball with budget m in the ambient Fin (2*n+1) space.
-- crossBall d n = innerBall d n n.
private def innerBall (d n m : ℕ) : Finset (Fin d → Fin (2 * n + 1)) :=
  Finset.univ.filter fun x =>
    ∑ i, (if (x i).val ≤ n then n - (x i).val else (x i).val - n) ≤ m

private lemma crossBall_eq_innerBall (d n : ℕ) : crossBall d n = innerBall d n n := rfl

-- Individual coordinate distance bound follows from sum bound.
private lemma innerBall_coord_le {d n m : ℕ} {x : Fin d → Fin (2 * n + 1)}
    (hx : x ∈ innerBall d n m) (i : Fin d) :
    (if (x i).val ≤ n then n - (x i).val else (x i).val - n) ≤ m :=
  le_trans (Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i))
    ((Finset.mem_filter.mp hx).2)

-- Shift bijection: innerBall d n m ≃ crossBall d m when m ≤ n.
-- Map: x ↦ (fun i => x(i) - (n-m)), inverse: y ↦ (fun i => y(i) + (n-m)).
private lemma innerBall_card_eq {d n m : ℕ} (hm : m ≤ n) :
    (innerBall d n m).card = (crossBall d m).card := by
  apply Finset.card_bij
    (fun (x : Fin d → Fin (2 * n + 1)) hx i =>
      ⟨(x i).val - (n - m), by
        have hb := innerBall_coord_le hx i
        split_ifs at hb with h <;> omega⟩)
  · intro x hx
    simp only [crossBall, Finset.mem_filter, Finset.mem_univ, true_and]
    have hmem := (Finset.mem_filter.mp hx).2
    have hterm : ∀ i : Fin d,
        (if ((x i).val - (n - m)) ≤ m then m - ((x i).val - (n - m))
         else ((x i).val - (n - m)) - m) =
        (if (x i).val ≤ n then n - (x i).val else (x i).val - n) := by
      intro i; have hb := innerBall_coord_le hx i; split_ifs with h1 h2 <;> omega
    calc ∑ i, (if ((x i).val - (n - m)) ≤ m then m - ((x i).val - (n - m))
                else ((x i).val - (n - m)) - m)
        = ∑ i, (if (x i).val ≤ n then n - (x i).val else (x i).val - n) :=
          Finset.sum_congr rfl (fun i _ => hterm i)
      _ ≤ m := hmem
  · intro x₁ hx₁ x₂ hx₂ heq
    funext i; apply Fin.ext
    have heqi := congr_fun heq i
    simp only [Fin.mk.injEq] at heqi
    have hb₁ := innerBall_coord_le hx₁ i
    have hb₂ := innerBall_coord_le hx₂ i
    split_ifs at hb₁ hb₂ with h1 h2 <;> omega
  · intro y hy
    refine ⟨fun i => ⟨(y i).val + (n - m), by have := (y i).isLt; omega⟩, ?_, ?_⟩
    · simp only [innerBall, Finset.mem_filter, Finset.mem_univ, true_and]
      have hmem := (Finset.mem_filter.mp hy).2
      have hterm : ∀ i : Fin d,
          (if ((y i).val + (n - m)) ≤ n then n - ((y i).val + (n - m))
           else ((y i).val + (n - m)) - n) =
          (if (y i).val ≤ m then m - (y i).val else (y i).val - m) := by
        intro i
        have hb := le_trans (Finset.single_le_sum (fun j _ => Nat.zero_le _)
          (Finset.mem_univ i)) hmem
        split_ifs with h1 h2 <;> omega
      calc ∑ i, (if ((y i).val + (n - m)) ≤ n then n - ((y i).val + (n - m))
                  else ((y i).val + (n - m)) - n)
          = ∑ i, (if (y i).val ≤ m then m - (y i).val else (y i).val - m) :=
            Finset.sum_congr rfl (fun i _ => hterm i)
        _ ≤ m := hmem
    · funext i; apply Fin.ext; omega

-- Symmetric sum over Fin(2m+1): midpoint value plus twice range sum.
private lemma sym_fin_sum (f : ℕ → ℕ) (m : ℕ) :
    ∑ k : Fin (2 * m + 1), (if k.val ≤ m then f k.val else f (2 * m - k.val)) =
    f m + 2 * ∑ k ∈ Finset.range m, f k := by
  -- Convert Fin sum to range sum (removing the dite wrapper from sum_fin_eq_sum_range)
  have hconv : ∑ k : Fin (2 * m + 1), (if k.val ≤ m then f k.val else f (2 * m - k.val)) =
               ∑ k ∈ Finset.range (2 * m + 1), (if k ≤ m then f k else f (2 * m - k)) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    rw [dif_pos (Finset.mem_range.mp hk)]
  rw [hconv]
  have hsplit : Finset.range (2 * m + 1) =
      Finset.range m ∪ {m} ∪ Finset.Ico (m + 1) (2 * m + 1) := by
    ext k; simp [Finset.mem_range, Finset.mem_Ico]; omega
  have hdisj1 : Disjoint (Finset.range m) ({m} : Finset ℕ) := by
    simp [Finset.disjoint_left, Finset.mem_range]
  have hdisj2 : Disjoint (Finset.range m ∪ {m}) (Finset.Ico (m + 1) (2 * m + 1)) := by
    simp [Finset.disjoint_left, Finset.mem_range, Finset.mem_Ico]; omega
  rw [hsplit, Finset.sum_union hdisj2, Finset.sum_union hdisj1]
  have hleft : ∑ k ∈ Finset.range m, (if k ≤ m then f k else f (2 * m - k)) =
      ∑ k ∈ Finset.range m, f k :=
    Finset.sum_congr rfl fun k hk => by simp [Nat.le_of_lt (Finset.mem_range.mp hk)]
  have hmid : ∑ k ∈ ({m} : Finset ℕ), (if k ≤ m then f k else f (2 * m - k)) = f m := by simp
  have hright : ∑ k ∈ Finset.Ico (m + 1) (2 * m + 1), (if k ≤ m then f k else f (2 * m - k)) =
      ∑ k ∈ Finset.range m, f k := by
    have heq : ∑ k ∈ Finset.Ico (m + 1) (2 * m + 1), (if k ≤ m then f k else f (2 * m - k)) =
        ∑ k ∈ Finset.Ico (m + 1) (2 * m + 1), f (2 * m - k) :=
      Finset.sum_congr rfl fun k hk => by
        simp [show ¬k ≤ m from by simp [Finset.mem_Ico] at hk; omega]
    rw [heq]
    apply Finset.sum_nbij (fun k => 2 * m - k)
    · intro k hk; simp [Finset.mem_range, Finset.mem_Ico] at hk ⊢; omega
    · intro k₁ hk₁ k₂ hk₂ h; simp [Finset.mem_range] at hk₁ hk₂; omega
    · intro k hk
      exact ⟨2 * m - k, by simp [Finset.mem_Ico, Finset.mem_range] at hk ⊢; omega,
             by simp [Finset.mem_Ico] at hk; omega⟩
    · intro k hk; congr 1; simp [Finset.mem_range] at hk; omega
  rw [hleft, hmid, hright]; ring

/-- **Main geometric theorem**: the cross-polytope lattice count equals crossEhrhart d n.

    Proof: induction on d. The inductive step uses innerBall fiber decomposition:
    slice by last coordinate j, apply IH to each fiber (size = crossEhrhart d (n-|j-n|)),
    then sum via sym_fin_sum and crossEhrhart_succ_d. -/
theorem crossBall_card (d n : ℕ) : (crossBall d n).card = crossEhrhart d n := by
  induction d generalizing n with
  | zero =>
    simp [crossBall, crossEhrhart]
  | succ d ih =>
    rw [crossBall_eq_innerBall]
    -- Generalize to all budgets m ≤ n to enable induction on the fiber sizes.
    suffices h : ∀ m ≤ n, (innerBall (d + 1) n m).card = crossEhrhart (d + 1) m from h n le_rfl
    intro m hm
    -- Partition by last coordinate.
    have hdecomp : innerBall (d + 1) n m =
        Finset.biUnion Finset.univ
          (fun j : Fin (2 * n + 1) =>
            (innerBall (d + 1) n m).filter (fun x => x (Fin.last d) = j)) := by
      ext x; simp
    rw [hdecomp, Finset.card_biUnion (by
      intro j _ k _ hjk
      simp only [Finset.disjoint_left, Finset.mem_filter]
      intro x ⟨_, hxj⟩ ⟨_, hxk⟩; exact hjk (hxj ▸ hxk))]
    -- Compute fiber sizes: biject via Fin.init (drop last coord).
    have hfiber : ∀ j : Fin (2 * n + 1),
        ((innerBall (d + 1) n m).filter (fun x => x (Fin.last d) = j)).card =
        if (if j.val ≤ n then n - j.val else j.val - n) ≤ m
        then (innerBall d n (m - (if j.val ≤ n then n - j.val else j.val - n))).card
        else 0 := by
      intro j
      -- Use by_cases: nested if in condition would cause split_ifs to generate 4 goals.
      by_cases hdist : (if j.val ≤ n then n - j.val else j.val - n) ≤ m
      · simp only [if_pos hdist]
        apply Finset.card_bij (fun x _ => Fin.init x)
        · intro x hx
          simp only [innerBall, Finset.mem_filter, Finset.mem_univ, true_and,
                     Fin.init, Function.comp] at hx ⊢
          obtain ⟨hsum, hlast⟩ := hx
          rw [Fin.sum_univ_castSucc] at hsum
          have hdist_eq : (if (x (Fin.last d)).val ≤ n then n - (x (Fin.last d)).val
                           else (x (Fin.last d)).val - n) =
                          (if j.val ≤ n then n - j.val else j.val - n) := by rw [hlast]
          omega
        · intro x₁ hx₁ x₂ hx₂ heq
          simp only [Finset.mem_filter] at hx₁ hx₂
          funext i
          refine Fin.lastCases ?_ ?_ i
          · rw [hx₁.2, hx₂.2]
          · exact fun k => congr_fun heq k
        · intro y hy
          refine ⟨Fin.snoc y j, ?_, ?_⟩
          · simp only [Finset.mem_filter, innerBall, Finset.mem_univ, true_and]
            rw [Fin.sum_univ_castSucc]
            simp only [Fin.snoc_castSucc, Fin.snoc_last]
            have hmem := (Finset.mem_filter.mp hy).2
            -- Split on j.val ≤ n to let omega see concrete bounds from hdist.
            -- Also expose hm : m ≤ n for omega's Nat subtraction reasoning.
            have hm' := hm
            by_cases hc : j.val ≤ n
            · simp only [if_pos hc] at hdist hmem ⊢; omega
            · simp only [if_neg hc] at hdist hmem ⊢; omega
          · simp [Fin.init_snoc]
      · simp only [if_neg hdist]
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro x hx
        simp only [Finset.mem_filter, innerBall, Finset.mem_univ, true_and] at hx
        obtain ⟨hsum, hlast⟩ := hx
        rw [Fin.sum_univ_castSucc] at hsum
        have hdist_eq : (if (x (Fin.last d)).val ≤ n then n - (x (Fin.last d)).val
                         else (x (Fin.last d)).val - n) =
                        (if j.val ≤ n then n - j.val else j.val - n) := by rw [hlast]
        push_neg at hdist; omega
    -- Express fiber-card sum = crossEhrhart sym sum, then apply sym_fin_sum.
    rw [show ∑ j : Fin (2 * n + 1),
              ((innerBall (d + 1) n m).filter (fun x => x (Fin.last d) = j)).card =
            ∑ k : Fin (2 * m + 1),
              (if k.val ≤ m then crossEhrhart d k.val else crossEhrhart d (2 * m - k.val))
        from ?_]
    · rw [sym_fin_sum, ← crossEhrhart_succ_d]
    · -- Prove the sum reindexing in two steps.
      -- Step 1: convert fiber cards to crossEhrhart via hfiber + innerBall_card_eq + ih.
      have hstep1 :
          ∑ j : Fin (2 * n + 1),
            ((innerBall (d + 1) n m).filter (fun x => x (Fin.last d) = j)).card =
          ∑ j : Fin (2 * n + 1),
            (if (if j.val ≤ n then n - j.val else j.val - n) ≤ m
             then crossEhrhart d (m - (if j.val ≤ n then n - j.val else j.val - n))
             else 0) := by
        apply Finset.sum_congr rfl; intro j _
        rw [hfiber j]
        -- Use by_cases on the combined condition to avoid split_ifs generating 4 goals.
        by_cases hdist : (if j.val ≤ n then n - j.val else j.val - n) ≤ m
        · simp only [if_pos hdist]
          rw [innerBall_card_eq ((Nat.sub_le m _).trans hm)]
          exact ih _
        · simp only [if_neg hdist]
      rw [hstep1]
      -- Step 2: biject filter(2n+1) with Fin(2m+1) via sum_bij'.
      -- Use sum_bij' (dependent bijection): forward map k↦⟨k+(n-m)⟩ is total in Fin(2m+1);
      -- inverse map j↦⟨j-(n-m)⟩ uses filter membership to prove the Fin(2m+1) bound.
      rw [← Finset.sum_filter]
      -- Use sum_image: the shift map k↦⟨k+(n-m),_⟩ from Fin(2m+1) has image = filter.
      -- This avoids sum_bij type inference issues entirely.
      let shift := fun k : Fin (2 * m + 1) =>
          (⟨k.val + (n - m), by have := k.isLt; have := hm; omega⟩ : Fin (2 * n + 1))
      -- Show image of shift = filter
      have himage : (Finset.univ : Finset (Fin (2 * m + 1))).image shift =
          Finset.univ.filter (fun j : Fin (2 * n + 1) =>
            (if j.val ≤ n then n - j.val else j.val - n) ≤ m) := by
        ext j
        constructor
        · intro hj
          rw [Finset.mem_image] at hj
          obtain ⟨k, _, hk⟩ := hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          -- hk : shift k = j; extract j.val = k.val + (n-m)
          have hval : k.val + (n - m) = j.val := congrArg Fin.val hk
          have := k.isLt; have := hm; split_ifs with h <;> omega
        · intro hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          rw [Finset.mem_image]
          refine ⟨⟨j.val - (n - m), by
              have := j.isLt; have := hm
              by_cases h : j.val ≤ n
              · simp only [if_pos h] at hj; omega
              · simp only [if_neg h] at hj; omega⟩, Finset.mem_univ _, ?_⟩
          -- Prove shift ⟨j.val-(n-m),...⟩ = j
          apply Fin.ext
          simp only [shift]
          have := hm
          by_cases h : j.val ≤ n
          · simp only [if_pos h] at hj; omega
          · simp only [if_neg h] at hj; omega
      -- Apply sum_image with injectivity of shift
      rw [← himage, Finset.sum_image (by
        intro k₁ _ k₂ _ h
        apply Fin.ext; simp only [shift, Fin.mk.injEq] at h; omega)]
      -- Now: ∑ k : Fin(2m+1), cE d(m-dist(shift k)) = ∑ k : Fin(2m+1), G k
      apply Finset.sum_congr rfl
      intro k _
      have hk := k.isLt; have := hm
      simp only [shift]
      -- Show cE d(m-dist(k+(n-m))) = G k
      by_cases hkm : k.val ≤ m
      · have hdist : (if k.val + (n - m) ≤ n then n - (k.val + (n - m))
                      else k.val + (n - m) - n) = m - k.val := by split_ifs with h <;> omega
        simp only [hdist, if_pos hkm]
        -- Goal: cE d (m - (m - k.val)) = cE d k.val; need m-(m-k)=k for k≤m
        congr 1; omega
      · have hdist : (if k.val + (n - m) ≤ n then n - (k.val + (n - m))
                      else k.val + (n - m) - n) = k.val - m := by split_ifs with h <;> omega
        simp only [hdist, if_neg hkm]
        -- Goal: cE d (m - (k.val - m)) = cE d (2*m - k.val); need m-(k-m)=2m-k for k≤2m
        congr 1; omega

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
