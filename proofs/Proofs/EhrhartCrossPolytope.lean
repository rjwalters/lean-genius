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

  Main results (11 theorems, 1 sorry):
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

  Remaining sorry (1):
  - crossBall_card succ-d: Finset slicing decomposition (geometric recursion)
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

/-- **Main geometric theorem**: the cross-polytope lattice count equals crossEhrhart d n.

    Proof sketch (induction on d):
    - Base d=0: crossBall 0 n = {∅}, card = 1 = crossEhrhart 0 n. ✓
    - Step: crossBall (d+1) n decomposes by last coordinate j ∈ {0,...,2n}.
      For each j, the fiber is crossBall d (n - |j - n|).
      Summing: card = Σ_{j=0}^{2n} crossBall d (n - |j-n|).card
             = crossBall d n + 2·Σ_{m=0}^{n-1} crossBall d m   [pair j↔(2n-j)]
      By IH and crossEhrhart_succ_d: = crossEhrhart d n + 2·Σ crossEhrhart d m
             = crossEhrhart (d+1) n.
    The Finset slicing argument is standard but lengthy. -/
theorem crossBall_card (d n : ℕ) : (crossBall d n).card = crossEhrhart d n := by
  induction d with
  | zero =>
    -- crossBall 0 n = singleton {empty function}, card = 1 = crossEhrhart 0 n
    simp [crossBall, crossEhrhart]
  | succ d ih => sorry

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
