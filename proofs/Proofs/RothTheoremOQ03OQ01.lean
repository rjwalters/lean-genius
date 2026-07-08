/-
  Roth Theorem OQ-03-OQ-01: Foundational Identities for the
  Gowers Norm and the k-AP Counting Operator

  The parent entry `RothTheoremOQ03` introduces, constructively, the two
  analytic operators at the heart of the density-increment / generalized
  von Neumann approach to Szemerédi's theorem:

    * the Gowers `U^s` uniformity norm
        ‖f‖_{U^s}^{2^s} = E_{x,h} ∏_{ω ∈ {0,1}^s} C^{|ω|} f(x + ω·h),
    * the k-AP counting operator
        Λ_k(f₀,…,f_{k-1}) = E_{x,d} ∏_{i} fᵢ(x + i·d).

  but records *no* algebraic properties of either.  This child proves the
  foundational degenerate / normalization identities that every later
  argument relies on, all fully machine-checked (0 axioms, no
  `native_decide`):

    * `conjugateByWeight_zero`     — the conjugation factor fixes `0`;
    * `gowersNorm_zero`            — ‖0‖_{U^s} = 0;
    * `kAPCount_const`             — Λ_k(c,…,c) = cᵏ;
    * `kAPCount_const_one`         — Λ_k(1,…,1) = 1 (total normalized mass);
    * `kAPCount_eq_zero_of_zero`   — a single zero slot annihilates Λ_k.

  These are precisely the checks that pin the operators down as genuine
  averages `E_{x,d} ∏ᵢ fᵢ(x+i·d)` (the `(N⁻¹)²·N² = 1` normalization),
  and the constant/zero base cases of the multilinear expansion
  `1_A = δ·1 + (1_A − δ)` that opens the generalized von Neumann argument.

  Self-contained: the operators are re-declared here in their own
  namespace using the current Mathlib norm `‖·‖` (rather than the parent's
  `Complex.abs`), so the file is robust to merge order and toolchain drift.

  References:
  - Gowers, "A new proof of Szemerédi's theorem" (2001)
  - Tao, "Higher order Fourier analysis" (2012)
-/

import Mathlib

namespace RothTheoremOQ03OQ01

open Finset BigOperators

-- ============================================================
-- The operators (constructive; norm via `‖·‖`)
-- ============================================================

/-- The shift determined by a hypercube vertex `ω` and shift vectors `h`:
    `ω · h = Σᵢ (if ωᵢ then hᵢ else 0)`. -/
noncomputable def hypercubeShift {N s : ℕ} (h : Fin s → ZMod N)
    (ω : Fin s → Bool) : ZMod N :=
  ∑ i : Fin s, if ω i then h i else 0

/-- Conjugation factor: conjugate exactly when the Hamming weight of `ω`
    is odd. `C^{|ω|}(z) = z` if `|ω|` even, `conj z` if `|ω|` odd. -/
noncomputable def conjugateByWeight {s : ℕ} (ω : Fin s → Bool) (z : ℂ) : ℂ :=
  if (Finset.univ.filter (fun i => ω i = true)).card % 2 = 0
  then z else starRingEnd ℂ z

/-- The Gowers `U^s` norm of `f : ZMod N → ℂ` (raised to the power `2^s`),
    `‖f‖_{U^s}^{2^s} = |E_{x,h} ∏_{ω} C^{|ω|} f(x + ω·h)|`, written as the
    modulus of a normalized finite sum. -/
noncomputable def gowersNorm (N s : ℕ) [NeZero N] (f : ZMod N → ℂ) : ℝ :=
  ‖(((N : ℂ)⁻¹) ^ (s + 1) *
      ∑ x : ZMod N, ∑ h : Fin s → ZMod N,
        ∏ ω : Fin s → Bool,
          conjugateByWeight ω (f (x + hypercubeShift h ω)))‖

/-- The k-AP counting operator, a normalized finite average:
    `Λ_k(f₀,…,f_{k-1}) = E_{x,d ∈ ZMod N} ∏_{i} fᵢ(x + i·d)`. -/
noncomputable def kAPCount {N : ℕ} [NeZero N] (k : ℕ)
    (f : Fin k → ZMod N → ℂ) : ℂ :=
  ((N : ℂ)⁻¹) ^ 2 * ∑ x : ZMod N, ∑ d : ZMod N,
    ∏ i : Fin k, f i (x + i.val • d)

-- ============================================================
-- Foundational identities
-- ============================================================

/-- The conjugation-by-weight factor sends `0` to `0`: both branches
    (the identity and complex conjugation) fix the origin. -/
@[simp] theorem conjugateByWeight_zero {s : ℕ} (ω : Fin s → Bool) :
    conjugateByWeight ω 0 = 0 := by
  unfold conjugateByWeight
  split <;> simp

/-- The Gowers `U^s` norm of the zero function is `0`: every hypercube
    factor is `conjugateByWeight ω 0 = 0`, so each `2^s`-fold product
    vanishes, the averaging sum is `0`, and `‖0‖ = 0`. -/
theorem gowersNorm_zero (N s : ℕ) [NeZero N] :
    gowersNorm N s (0 : ZMod N → ℂ) = 0 := by
  unfold gowersNorm
  have hzero : ∀ (x : ZMod N) (h : Fin s → ZMod N),
      (∏ ω : Fin s → Bool,
        conjugateByWeight ω ((0 : ZMod N → ℂ) (x + hypercubeShift h ω))) = 0 :=
    fun x h => Finset.prod_eq_zero (Finset.mem_univ (default : Fin s → Bool))
      (by rw [Pi.zero_apply]; exact conjugateByWeight_zero _)
  rw [Finset.sum_congr rfl (fun x _ =>
        Finset.sum_congr rfl (fun h _ => hzero x h))]
  simp

/-- The k-AP counting operator on the constant tuple `(c,…,c)` equals
    `c ^ k`: the inner product is `∏_{i} c = cᵏ`, and the normalized
    double average `(N⁻¹)² · ∑_{x,d} cᵏ = cᵏ` cancels the `N²` pairs
    against the `(N⁻¹)²` prefactor. -/
theorem kAPCount_const {N : ℕ} [NeZero N] (k : ℕ) (c : ℂ) :
    kAPCount k (fun (_ : Fin k) (_ : ZMod N) => c) = c ^ k := by
  unfold kAPCount
  have hprod : ∀ (x d : ZMod N),
      (∏ i : Fin k, (fun (_ : Fin k) (_ : ZMod N) => c) i (x + i.val • d))
        = c ^ k := by
    intro x d
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Finset.sum_congr rfl (fun x _ =>
        Finset.sum_congr rfl (fun d _ => hprod x d))]
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  rw [show ((N : ℂ)⁻¹) ^ 2 * ((N : ℂ) * ((N : ℂ) * c ^ k))
        = ((N : ℂ)⁻¹ * (N : ℂ)) ^ 2 * c ^ k from by ring,
      inv_mul_cancel₀ hN, one_pow, one_mul]

/-- Normalization: the count of the all-ones tuple is `1`, i.e.
    `Λ_k(1,…,1) = 1` — the total normalized `k`-AP mass and the base
    point of the `1_A = δ·1 + (1_A − δ)` decomposition. -/
theorem kAPCount_const_one {N : ℕ} [NeZero N] (k : ℕ) :
    kAPCount k (fun (_ : Fin k) (_ : ZMod N) => (1 : ℂ)) = 1 := by
  rw [kAPCount_const]; simp

/-- A single zero argument annihilates the whole count: if `f j` is the
    zero function for some position `j`, then `Λ_k(f₀,…,f_{k-1}) = 0`,
    because the `j`-th factor of every product term vanishes. -/
theorem kAPCount_eq_zero_of_zero {N : ℕ} [NeZero N] (k : ℕ)
    (f : Fin k → ZMod N → ℂ) (j : Fin k) (hj : f j = 0) :
    kAPCount k f = 0 := by
  unfold kAPCount
  have hprod : ∀ (x d : ZMod N), (∏ i : Fin k, f i (x + i.val • d)) = 0 :=
    fun x d => Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])
  rw [Finset.sum_congr rfl (fun x _ =>
        Finset.sum_congr rfl (fun d _ => hprod x d))]
  simp

-- ============================================================
-- Multilinearity in each slot
--
-- The k-AP counting operator is *multilinear*: linear separately in
-- each of its `k` function arguments.  These are exactly the identities
-- that drive the generalized von Neumann argument, where one slot is
-- expanded as `1_A = δ·1 + (1_A − δ)` and the count is split by linearity
-- in that slot.  We record linearity in an arbitrary slot `j` via
-- `Function.update`.
-- ============================================================

/-- Factor out the `j`-th slot of the inner product: replacing `f j` by an
    arbitrary function `g` (via `Function.update`) pulls the `j`-th factor
    `g (x + j·d)` out in front of the product over the remaining slots. -/
theorem prod_update_factor {N : ℕ} [NeZero N] (k : ℕ)
    (f : Fin k → ZMod N → ℂ) (j : Fin k) (g : ZMod N → ℂ) (x d : ZMod N) :
    (∏ i : Fin k, Function.update f j g i (x + i.val • d))
      = g (x + j.val • d) *
          ∏ i ∈ Finset.univ.erase j, f i (x + i.val • d) := by
  rw [← Finset.mul_prod_erase Finset.univ
        (fun i => Function.update f j g i (x + i.val • d)) (Finset.mem_univ j)]
  congr 1
  · simp
  · apply Finset.prod_congr rfl
    intro i hi
    simp only [Finset.mem_erase] at hi
    simp [hi.1]

/-- Additivity in slot `j`: `Λ_k` is additive in each function argument.
    Splitting the `j`-th slot as a sum `g₁ + g₂` splits the whole count.
    This is the linear step that lets the generalized von Neumann argument
    decompose `1_A = δ·1 + (1_A − δ)` inside a single AP-count slot. -/
theorem kAPCount_update_add {N : ℕ} [NeZero N] (k : ℕ)
    (f : Fin k → ZMod N → ℂ) (j : Fin k) (g₁ g₂ : ZMod N → ℂ) :
    kAPCount k (Function.update f j (g₁ + g₂))
      = kAPCount k (Function.update f j g₁)
        + kAPCount k (Function.update f j g₂) := by
  unfold kAPCount
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rw [prod_update_factor, prod_update_factor, prod_update_factor, Pi.add_apply]
  ring

/-- Scalar homogeneity in slot `j`: scaling one function argument by a
    constant `c` scales the whole count by `c`.  Together with
    `kAPCount_update_add` this establishes multilinearity of `Λ_k`. -/
theorem kAPCount_update_smul {N : ℕ} [NeZero N] (k : ℕ)
    (f : Fin k → ZMod N → ℂ) (j : Fin k) (c : ℂ) (g : ZMod N → ℂ) :
    kAPCount k (Function.update f j (c • g))
      = c * kAPCount k (Function.update f j g) := by
  unfold kAPCount
  have key : (∑ x : ZMod N, ∑ d : ZMod N,
                ∏ i : Fin k, Function.update f j (c • g) i (x + i.val • d))
      = c * ∑ x : ZMod N, ∑ d : ZMod N,
                ∏ i : Fin k, Function.update f j g i (x + i.val • d) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [prod_update_factor, prod_update_factor, Pi.smul_apply, smul_eq_mul]
    ring
  rw [key]; ring

/-- A zero slot makes the whole count vanish, phrased via `Function.update`:
    overwriting slot `j` with the zero function gives `Λ_k = 0`.  The
    `Function.update`-flavoured companion of `kAPCount_eq_zero_of_zero`, and the
    additive unit for the slotwise linear structure. -/
@[simp] theorem kAPCount_update_zero {N : ℕ} [NeZero N] (k : ℕ)
    (f : Fin k → ZMod N → ℂ) (j : Fin k) :
    kAPCount k (Function.update f j 0) = 0 :=
  kAPCount_eq_zero_of_zero k _ j (Function.update_self j 0 f)

/-- Subtractivity in slot `j`: `Λ_k` is additive under subtraction in each
    function argument.  Combined with `kAPCount_update_add`/`kAPCount_update_smul`
    this is the full linear structure the generalized von Neumann argument uses to
    telescope a slot expanded as `1_A = δ·1 + (1_A − δ)`. -/
theorem kAPCount_update_sub {N : ℕ} [NeZero N] (k : ℕ)
    (f : Fin k → ZMod N → ℂ) (j : Fin k) (g₁ g₂ : ZMod N → ℂ) :
    kAPCount k (Function.update f j (g₁ - g₂))
      = kAPCount k (Function.update f j g₁)
        - kAPCount k (Function.update f j g₂) := by
  have h1 : g₁ - g₂ = g₁ + (-1 : ℂ) • g₂ := by
    rw [neg_one_smul, ← sub_eq_add_neg]
  rw [h1, kAPCount_update_add, kAPCount_update_smul, neg_one_mul, ← sub_eq_add_neg]

/-- **The generalized von Neumann slot-split.**  For any scalar `δ`, expanding
    the `j`-th slot as `g = δ·1 + (g − δ·1)` splits the count into its *major
    term* `δ · Λ_k(…,1,…)` and a *balanced remainder* whose `j`-th slot
    `g − δ·1` has mean-zero flavour.  Taking `g = 1_A` and `δ = |A|/N` (the
    density) this is exactly the first step of the density-increment / von
    Neumann decomposition: the major term is the main `k`-AP count and the
    remainder is controlled by a Gowers uniformity norm. -/
theorem kAPCount_update_split {N : ℕ} [NeZero N] (k : ℕ)
    (f : Fin k → ZMod N → ℂ) (j : Fin k) (g : ZMod N → ℂ) (δ : ℂ) :
    kAPCount k (Function.update f j g)
      = δ * kAPCount k (Function.update f j 1)
        + kAPCount k (Function.update f j (g - δ • (1 : ZMod N → ℂ))) := by
  have hadd := kAPCount_update_add k f j (δ • (1 : ZMod N → ℂ))
    (g - δ • (1 : ZMod N → ℂ))
  have hg : δ • (1 : ZMod N → ℂ) + (g - δ • (1 : ZMod N → ℂ)) = g := by
    rw [add_sub_cancel]
  rw [hg] at hadd
  rw [hadd, kAPCount_update_smul]

/-- Negation in slot `j`: `Λ_k(…, −g, …) = −Λ_k(…, g, …)`.  The additive
    inverse of the slotwise linear structure, a one-liner off homogeneity
    at `c = −1`. -/
theorem kAPCount_update_neg {N : ℕ} [NeZero N] (k : ℕ)
    (f : Fin k → ZMod N → ℂ) (j : Fin k) (g : ZMod N → ℂ) :
    kAPCount k (Function.update f j (-g))
      = - kAPCount k (Function.update f j g) := by
  have hg : (-g) = (-1 : ℂ) • g := by rw [neg_one_smul]
  rw [hg, kAPCount_update_smul, neg_one_mul]

/-- **Finite-sum additivity in slot `j`.**  `Λ_k` commutes with a finite sum
    placed in a single slot:
    `Λ_k(…, ∑_{a∈s} g a, …) = ∑_{a∈s} Λ_k(…, g a, …)`.  This is the iterated
    form of `kAPCount_update_add` (proved by induction on the index set) and
    the primitive that lets the generalized von Neumann telescoping expand an
    indicator over a finite basis one slot at a time. -/
theorem kAPCount_update_sum {N : ℕ} [NeZero N] (k : ℕ)
    (f : Fin k → ZMod N → ℂ) (j : Fin k) {ι : Type*} (s : Finset ι)
    (g : ι → ZMod N → ℂ) :
    kAPCount k (Function.update f j (∑ a ∈ s, g a))
      = ∑ a ∈ s, kAPCount k (Function.update f j (g a)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, kAPCount_update_add, ih, Finset.sum_insert ha]

/-- **`Λ_k` is a linear functional in each slot.**  Combining finite-sum
    additivity with scalar homogeneity, a linear combination `∑_{a∈s} c a • g a`
    placed in slot `j` is read off coefficient-wise:
    `Λ_k(…, ∑_{a∈s} c a • g a, …) = ∑_{a∈s} c a · Λ_k(…, g a, …)`.  Taking the
    `g a` to be a basis of functions on `ZMod N` (e.g. indicators of points, or
    the additive characters) exhibits each slot of `Λ_k` as a genuine linear
    functional — the exact structure the density-increment argument exploits
    when it expands `1_A` and separates the major term from the balanced
    remainder. -/
theorem kAPCount_update_sum_smul {N : ℕ} [NeZero N] (k : ℕ)
    (f : Fin k → ZMod N → ℂ) (j : Fin k) {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (g : ι → ZMod N → ℂ) :
    kAPCount k (Function.update f j (∑ a ∈ s, c a • g a))
      = ∑ a ∈ s, c a * kAPCount k (Function.update f j (g a)) := by
  rw [kAPCount_update_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [kAPCount_update_smul]

end RothTheoremOQ03OQ01
