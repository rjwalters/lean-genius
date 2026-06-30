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

end RothTheoremOQ03OQ01
