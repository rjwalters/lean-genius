/-
  The Companion Matrix is Nonderogatory: μ_C = χ_C = p
  (cayley-hamilton-minpoly-oq-03-oq-03-oq-01)

  Context: The parent entry `cayley-hamilton-minpoly-oq-03-oq-03`
  (`CayleyHamiltonMinpolyOQ03OQ03.lean`) proves that a nonderogatory matrix `M`
  with a cyclic vector is *similar* to the companion matrix of its minimal
  polynomial: `P⁻¹ · M · P = C(μ_M)`, the rational canonical form as a single
  companion block.  That statement takes for granted that `C(μ_M)` is the right
  target — i.e. that the companion matrix of a monic polynomial `p` really does
  have `p` as *both* its minimal and characteristic polynomial.  This grandchild
  supplies exactly that missing converse, self-containedly.

  Answer (formalized here): For a monic polynomial `p` of degree `n ≥ 1` over a
  field `K`, we build the explicit **companion matrix** `C = companion p`, a
  concrete `n × n` matrix, and prove:

  1. **Krylov sequence = standard basis** (`companion_pow_mulVec_e0`):
     the standard vector `e₀` is a *cyclic vector* for `C`, and its Krylov
     sequence `{e₀, C·e₀, …, C^{n-1}·e₀}` is exactly the standard basis
     `{e₀, e₁, …, e_{n-1}}`.  Thus `C` is already in the coordinates given by the
     Krylov sequence — this is the sense in which "the Krylov sequence with a
     cyclic vector produces the companion matrix."

  2. **Krylov recurrence / annihilation** (`companion_aeval_eq_zero`):
     `p(C) = 0`.  The top Krylov vector closes the ladder:
     `C^n·e₀ = -∑_{i<n} p.coeff i • eᵢ`, which is precisely the last column of
     the companion matrix.

  3. **Minimal polynomial** (`companion_minpoly`): `μ_C = minpoly K C = p`.
     Because `e₀` is cyclic, no polynomial of degree `< n` annihilates `C`, so
     `p` is *the* minimal polynomial (not merely an annihilator).

  4. **Characteristic polynomial** (`companion_charpoly`): `χ_C = p`.
     Combining `μ_C = p` (degree `n`) with Cayley–Hamilton (`p ∣ χ_C`) and the
     fact that `χ_C` is monic of degree `n` forces `χ_C = p`.

  In particular `μ_C = χ_C = p`: the companion matrix is **nonderogatory**.  This
  is the fact that makes `companion p` the canonical representative of the
  rational canonical form — the target block that the parent entry's similarity
  `P⁻¹ · M · P = C(μ_M)` conjugates into.

  The determinant-free proof of `χ_C = p` is the point of interest: rather than
  the usual cofactor expansion of `det(X·I − C)`, we obtain `χ_C = p` from the
  cyclic-vector structure via the minimal polynomial and Mathlib's
  Cayley–Hamilton theorem `Matrix.aeval_self_charpoly`.

  This file is self-contained (imports only Mathlib): it re-derives the small
  Krylov expansion lemma it needs rather than importing the parent chain, so it
  stands alone.  Mathlib itself has no companion-matrix construction.

  References:
  - Horn & Johnson, "Matrix Analysis" §3.3 (companion matrices, RCF)
  - Dummit & Foote, "Abstract Algebra" §12.2 (rational canonical form)
  - Mathlib: LinearAlgebra.Matrix.Charpoly.Minpoly

  Companion to (does not import):
  - CayleyHamiltonMinpolyOQ03OQ03.lean   (parent: Krylov RCF similarity P⁻¹MP = C(μ_M))
  - CayleyHamiltonMinpolyOQ03OQ01.lean   (Krylov expansion `aeval_mulVec_eq_krylov_sum`)
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace MinpolyComplexity.RCF

open Matrix Polynomial Finset

variable {K : Type*} [Field K]

/-! ## Krylov infrastructure (self-contained; mirrors OQ-03/OQ-03-OQ-01) -/

/-- The `k`-th Krylov vector of `M` starting from `v`: `M^k · v`. -/
def krylovVec {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) (k : ℕ) : Fin n → K :=
  (M ^ k).mulVec v

/-- `mulVec` distributes over finite sums of matrices. -/
private theorem sum_mulVec {n : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    (∑ i ∈ s, f i).mulVec v = ∑ i ∈ s, (f i).mulVec v := by
  induction s using Finset.induction_on with
  | empty => simp [Matrix.zero_mulVec]
  | @insert a s' has ih =>
    rw [Finset.sum_insert has, Matrix.add_mulVec, ih, Finset.sum_insert has]

/-- **Krylov expansion**: evaluating `p` at `M` and applying to `v` gives the
    linear combination of Krylov vectors with the polynomial's coefficients. -/
theorem aeval_mulVec_eq_krylov_sum {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (v : Fin n → K) (p : K[X]) :
    (aeval M p).mulVec v =
      ∑ i ∈ range (p.natDegree + 1), p.coeff i • krylovVec M v i := by
  have haeval_expand : aeval M p =
      ∑ i ∈ range (p.natDegree + 1), p.coeff i • M ^ i := by
    simp only [aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    have hsub : p.support ⊆ range (p.natDegree + 1) := by
      intro i hi
      exact Finset.mem_range.mpr
        (Nat.lt_succ_of_le (Polynomial.le_natDegree_of_mem_supp _ hi))
    rw [Finset.sum_subset hsub]
    · congr 1; ext i
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    · intro i _ hi
      rw [Polynomial.notMem_support_iff.mp hi, map_zero, zero_mul]
  rw [haeval_expand, sum_mulVec]
  simp only [Matrix.smul_mulVec, krylovVec]

/-! ## The companion matrix -/

/-- The **companion matrix** of a polynomial `p` (dimension `p.natDegree`).
    Column `j` (for `j < n-1`) is `e_{j+1}` (the sub-diagonal `1`s), and the
    last column `j = n-1` holds the negated coefficients `-p.coeff i`.  Thus
    `C · e_j = e_{j+1}` for `j < n-1` and `C · e_{n-1} = -∑_i p.coeff i • e_i`. -/
def companion (p : K[X]) : Matrix (Fin p.natDegree) (Fin p.natDegree) K :=
  fun i j =>
    if (j : ℕ) = p.natDegree - 1 then - p.coeff (i : ℕ)
    else if (i : ℕ) = (j : ℕ) + 1 then 1 else 0

section Companion

variable {p : K[X]}

/-- The standard cyclic vector `e₀`. -/
private def e0 (hn : 0 < p.natDegree) : Fin p.natDegree → K := Pi.single ⟨0, hn⟩ 1

/-- Applying a matrix to a standard basis vector reads off a column. -/
private theorem mulVec_single_entry
    (M : Matrix (Fin p.natDegree) (Fin p.natDegree) K) (j i : Fin p.natDegree) :
    (M *ᵥ Pi.single j 1) i = M i j := by
  show ∑ x, M i x * (Pi.single j 1 : Fin p.natDegree → K) x = M i j
  rw [Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_apply, hb])
    (fun h => absurd (Finset.mem_univ j) h)]
  simp

/-- **Krylov sequence is the standard basis.** For `k < n`, `C^k · e₀ = e_k`. -/
theorem companion_pow_mulVec_e0 (hn : 0 < p.natDegree) :
    ∀ k : ℕ, (hk : k < p.natDegree) →
      (companion p ^ k) *ᵥ e0 hn = Pi.single (⟨k, hk⟩ : Fin p.natDegree) 1 := by
  intro k
  induction k with
  | zero =>
    intro hk
    rw [pow_zero, Matrix.one_mulVec]
    rfl
  | succ m ih =>
    intro hk
    have hm : m < p.natDegree := Nat.lt_of_succ_lt hk
    have hmlt : m < p.natDegree - 1 := by omega
    have hstep : companion p ^ (m + 1) = companion p * companion p ^ m := pow_succ' _ _
    rw [hstep, ← Matrix.mulVec_mulVec, ih hm]
    funext i
    rw [mulVec_single_entry (companion p) ⟨m, hm⟩ i]
    simp only [companion, Fin.val_mk, Pi.single_apply, Fin.ext_iff]
    rw [if_neg (show ¬ (m = p.natDegree - 1) by omega)]

/-- The **top Krylov vector** closes the ladder: `C^n · e₀ = -∑_i p.coeff i • e_i`
    (the last column of the companion matrix). -/
theorem companion_pow_natDegree_mulVec_e0 (hn : 0 < p.natDegree) :
    (companion p ^ p.natDegree) *ᵥ e0 hn = fun (i : Fin p.natDegree) => - p.coeff (i : ℕ) := by
  have hstep : companion p ^ p.natDegree
      = companion p * companion p ^ (p.natDegree - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hstep, ← Matrix.mulVec_mulVec, companion_pow_mulVec_e0 hn (p.natDegree - 1) (by omega)]
  funext i
  rw [mulVec_single_entry (companion p) ⟨p.natDegree - 1, by omega⟩ i]
  simp [companion]

/-- Coordinate form of the Krylov sequence: `(C^i · e₀) k = [k = i]` for `i < n`. -/
private theorem krylov_coord (hn : 0 < p.natDegree) (i : ℕ) (hi : i < p.natDegree)
    (k : Fin p.natDegree) :
    krylovVec (companion p) (e0 hn) i k = if (k : ℕ) = i then 1 else 0 := by
  show ((companion p ^ i) *ᵥ e0 hn) k = _
  rw [companion_pow_mulVec_e0 hn i hi, Pi.single_apply]
  simp [Fin.ext_iff]

/-- `p(C) · e₀ = 0`: the defining Krylov recurrence of the companion matrix. -/
private theorem companion_aeval_mulVec_e0 (hn : 0 < p.natDegree) (hp : p.Monic) :
    (aeval (companion p) p) *ᵥ e0 hn = 0 := by
  rw [aeval_mulVec_eq_krylov_sum]
  funext k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  rw [Finset.sum_range_succ]
  -- top term: p.coeff n • (C^n e₀) k = 1 • (-p.coeff k)
  have htop : krylovVec (companion p) (e0 hn) p.natDegree k = - p.coeff (k : ℕ) :=
    congrFun (companion_pow_natDegree_mulVec_e0 hn) k
  rw [htop, hp.coeff_natDegree]
  -- lower sum: ∑_{i<n} p.coeff i * [k = i] = p.coeff k
  have hlow : (∑ i ∈ Finset.range p.natDegree,
      p.coeff i * krylovVec (companion p) (e0 hn) i k) = p.coeff (k : ℕ) := by
    rw [Finset.sum_congr rfl
      (fun i hi => by rw [krylov_coord hn i (Finset.mem_range.mp hi) k])]
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq (Finset.range p.natDegree) (k : ℕ) (fun i => p.coeff i)]
    rw [if_pos (Finset.mem_range.mpr k.isLt)]
  rw [hlow]
  ring

/-- A matrix that annihilates every standard basis vector is zero. -/
private theorem matrix_eq_zero_of_mulVec_basis
    (M : Matrix (Fin p.natDegree) (Fin p.natDegree) K)
    (h : ∀ j, M *ᵥ Pi.single j 1 = 0) : M = 0 := by
  ext i j
  have := congrFun (h j) i
  rw [mulVec_single_entry M j i] at this
  simpa using this

/-- **Krylov annihilation**: `p(C) = 0`. -/
theorem companion_aeval_eq_zero (hn : 0 < p.natDegree) (hp : p.Monic) :
    aeval (companion p) p = 0 := by
  apply matrix_eq_zero_of_mulVec_basis
  intro j
  -- e_j = C^{j} · e₀ (Krylov sequence), and p(C) commutes with C^{j}
  have hj : Pi.single j 1 = (companion p ^ (j : ℕ)) *ᵥ e0 hn := by
    rw [companion_pow_mulVec_e0 hn (j : ℕ) j.isLt, Fin.eta]
  have hcomm : Commute (aeval (companion p) p) (companion p) := by
    have h := (Commute.all p X).map (aeval (companion p))
    rwa [aeval_X] at h
  rw [hj, Matrix.mulVec_mulVec, (hcomm.pow_right (j : ℕ)).eq,
      ← Matrix.mulVec_mulVec, companion_aeval_mulVec_e0 hn hp, Matrix.mulVec_zero]

/-! ## Minimal and characteristic polynomials -/

/-- `C` is integral over `K` (finite-dimensional matrix algebra). -/
private theorem companion_isIntegral : IsIntegral K (companion p) :=
  Algebra.IsIntegral.isIntegral _

/-- **Cyclic-vector degree bound**: any annihilating polynomial of `C` of degree
    `< n` is zero (because `e₀` is a cyclic vector). -/
private theorem companion_no_low_annihilator (hn : 0 < p.natDegree) (q : K[X])
    (hq0 : aeval (companion p) q = 0) (hdeg : q.natDegree < p.natDegree) : q = 0 := by
  -- q(C) · e₀ = ∑_{i ≤ deg q} q.coeff i • e_i, whose k-th coordinate is q.coeff k
  have hvec : (aeval (companion p) q) *ᵥ e0 hn = fun (k : Fin p.natDegree) => q.coeff (k : ℕ) := by
    rw [aeval_mulVec_eq_krylov_sum]
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_congr rfl
      (fun i hi => by
        rw [krylov_coord hn i (lt_of_le_of_lt
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hdeg) k])]
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq (Finset.range (q.natDegree + 1)) (k : ℕ) (fun i => q.coeff i)]
    by_cases hk : (k : ℕ) < q.natDegree + 1
    · rw [if_pos (Finset.mem_range.mpr hk)]
    · rw [if_neg (fun h => hk (Finset.mem_range.mp h))]
      exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm
  rw [hq0] at hvec
  -- every coefficient of q vanishes
  ext i
  by_cases hi : i < p.natDegree
  · have := congrFun hvec.symm ⟨i, hi⟩
    simpa using this
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

/-- **Minimal polynomial of the companion matrix**: `μ_C = p`. -/
theorem companion_minpoly (hn : 0 < p.natDegree) (hp : p.Monic) :
    minpoly K (companion p) = p := by
  have hInt : IsIntegral K (companion p) := companion_isIntegral
  have hdvd : minpoly K (companion p) ∣ p :=
    minpoly.dvd K _ (companion_aeval_eq_zero hn hp)
  -- degree ≥ n: minpoly is a nonzero annihilator, so has degree ≥ n
  have hge : p.natDegree ≤ (minpoly K (companion p)).natDegree := by
    by_contra hlt
    push_neg at hlt
    have := companion_no_low_annihilator hn (minpoly K (companion p))
      (minpoly.aeval K _) hlt
    exact minpoly.ne_zero hInt this
  -- degree ≤ n from the divisibility
  have hle : (minpoly K (companion p)).natDegree ≤ p.natDegree :=
    Polynomial.natDegree_le_of_dvd hdvd hp.ne_zero
  have hdeg : p.natDegree = (minpoly K (companion p)).natDegree := le_antisymm hge hle
  -- equal monic polynomials of equal degree that divide each other
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hInt) hp hdvd
    (by omega)).symm

/-- **Characteristic polynomial of the companion matrix**: `χ_C = p`.
    Determinant-free: via `μ_C = p` and Cayley–Hamilton. -/
theorem companion_charpoly (hn : 0 < p.natDegree) (hp : p.Monic) :
    (companion p).charpoly = p := by
  -- p = μ_C divides χ_C
  have hdvd : p ∣ (companion p).charpoly := by
    have hmc := minpoly_dvd_charpoly (companion p)
    rwa [companion_minpoly hn hp] at hmc
  -- χ_C is monic of degree n
  have hmonic : (companion p).charpoly.Monic := Matrix.charpoly_monic _
  have hdim : (companion p).charpoly.natDegree = p.natDegree := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le hp hmonic hdvd (by omega)

/-- **Nonderogatory**: `μ_C = χ_C`, both equal to `p`. -/
theorem companion_minpoly_eq_charpoly (hn : 0 < p.natDegree) (hp : p.Monic) :
    minpoly K (companion p) = (companion p).charpoly := by
  rw [companion_minpoly hn hp, companion_charpoly hn hp]

end Companion

end MinpolyComplexity.RCF
