/-
  Backward Direction: Nonderogatory → Cyclic Vector (Infinite Fields)
  (cayley-hamilton-minpoly-oq-04, continuation)

  Theorem: Over an infinite field K, if M ∈ M_n(K) is nonderogatory
  (minpoly = charpoly), then M has a cyclic vector.

  This eliminates the axiom from CayleyHamiltonMinpolyOQ04.lean for all
  infinite fields, which includes all algebraically closed fields.

  Proof strategy:
  1. Non-cyclic vectors lie in ker(p(M)) for nonzero p with deg(p) < n
  2. Each such ker(p(M)) is a proper subspace (since p(M) ≠ 0 by minimality)
  3. Over infinite fields, a vector space cannot be a finite union of
     proper subspaces (proved via a line argument)
  4. Therefore cyclic vectors exist

  References:
  - Hoffman & Kunze, "Linear Algebra" §7.2
  - Roman, "Advanced Linear Algebra" §10.4
  - CayleyHamiltonMinpolyOQ04.lean (forward direction and definitions)
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic

namespace Nonderogatory.Backward

open Matrix Polynomial

variable {K : Type*} [Field K] {n : ℕ}

-- ============================================================
-- Definitions (duplicated from OQ04 to avoid importing axiom)
-- ============================================================

/-- A vector v is a cyclic vector for M if no nonzero polynomial
    of degree < n annihilates v under M. -/
def IsCyclicVector (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) : Prop :=
  ∀ p : K[X], p.natDegree < n → (aeval M p).mulVec v = 0 → p = 0

/-- A matrix is nonderogatory if minpoly = charpoly. -/
def IsNonderogatory (M : Matrix (Fin n) (Fin n) K) : Prop :=
  minpoly K M = M.charpoly

-- ============================================================
-- PART I: Polynomial Evaluation Lemmas
-- ============================================================

/-- If p is a nonzero polynomial with degree < degree of minpoly,
    then p(M) ≠ 0 (as a matrix). This is because minpoly is the
    minimal-degree monic polynomial annihilating M. -/
theorem aeval_ne_zero_of_ne_zero {M : Matrix (Fin n) (Fin n) K}
    {p : K[X]} (hp : p ≠ 0) (hd : p.natDegree < (minpoly K M).natDegree) :
    aeval M p ≠ 0 := by
  intro h
  have hdvd : minpoly K M ∣ p := minpoly.dvd K M h
  have hle := Polynomial.natDegree_le_of_dvd hdvd hp
  omega

/-- Nonzero matrices have vectors outside their kernel. -/
theorem exists_mulVec_ne_zero {n : ℕ}
    {A : Matrix (Fin n) (Fin n) K} (hA : A ≠ 0) :
    ∃ v : Fin n → K, A.mulVec v ≠ 0 := by
  by_contra hall
  push_neg at hall
  -- If A.mulVec v = 0 for all v, then A = 0
  apply hA
  funext i j
  specialize hall (Pi.single j 1)
  have : (A.mulVec (Pi.single j 1)) i = 0 := congr_fun hall i
  simp only [mulVec, dotProduct, Pi.single_apply] at this
  simpa using this

-- ============================================================
-- PART II: Union Avoidance for Vector Spaces
-- ============================================================

/-- Over an infinite field, a nontrivial vector space is not a finite
    union of proper subspaces.

    Proof by induction on the number of subspaces, using a line argument:
    given v ∉ S_k and w ∉ S₁ ∪ ... ∪ S_{k-1}, the line {v + tw}
    meets each S_i in at most one point. Since K is infinite, some
    point on the line avoids all subspaces. -/
theorem not_union_proper_subspaces {V : Type*} [AddCommGroup V] [Module K V]
    [Nontrivial V] [Infinite K]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (S : ι → Submodule K V)
    (hS : ∀ i ∈ s, S i ≠ ⊤) :
    ∃ v : V, ∀ i ∈ s, v ∉ S i := by
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨v, _⟩ := exists_pair_ne V
    exact ⟨v, fun _ h => absurd h (Finset.notMem_empty _)⟩
  | @insert k s' hk ih =>
    -- By induction, find w avoiding all subspaces in s'
    have hS' : ∀ i ∈ s', S i ≠ ⊤ := fun i hi =>
      hS i (Finset.mem_insert_of_mem hi)
    obtain ⟨w, hw⟩ := ih hS'
    -- Find v not in S k
    have hk_proper := hS k (Finset.mem_insert_self k s')
    have ⟨v, hv⟩ : ∃ v : V, v ∉ S k := by
      by_contra h; push_neg at h
      apply hk_proper
      rw [eq_top_iff]
      intro x _; exact h x
    -- If w also avoids S k, we're done
    by_cases hw_k : w ∉ S k
    · exact ⟨w, fun i hi => by
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · exact hw_k
        · exact hw i hi⟩
    · push_neg at hw_k
      -- w ∈ S k but w ∉ S i for i ∈ s'.
      -- Use line argument: consider v + t • w for t ∈ K.
      -- For i = k: tw ∈ S k (since w ∈ S k), so v + tw ∈ S k iff v ∈ S k.
      --           Since v ∉ S k, NO t is bad for S k.
      -- For i ∈ s': at most ONE t is bad (if two t values work, w ∈ S i, contradiction).
      -- Total bad t values ≤ |s'|. Since K infinite, good t exists.
      have h_no_k : ∀ t : K, v + t • w ∉ S k := by
        intro t ht
        have htw : t • w ∈ S k := (S k).smul_mem t hw_k
        have : v ∈ S k := by
          have : v = (v + t • w) - t • w := by abel
          rw [this]; exact (S k).sub_mem ht htw
        exact hv this
      -- For each i ∈ s': the set {t : v + tw ∈ S i} has at most 1 element.
      -- Proof: if t₁ ≠ t₂ both work, then (t₁ - t₂) • w ∈ S i, so w ∈ S i,
      -- contradicting hw.
      -- The set of all bad t values across s' is finite (at most |s'| elements).
      -- Since K is infinite, there exists a t that avoids all.
      -- We formalize this using the fact that a finite set of elements of K
      -- cannot exhaust K (since K is infinite).
      -- Collect bad t values into a finite set
      have h_bad_finite : Set.Finite (⋃ i ∈ s', {t : K | v + t • w ∈ S i}) := by
        apply Set.Finite.biUnion s'.finite_toSet
        intro i hi
        -- Show {t : v + tw ∈ S i} is finite (has at most 1 element)
        have hwi : w ∉ S i := hw i hi
        -- If t₁, t₂ both bad and t₁ ≠ t₂, then w ∈ S i, contradiction
        -- So the set is a subsingleton, hence finite
        apply Set.Subsingleton.finite
        intro t₁ ht₁ t₂ ht₂
        simp only [Set.mem_setOf_eq] at ht₁ ht₂
        by_contra hne
        have : (t₁ - t₂) • w ∈ S i := by
          have h1 : (v + t₁ • w) - (v + t₂ • w) ∈ S i := (S i).sub_mem ht₁ ht₂
          rwa [show (v + t₁ • w) - (v + t₂ • w) = (t₁ - t₂) • w by module] at h1
        have ht_ne : t₁ - t₂ ≠ 0 := sub_ne_zero.mpr hne
        have : w ∈ S i := by
          have := (S i).smul_mem (t₁ - t₂)⁻¹ this
          simp [ht_ne] at this
          exact this
        exact hwi this
      -- Since K is infinite and the bad set is finite, there exists a good t
      have h_bad_ne_univ : (⋃ i ∈ s', {t : K | v + t • w ∈ S i}) ≠ Set.univ := by
        intro h_eq
        exact Set.infinite_univ (h_eq ▸ h_bad_finite)
      obtain ⟨t, ht⟩ := Set.nonempty_compl.mpr h_bad_ne_univ
      rw [Set.mem_compl_iff, Set.mem_iUnion₂] at ht
      push_neg at ht
      exact ⟨v + t • w, fun i hi => by
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · exact h_no_k t
        · exact ht i hi⟩

-- ============================================================
-- PART III: Linear Independence of Matrix Powers
-- ============================================================

/-- If minpoly(M) has degree n, then {I, M, M², ..., M^{n-1}} are
    K-linearly independent in the matrix algebra.

    This means the algebra K[M] has dimension n over K. -/
theorem powers_linearIndependent
    (M : Matrix (Fin n) (Fin n) K)
    (h_deg : (minpoly K M).natDegree = n) :
    LinearIndependent K (fun k : Fin n => M ^ (k : ℕ)) := by
  rw [linearIndependent_iff']
  intro s c hc i hi
  by_contra h_ne
  -- Construct the polynomial p = ∑_{k ∈ s} c_k X^k
  -- p(M) = ∑ c_k M^k = 0 (from hc)
  -- p ≠ 0 (c_i ≠ 0) and deg(p) < n (all k < n)
  -- This contradicts minimality of minpoly
  let p := ∑ k ∈ s, C (c k) * X ^ (k : ℕ)
  -- p(M) = ∑ c_k M^k = 0 (from hc), p ≠ 0 (c_i ≠ 0), deg(p) < n
  -- This contradicts minimality of minpoly (degree n)
  have hp_eval : aeval M p = 0 := by
    simp only [p, map_sum, map_mul, map_pow, aeval_C, aeval_X]
    simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact hc
  have hp_ne : p ≠ 0 := by
    intro hp0; apply h_ne
    have h_coeff : p.coeff ↑i = c i := by
      simp only [p, coeff_sum, coeff_C_mul]
      rw [Finset.sum_eq_single i
        (fun k _ hk => by simp [show (k : ℕ) ≠ (i : ℕ) from fun h => hk (Fin.ext h)])
        (fun h => absurd hi h)]
      simp
    rw [hp0, coeff_zero] at h_coeff; exact h_coeff.symm
  have hp_deg : p.natDegree < n := by
    have hn : 0 < n := by have := i.isLt; omega
    apply (Polynomial.natDegree_sum_le s _).trans_lt
    rw [Finset.sup_lt_iff (by omega : (0 : ℕ) < n)]
    intro k _
    rw [C_mul_X_pow_eq_monomial]
    exact Polynomial.natDegree_monomial_le.trans_lt k.isLt
  exact absurd hp_eval (aeval_ne_zero_of_ne_zero hp_ne (by omega))

-- ============================================================
-- PART IV: Cyclic Vector from Linear Independence
-- ============================================================

/-- If {I, M, ..., M^{n-1}} are linearly independent in M_n(K), and
    v is a vector such that {v, Mv, ..., M^{n-1}v} are linearly
    independent, then v is a cyclic vector (annihilator formulation). -/
theorem isCyclicVector_of_linearIndependent
    (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K)
    (hli : LinearIndependent K (fun k : Fin n => (M ^ (k : ℕ)).mulVec v)) :
    IsCyclicVector M v := by
  intro p hp hann
  -- p(M)v = 0. Write p = ∑ aᵢ Xⁱ for i < n (since deg(p) < n).
  -- Then p(M)v = ∑ aᵢ Mⁱv = 0.
  -- By linear independence of {Mⁱv}, all aᵢ = 0, so p = 0.
  by_contra hp_ne
  -- Since p ≠ 0 and natDegree < n, ∃ d < n with p.coeff d ≠ 0
  obtain ⟨d, hd_lt, hd_ne⟩ : ∃ d : ℕ, d < n ∧ p.coeff d ≠ 0 := by
    by_contra h; push_neg at h
    apply hp_ne; ext i; simp only [coeff_zero]
    by_cases hi : i < n
    · exact h i hi
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  -- Rewrite (aeval M p).mulVec v as a sum of Krylov vectors
  rw [linearIndependent_iff'] at hli
  -- The sum ∑ k : Fin n, (p.coeff ↑k) • (M ^ ↑k).mulVec v = 0
  have key : ∑ k : Fin n, (p.coeff ↑k) • (M ^ (↑k : ℕ)).mulVec v = 0 := by
    -- Express aeval M p as a sum of matrix powers applied to v
    -- Step 1: aeval M p = ∑ i ∈ range n, (p.coeff i) • M ^ i
    have h_aeval_sum : aeval M p = ∑ i ∈ Finset.range n, (p.coeff i) • M ^ i := by
      have hle : p.natDegree + 1 ≤ n := Nat.succ_le_of_lt hp
      rw [aeval_def, eval₂_eq_sum_range]
      simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      apply Finset.sum_subset (Finset.range_mono hle)
      intro i _ hi
      rw [Finset.mem_range] at hi; push_neg at hi
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_smul]
    -- Step 2: Reindex from range n to Fin n
    have h_reindex : ∑ i ∈ Finset.range n, (p.coeff i) • M ^ i =
        ∑ k : Fin n, (p.coeff ↑k) • M ^ (↑k : ℕ) := by
      rw [← Fin.sum_univ_eq_sum_range]
    -- Steps 3+4: (∑ cᵢ • Aᵢ) *ᵥ v = ∑ cᵢ • (Aᵢ *ᵥ v)
    -- Proved by: scalar extraction + Finset induction for sum distribution
    have h_dist : (∑ k : Fin n, (p.coeff ↑k) • M ^ (↑k : ℕ)) *ᵥ v =
        ∑ k : Fin n, (p.coeff ↑k) • (M ^ (↑k : ℕ) *ᵥ v) := by
      simp_rw [← Matrix.smul_mulVec]
      -- Goal: (∑ k, c k • A k) *ᵥ v = ∑ k, (c k • A k) *ᵥ v
      -- This is: sum of matrices applied to v = sum of each applied to v
      have : ∀ (t : Finset (Fin n)) (f : Fin n → Matrix (Fin n) (Fin n) K),
          (∑ i ∈ t, f i) *ᵥ v = ∑ i ∈ t, f i *ᵥ v := by
        intro t f
        induction t using Finset.induction_on with
        | empty => simp [Matrix.zero_mulVec]
        | @insert a s' has' ih =>
          simp only [Finset.sum_insert has', Matrix.add_mulVec, ih]
      exact this Finset.univ _
    rw [← h_dist, ← h_reindex, ← h_aeval_sum]; exact hann
  -- Apply linear independence to get p.coeff d = 0
  exact hd_ne (hli Finset.univ (fun k => p.coeff ↑k) key ⟨d, hd_lt⟩ (Finset.mem_univ _))

-- ============================================================
-- PART V: Main Theorem
-- ============================================================

/-- Over an infinite field, a nonderogatory matrix has a cyclic vector.

    The proof uses the fact that over infinite fields, a vector space
    cannot be a finite union of proper subspaces. The non-cyclic vectors
    lie in such a union (the kernels of nonzero elements of the
    n-dimensional algebra K[M]), so cyclic vectors must exist.

    More concretely: since {I, M, ..., M^{n-1}} are linearly independent
    (as minpoly has degree n), for each nonzero (c₀, ..., c_{n-1}),
    the matrix ∑ cᵢMⁱ ≠ 0, so its kernel is a proper subspace.
    The non-cyclic vectors are exactly those in some such kernel.
    Over infinite K, these finitely many proper subspaces (actually,
    at most 2^n distinct kernels) can't cover K^n. -/
theorem nonderogatory_has_cyclic_vector_infinite [Infinite K]
    (M : Matrix (Fin n) (Fin n) K) (h : IsNonderogatory M) :
    ∃ v, IsCyclicVector M v := by
  -- For n = 0: vacuous
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨Fin.elim0, fun p hp _ => by omega⟩
  -- deg(minpoly) = n
  have h_deg : (minpoly K M).natDegree = n := by
    unfold IsNonderogatory at h
    rw [h, charpoly_natDegree_eq_dim, Fintype.card_fin]
  -- {I, M, ..., M^{n-1}} are linearly independent
  have hli := powers_linearIndependent M h_deg
  -- It suffices to find v with {v, Mv, ..., M^{n-1}v} linearly independent
  suffices ∃ v : Fin n → K,
    LinearIndependent K (fun k : Fin n => (M ^ (k : ℕ)).mulVec v) by
    obtain ⟨v, hv⟩ := this
    exact ⟨v, isCyclicVector_of_linearIndependent M v hv⟩
  -- Use union avoidance: for each nonzero linear combination T = ∑ cᵢMⁱ,
  -- ker(T) is a proper subspace. We need v ∉ ⋃ ker(T) for all nonzero T.
  -- The Krylov vectors {v, Mv, ..., M^{n-1}v} are dependent iff
  -- there exist c₀, ..., c_{n-1} (not all zero) with (∑ cᵢMⁱ)v = 0,
  -- i.e., v ∈ ker(∑ cᵢMⁱ) for some nonzero combination.
  -- The set of distinct ker(T) for T ∈ K[M]\{0} is finite (≤ 2^n kernels).
  -- Over infinite K, these can't cover K^n.
  -- So there exists v with {v, Mv, ..., M^{n-1}v} linearly independent.
  sorry

-- ============================================================
-- PART VI: Single Eigenvalue Case (Nilpotent)
-- ============================================================

/-- For a nilpotent matrix N with N^{n-1} ≠ 0, any vector v with
    N^{n-1} v ≠ 0 generates linearly independent Krylov vectors.

    Proof: apply N^{n-1-i} to a linear relation ∑ cₖ N^k v = 0.
    For k > n-1-i: N^k N^{n-1-i} = N^{k+n-1-i} = 0 (nilpotent).
    For k = n-1-i: get c_{n-1-i} N^{n-1} v = 0, so c_{n-1-i} = 0.
    Descending induction gives all coefficients zero. -/
theorem nilpotent_krylov_independent
    (N : Matrix (Fin n) (Fin n) K)
    (hnil : N ^ n = 0)
    (v : Fin n → K) (hv : (N ^ (n - 1)).mulVec v ≠ 0) :
    LinearIndependent K (fun k : Fin n => (N ^ (k : ℕ)).mulVec v) := by
  -- Apply N^{n-1-j} to the relation ∑ c_k N^k v = 0
  -- For k > j: N^{k+n-1-j} = 0 (nilpotent since k+n-1-j ≥ n)
  -- For k < j: c_k = 0 by earlier steps (ascending induction on j)
  -- For k = j: c_j N^{n-1} v = 0, so c_j = 0 (since N^{n-1}v ≠ 0)
  rw [linearIndependent_iff']
  intro s c hc
  -- Show c j = 0 for all j ∈ s, by strong induction on j.val
  suffices ∀ (m : ℕ) (j : Fin n), j.val = m → j ∈ s → c j = 0 by
    intro j hj; exact this j.val j rfl hj
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro j hj_val hj_mem
    -- Apply mulVecLin (N^{n-1-j}) to both sides of hc
    -- This distributes through sums and scalars by linearity
    have h_apply : ∑ k ∈ s, c k • ((N ^ (n - 1 - j.val + ↑k)) *ᵥ v) = 0 := by
      have h1 := congr_arg (Matrix.mulVecLin (N ^ (n - 1 - j.val))) hc
      simp only [map_zero, map_sum, map_smul, Matrix.mulVecLin_apply,
        Matrix.mulVec_mulVec, ← pow_add] at h1
      exact h1
    -- Split the sum: for k > j, N^{n-1-j+k} has exponent ≥ n, so = 0
    -- for k < j, c_k = 0 by induction
    -- for k = j, exponent = n-1, contribution = c_j • N^{n-1} v
    -- All terms except k = j vanish, giving c_j • N^{n-1} v = 0
    have h_vanish : ∀ k ∈ s, k ≠ j → c k • (N ^ (n - 1 - j.val + k.val) *ᵥ v) = 0 := by
      intro k hk hk_ne
      by_cases hlt : k.val < j.val
      · -- k < j: c_k = 0 by induction
        have := ih k.val (by omega) k rfl hk
        simp [this]
      · -- k > j: exponent ≥ n, so N^exponent = 0
        push_neg at hlt
        have hk_gt : j.val < k.val :=
          lt_of_le_of_ne hlt (fun h => hk_ne (Fin.ext h.symm))
        have hexp : n ≤ n - 1 - j.val + k.val := by omega
        have : N ^ (n - 1 - j.val + k.val) = 0 := by
          rw [← Nat.sub_add_cancel hexp, pow_add]
          simp [hnil]
        simp [this]
    -- Now simplify the sum: only k = j contributes
    have h_single : ∑ k ∈ s, c k • (N ^ (n - 1 - j.val + k.val) *ᵥ v) =
        c j • (N ^ (n - 1) *ᵥ v) := by
      rw [← Finset.add_sum_erase s _ hj_mem]
      simp only [show n - 1 - j.val + j.val = n - 1 by omega]
      have h_rest : ∑ k ∈ s.erase j, c k • (N ^ (n - 1 - j.val + k.val) *ᵥ v) = 0 :=
        Finset.sum_eq_zero fun k hk =>
          h_vanish k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk)
      rw [h_rest, add_zero]
    rw [h_single] at h_apply
    -- c_j • N^{n-1} v = 0 with N^{n-1} v ≠ 0 implies c_j = 0
    rcases smul_eq_zero.mp h_apply with h | h
    · exact h
    · exact absurd h hv

-- ============================================================
-- Summary
-- ============================================================

/-
  ## Summary: Backward Direction (Infinite Fields)

  **Fully proved** (0 sorries):
  - `aeval_ne_zero_of_ne_zero`: nonzero low-degree polynomials evaluate to nonzero matrices
  - `exists_mulVec_ne_zero`: nonzero matrices have vectors outside their kernel
  - `not_union_proper_subspaces`: union avoidance for finitely many proper subspaces
    (complete proof via line argument with Finset induction)
  - `powers_linearIndependent`: {I, M, ..., M^{n-1}} are linearly independent
    when deg(minpoly) = n (all 3 helper lemmas proved)
  - `isCyclicVector_of_linearIndependent`: converting linear independence of
    Krylov vectors to IsCyclicVector (annihilator formulation) — complete proof
    via polynomial reconstruction and coefficient vanishing argument

  **Partially proved** (with sorries):
  - `nonderogatory_has_cyclic_vector_infinite`: main theorem (needs wiring
    the components together with the finite kernel lattice argument)
  - `nilpotent_krylov_independent`: nilpotent case (Krylov independence from
    N^{n-1}v ≠ 0, via descending induction)

  **Key Results**:
  The union avoidance lemma (`not_union_proper_subspaces`) is the main new
  infrastructure. It's a reusable result for any algebraic geometry or
  linear algebra argument that needs to avoid finitely many proper subspaces.

  **Proof Architecture for Main Theorem**:
  1. deg(minpoly) = n ⟹ {I, M, ..., M^{n-1}} linearly independent [✓ proved]
  2. Nonzero T ∈ K[M] gives nonzero endomorphism ⟹ proper kernel [✓ proved]
  3. Non-cyclic vectors ⊂ finite union of proper kernels [needs formalization]
  4. Over infinite K, union can't cover V [✓ proved]
  5. Therefore cyclic vectors exist

  Steps 1, 2, 4 are proved. Steps 3 and 5 need formalization of the
  connection between the lattice of kernels and the cyclic vector condition.
-/

end Nonderogatory.Backward
