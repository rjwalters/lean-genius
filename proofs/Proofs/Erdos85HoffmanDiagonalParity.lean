import Mathlib

/-
# Hoffman diagonal parity

Let `A` be a symmetric integer matrix with zero diagonal and constant EVEN
row sum `q`, and let `h ∈ ℤ[X]` satisfy the Hoffman identity
`aeval A h = c • J` (all entries equal to the integer `c`).  Then

  (i)  `c ≡ h(0) (mod 2)`                      (`hoffman_diagonal_parity`),
  (ii) if the order `n` is even, `c` is even,
       i.e. `2n ∣ h(q)`                          (`hoffman_diagonal_parity_even`).

Proof.  Reduce modulo two.  Every positive power of `A` has even diagonal:
for even exponents `(A^{2r})_{vv} = Σ_i (A^r)_{vi}² ≡ Σ_i (A^r)_{vi} = q^r ≡ 0`,
and for odd exponents `(A^{2r+1})_{vv} = xᵀ A x` with `x` the `v`-th row of
`A^r`, a quadratic form of a symmetric zero-diagonal matrix, which is even
because the off-diagonal terms pair up under the swap `(i,j) ↦ (j,i)`.
Hence `diag h(A) ≡ h(0)`, and comparing with `c • J` gives (i).  For (ii),
the all-ones vector is an eigenvector: `h(A)·1 = h(q)·1 = n c · 1`, and
`h(q) ≡ h(0)` because `q` is even, so `c ≡ n c ≡ 0`.

This is the general form of the condition used in the Erdős-85 A-REG
ledger (HOFFMAN_DIAGONAL_PARITY.md, Q16_HOFFMAN_DIAGONAL_PARITY_REJECTION.md):
no graph hypotheses enter, only symmetry, zero diagonal and even row sums.
For a `q`-regular graph on `n` vertices with simple eigenvalue `q` and `h`
annihilating the nonprincipal spectrum, `h(A) = (h(q)/n) J` is the Hoffman
identity, and (ii) says `2n ∣ h(q)`.
-/

namespace Erdos85

open Matrix Polynomial Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem zmod2_mul_self (x : ZMod 2) : x * x = x := by
  fin_cases x <;> rfl

theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> rfl

/-- The quadratic form of a symmetric zero-diagonal matrix over `ZMod 2`
vanishes identically: the diagonal terms are zero and the off-diagonal
terms cancel in pairs. -/
theorem dotProduct_mulVec_self_eq_zero (A : Matrix V V (ZMod 2))
    (hsymm : Aᵀ = A) (hdiag : ∀ v, A v v = 0) (x : V → ZMod 2) :
    x ⬝ᵥ (A *ᵥ x) = 0 := by
  have hsym : ∀ i j, A j i = A i j := fun i j => by
    calc A j i = Aᵀ i j := rfl
      _ = A i j := by rw [hsymm]
  have hexp : x ⬝ᵥ (A *ᵥ x) = ∑ p : V × V, x p.1 * (A p.1 p.2 * x p.2) := by
    simp only [dotProduct, mulVec, Finset.mul_sum, Fintype.sum_prod_type]
  rw [hexp, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p : V × V => p.1 = p.2)]
  have hdiagSum : ∑ p ∈ Finset.univ.filter (fun p : V × V => p.1 = p.2),
      x p.1 * (A p.1 p.2 * x p.2) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [hp.2, hdiag, zero_mul, mul_zero]
  have hoffSum : ∑ p ∈ Finset.univ.filter (fun p : V × V => ¬ p.1 = p.2),
      x p.1 * (A p.1 p.2 * x p.2) = 0 := by
    refine Finset.sum_involution (fun p _ => p.swap) ?_ ?_ ?_ ?_
    · intro p _
      simp only [Prod.fst_swap, Prod.snd_swap]
      have hswap : x p.2 * (A p.2 p.1 * x p.1) = x p.1 * (A p.1 p.2 * x p.2) := by
        rw [hsym p.1 p.2]; ring
      rw [hswap]
      exact zmod2_add_self _
    · intro p hp _
      rw [Finset.mem_filter] at hp
      intro hswap
      apply hp.2
      have := congrArg Prod.fst hswap
      simpa using this.symm
    · intro p hp
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨Finset.mem_univ _, fun h => hp.2 h.symm⟩
    · intro p _
      exact Prod.swap_swap p
  rw [hdiagSum, hoffSum, add_zero]

/-- Over `ZMod 2`: symmetric, zero diagonal, and `A · 1 = 0` imply that every
positive power of `A` has zero diagonal. -/
theorem diag_pow_eq_zero (A : Matrix V V (ZMod 2))
    (hsymm : Aᵀ = A) (hdiag : ∀ v, A v v = 0)
    (hone : A *ᵥ (fun _ => (1 : ZMod 2)) = 0) :
    ∀ k, 1 ≤ k → ∀ v, (A ^ k) v v = 0 := by
  have hpowT : ∀ r, (A ^ r)ᵀ = A ^ r := fun r => by rw [transpose_pow, hsymm]
  have hx : ∀ r v j, (A ^ r) j v = (A ^ r) v j := fun r v j => by
    calc (A ^ r) j v = (A ^ r)ᵀ v j := rfl
      _ = (A ^ r) v j := by rw [hpowT]
  have hpow1 : ∀ r, 1 ≤ r → A ^ r *ᵥ (fun _ => (1 : ZMod 2)) = 0 := by
    intro r hr
    induction r with
    | zero => omega
    | succ r _ =>
      rw [pow_succ, ← mulVec_mulVec, hone, mulVec_zero]
  intro k hk v
  obtain ⟨r, hr | hr⟩ := Nat.even_or_odd' k
  · -- k = 2 r with r ≥ 1
    have hr1 : 1 ≤ r := by omega
    subst hr
    rw [two_mul, pow_add, mul_apply]
    have hterm : ∀ j, (A ^ r) v j * (A ^ r) j v = (A ^ r) v j := fun j => by
      rw [hx, zmod2_mul_self]
    simp only [hterm]
    have := congrFun (hpow1 r hr1) v
    simpa [mulVec, dotProduct] using this
  · -- k = 2 r + 1
    subst hr
    have hsplit : 2 * r + 1 = r + (r + 1) := by omega
    rw [hsplit, pow_add, pow_succ', mul_apply]
    have hinner : ∀ i, (A * A ^ r) i v = ∑ j, A i j * (A ^ r) v j := fun i => by
      rw [mul_apply]
      simp only [hx]
    simp only [hinner]
    have := dotProduct_mulVec_self_eq_zero A hsymm hdiag (fun j => (A ^ r) v j)
    simpa [dotProduct, mulVec] using this

/-- If every positive power of `A` has zero diagonal, then `h(A)` has the
constant diagonal `h(0)`. -/
theorem aeval_diag_eq_coeff_zero (A : Matrix V V (ZMod 2))
    (hpow : ∀ k, 1 ≤ k → ∀ v, (A ^ k) v v = 0) (g : (ZMod 2)[X]) (v : V) :
    (aeval A g) v v = g.coeff 0 := by
  rw [aeval_eq_sum_range, Matrix.sum_apply, Finset.sum_range_succ']
  have hz : ∀ i, (g.coeff (i + 1) • A ^ (i + 1)) v v = 0 := fun i => by
    rw [Matrix.smul_apply, hpow (i + 1) (by omega) v, smul_zero]
  simp only [hz, Finset.sum_const_zero, zero_add, pow_zero, Matrix.smul_apply,
    Matrix.one_apply_eq, smul_eq_mul, mul_one]

/-- **Hoffman diagonal parity, congruence form.**  For a symmetric integer
matrix with zero diagonal and constant even row sum, `aeval A h = c • J`
forces `c ≡ h(0) (mod 2)`. -/
theorem hoffman_diagonal_parity [Nonempty V] (A : Matrix V V ℤ)
    (hsymm : Aᵀ = A) (hdiag : ∀ v, A v v = 0)
    {q : ℤ} (hq : Even q) (hrow : A *ᵥ (fun _ => (1 : ℤ)) = fun _ => q)
    (h : ℤ[X]) {c : ℤ} (hH : aeval A h = Matrix.of fun _ _ => c) :
    c ≡ h.coeff 0 [ZMOD 2] := by
  set φ : ℤ →+* ZMod 2 := Int.castRingHom (ZMod 2) with hφ
  set B : Matrix V V (ZMod 2) := A.map φ with hB
  have hBsymm : Bᵀ = B := by
    rw [hB, ← Matrix.transpose_map, hsymm]
  have hBdiag : ∀ v, B v v = 0 := fun v => by
    simp [hB, Matrix.map_apply, hdiag]
  have hqzero : φ q = 0 := by
    rw [hφ]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd q 2).2 (even_iff_two_dvd.1 hq)
  have hBone : B *ᵥ (fun _ => (1 : ZMod 2)) = 0 := by
    ext i
    have hm := RingHom.map_mulVec φ A (fun _ => (1 : ℤ)) i
    rw [hrow] at hm
    have h1 : (φ ∘ fun _ : V => (1 : ℤ)) = fun _ => (1 : ZMod 2) := by
      ext; simp
    rw [h1] at hm
    rw [Pi.zero_apply, hB, ← hm]
    exact hqzero
  have hpow := diag_pow_eq_zero B hBsymm hBdiag hBone
  obtain ⟨v⟩ := ‹Nonempty V›
  have hdiagB := aeval_diag_eq_coeff_zero B hpow (h.map φ) v
  rw [coeff_map] at hdiagB
  have hmap : (aeval A h).map φ = aeval B (h.map φ) := by
    rw [aeval_def, aeval_def, eval₂_map]
    have hhom := hom_eval₂ (p := h) (f := algebraMap ℤ (Matrix V V ℤ)) (g := φ.mapMatrix) A
    have hmm : φ.mapMatrix A = B := rfl
    rw [hmm] at hhom
    change φ.mapMatrix (eval₂ (algebraMap ℤ (Matrix V V ℤ)) A h) = _
    rw [hhom]
    congr 1
    exact RingHom.ext_int _ _
  rw [← hmap, hH] at hdiagB
  simp only [Matrix.map_apply, Matrix.of_apply, hφ, eq_intCast] at hdiagB
  exact (ZMod.intCast_eq_intCast_iff _ _ _).1 hdiagB

/-- The all-ones vector is an eigenvector of every `h(A)` with eigenvalue
`h(q)` when `A · 1 = q · 1`. -/
theorem aeval_mulVec_one (A : Matrix V V ℤ) {q : ℤ}
    (hrow : A *ᵥ (fun _ => (1 : ℤ)) = fun _ => q) (h : ℤ[X]) :
    aeval A h *ᵥ (fun _ => (1 : ℤ)) = fun _ => h.eval q := by
  have hpowvec : ∀ k, A ^ k *ᵥ (fun _ => (1 : ℤ)) = fun _ => q ^ k := by
    intro k
    induction k with
    | zero => ext i; simp [mulVec, dotProduct, Matrix.one_apply]
    | succ k ih =>
      have hq' : (fun _ : V => q) = q • fun _ : V => (1 : ℤ) := by ext; simp
      rw [pow_succ, ← mulVec_mulVec, hrow, hq', mulVec_smul, ih]
      ext i
      simp [pow_succ, mul_comm]
  rw [aeval_eq_sum_range, eval_eq_sum_range]
  ext i
  rw [Matrix.sum_mulVec, Finset.sum_apply]
  simp only [Matrix.smul_mulVec, hpowvec, Pi.smul_apply, smul_eq_mul]

/-- **Hoffman diagonal parity, divisibility form.**  If moreover the order
`n = |V|` is even, then `c` is even; since `h(q) = n c`, this is `2n ∣ h(q)`. -/
theorem hoffman_diagonal_parity_even [Nonempty V] (A : Matrix V V ℤ)
    (hsymm : Aᵀ = A) (hdiag : ∀ v, A v v = 0)
    {q : ℤ} (hq : Even q) (hrow : A *ᵥ (fun _ => (1 : ℤ)) = fun _ => q)
    (hn : Even (Fintype.card V))
    (h : ℤ[X]) {c : ℤ} (hH : aeval A h = Matrix.of fun _ _ => c) :
    Even c ∧ h.eval q = (Fintype.card V : ℤ) * c := by
  have hcong := hoffman_diagonal_parity A hsymm hdiag hq hrow h hH
  obtain ⟨v⟩ := ‹Nonempty V›
  -- h(q) = n c
  have hev : h.eval q = (Fintype.card V : ℤ) * c := by
    have h1 := congrFun (aeval_mulVec_one A hrow h) v
    rw [hH] at h1
    simp only [mulVec, dotProduct, Matrix.of_apply, mul_one, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul] at h1
    exact h1.symm
  refine ⟨?_, hev⟩
  -- reduce h(q) = n c modulo 2
  have hq2 : (q : ZMod 2) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd q 2).2 (even_iff_two_dvd.1 hq)
  have hn2 : ((Fintype.card V : ℕ) : ZMod 2) = 0 :=
    ZMod.natCast_eq_zero_iff_even.2 hn
  have hevq : ((h.eval q : ℤ) : ZMod 2) = ((h.coeff 0 : ℤ) : ZMod 2) := by
    have := (eval₂_hom (Int.castRingHom (ZMod 2)) q (p := h)).symm
    simp only [eq_intCast] at this
    rw [this, hq2, eval₂_at_zero, eq_intCast]
  have hc0 : ((h.coeff 0 : ℤ) : ZMod 2) = 0 := by
    rw [← hevq, hev]
    push_cast
    rw [hn2, zero_mul]
  have hc : ((c : ℤ) : ZMod 2) = 0 := by
    rw [(ZMod.intCast_eq_intCast_iff _ _ _).2 hcong]
    exact hc0
  exact even_iff_two_dvd.2 ((ZMod.intCast_zmod_eq_zero_iff_dvd c 2).1 hc)

end Erdos85
