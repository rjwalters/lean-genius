/-
  Hilbert 17 — the Gram core for "PSD quadratic forms are sums of squares".

  This file proves, with **zero axioms**, the matrix-level engine behind the
  axiom `quadratic_psd_is_sos_aux` in `Hilbert17SumOfSquares.lean`:

      a positive semidefinite real matrix `M` makes its quadratic form
      `x ↦ xᵀ M x` an honest **sum of squares of linear forms**.

  Concretely, with `S = √M` (the PSD square root, which is symmetric over ℝ),

      x ⬝ᵥ (M *ᵥ x) = ∑ i, ((S *ᵥ x) i)²,

  and each `(S *ᵥ x) i = ∑ j, S i j * x j` is a linear form in `x`.  This is the
  Gram / Cholesky route: `M PSD ⟺ M = Sᵀ S`, hence `xᵀ M x = ‖S x‖²`.

  What is NOT done here (the remaining multi-session "bridge"): connecting an
  arbitrary `Q : MvPolynomial (Fin n) ℝ` of `totalDegree = 2` to its symmetric
  coefficient matrix `M` and back to `IsSumOfSquaresMvPolynomial`.  That
  coefficient-extraction / homogenisation step is the genuine Mathlib gap noted
  in `research/problems/hilbert-17-oq-03/knowledge.md`; this file supplies the
  algebraic heart that any such bridge will call.
-/
import Mathlib

namespace Hilbert17

open Matrix
open scoped MatrixOrder

variable {n : ℕ}

/-- **Real PSD ⟹ symmetric Gram factorization.**

    A positive semidefinite real matrix `M` factors as `M = Sᵀ * S` where
    `S = √M` is symmetric (`Sᵀ = S`).  Over ℝ the conjugate transpose is the
    transpose, so the Hermitian square root is genuinely symmetric. -/
theorem sqrt_transpose_eq_self {M : Matrix (Fin n) (Fin n) ℝ}
    (_hM : M.PosSemidef) :
    (CFC.sqrt M)ᵀ = CFC.sqrt M := by
  have h : (CFC.sqrt M)ᴴ = CFC.sqrt M := ((CFC.sqrt_nonneg M).posSemidef).isHermitian
  rwa [conjTranspose_eq_transpose_of_trivial] at h

/-- `M = Sᵀ * S` with `S = √M`, the real Gram factorization of a PSD matrix. -/
theorem posSemidef_eq_transpose_mul_sqrt {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosSemidef) :
    (CFC.sqrt M)ᵀ * CFC.sqrt M = M := by
  rw [sqrt_transpose_eq_self hM]
  exact CFC.sqrt_mul_sqrt_self M

/-- **The Gram core: a PSD matrix's quadratic form is a sum of squares.**

    For a positive semidefinite real matrix `M`, the quadratic form
    `x ⬝ᵥ (M *ᵥ x) = xᵀ M x` equals `∑ i, ((√M *ᵥ x) i)²`, an explicit sum of
    squares of the linear forms `x ↦ (√M *ᵥ x) i = ∑ j, (√M) i j * x j`. -/
theorem posSemidef_quadratic_isSumSq {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosSemidef) (x : Fin n → ℝ) :
    x ⬝ᵥ (M *ᵥ x) = ∑ i, ((CFC.sqrt M *ᵥ x) i) ^ 2 := by
  set S := CFC.sqrt M with hSdef
  have hsymm : Sᵀ = S := sqrt_transpose_eq_self hM
  have hfac : Sᵀ * S = M := posSemidef_eq_transpose_mul_sqrt hM
  calc
    x ⬝ᵥ (M *ᵥ x)
        = x ⬝ᵥ ((Sᵀ * S) *ᵥ x) := by rw [hfac]
    _   = x ⬝ᵥ (Sᵀ *ᵥ (S *ᵥ x)) := by rw [← mulVec_mulVec]
    _   = (x ᵥ* Sᵀ) ⬝ᵥ (S *ᵥ x) := by rw [dotProduct_mulVec]
    _   = (S *ᵥ x) ⬝ᵥ (S *ᵥ x) := by rw [vecMul_transpose]
    _   = ∑ i, ((S *ᵥ x) i) ^ 2 := by rw [dotProduct]; simp [pow_two]

/-- **Packaged existence form.** Every PSD real matrix `M` admits a real matrix
    `B` (namely `B = √M`) such that the quadratic form `xᵀ M x` is the sum of
    squares of the linear forms given by the rows of `B`. -/
theorem posSemidef_exists_sumSq {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosSemidef) :
    ∃ B : Matrix (Fin n) (Fin n) ℝ,
      ∀ x : Fin n → ℝ, x ⬝ᵥ (M *ᵥ x) = ∑ i, ((B *ᵥ x) i) ^ 2 :=
  ⟨CFC.sqrt M, fun x => posSemidef_quadratic_isSumSq hM x⟩

open MvPolynomial in
/-- **Homogeneous quadratic-forms case of Hilbert's PSD = SOS, fully verified.**

    For a positive semidefinite real matrix `M`, the homogeneous degree-2
    polynomial `Q_M = ∑ i j, M i j · Xᵢ Xⱼ` is an honest polynomial sum of
    squares: `Q_M = ∑ k, (∑ j, (√M) k j · Xⱼ)²`.  The witnesses are the linear
    forms given by the rows of `√M`.

    This is exactly `IsSumOfSquaresMvPolynomial Q_M` (the existence form below),
    proved with zero axioms.  It is the homogeneous heart of
    `quadratic_psd_is_sos_aux`; the remaining gap is the reduction of an
    *arbitrary* `totalDegree = 2` polynomial to this matrix-given form. -/
theorem posSemidef_matrixQuadratic_isSumSq {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosSemidef) :
    ∃ (m : ℕ) (q : Fin m → MvPolynomial (Fin n) ℝ),
      (∑ i, ∑ j, C (M i j) * X i * X j) = ∑ k, q k ^ 2 := by
  refine ⟨n, fun k => ∑ j, C (CFC.sqrt M k j) * X j, ?_⟩
  apply MvPolynomial.funext
  intro x
  have key := posSemidef_quadratic_isSumSq hM x
  simp only [dotProduct, mulVec] at key
  simp only [map_sum, map_mul, map_pow, eval_C, eval_X]
  rw [← key]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-! ## The polynomial → matrix bridge for *homogeneous* quadratics

The lemmas above take a PSD matrix and produce an SOS polynomial.  This section
goes the other way for the genuinely interesting object: an arbitrary
**homogeneous degree-2 polynomial** `Q`.  We read off its symmetric Gram matrix
`quadMatrix Q`, prove `Q = ∑ i j, (quadMatrix Q) i j · Xᵢ Xⱼ`, show that PSD of
`Q` forces `quadMatrix Q` to be a PSD matrix, and feed that to the engine above.
The result (`homogeneous_quadratic_psd_isSumSq`) is the full
**homogeneous case** of Hilbert's "PSD = SOS for quadratics", in any number of
variables, with zero axioms.  (The remaining step for the *affine*
`totalDegree = 2` axiom `quadratic_psd_is_sos_aux` is the standard
homogenisation by one extra coordinate.) -/

open MvPolynomial

/-- A degree-2 exponent vector is either `Finsupp.single k 2` (a pure square) or
    `Finsupp.single a 1 + Finsupp.single b 1` with `a ≠ b` (a genuine cross term). -/
lemma degree_two_cases {d : Fin n →₀ ℕ} (hd : d.degree = 2) :
    (∃ k, d = Finsupp.single k 2) ∨ (∃ a b, a ≠ b ∧ d = Finsupp.single a 1 + Finsupp.single b 1) := by
  have hsum : ∑ i ∈ d.support, d i = 2 := by rw [← Finsupp.degree_apply]; exact hd
  have hpos : ∀ i ∈ d.support, 1 ≤ d i := fun i hi =>
    Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  have hcard : d.support.card ≤ 2 := by
    calc d.support.card = ∑ _i ∈ d.support, 1 := by simp
      _ ≤ ∑ i ∈ d.support, d i := Finset.sum_le_sum hpos
      _ = 2 := hsum
  have hcard0 : d.support.card ≠ 0 := by
    intro h0
    rw [Finset.card_eq_zero] at h0
    rw [h0, Finset.sum_empty] at hsum
    omega
  interval_cases hc : d.support.card
  · exact absurd rfl hcard0
  · obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hc
    left; refine ⟨k, ?_⟩
    have hdk : d k = 2 := by rw [hk, Finset.sum_singleton] at hsum; exact hsum
    ext m
    by_cases hm : m = k
    · subst hm; simp [hdk]
    · have hms : m ∉ d.support := by rw [hk]; simp [hm]
      rw [Finsupp.notMem_support_iff.mp hms]
      simp [Finsupp.single_apply, Ne.symm hm]
  · obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp hc
    right; refine ⟨a, b, hab, ?_⟩
    rw [hs, Finset.sum_pair hab] at hsum
    have hap : 1 ≤ d a := hpos a (by rw [hs]; simp)
    have hbp : 1 ≤ d b := hpos b (by rw [hs]; simp)
    have hda : d a = 1 := by omega
    have hdb : d b = 1 := by omega
    ext m
    by_cases hma : m = a
    · subst hma; simp [hda, Finsupp.add_apply, Ne.symm hab]
    by_cases hmb : m = b
    · subst hmb; simp [hdb, Finsupp.add_apply, hab]
    · have hms : m ∉ d.support := by rw [hs]; simp [hma, hmb]
      rw [Finsupp.notMem_support_iff.mp hms]
      simp [Finsupp.add_apply, Ne.symm hma, Ne.symm hmb]

/-- `Finsupp.single i 1 + Finsupp.single j 1 = Finsupp.single k 2` exactly when `i = j = k`. -/
lemma match_diag {i j k : Fin n} :
    (Finsupp.single i 1 + Finsupp.single j 1 : Fin n →₀ ℕ) = Finsupp.single k 2 ↔ i = k ∧ j = k := by
  constructor
  · intro h
    have hk := DFunLike.congr_fun h k
    simp only [Finsupp.add_apply, Finsupp.single_apply] at hk
    by_cases hik : i = k <;> by_cases hjk : j = k <;> simp_all
  · rintro ⟨rfl, rfl⟩; rw [← Finsupp.single_add]

/-- For `a ≠ b`, `Finsupp.single i 1 + Finsupp.single j 1 = Finsupp.single a 1 + Finsupp.single b 1` exactly when
    `(i,j)` is `(a,b)` or `(b,a)`. -/
lemma match_offdiag {i j a b : Fin n} (hab : a ≠ b) :
    (Finsupp.single i 1 + Finsupp.single j 1 : Fin n →₀ ℕ) = Finsupp.single a 1 + Finsupp.single b 1 ↔
      (i = a ∧ j = b) ∨ (i = b ∧ j = a) := by
  constructor
  · intro h
    have ha : (if i = a then 1 else 0) + (if j = a then (1:ℕ) else 0) = 1 := by
      have := DFunLike.congr_fun h a
      simpa [Finsupp.add_apply, Finsupp.single_apply, hab, Ne.symm hab] using this
    have hb : (if i = b then 1 else 0) + (if j = b then (1:ℕ) else 0) = 1 := by
      have := DFunLike.congr_fun h b
      simpa [Finsupp.add_apply, Finsupp.single_apply, hab, Ne.symm hab] using this
    by_cases hia : i = a
    · refine Or.inl ⟨hia, ?_⟩
      have hib : i ≠ b := by rw [hia]; exact hab
      rw [if_neg hib, zero_add] at hb
      by_contra hjb; rw [if_neg hjb] at hb; simp at hb
    · rw [if_neg hia, zero_add] at ha
      have hja : j = a := by by_contra hja; rw [if_neg hja] at ha; simp at ha
      refine Or.inr ⟨?_, hja⟩
      have hjb : j ≠ b := by rw [hja]; exact hab
      rw [if_neg hjb, add_zero] at hb
      by_contra hib; rw [if_neg hib] at hb; simp at hb
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · rw [add_comm]

/-- Collapse the diagonal coefficient double sum: only `(k,k)` survives. -/
lemma sum_ite_diag (f : Fin n → Fin n → ℝ) (k : Fin n) :
    ∑ i, ∑ j, (if (Finsupp.single i 1 + Finsupp.single j 1 : Fin n →₀ ℕ) = Finsupp.single k 2 then f i j else 0)
      = f k k := by
  rw [← Finset.sum_product', ← Finset.sum_filter]
  rw [show (Finset.univ ×ˢ Finset.univ).filter
        (fun p : Fin n × Fin n => (Finsupp.single p.1 1 + Finsupp.single p.2 1 : Fin n →₀ ℕ) = Finsupp.single k 2)
        = {(k, k)} from ?_]
  · rw [Finset.sum_singleton]
  · ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    rw [match_diag]
    constructor
    · rintro ⟨h1, h2⟩; exact Prod.ext h1 h2
    · rintro rfl; exact ⟨rfl, rfl⟩

/-- Collapse the off-diagonal coefficient double sum: `(a,b)` and `(b,a)` survive. -/
lemma sum_ite_offdiag (f : Fin n → Fin n → ℝ) {a b : Fin n} (hab : a ≠ b) :
    ∑ i, ∑ j, (if (Finsupp.single i 1 + Finsupp.single j 1 : Fin n →₀ ℕ) = Finsupp.single a 1 + Finsupp.single b 1
        then f i j else 0) = f a b + f b a := by
  rw [← Finset.sum_product', ← Finset.sum_filter]
  rw [show (Finset.univ ×ˢ Finset.univ).filter
        (fun p : Fin n × Fin n =>
          (Finsupp.single p.1 1 + Finsupp.single p.2 1 : Fin n →₀ ℕ) = Finsupp.single a 1 + Finsupp.single b 1)
        = {(a, b), (b, a)} from ?_]
  · rw [Finset.sum_pair (by simp [Prod.ext_iff, hab, Ne.symm hab])]
  · ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    rw [match_offdiag hab]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl (Prod.ext h1 h2)
      · exact Or.inr (Prod.ext h1 h2)
    · rintro (rfl | rfl)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩

/-- **The symmetric Gram matrix of a quadratic polynomial.**  Diagonal entry is
    the pure-square coefficient; off-diagonal entry is half the cross-term
    coefficient (so the pair `(i,j),(j,i)` reconstitutes the full cross term). -/
noncomputable def quadMatrix (Q : MvPolynomial (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    if i = j then Q.coeff (Finsupp.single i 2)
    else (Q.coeff (Finsupp.single i 1 + Finsupp.single j 1)) / 2

@[simp] lemma quadMatrix_apply (Q : MvPolynomial (Fin n) ℝ) (i j : Fin n) :
    quadMatrix Q i j =
      if i = j then Q.coeff (Finsupp.single i 2)
      else (Q.coeff (Finsupp.single i 1 + Finsupp.single j 1)) / 2 := rfl

/-- `quadMatrix Q` is symmetric. -/
lemma quadMatrix_transpose (Q : MvPolynomial (Fin n) ℝ) :
    (quadMatrix Q)ᵀ = quadMatrix Q := by
  ext i j
  simp only [Matrix.transpose_apply, quadMatrix_apply]
  by_cases h : i = j
  · subst h; rfl
  · rw [if_neg (Ne.symm h), if_neg h, add_comm (Finsupp.single j 1) (Finsupp.single i 1)]

/-- **Representation theorem.** A homogeneous degree-2 polynomial equals the
    quadratic form of its Gram matrix: `Q = ∑ i j, (quadMatrix Q) i j · Xᵢ Xⱼ`. -/
lemma quad_repr (Q : MvPolynomial (Fin n) ℝ) (hhom : Q.IsHomogeneous 2) :
    Q = ∑ i, ∑ j, C (quadMatrix Q i j) * X i * X j := by
  ext d
  have hR : coeff d (∑ i, ∑ j, C (quadMatrix Q i j) * X i * X j)
      = ∑ i, ∑ j, (if (Finsupp.single i 1 + Finsupp.single j 1 : Fin n →₀ ℕ) = d
          then quadMatrix Q i j else 0) := by
    rw [coeff_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [coeff_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_assoc, coeff_C_mul,
      show (X i * X j : MvPolynomial (Fin n) ℝ) = monomial (Finsupp.single i 1 + Finsupp.single j 1) 1 from by
        rw [← pow_one (X i), ← pow_one (X j), X_pow_eq_monomial, X_pow_eq_monomial,
            monomial_mul, one_mul],
      coeff_monomial]
    split_ifs <;> simp
  rw [hR]
  by_cases hdeg : d.degree = 2
  · rcases degree_two_cases hdeg with ⟨k, rfl⟩ | ⟨a, b, hab, rfl⟩
    · rw [sum_ite_diag]; simp [quadMatrix_apply]
    · rw [sum_ite_offdiag _ hab]
      simp only [quadMatrix_apply, if_neg hab, if_neg (Ne.symm hab)]
      rw [add_comm (Finsupp.single b 1) (Finsupp.single a 1)]; ring
  · rw [hhom.coeff_eq_zero hdeg]
    symm
    apply Finset.sum_eq_zero; intro i _
    apply Finset.sum_eq_zero; intro j _
    rw [if_neg]
    intro hcontra
    apply hdeg
    rw [← hcontra, map_add, Finsupp.degree_single, Finsupp.degree_single]

/-- **Homogeneous Hilbert 17 for quadratics, fully verified (0 axioms).**

    Every positive-semidefinite *homogeneous* real quadratic form in `n`
    variables is an honest polynomial sum of squares of linear forms.  The
    witnesses are the rows of `√(quadMatrix Q)`.  This is the polynomial-level
    homogeneous case of `quadratic_psd_is_sos_aux`; only the affine
    homogenisation step remains. -/
theorem homogeneous_quadratic_psd_isSumSq (Q : MvPolynomial (Fin n) ℝ)
    (hhom : Q.IsHomogeneous 2) (hpsd : ∀ x : Fin n → ℝ, 0 ≤ MvPolynomial.eval x Q) :
    ∃ (m : ℕ) (q : Fin m → MvPolynomial (Fin n) ℝ), Q = ∑ i, q i ^ 2 := by
  have hrepr := quad_repr Q hhom
  have hM : (quadMatrix Q).PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x => ?_⟩
    · show (quadMatrix Q)ᴴ = quadMatrix Q
      rw [conjTranspose_eq_transpose_of_trivial]
      exact quadMatrix_transpose Q
    · have hstar : (star x : Fin n → ℝ) = x := by ext i; simp
      have heval : x ⬝ᵥ ((quadMatrix Q) *ᵥ x) = MvPolynomial.eval x Q := by
        conv_rhs => rw [hrepr]
        simp only [map_sum, map_mul, eval_C, eval_X, dotProduct, mulVec]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      rw [hstar, heval]
      exact hpsd x
  obtain ⟨m, q, hq⟩ := posSemidef_matrixQuadratic_isSumSq hM
  exact ⟨m, q, hrepr.trans hq⟩

/-! ## Affine homogenisation — the full `totalDegree ≤ 2` case

Given an arbitrary `Q : MvPolynomial (Fin n) ℝ` with `totalDegree Q ≤ 2` that is
positive semidefinite, we homogenise by one extra coordinate `x₀ = X 0`: each
monomial `X^d` of `Q` (necessarily of degree `≤ 2`) is replaced by
`x₀^{2 - deg d} · X^d`, lifted to `Fin (n+1)` via `Finsupp.cons`.  The result
`homogenize Q` is a genuine *homogeneous* quadratic form in `n+1` variables.

* `homogenize_isHomogeneous` — it really is homogeneous of degree 2;
* `eval_cons_one_homogenize` — setting `x₀ = 1` recovers `Q` at the value level;
* `homogenize_nonneg` — PSD transfers: on `{x₀ ≠ 0}` by a homogeneity scaling
  identity, and at `x₀ = 0` by continuity (polynomial evaluation is continuous);
* `affine_quadratic_psd_isSumSq` — feed the homogeneous theorem and dehomogenise
  the resulting linear forms (`bind₁ (Fin.cons 1 X)`) back to affine forms in `n`
  variables.  This is the full affine case of `quadratic_psd_is_sos_aux`. -/

/-- Degree of a `Finsupp.cons`: the new head coordinate adds to the tail degree. -/
lemma degree_cons (y : ℕ) (s : Fin n →₀ ℕ) :
    (Finsupp.cons y s).degree = y + s.degree := by
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Fin.sum_univ_succ]
  simp [Finsupp.cons_zero, Finsupp.cons_succ]

/-- **Homogenisation by one extra coordinate.**  Each monomial `X^d` of `Q`
    becomes `X 0 ^ (2 - deg d) · X^d`, the variables shifted up by one index via
    `Finsupp.cons`.  For `totalDegree Q ≤ 2` every term lands in degree exactly 2. -/
noncomputable def homogenize (Q : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin (n + 1)) ℝ :=
  ∑ d ∈ Q.support, monomial (Finsupp.cons (2 - d.degree) d) (Q.coeff d)

/-- For `totalDegree Q ≤ 2`, the homogenisation is homogeneous of degree 2. -/
lemma homogenize_isHomogeneous (Q : MvPolynomial (Fin n) ℝ) (hQ : Q.totalDegree ≤ 2) :
    (homogenize Q).IsHomogeneous 2 := by
  apply IsHomogeneous.sum
  intro d hd
  apply isHomogeneous_monomial
  rw [degree_cons]
  have hdle : d.degree ≤ 2 := by
    calc d.degree = d.sum (fun _ e => e) := rfl
      _ ≤ Q.totalDegree := le_totalDegree hd
      _ ≤ 2 := hQ
  omega

/-- **Scaling identity for homogeneous quadratics.**  For a homogeneous degree-2
    polynomial, evaluation scales as `eval (c • x) p = c² · eval x p`. -/
lemma eval_smul_homogeneous {m : ℕ} {p : MvPolynomial (Fin m) ℝ} (hp : p.IsHomogeneous 2)
    (c : ℝ) (x : Fin m → ℝ) : eval (c • x) p = c ^ 2 * eval x p := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [eval_monomial, eval_monomial,
      Finsupp.prod_fintype _ _ (fun i => pow_zero _),
      Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  have hdeg : d.degree = 2 := by
    by_contra h; exact (mem_support_iff.mp hd) (hp.coeff_eq_zero h)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_eq_sum, hdeg]
  ring

/-- **Setting `x₀ = 1` recovers `Q`** (value level): evaluating `homogenize Q` at
    `Fin.cons 1 w` gives `eval w Q`.  The head factor `1 ^ (2 - deg d) = 1`
    disappears and the shifted variables `X (j+1)` read off `w j`. -/
lemma eval_cons_one_homogenize (Q : MvPolynomial (Fin n) ℝ) (w : Fin n → ℝ) :
    eval (Fin.cons (1 : ℝ) w) (homogenize Q) = eval w Q := by
  rw [homogenize, map_sum]
  conv_rhs => rw [Q.as_sum, map_sum]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [eval_monomial, eval_monomial,
      Finsupp.prod_fintype _ _ (fun i => pow_zero _),
      Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  congr 1
  rw [Fin.prod_univ_succ]
  simp [Finsupp.cons_zero, Finsupp.cons_succ, Fin.cons_zero, Fin.cons_succ]

/-- PSD on the dense slice `{x₀ ≠ 0}`: rescale to `x₀ = 1` and use the scaling
    identity together with `eval_cons_one_homogenize`. -/
lemma homogenize_nonneg_pos {Q : MvPolynomial (Fin n) ℝ}
    (hpsd : ∀ x : Fin n → ℝ, 0 ≤ eval x Q) (hQ : Q.totalDegree ≤ 2)
    (y : Fin (n + 1) → ℝ) (hy : y 0 ≠ 0) : 0 ≤ eval y (homogenize Q) := by
  set c := y 0 with hc
  have hc0 : c ≠ 0 := hy
  set w : Fin n → ℝ := fun j => y (Fin.succ j) * c⁻¹ with hw
  have hyeq : y = c • (Fin.cons (1 : ℝ) w : Fin (n + 1) → ℝ) := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp [Fin.cons_zero, hc]
    · intro j
      simp only [Pi.smul_apply, Fin.cons_succ, smul_eq_mul, hw]
      field_simp
  rw [hyeq, eval_smul_homogeneous (homogenize_isHomogeneous Q hQ),
      eval_cons_one_homogenize]
  exact mul_nonneg (sq_nonneg c) (hpsd w)

/-- **PSD transfers to the homogenisation.**  If `Q` is PSD then so is
    `homogenize Q` — nonnegativity holds on the dense set `x₀ ≠ 0`
    (`homogenize_nonneg_pos`) and extends to `x₀ = 0` by continuity of polynomial
    evaluation. -/
lemma homogenize_nonneg {Q : MvPolynomial (Fin n) ℝ}
    (hpsd : ∀ x : Fin n → ℝ, 0 ≤ eval x Q) (hQ : Q.totalDegree ≤ 2)
    (y : Fin (n + 1) → ℝ) : 0 ≤ eval y (homogenize Q) := by
  by_cases hy : y 0 = 0
  · have hupd : Continuous fun t : ℝ => Function.update y 0 t :=
      Continuous.update continuous_const 0 continuous_id
    have hcont : Continuous fun t : ℝ => eval (Function.update y 0 t) (homogenize Q) :=
      (MvPolynomial.continuous_eval (p := homogenize Q)).comp hupd
    have htend : Filter.Tendsto (fun t : ℝ => eval (Function.update y 0 t) (homogenize Q))
        (nhdsWithin 0 {0}ᶜ) (nhds (eval (Function.update y 0 (0 : ℝ)) (homogenize Q))) :=
      (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    have hpos : ∀ᶠ t in nhdsWithin (0 : ℝ) {0}ᶜ,
        0 ≤ eval (Function.update y 0 t) (homogenize Q) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      refine homogenize_nonneg_pos hpsd hQ _ ?_
      simpa using ht
    have h0 : 0 ≤ eval (Function.update y 0 (0 : ℝ)) (homogenize Q) := ge_of_tendsto htend hpos
    have hself : Function.update y 0 (0 : ℝ) = y := by
      rw [← hy]; exact Function.update_eq_self 0 y
    rwa [hself] at h0
  · exact homogenize_nonneg_pos hpsd hQ y hy

/-- `eval` of a `bind₁` substitution at `Fin.cons 1 X` equals evaluation at the
    augmented point `Fin.cons 1 w`. -/
lemma eval_cons_bind₁ (P : MvPolynomial (Fin (n + 1)) ℝ) (w : Fin n → ℝ) :
    eval w (bind₁ (Fin.cons (1 : MvPolynomial (Fin n) ℝ) X) P)
      = eval (Fin.cons (1 : ℝ) w) P := by
  have h := aeval_bind₁ w (Fin.cons (1 : MvPolynomial (Fin n) ℝ) X) P
  simp only [aeval_eq_eval] at h
  rw [h]
  have hfun : (fun i => eval w
        ((Fin.cons (1 : MvPolynomial (Fin n) ℝ) X : Fin (n + 1) → MvPolynomial (Fin n) ℝ) i))
      = (Fin.cons (1 : ℝ) w : Fin (n + 1) → ℝ) := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp [Fin.cons_zero]
    · intro j; simp [Fin.cons_succ]
  rw [hfun]

/-- **Affine case of Hilbert 17 for quadratics, fully verified (0 axioms).**

    Every positive-semidefinite polynomial `Q` of `totalDegree ≤ 2` in `n`
    variables is an honest polynomial sum of squares — of *affine*-linear forms.
    Homogenise to `homogenize Q` (a PSD homogeneous quadratic in `n+1`
    variables), apply `homogeneous_quadratic_psd_isSumSq`, then dehomogenise the
    linear forms by setting `X 0 = 1` (`bind₁ (Fin.cons 1 X)`). -/
theorem affine_quadratic_psd_isSumSq (Q : MvPolynomial (Fin n) ℝ)
    (hQ : Q.totalDegree ≤ 2) (hpsd : ∀ x : Fin n → ℝ, 0 ≤ eval x Q) :
    ∃ (m : ℕ) (q : Fin m → MvPolynomial (Fin n) ℝ), Q = ∑ i, q i ^ 2 := by
  obtain ⟨m, q, hq⟩ := homogeneous_quadratic_psd_isSumSq (homogenize Q)
    (homogenize_isHomogeneous Q hQ) (homogenize_nonneg hpsd hQ)
  have hdeh : bind₁ (Fin.cons (1 : MvPolynomial (Fin n) ℝ) X) (homogenize Q) = Q := by
    apply MvPolynomial.funext
    intro w
    rw [eval_cons_bind₁, eval_cons_one_homogenize]
  refine ⟨m, fun k => bind₁ (Fin.cons (1 : MvPolynomial (Fin n) ℝ) X) (q k), ?_⟩
  calc Q = bind₁ (Fin.cons (1 : MvPolynomial (Fin n) ℝ) X) (homogenize Q) := hdeh.symm
    _ = bind₁ (Fin.cons (1 : MvPolynomial (Fin n) ℝ) X) (∑ k, q k ^ 2) := by rw [hq]
    _ = ∑ k, (bind₁ (Fin.cons (1 : MvPolynomial (Fin n) ℝ) X) (q k)) ^ 2 := by
        rw [map_sum]; simp_rw [map_pow]

end Hilbert17
