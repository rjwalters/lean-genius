import Mathlib

/-
# Cauchy interlacing — the Courant–Fischer max–min keystone (bound form)

This file closes (modulo two isolated finite-cardinality facts) the single
documented Mathlib gap blocking Cauchy interlacing: the variational
characterisation of the descending k-th eigenvalue of a symmetric operator.

Prior sessions left the keystone as `theorem courant_fischer_placeholder : True`
in `CauchyInterlacing.lean`. That is a dishonest stand-in. Here we state the
real content — and prove it — in **bound form**, which sidesteps the
conditionally-complete-lattice junk-value issues of an `iSup`/`iInf`
formulation while carrying exactly the same mathematical information:

* LOWER (an optimal subspace exists): there is a `(k+1)`-dimensional subspace on
  which every nonzero Rayleigh quotient is `≥ μ k`.
* UPPER (no subspace beats it): on *every* `(k+1)`-dimensional subspace some
  nonzero vector has Rayleigh quotient `≤ μ k`.

Together these say `μ k = max_{dim S = k+1} min_{0≠x∈S} R(x)` — the
Courant–Fischer max–min identity.

## Architecture

Both halves reduce to the two leaf sublemmas already machine-checked in
`CauchyInterlacingSublemmas.lean` (#24939, 0-sorry/0-axiom), which we inline
here so the file builds as a single Lake target:

* `rayleigh_bounds_on_eigenspan` (Sublemma A): the Rayleigh quotient of a vector
  in the eigenspan over an index set `I` lies in `[inf' μ, sup' μ]`.
* `inf_ne_bot_of_finrank_add_lt` (Sublemma B): two subspaces whose dimensions
  exceed the ambient dimension meet nontrivially.

New in this file:

* `finrank_span_image_eq_card`: the eigenspan over `I` has dimension `I.card`
  (orthonormal ⇒ independent ⇒ `finrank_span_eq_card`).
* `rayleigh_ge_on_eigenspan_of_lb` / `exists_rayleigh_le_in_subspace`: the two
  *index-set-parametrised* keystone halves (the reusable content).
* `eigenvalue_maxmin_lower` / `eigenvalue_maxmin_upper`: the Fin-interval
  corollaries phrasing them for the descending k-th eigenvalue of an antitone
  enumeration `μ` — the keystone proper.

Everything is in the abstract `LinearMap.IsSymmetric` / `OrthonormalBasis`
framework (eigenvalues supplied as `μ : Fin n → ℝ` with `T (b i) = μ i • b i`),
matching the sublemmas. Bridging to `Matrix.IsHermitian.eigenvalues₀` /
`CauchyInterlacing.sortedEigs` and assembling the final interlacing inequality
remains future work.

Research file — intentionally NOT registered in `Proofs.lean`.
-/

open scoped InnerProductSpace

namespace CauchyInterlacing.Keystone

/-! ## Inlined sublemmas (verbatim from `CauchyInterlacingSublemmas.lean`, verified) -/

theorem inf_ne_bot_of_finrank_add_lt
    {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [FiniteDimensional 𝕜 E] (V W : Submodule 𝕜 E)
    (h : Module.finrank 𝕜 E < Module.finrank 𝕜 V + Module.finrank 𝕜 W) :
    ∃ x ∈ V ⊓ W, x ≠ 0 := by
  have hkey := Submodule.finrank_sup_add_finrank_inf_eq V W
  have hle : Module.finrank 𝕜 (V ⊔ W : Submodule 𝕜 E) ≤ Module.finrank 𝕜 E :=
    Submodule.finrank_le _
  have hpos : 0 < Module.finrank 𝕜 (V ⊓ W : Submodule 𝕜 E) := by omega
  have hne : (V ⊓ W : Submodule 𝕜 E) ≠ ⊥ := by
    intro hbot
    rw [hbot] at hpos
    simp at hpos
  exact (Submodule.ne_bot_iff _).1 hne

theorem weighted_mean_mem_inf_sup
    {n : ℕ} (μ : Fin n → ℝ) (I : Finset (Fin n)) (hI : I.Nonempty)
    (w : Fin n → ℝ) (hw : ∀ i ∈ I, 0 ≤ w i) (hpos : 0 < ∑ i ∈ I, w i) :
    I.inf' hI μ ≤ (∑ i ∈ I, w i * μ i) / (∑ i ∈ I, w i)
      ∧ (∑ i ∈ I, w i * μ i) / (∑ i ∈ I, w i) ≤ I.sup' hI μ := by
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hpos, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [mul_comm (I.inf' hI μ) (w i)]
    exact mul_le_mul_of_nonneg_left (Finset.inf'_le μ hi) (hw i hi)
  · rw [div_le_iff₀ hpos, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [mul_comm (I.sup' hI μ) (w i)]
    exact mul_le_mul_of_nonneg_left (Finset.le_sup' μ hi) (hw i hi)

theorem repr_eq_zero_of_not_mem
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {n : ℕ}
    (b : OrthonormalBasis (Fin n) 𝕜 E)
    (I : Finset (Fin n))
    (x : E) (hx : x ∈ Submodule.span 𝕜 ((b : Fin n → E) '' (↑I : Set (Fin n)))) :
    ∀ i, i ∉ I → b.repr x i = 0 := by
  intro i hiI
  rw [b.repr_apply_apply]
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      have hij : i ≠ j := by
        rintro rfl; exact hiI (Finset.mem_coe.mp hj)
      have h := (orthonormal_iff_ite.mp b.orthonormal) i j
      rw [if_neg hij] at h
      exact h
  | zero => simp
  | add y z _ _ hyih hzih => rw [inner_add_right, hyih, hzih, add_zero]
  | smul a y _ hyih => rw [inner_smul_right, hyih, mul_zero]

theorem norm_sq_eq_sum_repr_sq
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {n : ℕ}
    (b : OrthonormalBasis (Fin n) 𝕜 E)
    (I : Finset (Fin n))
    (x : E) (hx : x ∈ Submodule.span 𝕜 ((b : Fin n → E) '' (↑I : Set (Fin n)))) :
    ‖x‖ ^ 2 = ∑ i ∈ I, ‖b.repr x i‖ ^ 2 := by
  have hsupp := repr_eq_zero_of_not_mem b I x hx
  have h_full : ‖x‖ ^ 2 = ∑ i, ‖b.repr x i‖ ^ 2 := by
    rw [← b.repr.norm_map x, EuclideanSpace.norm_eq,
        Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  rw [h_full]
  exact (Finset.sum_subset (Finset.subset_univ I)
    (fun i _ hi => by rw [hsupp i hi]; simp)).symm

theorem repr_apply_of_diag
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {n : ℕ}
    (T : E →ₗ[𝕜] E) (b : OrthonormalBasis (Fin n) 𝕜 E) (μ : Fin n → ℝ)
    (hb : ∀ i, T (b i) = (μ i : 𝕜) • b i) (x : E) :
    ∀ i, b.repr (T x) i = b.repr x i * (μ i : 𝕜) := by
  intro i
  have hTx : T x = ∑ j, b.repr x j • ((μ j : 𝕜) • b j) := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_smul, hb j]
  rw [b.repr_apply_apply, hTx, inner_sum]
  rw [Finset.sum_eq_single i]
  · rw [inner_smul_right, inner_smul_right,
        (orthonormal_iff_ite.mp b.orthonormal) i i, if_pos rfl, mul_one]
  · intro j _ hji
    rw [inner_smul_right, inner_smul_right,
        (orthonormal_iff_ite.mp b.orthonormal) i j, if_neg (fun h => hji h.symm),
        mul_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem re_inner_apply_eq_sum_repr_mul
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {n : ℕ}
    (T : E →ₗ[𝕜] E) (b : OrthonormalBasis (Fin n) 𝕜 E) (μ : Fin n → ℝ)
    (hb : ∀ i, T (b i) = (μ i : 𝕜) • b i)
    (I : Finset (Fin n))
    (x : E) (hx : x ∈ Submodule.span 𝕜 ((b : Fin n → E) '' (↑I : Set (Fin n)))) :
    RCLike.re (@inner 𝕜 E _ (T x) x) = ∑ i ∈ I, ‖b.repr x i‖ ^ 2 * μ i := by
  have hsupp := repr_eq_zero_of_not_mem b I x hx
  have hrepr := repr_apply_of_diag T b μ hb x
  have hinner : (@inner 𝕜 E _ (T x) x)
      = ∑ i, (μ i : 𝕜) * ((‖b.repr x i‖ ^ 2 : ℝ) : 𝕜) := by
    rw [← b.repr.inner_map_map (T x) x, PiLp.inner_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [RCLike.inner_apply, hrepr i, map_mul, RCLike.conj_ofReal, ← mul_assoc,
        RCLike.mul_conj]
    push_cast
    ring
  rw [hinner, map_sum]
  rw [← Finset.sum_subset (Finset.subset_univ I)
        (fun i _ hi => by rw [hsupp i hi]; simp)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [RCLike.re_ofReal_mul]
  simp [mul_comm]

theorem rayleigh_bounds_on_eigenspan
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {n : ℕ}
    (T : E →ₗ[𝕜] E) (b : OrthonormalBasis (Fin n) 𝕜 E) (μ : Fin n → ℝ)
    (hb : ∀ i, T (b i) = (μ i : 𝕜) • b i)
    (I : Finset (Fin n)) (hI : I.Nonempty)
    (x : E) (hx : x ∈ Submodule.span 𝕜 ((b : Fin n → E) '' (↑I : Set (Fin n))))
    (hx0 : x ≠ 0) :
    I.inf' hI μ ≤ RCLike.re (@inner 𝕜 E _ (T x) x) / ‖x‖ ^ 2
      ∧ RCLike.re (@inner 𝕜 E _ (T x) x) / ‖x‖ ^ 2 ≤ I.sup' hI μ := by
  have hwnonneg : ∀ i ∈ I, 0 ≤ ‖b.repr x i‖ ^ 2 := fun i _ => sq_nonneg _
  have h1 : ‖x‖ ^ 2 = ∑ i ∈ I, ‖b.repr x i‖ ^ 2 := norm_sq_eq_sum_repr_sq b I x hx
  have h2 : RCLike.re (@inner 𝕜 E _ (T x) x) = ∑ i ∈ I, ‖b.repr x i‖ ^ 2 * μ i :=
    re_inner_apply_eq_sum_repr_mul T b μ hb I x hx
  have h3 : 0 < ∑ i ∈ I, ‖b.repr x i‖ ^ 2 := by
    rw [← h1]
    exact pow_pos (norm_pos_iff.mpr hx0) 2
  rw [h1, h2]
  exact weighted_mean_mem_inf_sup μ I hI (fun i => ‖b.repr x i‖ ^ 2) hwnonneg h3

/-! ## New: dimension of an eigenspan -/

/-- The span of an orthonormal subfamily indexed by a finite set `I` has
dimension `I.card`. Orthonormality gives linear independence of the whole basis,
which restricts to the subfamily, and `finrank_span_eq_card` converts the span's
dimension to the cardinality of its (injective) index set. -/
theorem finrank_span_image_eq_card
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {n : ℕ}
    (b : OrthonormalBasis (Fin n) 𝕜 E) (I : Finset (Fin n)) :
    Module.finrank 𝕜 (Submodule.span 𝕜 ((b : Fin n → E) '' (↑I : Set (Fin n))))
      = I.card := by
  have hli : LinearIndependent 𝕜
      ((b : Fin n → E) ∘ (Subtype.val : (↑I : Set (Fin n)) → Fin n)) :=
    (b.orthonormal.linearIndependent).comp _ Subtype.val_injective
  have hrange : Set.range ((b : Fin n → E) ∘ (Subtype.val : (↑I : Set (Fin n)) → Fin n))
      = (b : Fin n → E) '' (↑I : Set (Fin n)) := by
    rw [Set.range_comp, Subtype.range_coe]
  rw [← hrange, finrank_span_eq_card hli]
  simp

/-! ## New: the two keystone halves (index-set parametrised) -/

/-- **Keystone, lower half (index-set form).** If every index `i ∈ I` has
`c ≤ μ i`, then every nonzero vector in the eigenspan over `I` has Rayleigh
quotient `≥ c`. Specialised to `I = {0,…,k}` and `c = μ k` (antitone `μ`) this is
the "an optimal `(k+1)`-dimensional subspace exists" half of Courant–Fischer. -/
theorem rayleigh_ge_on_eigenspan_of_lb
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {n : ℕ}
    (T : E →ₗ[𝕜] E) (b : OrthonormalBasis (Fin n) 𝕜 E) (μ : Fin n → ℝ)
    (hb : ∀ i, T (b i) = (μ i : 𝕜) • b i)
    (I : Finset (Fin n)) (hI : I.Nonempty) (c : ℝ) (hc : ∀ i ∈ I, c ≤ μ i)
    (x : E) (hx : x ∈ Submodule.span 𝕜 ((b : Fin n → E) '' (↑I : Set (Fin n))))
    (hx0 : x ≠ 0) :
    c ≤ RCLike.re (@inner 𝕜 E _ (T x) x) / ‖x‖ ^ 2 := by
  have hbd := (rayleigh_bounds_on_eigenspan T b μ hb I hI x hx hx0).1
  exact le_trans (Finset.le_inf' hI μ hc) hbd

/-- **Keystone, upper half (index-set form).** Let `J` be an index set every
member of which has `μ i ≤ c`, and let `S` be a subspace large enough that
`finrank E < finrank S + J.card`. Then `S` contains a nonzero vector whose
Rayleigh quotient is `≤ c`. Specialised to `J = {k,…,n-1}`, `c = μ k`,
`finrank S = k+1` this is the "no `(k+1)`-dimensional subspace beats `μ k`" half:
`(k+1) + (n-k) = n+1 > n`. -/
theorem exists_rayleigh_le_in_subspace
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {n : ℕ}
    (T : E →ₗ[𝕜] E) (b : OrthonormalBasis (Fin n) 𝕜 E) (μ : Fin n → ℝ)
    (hb : ∀ i, T (b i) = (μ i : 𝕜) • b i)
    (J : Finset (Fin n)) (c : ℝ) (hc : ∀ i ∈ J, μ i ≤ c)
    (S : Submodule 𝕜 E)
    (hdim : Module.finrank 𝕜 E < Module.finrank 𝕜 S + J.card) :
    ∃ x ∈ S, x ≠ 0 ∧ RCLike.re (@inner 𝕜 E _ (T x) x) / ‖x‖ ^ 2 ≤ c := by
  set W : Submodule 𝕜 E := Submodule.span 𝕜 ((b : Fin n → E) '' (↑J : Set (Fin n)))
    with hW
  have hWdim : Module.finrank 𝕜 W = J.card := finrank_span_image_eq_card b J
  -- `J` is nonempty: otherwise `J.card = 0` and `finrank E < finrank S ≤ finrank E`.
  have hJne : J.Nonempty := by
    rcases J.eq_empty_or_nonempty with hempty | hne
    · exfalso
      have hSle : Module.finrank 𝕜 S ≤ Module.finrank 𝕜 E := Submodule.finrank_le _
      rw [hempty] at hdim
      simp at hdim
      omega
    · exact hne
  have hdim' : Module.finrank 𝕜 E < Module.finrank 𝕜 S + Module.finrank 𝕜 W := by
    rw [hWdim]; exact hdim
  obtain ⟨x, hxSW, hx0⟩ := inf_ne_bot_of_finrank_add_lt S W hdim'
  rw [Submodule.mem_inf] at hxSW
  obtain ⟨hxS, hxW⟩ := hxSW
  refine ⟨x, hxS, hx0, ?_⟩
  have hbd := (rayleigh_bounds_on_eigenspan T b μ hb J hJne x hxW hx0).2
  exact le_trans hbd (Finset.sup'_le hJne μ hc)

/-! ## New: the Fin-interval keystone corollaries (descending convention)

With `μ : Fin n → ℝ` antitone (the descending eigenvalue enumeration), the two
halves above instantiate at `I = Finset.Iic k` (lower) and `J = Finset.Ici k`
(upper) with `c = μ k`. The only extra ingredients are the order facts
`μ k ≤ μ i` for `i ≤ k` and `μ i ≤ μ k` for `k ≤ i` (both from `Antitone μ`) and
the interval cardinalities `#(Iic k) = k+1`, `#(Ici k) = n-k`. -/

/-- **Courant–Fischer, lower half.** For antitone `μ`, the `(k+1)`-dimensional
eigenspan `span {b 0,…,b k}` has every nonzero Rayleigh quotient `≥ μ k`; i.e. an
optimal subspace witnessing `max_{dim=k+1} min R ≥ μ k` exists. -/
theorem eigenvalue_maxmin_lower
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {n : ℕ}
    (T : E →ₗ[𝕜] E) (b : OrthonormalBasis (Fin n) 𝕜 E) (μ : Fin n → ℝ)
    (hb : ∀ i, T (b i) = (μ i : 𝕜) • b i) (hμ : Antitone μ) (k : Fin n) :
    ∃ S : Submodule 𝕜 E, Module.finrank 𝕜 S = (k : ℕ) + 1 ∧
      ∀ x ∈ S, x ≠ 0 → μ k ≤ RCLike.re (@inner 𝕜 E _ (T x) x) / ‖x‖ ^ 2 := by
  refine ⟨Submodule.span 𝕜 ((b : Fin n → E) '' (↑(Finset.Iic k) : Set (Fin n))), ?_, ?_⟩
  · rw [finrank_span_image_eq_card b (Finset.Iic k)]
    simp [Fin.card_Iic]
  · intro x hx hx0
    have hI : (Finset.Iic k).Nonempty := ⟨k, Finset.mem_Iic.2 le_rfl⟩
    refine rayleigh_ge_on_eigenspan_of_lb T b μ hb (Finset.Iic k) hI (μ k) ?_ x hx hx0
    intro i hi
    exact hμ (Finset.mem_Iic.1 hi)

/-- **Courant–Fischer, upper half.** For antitone `μ`, *every*
`(k+1)`-dimensional subspace `S` contains a nonzero vector with Rayleigh quotient
`≤ μ k`; i.e. no subspace beats `μ k`, so `max_{dim=k+1} min R ≤ μ k`. The
witness lives in `S ∩ span {b k,…,b (n-1)}`, nonempty by the dimension count
`(k+1) + (n-k) = n+1 > n`. -/
theorem eigenvalue_maxmin_upper
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {n : ℕ}
    (T : E →ₗ[𝕜] E) (b : OrthonormalBasis (Fin n) 𝕜 E) (μ : Fin n → ℝ)
    (hb : ∀ i, T (b i) = (μ i : 𝕜) • b i) (hμ : Antitone μ) (k : Fin n)
    (S : Submodule 𝕜 E) (hS : Module.finrank 𝕜 S = (k : ℕ) + 1) :
    ∃ x ∈ S, x ≠ 0 ∧ RCLike.re (@inner 𝕜 E _ (T x) x) / ‖x‖ ^ 2 ≤ μ k := by
  have hEdim : Module.finrank 𝕜 E = n := by
    rw [Module.finrank_eq_card_basis b.toBasis, Fintype.card_fin]
  have hcard : (Finset.Ici k).card = n - (k : ℕ) := by simp [Fin.card_Ici]
  have hk : (k : ℕ) < n := k.isLt
  have hdim : Module.finrank 𝕜 E < Module.finrank 𝕜 S + (Finset.Ici k).card := by
    rw [hEdim, hS, hcard]; omega
  refine exists_rayleigh_le_in_subspace T b μ hb (Finset.Ici k) (μ k) ?_ S hdim
  intro i hi
  exact hμ (Finset.mem_Ici.1 hi)

end CauchyInterlacing.Keystone
