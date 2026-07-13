/-
# Rational Canonical Form — Existence (strong / invariant-factor form)

`rational_canonical_form_exists`: every square matrix `M` over a field admits an
invariant-factor chain — monic polynomials of positive degree forming a
divisibility chain `p₁ ∣ p₂ ∣ ⋯ ∣ pₖ` — whose product equals `M.charpoly` and
whose last factor equals `minpoly F M`.

This is the structural content behind the lone bridge `sorry` of
`minpoly-charpoly-oq-03-oq-01` (`xModule_has_invariantFactorChain`) and of the
parent OQ-03's main RCF existence statement. It is *not* available off-the-shelf
in Mathlib: the development builds the required theory from scratch —

* `RCF.mulX` and `charpoly_mulX_aeval'`/`_congr`/`_quotient`: the `F[X]`-module
  structure on `Fⁿ` with `X` acting via `M`, and that the charpoly of
  "multiplication by `X`" recovers `M.charpoly`, is invariant under `F[X]`-linear
  equivalences, and equals `g` on the cyclic module `F[X]/(g)` for monic `g`;
* `det_blockDiagonal'`/`charpoly_blockDiagonal'` and the internal/external direct
  sum lemmas: multiplicativity of the charpoly over finite direct sums;
* `decomp_charpoly_minpoly`/`exists_elementary_divisors`: primary decomposition
  via Mathlib's structure theorem for f.g. torsion modules over a PID — charpoly
  is the product of the monic associates of the elementary divisors (prime
  powers), minpoly is governed by their lcm;
* `exists_chain_aux`/`exists_chain_of_prime_powers`: a purely combinatorial
  regrouping of prime powers into an invariant-factor (divisibility) chain by
  strong induction, peeling off the lcm at each step.

The final theorem is fully proved with **no `sorry` and no added axioms** (it
type-checks depending only on the standard `propext` / `Classical.choice` /
`Quot.sound`).

Provenance: the proof body was synthesized by the Aristotle proof-search system
(project `d2395b8d`, task `5bec9f0a`) against a self-contained Mathlib-only
statement, then integrated here verbatim (wrapped in a namespace). The local
`InvariantFactorChain` structure is field-identical to the parent's
`MinpolyCharpolyOQ03.InvariantFactorChain`; the bridge in
`MinpolyCharpolyOQ03OQ01.lean` converts between them via a one-line field copy.
-/
import Mathlib

namespace RationalCanonicalFormExists

open Matrix Polynomial

variable {F : Type*} [Field F]

/-- An invariant-factor chain: monic polynomials of positive degree forming a
divisibility chain `p₁ ∣ p₂ ∣ ⋯ ∣ pₖ`. -/
structure InvariantFactorChain (F : Type*) [Field F] where
  factors : List F[X]
  monic : ∀ p ∈ factors, p.Monic
  posDegree : ∀ p ∈ factors, 0 < p.natDegree
  chain : ∀ i j : Fin factors.length, i.val ≤ j.val → factors[i] ∣ factors[j]

noncomputable def InvariantFactorChain.prodFactors (c : InvariantFactorChain F) : F[X] :=
  c.factors.prod

noncomputable def InvariantFactorChain.lastFactor (c : InvariantFactorChain F) : F[X] :=
  c.factors.getLast?.getD 1

namespace RCF

/-- The `F`-linear endomorphism "multiplication by `X`" on an `F[X]`-module `W`. -/
noncomputable def mulX (F : Type*) [Field F] (W : Type*) [AddCommGroup W] [Module F[X] W]
    [Module F W] [IsScalarTower F F[X] W] : W →ₗ[F] W :=
  (LinearMap.lsmul F[X] W (X : F[X])).restrictScalars F

/-
The characteristic polynomial of multiplication-by-`X` on `AEval' f` is `f.charpoly`.
-/
lemma charpoly_mulX_aeval' {W : Type*} [AddCommGroup W] [Module F W]
    [Module.Finite F W] [Module.Free F W] (f : Module.End F W) :
    (mulX F (Module.AEval' f)).charpoly = f.charpoly := by
  -- By definition of $AEval'$, we know that $mulX F (Module.AEval' f)$ is conjugate to $f$.
  have h_conj : (mulX F (Module.AEval' f)) = (LinearEquiv.conj (Module.AEval'.of f) f) := by
    ext m;
    convert Module.AEval'.of_symm_X_smul f ( ( Module.AEval'.of f ).symm m ) using 1;
  rw [ h_conj, LinearEquiv.charpoly_conj ]

/-
An `F[X]`-linear equivalence preserves the charpoly of multiplication-by-`X`.
-/
lemma charpoly_mulX_congr {W₁ W₂ : Type*}
    [AddCommGroup W₁] [Module F[X] W₁] [Module F W₁] [IsScalarTower F F[X] W₁]
    [Module.Finite F W₁] [Module.Free F W₁]
    [AddCommGroup W₂] [Module F[X] W₂] [Module F W₂] [IsScalarTower F F[X] W₂]
    [Module.Finite F W₂] [Module.Free F W₂]
    (e : W₁ ≃ₗ[F[X]] W₂) :
    (mulX F W₁).charpoly = (mulX F W₂).charpoly := by
  convert (LinearEquiv.charpoly_conj (e.restrictScalars F) (mulX F W₁)).symm using 2
  ext w₂
  -- residual point-wise goal: `X • w₂ = ((e.restrictScalars F).conj (mulX F W₁)) w₂`.
  -- Unfold the conjugation and use that the underlying `e` is `F[X]`-linear, so it
  -- commutes with the `X`-action.
  simp only [mulX, LinearEquiv.conj_apply, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, LinearMap.lsmul_apply,
    LinearEquiv.restrictScalars_apply, LinearEquiv.coe_coe]
  rw [map_smul, show ((e.restrictScalars F).symm) w₂ = e.symm w₂ from rfl,
    e.apply_symm_apply]

/-
Determinant of a (dependent) block-diagonal matrix is the product of the determinants.
-/
lemma det_blockDiagonal' {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ι → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    (Mat : (i : ι) → Matrix (m i) (m i) R) :
    (Matrix.blockDiagonal' Mat).det = ∏ i, (Mat i).det := by
  induction' h : Fintype.card ι with k ih generalizing ι;
  · rw [ Fintype.card_eq_zero_iff ] at h;
    simp +decide [ Matrix.det_apply' ];
  · obtain ⟨i, hi⟩ : ∃ i : ι, True := by
      exact Fintype.card_pos_iff.mp ( h.symm ▸ Nat.succ_pos _ ) |> fun ⟨ i ⟩ => ⟨ i, trivial ⟩;
    -- Let's denote the remaining part of the index type by `ι'`.
    set ι' := {j : ι | j ≠ i} with hι';
    -- By definition of `blockDiagonal'`, we can rewrite the determinant as the product of the determinants of the blocks.
    have h_det : (blockDiagonal' Mat).det = (Matrix.fromBlocks (Mat i) 0 0 (blockDiagonal' (fun j : ι' => Mat j.val))).det := by
      obtain ⟨e, he⟩ : ∃ e : (Σ j : ι, m j) ≃ (m i) ⊕ (Σ j : ι', m j.val), ∀ x y, (blockDiagonal' Mat) x y = (Matrix.fromBlocks (Mat i) 0 0 (blockDiagonal' (fun j : ι' => Mat j.val))) (e x) (e y) := by
        refine' ⟨ _, _ ⟩;
        refine' Equiv.ofBijective ( fun x => if hx : x.1 = i then Sum.inl ( hx ▸ x.2 ) else Sum.inr ⟨ ⟨ x.1, hx ⟩, x.2 ⟩ ) ⟨ fun x y hxy => _, fun x => _ ⟩;
        grind;
        rcases x with ( x | ⟨ ⟨ j, hj ⟩, x ⟩ );
        exact ⟨ ⟨ i, x ⟩, by simp +decide ⟩;
        exact ⟨ ⟨ j, x ⟩, by simp +decide [ hj.out ] ⟩;
        rintro ⟨ x, y ⟩ ⟨ u, v ⟩ ; by_cases hx : x = i <;> by_cases hu : u = i <;> simp +decide [ hx, hu, blockDiagonal' ] ;
        · aesop;
        · exact fun h => False.elim ( hu h.symm );
      rw [ ← Matrix.det_submatrix_equiv_self e ];
      exact congr_arg Matrix.det ( by ext x y; exact he x y );
    rw [ h_det, Matrix.det_fromBlocks_zero₂₁, ih ];
    · rw [ Finset.prod_eq_mul_prod_diff_singleton ( Finset.mem_univ i ) ];
      refine' congr rfl ( Finset.prod_bij ( fun j _ => j ) _ _ _ _ ) <;> simp +decide;
      · exact fun x hx => hx;
      · exact fun j hj => hj;
    · simp +decide [ h, hι' ]

/-
Characteristic polynomial of a (dependent) block-diagonal matrix is the product.
-/
lemma charpoly_blockDiagonal' {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ι → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    (Mat : (i : ι) → Matrix (m i) (m i) R) :
    (Matrix.blockDiagonal' Mat).charpoly = ∏ i, (Mat i).charpoly := by
  convert det_blockDiagonal' _ using 1;
  all_goals try infer_instance;
  unfold Matrix.charpoly;
  congr;
  ext ⟨ i, a ⟩ ⟨ j, b ⟩ ; by_cases hij : i = j <;> simp +decide [ hij, Matrix.charmatrix ] ;
  · subst hij; simp +decide [ Matrix.diagonal ] ;
  · simp +decide [ hij, blockDiagonal' ]

/-
The charpoly of multiplication-by-`X` over an internal direct sum is the product of the
charpolys of the restrictions to the summands.
-/
lemma charpoly_mulX_isInternal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : Type*} [AddCommGroup W] [Module F[X] W] [Module F W] [IsScalarTower F F[X] W]
    [Module.Finite F W] [Module.Free F W]
    {S : ι → Submodule F W}
    (hmap : ∀ i, ∀ x ∈ S i, mulX F W x ∈ S i)
    (h : DirectSum.IsInternal S) :
    (mulX F W).charpoly = ∏ i, ((mulX F W).restrict (fun x hx => hmap i x hx)).charpoly := by
  convert ( RCF.charpoly_blockDiagonal' fun i => LinearMap.toMatrix ( Module.Free.chooseBasis F ( S i ) ) ( Module.Free.chooseBasis F ( S i ) ) ( ( mulX F W ).restrict ( hmap i ) ) ) using 1;
  convert ( LinearMap.charpoly_toMatrix ( mulX F W ) ( h.collectedBasis ( fun i => Module.Free.chooseBasis F ( S i ) ) ) ) |> Eq.symm using 1;
  rw [ LinearMap.toMatrix_directSum_collectedBasis_eq_blockDiagonal' ]

/-
The canonical component submodules of an external direct sum form an internal direct sum
(viewed as `F`-submodules).
-/
lemma directSum_components_isInternal {ι : Type*} [DecidableEq ι]
    (W : ι → Type*) [∀ i, AddCommGroup (W i)] [∀ i, Module F[X] (W i)]
    [∀ i, Module F (W i)] [∀ i, IsScalarTower F F[X] (W i)] :
    DirectSum.IsInternal
      (fun i => (LinearMap.range (DirectSum.lof F[X] ι W i)).restrictScalars F) := by
  convert DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top _ _;
  · intro i; simp +decide [ Submodule.restrictScalars ] ;
    rw [ Submodule.disjoint_def ] ; simp +decide [ Submodule.mem_iSup ];
    intro a ha; specialize ha ( LinearMap.ker ( DirectSum.component F[X] ι W i ) |> Submodule.restrictScalars F ) ; simp_all +decide [ SetLike.le_def ] ;
    convert ha _;
    · exact ⟨ fun h => by simpa using congr_arg ( fun x => x i ) h, fun h => by simp +decide [ h ] ⟩;
    · intro j hj a; erw [ DirectSum.component.of ] ; aesop;
  · refine' eq_top_iff.mpr fun x hx => _;
    induction x using DirectSum.induction_on ; aesop;
    · exact Submodule.mem_iSup_of_mem ‹_› ( Set.mem_range_self _ );
    · aesop

/-
The charpoly of multiplication-by-`X` over a finite direct sum is the product.
-/
lemma charpoly_mulX_directSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : ι → Type*) [∀ i, AddCommGroup (W i)] [∀ i, Module F[X] (W i)]
    [∀ i, Module F (W i)] [∀ i, IsScalarTower F F[X] (W i)]
    [∀ i, Module.Finite F (W i)] [∀ i, Module.Free F (W i)] :
    (mulX F (DirectSum ι W)).charpoly = ∏ i, (mulX F (W i)).charpoly := by
  convert RCF.charpoly_mulX_isInternal _ _;
  any_goals try exact fun i => ( LinearMap.range ( DirectSum.lof F[X] ι W i ) ).restrictScalars F;
  any_goals exact RCF.directSum_components_isInternal W;
  swap;
  intro i x hx;
  obtain ⟨ y, rfl ⟩ := hx;
  exact ⟨ ( X : F[X] ) • y, by simp +decide [ mulX ] ⟩;
  convert RCF.charpoly_mulX_congr _;
  · infer_instance;
  · infer_instance;
  · infer_instance;
  · refine' LinearEquiv.ofBijective _ ⟨ _, _ ⟩;
    refine' { toFun := fun x => ⟨ DirectSum.lof F[X] ι W _ x, _ ⟩, map_add' := _, map_smul' := _ };
    all_goals simp +decide [ Function.Injective, Function.Surjective ];
    · aesop;
    · intro x y hxy;
      replace hxy := congr_arg ( fun f => f ‹_› ) hxy ; aesop

/-
The charpoly of multiplication-by-`X` on the cyclic module `F[X] ⧸ (g)` is `g`
(for `g` monic).
-/
set_option maxHeartbeats 1000000 in
lemma charpoly_mulX_quotient (g : F[X]) (hg : g.Monic)
    [Module.Finite F (F[X] ⧸ Ideal.span {g})] :
    (mulX F (F[X] ⧸ Ideal.span {g})).charpoly = g := by
  -- The minimal polynomial of multiplication-by-`X` on `F[X] ⧸ Ideal.span {g}` is `g`.
  have h_minpoly : minpoly F (mulX F (F[X] ⧸ Ideal.span {g})) = g := by
    have h_minpoly : ∀ p : F[X], aeval (mulX F (F[X] ⧸ Ideal.span {g})) p = 0 ↔ g ∣ p := by
      intro p
      have h_aeval : ∀ w : F[X] ⧸ Ideal.span {g}, (aeval (mulX F (F[X] ⧸ Ideal.span {g})) p) w = p • w := by
        induction p using Polynomial.induction_on <;> simp_all +decide [ Polynomial.aeval_add, Polynomial.aeval_X, Polynomial.aeval_C ];
        · intro w; exact (by
          convert rfl;
          ext; simp [HSMul.hSMul];
          simp +decide [ SMul.smul ];
          simp +decide [ Algebra.smul_def ]);
        · simp +decide [ add_smul ];
        · simp_all +decide [ pow_succ, mulX ];
          simp +decide [ ← mul_assoc, ← smul_assoc ];
      constructor;
      · intro h
        have h_annihilator : p • (1 : F[X] ⧸ Ideal.span {g}) = 0 := by
          rw [ ← h_aeval, h, LinearMap.zero_apply ];
        erw [ Ideal.Quotient.eq_zero_iff_mem ] at h_annihilator;
        simpa [ Ideal.mem_span_singleton ] using h_annihilator;
      · intro hp
        have h_annihilate : ∀ w : F[X] ⧸ Ideal.span {g}, p • w = 0 := by
          obtain ⟨ q, rfl ⟩ := hp;
          intro w
          obtain ⟨ w', rfl ⟩ := Ideal.Quotient.mk_surjective w;
          erw [ Ideal.Quotient.eq_zero_iff_mem ];
          exact Ideal.mem_span_singleton.mpr ⟨ q * w', by simp +decide [ mul_comm, mul_left_comm ] ⟩;
        exact LinearMap.ext fun w => h_aeval w ▸ h_annihilate w;
    have h_minpoly : minpoly F (mulX F (F[X] ⧸ Ideal.span {g})) ∣ g := by
      exact minpoly.dvd F _ ( h_minpoly _ |>.2 dvd_rfl );
    refine' Polynomial.eq_of_monic_of_associated _ hg _;
    · exact minpoly.monic ( show IsIntegral F ( mulX F ( F[X] ⧸ Ideal.span { g } ) ) from by exact ( LinearMap.isIntegral _ ) );
    · exact associated_of_dvd_dvd h_minpoly ( ‹∀ p : F[X], ( aeval ( mulX F ( F[X] ⧸ Ideal.span { g } ) ) ) p = 0 ↔ g ∣ p› _ |>.1 ( minpoly.aeval F ( mulX F ( F[X] ⧸ Ideal.span { g } ) ) ) );
  have h_deg : Polynomial.natDegree (minpoly F (mulX F (F[X] ⧸ Ideal.span {g}))) = Polynomial.natDegree ((mulX F (F[X] ⧸ Ideal.span {g})).charpoly) := by
    convert finrank_quotient_span_eq_natDegree ( f := g ) using 1;
    · rw [ h_minpoly, finrank_quotient_span_eq_natDegree ];
    · convert LinearMap.charpoly_natDegree ( mulX F ( F[X] ⧸ Ideal.span { g } ) ) using 1;
      rw [ ← finrank_quotient_span_eq_natDegree ];
  -- Since the minimal polynomial divides the characteristic polynomial and they have the same degree, they must be equal.
  have h_div : minpoly F (mulX F (F[X] ⧸ Ideal.span {g})) ∣ (mulX F (F[X] ⧸ Ideal.span {g})).charpoly := by
    exact LinearMap.minpoly_dvd_charpoly _;
  obtain ⟨ q, hq ⟩ := h_div;
  have hq_monic : q.Monic := by
    have := LinearMap.charpoly_monic ( mulX F ( F[X] ⧸ Ideal.span { g } ) );
    rw [ hq, Polynomial.Monic, Polynomial.leadingCoeff_mul ] at this ; aesop;
  by_cases hq_zero : q = 0 <;> simp_all +decide [ Polynomial.natDegree_mul' ]

/-
The quotient of `F[X]` by the span of a nonzero polynomial is finite-dimensional over `F`.
-/
lemma finite_quotient_span (g : F[X]) (hg : g ≠ 0) :
    Module.Finite F (F[X] ⧸ Ideal.span {g}) := by
  convert ( AdjoinRoot.powerBasis hg ).finite

/-- The monic associate of a polynomial. -/
noncomputable def monicAssoc (g : F[X]) : F[X] := g * Polynomial.C (g.leadingCoeff)⁻¹

lemma monicAssoc_monic {g : F[X]} (hg : g ≠ 0) : (monicAssoc g).Monic :=
  Polynomial.monic_mul_leadingCoeff_inv hg

lemma monicAssoc_associated {g : F[X]} (hg : g ≠ 0) : Associated (monicAssoc g) g := by
  refine' associated_of_dvd_dvd _ _;
  · exact ⟨ Polynomial.C ( Polynomial.leadingCoeff g ), by rw [ monicAssoc, mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ ( Polynomial.leadingCoeff_ne_zero.mpr hg ), Polynomial.C_1, mul_one ] ⟩;
  · exact dvd_mul_right _ _

lemma span_monicAssoc {g : F[X]} (hg : g ≠ 0) :
    Ideal.span {monicAssoc g} = Ideal.span {g} :=
  Ideal.span_singleton_eq_span_singleton.mpr (monicAssoc_associated hg)

lemma monicAssoc_natDegree {g : F[X]} (hg : g ≠ 0) : (monicAssoc g).natDegree = g.natDegree := by
  unfold monicAssoc;
  rw [ Polynomial.natDegree_mul' ] <;> aesop

/-
The module-theoretic core: given a primary decomposition of the `F[X]`-module `M`,
the charpoly is the product of the monic associates of the prime powers, and the minpoly
divisibility is governed by the prime powers.
-/
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
lemma decomp_charpoly_minpoly {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n F)
    {ι' : Type*} [Fintype ι']
    (p : ι' → F[X]) (hp : ∀ i, Irreducible (p i)) (ev : ι' → ℕ)
    (e : Module.AEval' (Matrix.toLin' M) ≃ₗ[F[X]]
          DirectSum ι' (fun i => F[X] ⧸ Ideal.span {p i ^ ev i})) :
    M.charpoly = ∏ i, monicAssoc (p i ^ ev i) ∧
    (∀ c : F[X], minpoly F M ∣ c ↔ ∀ i, (p i ^ ev i) ∣ c) := by
  classical
  haveI hfin : ∀ i, Module.Finite F (F[X] ⧸ Ideal.span {p i ^ ev i}) :=
    fun i => RCF.finite_quotient_span _ (pow_ne_zero _ (hp i).ne_zero)
  refine ⟨?_, ?_⟩
  · have key : M.charpoly = ∏ i, (mulX F (F[X] ⧸ Ideal.span {p i ^ ev i})).charpoly := by
      rw [← RCF.charpoly_mulX_directSum, ← RCF.charpoly_mulX_congr e,
        RCF.charpoly_mulX_aeval', Matrix.charpoly_toLin']
    rw [key]
    refine Finset.prod_congr rfl fun i _ => ?_
    haveI : Module.Finite F (F[X] ⧸ Ideal.span {monicAssoc (p i ^ ev i)}) :=
      RCF.finite_quotient_span _
        (RCF.monicAssoc_monic (pow_ne_zero _ (hp i).ne_zero)).ne_zero
    rw [RCF.charpoly_mulX_congr (Submodule.quotEquivOfEq _ _
        (RCF.span_monicAssoc (pow_ne_zero _ (hp i).ne_zero)).symm),
      RCF.charpoly_mulX_quotient (monicAssoc (p i ^ ev i))
        (RCF.monicAssoc_monic (pow_ne_zero _ (hp i).ne_zero))]
  · have h_annihilator : Ideal.span {minpoly F M} = ⨅ i, Ideal.span {p i ^ ev i} := by
      have h_annihilator : Module.annihilator F[X] (DirectSum ι' (fun i => F[X] ⧸ Ideal.span {p i ^ ev i})) = ⨅ i, Ideal.span {p i ^ ev i} := by
        have h_annihilator : ∀ i, Module.annihilator F[X] (F[X] ⧸ Ideal.span {p i ^ ev i}) = Ideal.span {p i ^ ev i} := by
          intro i;
          exact Ideal.annihilator_quotient;
        convert Module.annihilator_dfinsupp;
        rw [ h_annihilator ];
      rw [ ← h_annihilator, ← e.annihilator_eq ];
      rw [ ← minpoly_toLin', Polynomial.span_minpoly_eq_annihilator ];
    intro c; rw [ Ideal.ext_iff ] at h_annihilator; specialize h_annihilator c; simp_all +decide [ Ideal.mem_span_singleton, Submodule.mem_iInf ] ;

/-
Existence of elementary divisors: monic prime powers whose product is the charpoly,
and whose lcm (characterized by the universal divisibility property) is the minpoly.
-/
lemma exists_elementary_divisors {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n F) :
    ∃ (m : ℕ) (q : Fin m → F[X]),
      (∀ i, (q i).Monic) ∧ (∀ i, 0 < (q i).natDegree) ∧
      (∀ i, ∃ π : F[X], Irreducible π ∧ ∃ k : ℕ, 0 < k ∧ q i = π ^ k) ∧
      M.charpoly = ∏ i, q i ∧
      (∀ c : F[X], minpoly F M ∣ c ↔ ∀ i, q i ∣ c) := by
  obtain ⟨ι', _instι', p, hp, ev, ⟨e⟩⟩ := Module.equiv_directSum_of_isTorsion (Module.AEval.isTorsion_of_finiteDimensional F (n → F) (Matrix.toLin' M));
  obtain ⟨hchar, hmin⟩ := RCF.decomp_charpoly_minpoly M p hp ev e;
  refine' ⟨ Fintype.card { i : ι' // 0 < ev i }, fun j => monicAssoc ( p ( Fintype.equivFin { i : ι' // 0 < ev i } |>.symm j ) ^ ev ( Fintype.equivFin { i : ι' // 0 < ev i } |>.symm j ) ), _, _, _, _, _ ⟩;
  · exact fun i => monicAssoc_monic ( pow_ne_zero _ ( hp _ |> Irreducible.ne_zero ) );
  · intro i
    simp [monicAssoc];
    rw [ Polynomial.natDegree_mul' ] <;> simp +decide [ Polynomial.natDegree_pow, Polynomial.natDegree_C ];
    · exact ⟨ by simpa using ( Fintype.equivFin { i // 0 < ev i } ).symm i |>.2, Polynomial.natDegree_pos_iff_degree_pos.mpr ( Polynomial.degree_pos_of_irreducible ( hp _ ) ) ⟩;
    · exact fun h => absurd h ( Polynomial.ne_zero_of_degree_gt ( Polynomial.degree_pos_of_irreducible ( hp _ ) ) );
  · intro i;
    refine' ⟨ monicAssoc ( p ( Fintype.equivFin { i // 0 < ev i } |>.symm i ) ), _, ev ( Fintype.equivFin { i // 0 < ev i } |>.symm i ), _, _ ⟩;
    · have := monicAssoc_associated ( show p ( Fintype.equivFin { i // 0 < ev i } |>.symm i ) ≠ 0 from fun h => by simpa [ h ] using hp ( Fintype.equivFin { i // 0 < ev i } |>.symm i ) );
      exact this.irreducible_iff.mpr ( hp _ );
    · exact ( Fintype.equivFin { i // 0 < ev i } |>.symm i ) |>.2;
    · unfold monicAssoc; simp +decide [ Polynomial.leadingCoeff_pow ] ;
      rw [ mul_pow, ← Polynomial.C_pow, inv_pow ];
  · rw [ hchar, ← Finset.prod_subset ( Finset.subset_univ { i : ι' | 0 < ev i } ) ];
    · refine' Finset.prod_bij ( fun i hi => Fintype.equivFin { i : ι' // 0 < ev i } ⟨ i, Finset.mem_filter.mp hi |>.2 ⟩ ) _ _ _ _ <;> simp +decide;
      exact fun b => ⟨ _, Subtype.property ( Fintype.equivFin { i // 0 < ev i } |>.symm b ), by simp +decide ⟩;
    · simp +contextual [ monicAssoc ];
  · intro c;
    convert hmin c using 1;
    constructor <;> intro h i;
    · by_cases hi : 0 < ev i;
      · convert dvd_trans _ ( h ( Fintype.equivFin { i : ι' // 0 < ev i } ⟨ i, hi ⟩ ) ) using 1;
        simp +decide [ monicAssoc ];
      · aesop;
    · exact dvd_trans ( monicAssoc_associated ( pow_ne_zero _ ( hp _ |> Irreducible.ne_zero ) ) |> Associated.dvd ) ( h _ )

/-
Distinct monic irreducible polynomials give coprime powers.
-/
lemma coprime_monic_irreducible_pow {a b : F[X]} (ha : Irreducible a) (hb : Irreducible b)
    (hma : a.Monic) (hmb : b.Monic) (hne : a ≠ b) (m k : ℕ) :
    IsCoprime (a ^ m) (b ^ k) := by
  refine' IsCoprime.pow _;
  refine' ha.coprime_iff_not_dvd.mpr _;
  rintro ⟨ c, rfl ⟩;
  rw [ irreducible_mul_iff ] at hb;
  cases' hb with hb hb <;> simp_all +decide [ Polynomial.Monic.def, Polynomial.leadingCoeff_mul ];
  · rw [ Polynomial.isUnit_iff ] at hb ; aesop;
  · exact ha.not_isUnit hb.2

/-
Auxiliary regrouping over a `Finset`, by strong induction (peeling off the lcm).
-/
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
lemma exists_chain_aux {ι : Type*} [DecidableEq ι]
    (π : ι → F[X]) (k : ι → ℕ)
    (hmonπ : ∀ i, (π i).Monic) (hirr : ∀ i, Irreducible (π i)) (hk : ∀ i, 0 < k i)
    (s : Finset ι) :
    ∃ L : List F[X],
      (∀ p ∈ L, p.Monic) ∧ (∀ p ∈ L, 0 < p.natDegree) ∧
      (∀ a b : Fin L.length, (a : ℕ) ≤ b → L[a] ∣ L[b]) ∧
      L.prod = ∏ i ∈ s, π i ^ k i ∧
      (∀ c : F[X], (L.getLast?.getD 1 ∣ c) ↔ ∀ i ∈ s, π i ^ k i ∣ c) := by
  by_cases hs : s.Nonempty;
  · induction' s using Finset.strongInduction with s ih;
    obtain ⟨R, d, hR, hd⟩ : ∃ R : Finset ι, ∃ d : F[X], R ⊆ s ∧ R.Nonempty ∧ d = ∏ i ∈ R, (π i) ^ (k i) ∧ (∀ i ∈ s, (π i) ^ (k i) ∣ d) ∧ (∀ c : F[X], d ∣ c ↔ ∀ i ∈ R, (π i) ^ (k i) ∣ c) := by
      obtain ⟨R, hR⟩ : ∃ R : Finset ι, R ⊆ s ∧ R.Nonempty ∧ (∀ i ∈ s, ∃ j ∈ R, π i = π j ∧ k i ≤ k j) ∧ (∀ i ∈ R, ∀ j ∈ R, π i = π j → i = j) := by
        have hR : ∃ R : Finset ι, R ⊆ s ∧ (∀ i ∈ s, ∃ j ∈ R, π i = π j ∧ k i ≤ k j) ∧ (∀ i ∈ R, ∀ j ∈ R, π i = π j → i = j) := by
          have hR : ∀ t : Finset ι, t ⊆ s → ∃ R : Finset ι, R ⊆ t ∧ (∀ i ∈ t, ∃ j ∈ R, π i = π j ∧ k i ≤ k j) ∧ (∀ i ∈ R, ∀ j ∈ R, π i = π j → i = j) := by
            intro t ht;
            induction' t using Finset.induction with i t hi ih;
            · exact ⟨ ∅, by simp +decide ⟩;
            · obtain ⟨ R, hR₁, hR₂, hR₃ ⟩ := ih ( Finset.Subset.trans ( Finset.subset_insert _ _ ) ht );
              by_cases hiR : ∃ j ∈ R, π i = π j ∧ k i ≤ k j;
              · use R;
                grind;
              · by_cases hiR : ∃ j ∈ R, π i = π j;
                · obtain ⟨ j, hj₁, hj₂ ⟩ := hiR;
                  use Insert.insert i (R.erase j);
                  grind;
                · use Insert.insert i R;
                  grind;
          exact hR s Finset.Subset.rfl;
        grind +extAll;
      refine' ⟨ R, _, hR.1, hR.2.1, rfl, _, _ ⟩;
      · intro i hi; obtain ⟨ j, hj, hij, hkj ⟩ := hR.2.2.1 i hi; exact dvd_trans ( pow_dvd_pow _ hkj ) ( Finset.dvd_prod_of_mem _ hj |> dvd_trans ( by simp +decide [ hij ] ) ) ;
      · intro c;
        refine' ⟨ fun h i hi => dvd_trans _ h, fun h => _ ⟩;
        · exact Finset.dvd_prod_of_mem _ hi;
        · refine' Finset.prod_dvd_of_coprime _ _;
          · intro i hi j hj hij;
            exact IsCoprime.pow ( by exact ( hirr i |> Irreducible.coprime_iff_not_dvd ) |>.2 fun h => hij <| hR.2.2.2 i hi j hj <| Polynomial.eq_of_monic_of_associated ( hmonπ i ) ( hmonπ j ) <| associated_of_dvd_dvd h <| (hirr i).dvd_symm (hirr j) h );
          · exact h;
    obtain ⟨L', hL'mon, hL'pos, hL'chain, hL'prod, hL'last⟩ : ∃ L' : List F[X], (∀ p ∈ L', p.Monic) ∧ (∀ p ∈ L', 0 < p.natDegree) ∧ (∀ a b : Fin L'.length, a.val ≤ b.val → L'[a] ∣ L'[b]) ∧ L'.prod = ∏ i ∈ s \ R, (π i) ^ (k i) ∧ (∀ c : F[X], L'.getLast?.getD 1 ∣ c ↔ ∀ i ∈ s \ R, (π i) ^ (k i) ∣ c) := by
      by_cases hR' : (s \ R).Nonempty;
      · grind +extAll;
      · use [] ; simp_all +decide [ Finset.Nonempty ] ;
        rw [ Finset.sdiff_eq_empty_iff_subset.mpr hR', Finset.prod_empty ];
    refine' ⟨ L' ++ [ d ], _, _, _, _, _ ⟩;
    · simp +zetaDelta at *;
      rintro p ( hp | rfl ) <;> [ exact hL'mon p hp; exact hd.2.1.symm ▸ Polynomial.monic_prod_of_monic _ _ fun i hi => Polynomial.Monic.pow ( hmonπ i ) _ ];
    · simp_all +decide [ Polynomial.Monic.def ];
      rintro p ( hp | rfl );
      · exact hL'pos p hp;
      · rw [ Polynomial.natDegree_prod _ _ fun i hi => pow_ne_zero _ ( Polynomial.ne_zero_of_degree_gt ( Polynomial.degree_pos_of_irreducible ( hirr i ) ) ) ];
        exact Finset.sum_pos ( fun i hi => by rw [ Polynomial.natDegree_pow, Polynomial.natDegree_eq_of_degree_eq_some ( Polynomial.degree_eq_natDegree ( Polynomial.ne_zero_of_degree_gt ( Polynomial.degree_pos_of_irreducible ( hirr i ) ) ) ) ] ; exact mul_pos ( hk i ) ( Polynomial.natDegree_pos_iff_degree_pos.mpr ( Polynomial.degree_pos_of_irreducible ( hirr i ) ) ) ) hd.1;
    · intro a b hab;
      by_cases ha : a.val < L'.length <;> by_cases hb : b.val < L'.length <;> simp +decide [ ha, hb ] at hab ⊢;
      · exact hL'chain ⟨ a, ha ⟩ ⟨ b, hb ⟩ hab;
      · have h_div : L'[a] ∣ L'.getLast?.getD 1 := by
          convert hL'chain ⟨ a, ha ⟩ ⟨ L'.length - 1, Nat.sub_lt ( by linarith ) zero_lt_one ⟩ _ using 1;
          · grind;
          · exact Nat.le_pred_of_lt ha;
        refine' dvd_trans h_div _;
        grind;
      · exact False.elim ( ha ( lt_of_le_of_lt hab hb ) );
      · grind;
    · simp +decide [ *, Finset.prod_sdiff hR ];
    · intro c; constructor <;> intro hc <;> simp_all +decide ;
      · exact fun i hi => dvd_trans ( hd.2.2.1 i hi ) ( hd.2.1.symm ▸ hc );
      · grind;
  · refine' ⟨ [ ], _, _, _, _, _ ⟩ <;> simp +decide [ Finset.not_nonempty_iff_eq_empty.mp hs ]

/-
Regrouping prime powers into an invariant-factor chain (pure polynomial combinatorics).
-/
lemma exists_chain_of_prime_powers {ι : Type*} [Fintype ι]
    (q : ι → F[X]) (hmon : ∀ i, (q i).Monic)
    (hpp : ∀ i, ∃ π : F[X], Irreducible π ∧ ∃ k : ℕ, 0 < k ∧ q i = π ^ k) :
    ∃ L : List F[X],
      (∀ p ∈ L, p.Monic) ∧ (∀ p ∈ L, 0 < p.natDegree) ∧
      (∀ s t : Fin L.length, (s : ℕ) ≤ t → L[s] ∣ L[t]) ∧
      L.prod = ∏ i, q i ∧
      (∀ c : F[X], (L.getLast?.getD 1 ∣ c) ↔ ∀ i, q i ∣ c) := by
  choose π hirr k hk hq using hpp;
  -- Define the monic prime base `base i := RCF.monicAssoc (π i)`.
  set base : ι → F[X] := fun i => RCF.monicAssoc (π i);
  -- By definition of `base`, we know that `base i` is monic and irreducible.
  have hbase_monic : ∀ i, (base i).Monic := by
    exact fun i => monicAssoc_monic ( hirr i |> Irreducible.ne_zero )
  have hbase_irr : ∀ i, Irreducible (base i) := by
    intro i;
    have := RCF.monicAssoc_associated ( show π i ≠ 0 from fun h => by simpa [ h ] using hirr i );
    exact this.irreducible_iff.mpr ( hirr i )
  have hbase_pow : ∀ i, q i = base i ^ k i := by
    intro i
    simp [base, hq];
    simp +decide [ monicAssoc ];
    have := hmon i; simp_all +decide [ Polynomial.Monic.def ] ;
    rw [ mul_pow, ← Polynomial.C_pow, inv_pow, hmon i, inv_one, Polynomial.C_1, mul_one ];
  convert exists_chain_aux base k hbase_monic hbase_irr hk Finset.univ using 1;
  · simp +decide [ ← hbase_pow ];
  · exact Classical.decEq ι

end RCF

/-- Rational canonical form, existence (strong form): every square matrix `M`
over a field admits an invariant-factor chain whose product equals `charpoly M`
and whose last factor equals `minpoly M`. -/
theorem rational_canonical_form_exists
    {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n F) :
    ∃ c : InvariantFactorChain F,
      c.prodFactors = M.charpoly ∧ c.lastFactor = minpoly F M := by
  obtain ⟨m, q, hmon, _, hpp, hchar, hmin⟩ := RCF.exists_elementary_divisors M
  obtain ⟨L, hLmon, hLpos, hLchain, hLprod, hLlast⟩ :=
    RCF.exists_chain_of_prime_powers q hmon hpp
  refine ⟨⟨L, hLmon, hLpos, hLchain⟩, ?_, ?_⟩
  · show L.prod = M.charpoly
    rw [hLprod, hchar]
  · show L.getLast?.getD 1 = minpoly F M
    -- both monic, mutually divide via the lcm characterizations
    have hMint : IsIntegral F M := Algebra.IsIntegral.isIntegral M
    have hlast_monic : (L.getLast?.getD 1).Monic := by
      rcases h : L.getLast? with _ | a
      · simp [monic_one]
      · simp only [Option.getD_some]
        exact hLmon a (List.mem_of_mem_getLast? h)
    have h1 : (L.getLast?.getD 1) ∣ minpoly F M := by
      rw [hLlast]; intro i; exact (hmin _).mp dvd_rfl i
    have h2 : minpoly F M ∣ (L.getLast?.getD 1) := by
      rw [hmin]; intro i; exact (hLlast _).mp dvd_rfl i
    exact Polynomial.eq_of_monic_of_associated hlast_monic (minpoly.monic hMint)
      (associated_of_dvd_dvd h1 h2)

end RationalCanonicalFormExists
