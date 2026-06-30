/-
  The minimal polynomial divides the generalized-eigenspace product
  Open Question (cayley-hamilton-minpoly-oq-01-oq-01)

  Parent: cayley-hamilton-minpoly-oq-01 (Jordan Canonical Form and the Minimal Polynomial)

  The parent file axiomatizes the full JCF–minpoly product formula

      minpoly K f = ∏_{μ} (X - μ)^{e_μ},   e_μ = maxGenEigenspaceIndex f μ

  as `minpoly_product_formula`, noting that Mathlib 4.26.0 does not yet provide
  the explicit Jordan block matrix decomposition.

  This file proves the FORWARD divisibility direction of that formula WITHOUT any
  Jordan block infrastructure — purely from Mathlib's generalized-eigenspace
  theory (`iSup_maxGenEigenspace_eq_top`):

      minpoly K f  ∣  ∏_{μ eigenvalue} (X - μ)^{e_μ}.

  The key idea: over an algebraically closed field the maximal generalized
  eigenspaces span V (Axler 8.21 = `iSup_maxGenEigenspace_eq_top`). On the
  μ-summand the factor `(X - μ)^{e_μ}` already annihilates, and since the factors
  commute (the product lives in the commutative ring K[X]) the whole product
  annihilates f. Hence the product is a multiple of the minimal polynomial.

  This file then closes the gap entirely, proving the parent's axiomatized
  identity `minpoly_product_formula` as a theorem
  (`minpoly_eq_prod_pow_maxGenEigenspaceIndex`):

      minpoly K f = ∏_{μ eigenvalue} (X - μ)^{maxGenEigenspaceIndex f μ}.

  The reverse divisibility `∏ ∣ minpoly` is supplied **without** assembling a
  primary decomposition and, notably, needs only `FiniteDimensional` (no
  algebraic closure): it argues one eigenvalue at a time via the **exactness** of
  the generalized-eigenspace index.

    * `genEigenspace_lt_succ_of_lt_maxGenEigenspaceIndex` — below the limit index the
      generalized-eigenspace chain strictly increases, so `maxGenEigenspaceIndex` is
      the *exact* nilpotency index of `f - μ`, not just an upper bound.  Proved from
      Mathlib's `Module.End.ker_pow_constant` plus the least-index characterization
      of `maxGenEigenspaceIndex` (= `monotonicSequenceLimitIndex`).
    * `exists_mem_maxGenEigenspace_pow_pred_ne_zero` — the concrete witness: a vector
      in the maximal generalized eigenspace not killed by `(f - μ)^{e-1}`.
    * `pow_maxGenEigenspaceIndex_dvd_minpoly` — single-factor reverse divisibility
      `(X - μ)^{e_μ} ∣ minpoly`, via the witness, the root-multiplicity
      factorisation `minpoly = (X-μ)^m·g`, and `(X-μ)`–`g` coprimality (Bézout).
    * `prod_pow_maxGenEigenspaceIndex_dvd_minpoly` — the full product divides, by
      pairwise coprimality of the distinct linear-power factors.
    * `minpoly_eq_prod_pow_maxGenEigenspaceIndex` — the two divisibilities and
      monicity of both sides give the exact identity.

  Status: 0 sorries, 0 axioms. Fully verified against Mathlib 4.26.0
  (`#print axioms` lists only `propext`, `Classical.choice`, `Quot.sound`).

  References:
  - Axler, "Linear Algebra Done Right", Lemma 8.21 (generalized eigenspaces span)
  - Mathlib: LinearAlgebra.Eigenspace.{Basic, Triangularizable}
-/

import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open Module.End Polynomial

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

namespace JordanMinpolyOQ01OQ01

/-- If `ν` is not an eigenvalue of `f`, its maximal generalized eigenspace is trivial.
    (Contrapositive: a nonzero generalized eigenvector forces an eigenvalue.) -/
theorem maxGenEigenspace_eq_bot_of_not_hasEigenvalue [FiniteDimensional K V]
    {f : Module.End K V} {ν : K} (h : ¬ f.HasEigenvalue ν) :
    f.maxGenEigenspace ν = ⊥ := by
  by_contra hbot
  rw [maxGenEigenspace_eq] at hbot
  exact h (hasEigenvalue_of_hasGenEigenvalue (hasGenEigenvalue_iff.mpr hbot))

/-- `aeval f` of the factor `(X - C ν)^k` is the endomorphism `(f - ν • 1)^k`,
    matching the form used by `genEigenspace_nat`. -/
theorem aeval_linear_factor_pow (f : Module.End K V) (ν : K) (k : ℕ) :
    aeval f ((X - C ν) ^ k) = (f - ν • 1) ^ k := by
  rw [map_pow, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]

/-- **Forward divisibility of the JCF product formula.**

    Over an algebraically closed field, the minimal polynomial of `f` divides the
    product over the eigenvalues of `(X - μ)^{maxGenEigenspaceIndex f μ}`.

    Proof: the product polynomial annihilates `f`. The maximal generalized
    eigenspaces span `V`; on the `ν`-eigenspace the factor `(X - ν)^{e_ν}`
    already kills every vector, and the remaining (commuting) factors then map `0`
    to `0`. So the product evaluates to `0` on a spanning family, hence is `0`, and
    `minpoly.dvd` finishes. No Jordan block matrices required. -/
theorem minpoly_dvd_maxGenEigenspace_product [IsAlgClosed K] [FiniteDimensional K V]
    (f : Module.End K V) :
    minpoly K f ∣
      ∏ μ ∈ (finite_hasEigenvalue f).toFinset, (X - C μ) ^ f.maxGenEigenspaceIndex μ := by
  classical
  set s := (finite_hasEigenvalue f).toFinset with hs
  -- It suffices that the product annihilates f.
  refine minpoly.dvd K f ?_
  -- Show the endomorphism aeval f (∏ ...) is zero by checking its kernel is ⊤.
  rw [← LinearMap.ker_eq_top, eq_top_iff, ← iSup_maxGenEigenspace_eq_top f]
  refine iSup_le fun ν => ?_
  intro v hv
  rw [LinearMap.mem_ker]
  by_cases hν : ν ∈ s
  · -- ν is an eigenvalue: pull out its factor, which annihilates v.
    have efac : ((f - ν • 1) ^ f.maxGenEigenspaceIndex ν) v = 0 := by
      have hv' : v ∈ f.genEigenspace ν (f.maxGenEigenspaceIndex ν) := by
        rw [← maxGenEigenspace_eq]; exact hv
      rwa [genEigenspace_nat, LinearMap.mem_ker] at hv'
    rw [show (∏ μ ∈ s, (X - C μ) ^ f.maxGenEigenspaceIndex μ)
          = (∏ μ ∈ s.erase ν, (X - C μ) ^ f.maxGenEigenspaceIndex μ)
            * (X - C ν) ^ f.maxGenEigenspaceIndex ν
        from (Finset.prod_erase_mul s _ hν).symm,
       map_mul, Module.End.mul_apply, aeval_linear_factor_pow, efac, map_zero]
  · -- ν is not an eigenvalue: its eigenspace is trivial, so v = 0.
    have hnev : ¬ f.HasEigenvalue ν := fun hev =>
      hν ((Set.Finite.mem_toFinset _).mpr hev)
    have hv0 : v = 0 := by
      have : v ∈ (⊥ : Submodule K V) := by
        rw [← maxGenEigenspace_eq_bot_of_not_hasEigenvalue hnev]; exact hv
      simpa using this
    rw [hv0, map_zero]

/-- **Exactness of the generalized-eigenspace index.**

    Below `maxGenEigenspaceIndex` the generalized-eigenspace chain is *strictly*
    increasing: for every `k < f.maxGenEigenspaceIndex μ`,

        `f.genEigenspace μ k < f.genEigenspace μ (k + 1)`.

    Equivalently `maxGenEigenspaceIndex f μ` is the *exact* nilpotency index of
    `f - μ` on the maximal generalized eigenspace, not merely an upper bound: the
    chain cannot already be constant strictly below its limit index.

    This is the missing ingredient (`maxGenEigenspaceIndex_exact`) that the reverse
    divisibility `∏ (X - μ)^{e_μ} ∣ minpoly K f` requires.  It follows from
    Mathlib's one-step kernel-stabilization lemma `Module.End.ker_pow_constant`
    (equality of two consecutive kernels of a power forces the chain constant
    afterwards) together with the fact that `maxGenEigenspaceIndex` is, by
    definition, the *least* index at which the chain stabilizes. -/
theorem genEigenspace_lt_succ_of_lt_maxGenEigenspaceIndex [FiniteDimensional K V]
    (f : Module.End K V) (μ : K) {k : ℕ} (hk : k < f.maxGenEigenspaceIndex μ) :
    f.genEigenspace μ (k : ℕ∞) < f.genEigenspace μ ((k : ℕ∞) + 1) := by
  -- The chain is monotone, so it suffices to rule out equality at this step.
  refine lt_of_le_of_ne ((f.genEigenspace μ).monotone (by exact_mod_cast Nat.le_succ k)) ?_
  intro heq
  -- Equality of two consecutive generalized eigenspaces = equality of two
  -- consecutive kernels of powers of `f - μ`.
  have hker : LinearMap.ker ((f - μ • 1) ^ k)
      = LinearMap.ker ((f - μ • 1) ^ k.succ) := by
    have h1 : f.genEigenspace μ (k : ℕ∞) = LinearMap.ker ((f - μ • 1) ^ k) :=
      genEigenspace_nat
    have h2 : f.genEigenspace μ ((k + 1 : ℕ) : ℕ∞)
        = LinearMap.ker ((f - μ • 1) ^ (k + 1)) := genEigenspace_nat
    have hcast : ((k + 1 : ℕ) : ℕ∞) = (k : ℕ∞) + 1 := by push_cast; ring
    rw [Nat.succ_eq_add_one, ← h1, ← h2, hcast]
    exact heq
  -- `ker_pow_constant` then makes the kernel chain constant from `k` onwards, so
  -- the generalized-eigenspace chain is constant from `k` onwards too.
  have hstab : ∀ d : ℕ,
      f.genEigenspace μ (k : ℕ∞) = f.genEigenspace μ ((k + d : ℕ) : ℕ∞) := by
    intro d
    have hk' := Module.End.ker_pow_constant (f := f - μ • 1) (k := k) hker d
    rw [(genEigenspace_nat : f.genEigenspace μ (k : ℕ∞) = _),
        (genEigenspace_nat : f.genEigenspace μ ((k + d : ℕ) : ℕ∞) = _)]
    exact hk'
  -- Hence `k` is a stabilization index of the defining monotone sequence.
  have hmem : ∀ m : ℕ, k ≤ m →
      ((f.genEigenspace μ).comp WithTop.coeOrderHom.toOrderHom) k
        = ((f.genEigenspace μ).comp WithTop.coeOrderHom.toOrderHom) m := by
    intro m hm
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
    simpa using hstab d
  -- But `maxGenEigenspaceIndex` is the *least* such index, contradicting `k < it`.
  have hle : f.maxGenEigenspaceIndex μ ≤ k := Nat.sInf_le hmem
  exact absurd hk (not_lt.mpr hle)

/-- **The index is the exact nilpotency degree.**  When `maxGenEigenspaceIndex f μ`
    is positive there is a vector `v` in the maximal generalized eigenspace with
    `(f - μ)^{e-1} v ≠ 0` (while `(f - μ)^e v = 0`).  This is the concrete witness
    that distinguishes the *exact* product formula from the forward divisibility:
    no smaller exponent than `e_μ = maxGenEigenspaceIndex f μ` annihilates the
    whole `μ`-summand. -/
theorem exists_mem_maxGenEigenspace_pow_pred_ne_zero [FiniteDimensional K V]
    (f : Module.End K V) (μ : K) (hpos : 0 < f.maxGenEigenspaceIndex μ) :
    ∃ v ∈ f.maxGenEigenspace μ,
      ((f - μ • 1) ^ (f.maxGenEigenspaceIndex μ - 1)) v ≠ 0 := by
  set e := f.maxGenEigenspaceIndex μ with he
  have hlt := genEigenspace_lt_succ_of_lt_maxGenEigenspaceIndex f μ (k := e - 1) (by omega)
  have hcast : ((e - 1 : ℕ) : ℕ∞) + 1 = ((e : ℕ) : ℕ∞) := by
    have hsub : e - 1 + 1 = e := by omega
    calc ((e - 1 : ℕ) : ℕ∞) + 1 = (((e - 1) + 1 : ℕ) : ℕ∞) := by push_cast; ring
      _ = ((e : ℕ) : ℕ∞) := by rw [hsub]
  rw [hcast] at hlt
  obtain ⟨v, hv_mem, hv_not⟩ := SetLike.exists_of_lt hlt
  refine ⟨v, ?_, ?_⟩
  · rw [maxGenEigenspace_eq]; exact hv_mem
  · rw [genEigenspace_nat, LinearMap.mem_ker] at hv_not
    exact hv_not

/-- **Reverse divisibility, one factor at a time.**

    For *every* scalar `μ` the maximal-generalized-eigenspace power
    `(X - μ)^{e_μ}` divides the minimal polynomial of `f`
    (`e_μ = maxGenEigenspaceIndex f μ`).

    This is the genuine reverse direction of the JCF product formula and the
    previously-documented blocker: it needs the *exactness* of the index, i.e.
    that no smaller exponent kills the whole `μ`-summand.  Notably it requires
    only `FiniteDimensional` — **no algebraic closure** — since it argues one
    eigenvalue at a time.

    Proof.  If `e_μ = 0` it is trivial.  Otherwise write
    `minpoly = (X - μ)^m · g` with `m = rootMultiplicity μ (minpoly)` and
    `(X - μ) ∤ g`.  Since `X - μ` is prime and does not divide `g`, the factors
    `(X - μ)^{e_μ}` and `g` are coprime; Bézout gives `a, b` with
    `a·(X-μ)^{e_μ} + b·g = 1`.  Take the exactness witness `v` with
    `(f-μ)^{e_μ} v = 0` but `(f-μ)^{e_μ-1} v ≠ 0`.  Evaluating Bézout at `v`
    kills the first term and yields `v = b(f)·(g(f) v)`.  Because `minpoly`
    annihilates `f`, `(f-μ)^m (g(f) v) = 0`; as `b(f)` commutes with `(f-μ)^m`
    this forces `(f-μ)^m v = 0`.  Exactness (`(f-μ)^{e_μ-1} v ≠ 0`) then forces
    `e_μ ≤ m`, so `(X-μ)^{e_μ} ∣ (X-μ)^m ∣ minpoly`. -/
theorem pow_maxGenEigenspaceIndex_dvd_minpoly [FiniteDimensional K V]
    (f : Module.End K V) (μ : K) :
    (X - C μ) ^ f.maxGenEigenspaceIndex μ ∣ minpoly K f := by
  set e := f.maxGenEigenspaceIndex μ with he
  rcases Nat.eq_zero_or_pos e with he0 | hpos
  · simp [he0]
  -- `minpoly` factorisation at the root `μ`.
  have hint : IsIntegral K f := Algebra.IsIntegral.isIntegral f
  have hmp0 : minpoly K f ≠ 0 := minpoly.ne_zero hint
  set m := (minpoly K f).rootMultiplicity μ with hm
  obtain ⟨g, hg_eq, hg_not_dvd⟩ :=
    (minpoly K f).exists_eq_pow_rootMultiplicity_mul_and_not_dvd hmp0 μ
  -- `(X - μ)^e` and `g` are coprime: `X - μ` is prime and `∤ g`.
  have hcop : IsCoprime ((X - C μ) ^ e) g :=
    ((prime_X_sub_C μ).coprime_iff_not_dvd.2 hg_not_dvd).pow_left
  -- Exactness witness.
  obtain ⟨v, hv_mem, hv_ne⟩ := exists_mem_maxGenEigenspace_pow_pred_ne_zero f μ hpos
  have hv_e : ((f - μ • 1) ^ e) v = 0 := by
    have hmem : v ∈ f.genEigenspace μ (e : ℕ∞) := by rw [← maxGenEigenspace_eq]; exact hv_mem
    rwa [genEigenspace_nat, LinearMap.mem_ker] at hmem
  -- Bézout, evaluated at `v`: the `(X-μ)^e` term dies, leaving `v = b(f)(g(f) v)`.
  obtain ⟨a, b, hab⟩ := hcop
  have key : (aeval f b) ((aeval f g) v) = v := by
    have h1 : (aeval f a) * (aeval f ((X - C μ) ^ e)) + (aeval f b) * (aeval f g)
        = (1 : Module.End K V) := by
      rw [← map_mul, ← map_mul, ← map_add, hab, map_one]
    have key0 := congrArg (fun T : Module.End K V => T v) h1
    simp only [LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply] at key0
    rwa [aeval_linear_factor_pow, hv_e, map_zero, zero_add] at key0
  -- `minpoly` annihilates `f`, so `(f-μ)^m (g(f) v) = 0`.
  have hmg : ((f - μ • 1) ^ m) ((aeval f g) v) = 0 := by
    have hz : aeval f (minpoly K f) = 0 := minpoly.aeval K f
    rw [hg_eq, map_mul, aeval_linear_factor_pow] at hz
    have := congrArg (fun T : Module.End K V => T v) hz
    simpa [Module.End.mul_apply] using this
  -- `b(f)` commutes with `(f-μ)^m`, so `(f-μ)^m v = b(f)((f-μ)^m (g(f) v)) = 0`.
  have hcomm : Commute ((f - μ • 1) ^ m) (aeval f b) := by
    have : Commute (aeval f ((X - C μ) ^ m)) (aeval f b) :=
      (Commute.all ((X - C μ) ^ m) b).map (aeval f)
    rwa [aeval_linear_factor_pow] at this
  have hmv : ((f - μ • 1) ^ m) v = 0 := by
    calc ((f - μ • 1) ^ m) v
        = ((f - μ • 1) ^ m) ((aeval f b) ((aeval f g) v)) := by rw [key]
      _ = (aeval f b) (((f - μ • 1) ^ m) ((aeval f g) v)) := by
            rw [← Module.End.mul_apply, hcomm.eq, Module.End.mul_apply]
      _ = (aeval f b) 0 := by rw [hmg]
      _ = 0 := map_zero _
  -- Exactness forces `e ≤ m`.
  have hme : e ≤ m := by
    by_contra hlt
    push_neg at hlt
    apply hv_ne
    have hsplit : e - 1 = (e - 1 - m) + m := by omega
    rw [hsplit, pow_add, Module.End.mul_apply, hmv, map_zero]
  calc (X - C μ) ^ e ∣ (X - C μ) ^ m := pow_dvd_pow _ hme
    _ ∣ minpoly K f := pow_rootMultiplicity_dvd _ _

/-- **Reverse divisibility of the JCF product formula.**

    The full eigenvalue product `∏ (X - μ)^{e_μ}` divides `minpoly K f`.
    The single factors are pairwise coprime (distinct `μ`), so divisibility of
    the product follows from divisibility of each factor
    (`pow_maxGenEigenspaceIndex_dvd_minpoly`).  Like the per-factor statement
    this needs only `FiniteDimensional`. -/
theorem prod_pow_maxGenEigenspaceIndex_dvd_minpoly [FiniteDimensional K V]
    (f : Module.End K V) :
    (∏ μ ∈ (finite_hasEigenvalue f).toFinset, (X - C μ) ^ f.maxGenEigenspaceIndex μ)
      ∣ minpoly K f := by
  refine Finset.prod_dvd_of_coprime (fun a _ b _ hab => ?_)
    (fun μ _ => pow_maxGenEigenspaceIndex_dvd_minpoly f μ)
  exact (pairwise_coprime_X_sub_C Function.injective_id hab).pow

/-- **The Jordan-canonical-form minimal-polynomial product formula.**

    Over an algebraically closed field, in finite dimensions,

        `minpoly K f = ∏_{μ eigenvalue} (X - μ)^{maxGenEigenspaceIndex f μ}`.

    This is the exact identity that the parent file (`cayley-hamilton-minpoly-oq-01`)
    only *axiomatized* as `minpoly_product_formula`.  It is obtained here with no
    Jordan-block matrix infrastructure, purely from generalized-eigenspace theory:

      * forward divisibility `minpoly ∣ ∏` from `iSup_maxGenEigenspace_eq_top`
        (`minpoly_dvd_maxGenEigenspace_product`);
      * reverse divisibility `∏ ∣ minpoly` from index exactness
        (`prod_pow_maxGenEigenspaceIndex_dvd_minpoly`);
      * both sides are monic, so the two divisibilities upgrade to equality. -/
theorem minpoly_eq_prod_pow_maxGenEigenspaceIndex [IsAlgClosed K] [FiniteDimensional K V]
    (f : Module.End K V) :
    minpoly K f
      = ∏ μ ∈ (finite_hasEigenvalue f).toFinset, (X - C μ) ^ f.maxGenEigenspaceIndex μ := by
  have hint : IsIntegral K f := Algebra.IsIntegral.isIntegral f
  refine eq_of_monic_of_associated (minpoly.monic hint)
    (monic_prod_of_monic _ _ (fun μ _ => (monic_X_sub_C μ).pow _)) ?_
  exact associated_of_dvd_dvd
    (minpoly_dvd_maxGenEigenspace_product f)
    (prod_pow_maxGenEigenspaceIndex_dvd_minpoly f)

end JordanMinpolyOQ01OQ01
