import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Tactic
import Proofs.MinpolyCharpolyOQ03
import Proofs.RationalCanonicalFormExists

/-
# OQ-03-OQ-01 (S1 Scaffold): F[X]-Module Structure on K^n via Matrix Action

## Parent open question

This file is the **first sub-OQ** of `minpoly-charpoly-oq-03` (rational
canonical form, see `Proofs/MinpolyCharpolyOQ03.lean`), which decomposed
its existence proof into four sub-OQs:

| Sub-OQ | Content | Estimated lines |
|--------|---------|-----------------|
| **OQ-03-OQ-01** | F[X]-module structure on K^n via M; finitely generated + torsion. | ~150 |
| OQ-03-OQ-02 | Apply `Module.equiv_directSum_of_isTorsion` for the chain decomposition. | ~300 |
| OQ-03-OQ-03 | Cyclic-summand ↔ companion-block correspondence. | ~250 |
| OQ-03-OQ-04 | Global assembly of the similarity transform. | ~200 |

This file delivers **OQ-03-OQ-01**: the foundational ground on which the
remaining three sub-OQs are built.

## What this file does

For a square matrix `M : Matrix n n F` over a field `F`, we package `K^n`
(i.e., `n → F`) as an `F[X]`-module in which the indeterminate `X` acts
as `M`. Concretely, we use Mathlib's existing `Module.AEval'` synonym
applied to `M.mulVecLin`, the linear endomorphism induced by `M`:

```
xModule M := Module.AEval' (M.mulVecLin : (n → F) →ₗ[F] (n → F))
```

We then state and (where tractable) prove two structural properties
that OQ-03-OQ-02 will consume:

1. **Finite generation over F[X]** — inherited automatically from the
   `F`-finite-dimensionality of `K^n` via Mathlib's instance
   `Module.AEval.instFinitePolynomial`. No work required.
2. **Torsion over F[X]** — every element is annihilated by `charpoly M`,
   which is monic (hence nonzero in `F[X]`). This is the Cayley–Hamilton
   contribution.

## Current scope (deliberate boundary)

Both structural deliverables consumed by OQ-03-OQ-02 are now **proved**:

* `Module.Finite F[X] (xModule M)` — provided unconditionally (no sorry)
  via `Module.AEval.instFinitePolynomial`.
* `xModule_isTorsionBy_charpoly` and `xModule_isTorsion` — proved
  (Cayley–Hamilton on the `Module.AEval'` synonym, routed through
  `charpoly_mulVecLin` + `LinearMap.aeval_self_charpoly`, then upgraded
  to torsion via `charpoly_monic ⇒ nonZeroDivisor`).

The invariant-factor-chain bridge `xModule_has_invariantFactorChain` (to
the parent's strong form) is now **fully discharged** — no `sorry`. The
heavy regrouping algorithm (`Module.equiv_directSum_of_isTorsion` →
primary decomposition → prime-power regrouping into a divisibility chain)
lives in the companion file `Proofs/RationalCanonicalFormExists.lean` as
the axiom-free theorem `rational_canonical_form_exists`; the bridge here
is a one-line field copy between the two field-identical
`InvariantFactorChain` structures.

Note: this file is now **build-verified sorry-free** (researcher-1, S15:
`docker-build.sh Proofs.MinpolyCharpolyOQ03OQ01`, 7746 jobs, 0 sorry in
this file and its companion; the lone `sorry` warning in the build is the
unrelated parent `Proofs/MinpolyCharpolyOQ03.lean:228`). The torsion
proofs were previously build-verified (researcher-7, S13: 3070 jobs). An
earlier revision was build-broken: it
relied on `LinearMap.charpoly`/`aeval_self_charpoly` and
`charpoly_mulVecLin` without importing `Mathlib.LinearAlgebra.Charpoly.{Basic,ToMatrix}`,
and tried to feed the strict-implicit `IsTorsionBy` proof directly into
the `IsTorsion` existential. Both are now fixed.

## References

* `Mathlib.Algebra.Polynomial.Module.AEval` — the AEval'-as-F[X]-module
  construction, with `instFinitePolynomial` automatically lifting
  R-finiteness to R[X]-finiteness.
* `Mathlib.Algebra.Module.Torsion.Basic` — definitions of
  `Module.IsTorsion`, `Module.IsTorsionBy`, `isTorsionBy_iff_mem_annihilator`.
* `Mathlib.LinearAlgebra.Matrix.Charpoly.Basic` — `Matrix.charpoly`,
  `Matrix.aeval_self_charpoly` (Cayley–Hamilton).
* `Mathlib.LinearAlgebra.Charpoly.Basic` — `LinearMap.charpoly`,
  `LinearMap.aeval_self_charpoly`.
* `Proofs.MinpolyCharpolyOQ03` — parent sub-OQ scaffold defining the
  `InvariantFactorChain` data structure consumed by OQ-03-OQ-02+.

Tags: linear-algebra, matrices, polynomial-module, AEval,
finitely-generated-modules, torsion-modules, cayley-hamilton,
structure-theorem-pid, rational-canonical-form
-/

namespace MinpolyCharpolyOQ03OQ01

open Matrix Polynomial Module

variable {F : Type*} [Field F]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Part 1: The F[X]-module structure on K^n via M

Given a matrix `M : Matrix n n F`, we promote `n → F` to an `F[X]`-module
in which the action of the indeterminate `X` is the linear map induced
by `M`. The standard Mathlib idiom is `Module.AEval'` applied to the
endomorphism `M.mulVecLin`. -/

/-- The F-linear endomorphism of `K^n = (n → F)` induced by a matrix `M`.
    This is just `M.mulVecLin`, given a stable name for use throughout
    this development. -/
def endo (M : Matrix n n F) : (n → F) →ₗ[F] (n → F) := M.mulVecLin

/-- **The F[X]-module structure on K^n via the matrix M.**

    `xModule M` is `n → F` viewed as an `F[X]`-module, where the
    indeterminate `X` acts as the linear endomorphism `M.mulVecLin`.
    Polynomial action is given by `p • v = (aeval (endo M) p) v`.

    This is the foundational `F[X]`-module to which OQ-03-OQ-02 will
    apply the PID structure theorem `Module.equiv_directSum_of_isTorsion`. -/
abbrev xModule (M : Matrix n n F) := Module.AEval' (endo M)

/-- Canonical equivalence `(n → F) ≃ₗ[F] xModule M` as F-modules (the
    underlying types are definitionally equal; this is `Module.AEval'.of`
    specialised to our setting). -/
noncomputable def xModule.of (M : Matrix n n F) :
    (n → F) ≃ₗ[F] xModule M := Module.AEval'.of (endo M)

/-! ## Part 2: Finite generation over F[X] (unconditional)

`Module.Finite F (n → F)` is automatic from `Fintype n` + `Field F`.
Mathlib then upgrades this to `Module.Finite F[X]` via the instance
`Module.AEval.instFinitePolynomial`. We expose this as a named
instance for downstream use. -/

instance xModule.instFinite (M : Matrix n n F) :
    Module.Finite F[X] (xModule M) := inferInstance

/-! ## Part 3: Torsion over F[X] (proved)

The F[X]-module `xModule M` is torsion: every element is annihilated
by `charpoly M`, which is monic (hence nonzero in F[X] as F is a
field). This is the Cayley–Hamilton contribution.

The proof routes through:
1. `Matrix.aeval_self_charpoly`: `aeval M M.charpoly = 0` (as a matrix).
2. The basis-induced algebra equivalence
   `Matrix n n F ≃ₐ[F] ((n → F) →ₗ[F] (n → F))` (via `Matrix.toLin'` /
   `Pi.basisFun`).
3. Naturality: `aeval` commutes with algebra homomorphisms, so
   `aeval (endo M) M.charpoly = 0` as a LinearMap, hence as smul.
4. Lift `IsTorsionBy F[X] (xModule M) M.charpoly` to `IsTorsion` via
   monic ⇒ nonzero ⇒ nonZeroDivisor.

The lemma `xModule_isTorsionBy_charpoly` captures steps 1–3;
`xModule_isTorsion` is the deliverable consumed by OQ-03-OQ-02. Both
are proved and build-verified. -/

/-- The characteristic polynomial of `M` annihilates every element of
    the `F[X]`-module `xModule M`. This is Cayley–Hamilton transported
    to the `Module.AEval'` synonym.

    Proof: route through `Matrix.charpoly_mulVecLin` (identifying
    `(endo M).charpoly = M.charpoly`) and `LinearMap.aeval_self_charpoly`
    (the LinearMap-side Cayley–Hamilton). The `Module.AEval.of_symm_smul`
    `rfl` lemma collapses the smul-tower in one rewrite. See S7 PREP
    `sessions/2026-05-12-s07-prep-oq03-oq01-s2-isTorsionBy-discharge.md`
    for the API audit and alternate routes. -/
theorem xModule_isTorsionBy_charpoly (M : Matrix n n F) :
    Module.IsTorsionBy F[X] (xModule M) M.charpoly := by
  -- Cayley–Hamilton on the endomorphism, transported to `M.charpoly` via
  -- `charpoly_mulVecLin` (note `endo` is a `def`, so it needs unfolding to
  -- expose `M.mulVecLin` for the rewrite).
  have hk : aeval (endo M) M.charpoly = 0 := by
    have h1 : (endo M).charpoly = M.charpoly := by
      unfold endo; exact charpoly_mulVecLin M
    rw [← h1]; exact LinearMap.aeval_self_charpoly (endo M)
  intro x
  obtain ⟨m, rfl⟩ := (Module.AEval'.of (endo M)).surjective x
  rw [← Module.AEval.of_aeval_smul, hk, zero_smul, map_zero]

/-- **The F[X]-module `xModule M` is torsion.**

    Every element is annihilated by `M.charpoly`, which is monic and
    therefore a non-zero-divisor in `F[X]` (an integral domain).
    Combined with `xModule.instFinite`, this satisfies the hypothesis
    of Mathlib's PID structure theorem
    `Module.equiv_directSum_of_isTorsion`, which OQ-03-OQ-02 will apply
    to extract the invariant-factor decomposition. -/
theorem xModule_isTorsion (M : Matrix n n F) :
    Module.IsTorsion F[X] (xModule M) := by
  have hne : M.charpoly ≠ 0 := (charpoly_monic M).ne_zero
  have hnzd : M.charpoly ∈ nonZeroDivisors F[X] :=
    mem_nonZeroDivisors_of_ne_zero hne
  have hk : aeval (endo M) M.charpoly = 0 := by
    have h1 : (endo M).charpoly = M.charpoly := by
      unfold endo; exact charpoly_mulVecLin M
    rw [← h1]; exact LinearMap.aeval_self_charpoly (endo M)
  intro x
  -- The `F[X]⁰`-element `⟨M.charpoly, hnzd⟩` annihilates `x`; its submonoid
  -- smul reduces definitionally to the `F[X]`-smul, so `show` recovers the
  -- plain Cayley–Hamilton computation.
  refine ⟨⟨M.charpoly, hnzd⟩, ?_⟩
  obtain ⟨m, rfl⟩ := (Module.AEval'.of (endo M)).surjective x
  show (M.charpoly : F[X]) • (Module.AEval'.of (endo M) m) = 0
  rw [← Module.AEval.of_aeval_smul, hk, zero_smul, map_zero]

/-! ## Part 4: Deliverable surface for OQ-03-OQ-02 (statement only)

OQ-03-OQ-02 will combine `xModule.instFinite` and `xModule_isTorsion`
with Mathlib's `Module.equiv_directSum_of_isTorsion` to obtain a direct
sum decomposition of `xModule M` into cyclic F[X]-summands
`F[X] / (pᵢ)` with divisibility chain `p₁ ∣ p₂ ∣ ⋯ ∣ pₖ`. We state
the deliverable here so its API surface is fixed by this sub-OQ.

The chain is packaged as the parent's `InvariantFactorChain` structure
(see `Proofs/MinpolyCharpolyOQ03.lean`). -/

/-- **OQ-03-OQ-02 target (now fully proved)**:
    `xModule M` admits an invariant-factor chain whose product equals
    `M.charpoly` **and** whose last factor equals `minpoly F M`. This is
    a restatement of the parent's `rational_canonical_form_exists`
    consuming the F[X]-module constructed in this file. The two are
    mutually-derivable; the benefit of stating both is to fix the
    bridging surface between this sub-OQ and the parent.

    *Faithfulness note (S14-alignment).* The `lastFactor = minpoly`
    conjunct is **not** optional padding: without it the existential is
    vacuously satisfiable by a degenerate chain (`factors = [M.charpoly]`
    for nonempty `n`, or the empty chain for the `0 × 0` case), which
    would make the bridge strictly weaker than the parent's S14
    strong-form `rational_canonical_form_exists`. Adding `c.lastFactor =
    minpoly F M` forces the genuine invariant-factor decomposition
    (`minpoly = charpoly` holds only for non-derogatory `M`), restoring
    the claimed mutual-derivability with the parent. The proof is
    discharged by the companion `rational_canonical_form_exists`. -/
theorem xModule_has_invariantFactorChain (M : Matrix n n F) :
    ∃ c : MinpolyCharpolyOQ03.InvariantFactorChain F,
      c.prodFactors = M.charpoly ∧ c.lastFactor = minpoly F M := by
  -- Discharged by `RationalCanonicalFormExists.rational_canonical_form_exists`
  -- (the strong-form RCF existence theorem, proved axiom-free in the companion
  -- file). Its `InvariantFactorChain` is field-identical to the parent's, so we
  -- copy the four fields across; `prodFactors`/`lastFactor` are definitionally
  -- `factors.prod` / `factors.getLast?.getD 1` on both, hence the equalities
  -- transport unchanged.
  obtain ⟨c, hprod, hlast⟩ := RationalCanonicalFormExists.rational_canonical_form_exists M
  exact ⟨⟨c.factors, c.monic, c.posDegree, c.chain⟩, hprod, hlast⟩

end MinpolyCharpolyOQ03OQ01
