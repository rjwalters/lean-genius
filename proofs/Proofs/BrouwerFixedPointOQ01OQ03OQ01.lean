import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic
import Proofs.BorsukUlam
import Proofs.BrouwerFixedPoint
import Proofs.BrouwerFixedPointOQ01OQ03

/-
# De-Axiomatizing the Ham Sandwich Theorem
# (brouwer-fixed-point-oq-01-oq-03-oq-01)

## The Open Question

**OQ-01-OQ-03-OQ-01**: The parent entry OQ-01-OQ-03 derived the n-dimensional
Borsuk–Ulam theorem and stated the **Ham Sandwich Theorem** as an *axiom*
(`ham_sandwich_theorem`), with the honest note that the obstruction to a real
proof is the *continuity of the bisecting-measure function* for parameterized
half-spaces. This sub-question asks: **how much of that axiom is actually
topological (hence already available from Borsuk–Ulam), and how much is the
genuine analytic input?**

## Result

We separate the two. The *topological core* — that a continuous odd discrepancy
map on the sphere has a zero, and that this zero is exactly a simultaneous
bisection — is proved here outright from the already-established
`borsuk_ulam_antipodal_collapse`. The *only* remaining input is the analytic
fact that the half-volume discrepancy map is **continuous**; everything else
(oddness, and "discrepancy zero ⇒ equal volumes") is proved.

Concretely:

1. `ham_sandwich_reduction` — the abstract reduction: a continuous odd
   `F : Sⁿ → ℝⁿ` together with a bridge "`F x = 0 ⇒ x bisects` " yields a
   bisecting point. Proved from `borsuk_ulam_antipodal_collapse`. No axiom.

2. `discrepancy_odd_of_swap` — the half-volume discrepancy is **odd** purely
   from the antipodal swap `pos(-x) = neg(x)` of the two half-spaces. This is
   the elementary measure-theoretic half of the construction; it needs no
   continuity. Proved.

3. `ham_sandwich_of_discrepancy` — the capstone: given the discrepancy map
   *as a continuous `SphereFun`* (the one analytic hypothesis), the antipodal
   swap, and finiteness of the volumes, there is a hyperplane that
   simultaneously bisects all `n` bodies. Proved from (1)+(2).

The standing `ham_sandwich_theorem` axiom in `BrouwerFixedPointOQ01OQ03.lean`
is therefore reduced to the single statement "the half-volume discrepancy map
is continuous on Sⁿ", which is the genuine Lebesgue-continuity input.

## Summary: 0 sorries, 0 new axioms.
Depends on `BorsukUlam.lean` (1 axiom: `no_continuous_odd_nonzero_on_sphere`).
-/

set_option linter.unusedVariables false

namespace BrouwerFixedPointOQ01OQ03OQ01

open BorsukUlam BrouwerFixedPointOQ01OQ03 MeasureTheory

-- ============================================================
-- PART 1: The abstract topological reduction
-- ============================================================

/-- **Ham Sandwich Reduction (topological core).**

    Let `F : Sⁿ → ℝⁿ` be continuous and odd (`F(-x) = -F(x)`), and let
    `Bisected` be any predicate on points such that `F x = 0` forces
    `Bisected x`. Then some point of `Sⁿ` satisfies `Bisected`.

    This is the entire topological content of the Ham Sandwich theorem,
    obtained directly from `borsuk_ulam_antipodal_collapse`: the odd map `F`
    must vanish somewhere on the sphere, and a vanishing point is a bisection. -/
theorem ham_sandwich_reduction (n : ℕ) (hn : n ≥ 1) (F : SphereFun n)
    (hodd : ∀ x, F.toFun (-x) = -F.toFun x)
    (Bisected : EuclideanSpace ℝ (Fin (n + 1)) → Prop)
    (hbridge : ∀ x ∈ Sphere n, F.toFun x = 0 → Bisected x) :
    ∃ x ∈ Sphere n, Bisected x := by
  obtain ⟨x, hx, hFx⟩ := borsuk_ulam_antipodal_collapse n hn F hodd
  exact ⟨x, hx, hbridge x hx hFx⟩

-- ============================================================
-- PART 2: The half-volume discrepancy is odd
-- ============================================================

/-- The signed half-volume discrepancy for `n` bodies, as a real vector
    indexed by the bodies:
    `Dᵢ(x) = vol(bodyᵢ ∩ pos x i) − vol(bodyᵢ ∩ neg x i)`.

    Here `pos x i`, `neg x i` are the two open half-spaces cut out of body `i`
    by the oriented hyperplane indexed by the direction-point `x ∈ Sⁿ`. -/
noncomputable def discrepancy (n : ℕ)
    (bodies : Fin n → Set (EuclideanSpace ℝ (Fin n)))
    (pos neg : EuclideanSpace ℝ (Fin (n + 1)) → Fin n → Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin n) : ℝ :=
  (volume (bodies i ∩ pos x i)).toReal - (volume (bodies i ∩ neg x i)).toReal

/-- **Oddness of the discrepancy.** Reversing the orientation of the cutting
    hyperplane (`x ↦ -x`) swaps the two half-spaces (`pos(-x) = neg(x)` and
    `neg(-x) = pos(x)`), hence negates every component of the discrepancy.

    This is the elementary half of the Ham Sandwich construction: it is purely
    set-theoretic / measure-additive and requires **no** continuity. -/
theorem discrepancy_odd_of_swap (n : ℕ)
    (bodies : Fin n → Set (EuclideanSpace ℝ (Fin n)))
    (pos neg : EuclideanSpace ℝ (Fin (n + 1)) → Fin n → Set (EuclideanSpace ℝ (Fin n)))
    (hswap : ∀ x i, pos (-x) i = neg x i)
    (hswap' : ∀ x i, neg (-x) i = pos x i)
    (x : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin n) :
    discrepancy n bodies pos neg (-x) i = -discrepancy n bodies pos neg x i := by
  unfold discrepancy
  rw [hswap x i, hswap' x i]
  ring

-- ============================================================
-- PART 3: Capstone — Ham Sandwich, conditional only on continuity
-- ============================================================

/-- **Ham Sandwich Theorem from Borsuk–Ulam (continuity isolated).**

    Suppose we are given `n` bodies in `ℝⁿ`, the two half-space assignments
    `pos`, `neg`, and the discrepancy map packaged as a *continuous* `SphereFun`
    `F` whose `i`-th component is `discrepancy … x i` (hypothesis `hcomp`).
    Assume the antipodal swap of half-spaces and that all the relevant volumes
    are finite. Then there is a direction-point `x ∈ Sⁿ` whose oriented
    hyperplane **simultaneously bisects every body**:
    `vol(bodyᵢ ∩ pos x i) = vol(bodyᵢ ∩ neg x i)` for all `i`.

    The *only* analytic hypothesis is the continuity of `F` (baked into
    `SphereFun`). Everything else — oddness and "zero discrepancy ⇒ equal
    volumes" — is proved. This reduces the opaque `ham_sandwich_theorem` axiom
    of the parent file to the single Lebesgue-continuity input. -/
theorem ham_sandwich_of_discrepancy (n : ℕ) (hn : n ≥ 1)
    (bodies : Fin n → Set (EuclideanSpace ℝ (Fin n)))
    (pos neg : EuclideanSpace ℝ (Fin (n + 1)) → Fin n → Set (EuclideanSpace ℝ (Fin n)))
    (F : SphereFun n)
    (hswap : ∀ x i, pos (-x) i = neg x i)
    (hswap' : ∀ x i, neg (-x) i = pos x i)
    (hfin_pos : ∀ x i, volume (bodies i ∩ pos x i) ≠ ⊤)
    (hfin_neg : ∀ x i, volume (bodies i ∩ neg x i) ≠ ⊤)
    (hcomp : ∀ x i, F.toFun x i = discrepancy n bodies pos neg x i) :
    ∃ x ∈ Sphere n, ∀ i, volume (bodies i ∩ pos x i) = volume (bodies i ∩ neg x i) := by
  -- F is odd because the discrepancy is odd.
  have hodd : ∀ x, F.toFun (-x) = -F.toFun x := by
    intro x
    have key : WithLp.ofLp (F.toFun (-x)) = WithLp.ofLp (-F.toFun x) := by
      funext i
      show (F.toFun (-x)).ofLp i = (-F.toFun x).ofLp i
      rw [hcomp (-x) i, discrepancy_odd_of_swap n bodies pos neg hswap hswap' x i,
        ← hcomp x i]
      simp
    exact WithLp.ofLp_injective _ key
  -- Apply the reduction with the genuine bisection predicate.
  refine ham_sandwich_reduction n hn F hodd
    (fun x => ∀ i, volume (bodies i ∩ pos x i) = volume (bodies i ∩ neg x i))
    ?_
  intro x hx hFx i
  -- F x = 0 means every discrepancy component vanishes.
  have hzero : discrepancy n bodies pos neg x i = 0 := by
    rw [← hcomp x i, hFx]; simp
  -- A zero discrepancy with finite volumes forces equal volumes.
  have hsub : (volume (bodies i ∩ pos x i)).toReal
      = (volume (bodies i ∩ neg x i)).toReal := by
    unfold discrepancy at hzero
    linarith [hzero]
  exact (ENNReal.toReal_eq_toReal_iff' (hfin_pos x i) (hfin_neg x i)).mp hsub

/-
## Significance and the Remaining Gap

The parent file `BrouwerFixedPointOQ01OQ03.lean` carries `ham_sandwich_theorem`
as an axiom, justified by: *"the continuity of the bisecting-measure function
… is beyond the current proof scope."* This file confirms that diagnosis is
exact: with that one continuity fact in hand (as the `SphereFun` packaging of
the discrepancy map), the Ham Sandwich conclusion is fully **proved**, not
axiomatized. The oddness and the "zero ⇒ bisected" steps, which one might worry
also hide content, are dispatched here by elementary means.

Remaining analytic work to fully retire the axiom:
  * show `x ↦ vol(bodyᵢ ∩ {y | ⟨u(x), y⟩ < t(x)})` is continuous on `Sⁿ`
    (Lebesgue continuity of parameterized half-spaces; dominated convergence),
  * verify the antipodal swap `pos(-x) = neg(x)` for the standard
    direction/threshold parameterization,
  * establish finiteness `vol(bodyᵢ) < ⊤` (bounded bodies).
Each is a self-contained measure-theory lemma; none is topological.
-/

end BrouwerFixedPointOQ01OQ03OQ01
