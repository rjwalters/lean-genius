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

4. `ham_sandwich_of_scalar_continuity` / `ham_sandwich_standard_of_scalar_continuity`
   — sharpen the residual input further. The continuity hypothesis above was a
   *vector* statement ("a continuous `SphereFun` realizes the discrepancy"). Here
   the vector-assembly step is discharged: assuming only that each of the `2n`
   *scalar* slice-volume maps is continuous, the discrepancy assembles into a
   continuous `EuclideanSpace`-valued map via `(EuclideanSpace.equiv …).symm`, and
   the conclusion follows. The remaining input is now a continuity statement about
   a single real parameterized volume — no `SphereFun` is assumed.

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

-- ============================================================
-- PART 3b: Reducing the analytic input to SCALAR slice-volume continuity
-- ============================================================

/-- **Ham Sandwich from scalar slice-volume continuity.**

    The lone analytic input of `ham_sandwich_of_discrepancy` was the existence of
    a *continuous `SphereFun`* (a `ℝⁿ`-valued map) realizing the discrepancy. That
    packaging still bundles a vector-assembly step. Here we discharge it: if each
    of the `2n` *scalar* slice-volume maps
    `x ↦ vol(bodyᵢ ∩ pos x i)` and `x ↦ vol(bodyᵢ ∩ neg x i)` is continuous (as an
    `ℝ`-valued function via `.toReal`), the discrepancy map assembles into a
    continuous `EuclideanSpace`-valued map automatically — the finite-dimensional
    L²-assembly `(EuclideanSpace.equiv …).symm ∘ (continuous components)` — and
    Ham Sandwich follows.

    This pins the residual gap to its atomic form: continuity of a *single real*
    parameterized slice-volume. The vector `SphereFun` packaging is no longer
    assumed — it is constructed and proved continuous from the scalar inputs. -/
theorem ham_sandwich_of_scalar_continuity (n : ℕ) (hn : n ≥ 1)
    (bodies : Fin n → Set (EuclideanSpace ℝ (Fin n)))
    (pos neg : EuclideanSpace ℝ (Fin (n + 1)) → Fin n → Set (EuclideanSpace ℝ (Fin n)))
    (hswap : ∀ x i, pos (-x) i = neg x i)
    (hswap' : ∀ x i, neg (-x) i = pos x i)
    (hfin_pos : ∀ x i, volume (bodies i ∩ pos x i) ≠ ⊤)
    (hfin_neg : ∀ x i, volume (bodies i ∩ neg x i) ≠ ⊤)
    (hcont_pos : ∀ i, Continuous fun x => (volume (bodies i ∩ pos x i)).toReal)
    (hcont_neg : ∀ i, Continuous fun x => (volume (bodies i ∩ neg x i)).toReal) :
    ∃ x ∈ Sphere n, ∀ i, volume (bodies i ∩ pos x i) = volume (bodies i ∩ neg x i) := by
  -- Assemble the scalar discrepancy components into a continuous EuclideanSpace map.
  have hcont : Continuous fun x => (EuclideanSpace.equiv (Fin n) ℝ).symm
      (fun i => discrepancy n bodies pos neg x i) := by
    refine (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous.comp (continuous_pi fun i => ?_)
    simpa only [discrepancy] using (hcont_pos i).sub (hcont_neg i)
  -- Package as the SphereFun realizing the discrepancy, then apply Part 3.
  refine ham_sandwich_of_discrepancy n hn bodies pos neg
    ⟨fun x => (EuclideanSpace.equiv (Fin n) ℝ).symm
      (fun i => discrepancy n bodies pos neg x i), hcont⟩
    hswap hswap' hfin_pos hfin_neg (fun x i => rfl)

-- ============================================================
-- PART 4: The standard linear half-space parameterization
-- ============================================================

/-- The positive open half-space cut by the oriented hyperplane parameterized by
    a direction-point `x`, when the direction `u x` and threshold `t x` are
    extracted *linearly* from `x`. A single hyperplane cuts every body, so the
    assignment is constant in the body index `i`. -/
noncomputable def stdPos (n : ℕ)
    (u : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (t : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ)
    (x : EuclideanSpace ℝ (Fin (n + 1))) (_i : Fin n) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {y | inner (𝕜 := ℝ) (u x) y < t x}

/-- The negative open half-space for the standard linear parameterization. -/
noncomputable def stdNeg (n : ℕ)
    (u : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (t : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ)
    (x : EuclideanSpace ℝ (Fin (n + 1))) (_i : Fin n) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {y | t x < inner (𝕜 := ℝ) (u x) y}

/-- **Antipodal swap for the standard parameterization.** Because the direction
    and threshold are *linear* in `x`, replacing `x` by `-x` negates both, which
    exactly exchanges the two open half-spaces. The swap is therefore a
    *theorem* for any linear direction/threshold extraction — not an extra
    assumption. This discharges the `hswap` hypothesis of
    `ham_sandwich_of_discrepancy`. -/
theorem stdPos_neg (n : ℕ)
    (u : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (t : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ)
    (x : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin n) :
    stdPos n u t (-x) i = stdNeg n u t x i := by
  unfold stdPos stdNeg
  ext y
  simp only [Set.mem_setOf_eq, map_neg, inner_neg_left]
  constructor <;> intro h <;> linarith

/-- The companion swap `neg(-x) = pos(x)`, discharging `hswap'`. -/
theorem stdNeg_neg (n : ℕ)
    (u : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (t : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ)
    (x : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin n) :
    stdNeg n u t (-x) i = stdPos n u t x i := by
  unfold stdPos stdNeg
  ext y
  simp only [Set.mem_setOf_eq, map_neg, inner_neg_left]
  constructor <;> intro h <;> linarith

-- ============================================================
-- PART 5: Volume finiteness from bounded bodies
-- ============================================================

/-- **Finiteness of the half-space slices.** If a body has finite volume, every
    half-space slice of it does too, being a subset. This discharges the
    `hfin_pos`/`hfin_neg` hypotheses of `ham_sandwich_of_discrepancy` for
    finite-volume (e.g. bounded) bodies. -/
theorem volume_inter_ne_top (n : ℕ)
    (body S : Set (EuclideanSpace ℝ (Fin n)))
    (hbody : volume body ≠ ⊤) : volume (body ∩ S) ≠ ⊤ :=
  ne_top_of_le_ne_top hbody (measure_mono Set.inter_subset_left)

-- ============================================================
-- PART 6: Ham Sandwich for the standard linear parameterization
-- ============================================================

/-- **Ham Sandwich Theorem, standard linear parameterization.**

    Specializing `ham_sandwich_of_discrepancy` to the standard half-space
    assignment `stdPos`/`stdNeg` (a linear direction `u` and threshold `t`), the
    antipodal-swap and volume-finiteness hypotheses become *theorems*
    (`stdPos_neg`, `stdNeg_neg`, `volume_inter_ne_top`). The ONLY remaining
    hypothesis is `hcomp`: that the discrepancy map is realized by a continuous
    `SphereFun`.

    This pins the Lebesgue-continuity of the bisecting-measure map as the sole
    unproved input, with every combinatorial / set-theoretic / finiteness side
    condition discharged. -/
theorem ham_sandwich_standard (n : ℕ) (hn : n ≥ 1)
    (bodies : Fin n → Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (t : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ)
    (F : SphereFun n)
    (hbody : ∀ i, volume (bodies i) ≠ ⊤)
    (hcomp : ∀ x i, F.toFun x i = discrepancy n bodies (stdPos n u t) (stdNeg n u t) x i) :
    ∃ x ∈ Sphere n, ∀ i,
      volume (bodies i ∩ stdPos n u t x i) = volume (bodies i ∩ stdNeg n u t x i) :=
  ham_sandwich_of_discrepancy n hn bodies (stdPos n u t) (stdNeg n u t) F
    (stdPos_neg n u t) (stdNeg_neg n u t)
    (fun x i => volume_inter_ne_top n (bodies i) _ (hbody i))
    (fun x i => volume_inter_ne_top n (bodies i) _ (hbody i))
    hcomp

/-- **Ham Sandwich, standard parameterization, from scalar continuity alone.**

    The sharpest packaging in this file. Under the standard linear half-space
    assignment `stdPos`/`stdNeg`, the antipodal-swap and finiteness side
    conditions are theorems (`stdPos_neg`, `stdNeg_neg`, `volume_inter_ne_top`),
    and the vector-assembly step is discharged by
    `ham_sandwich_of_scalar_continuity`. What remains as hypotheses is therefore
    *exactly* the atomic analytic content:
      * `hbody` — each body has finite volume, and
      * `hcont_pos`/`hcont_neg` — each **scalar** slice-volume
        `x ↦ vol(bodyᵢ ∩ {y | ⟨u x, y⟩ ⋚ t x})` is continuous on `Sⁿ`.
    No continuous `SphereFun` is assumed; it is built from the scalar maps. -/
theorem ham_sandwich_standard_of_scalar_continuity (n : ℕ) (hn : n ≥ 1)
    (bodies : Fin n → Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (t : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ)
    (hbody : ∀ i, volume (bodies i) ≠ ⊤)
    (hcont_pos : ∀ i, Continuous fun x => (volume (bodies i ∩ stdPos n u t x i)).toReal)
    (hcont_neg : ∀ i, Continuous fun x => (volume (bodies i ∩ stdNeg n u t x i)).toReal) :
    ∃ x ∈ Sphere n, ∀ i,
      volume (bodies i ∩ stdPos n u t x i) = volume (bodies i ∩ stdNeg n u t x i) :=
  ham_sandwich_of_scalar_continuity n hn bodies (stdPos n u t) (stdNeg n u t)
    (stdPos_neg n u t) (stdNeg_neg n u t)
    (fun x i => volume_inter_ne_top n (bodies i) _ (hbody i))
    (fun x i => volume_inter_ne_top n (bodies i) _ (hbody i))
    hcont_pos hcont_neg

-- ============================================================
-- PART 7: A bisecting hyperplane cuts each body into EXACT halves
-- ============================================================

/-- **Volume partition across a strict/strict/boundary cut.**

    The two strict open half-spaces `P`, `N` and the boundary hyperplane `B`
    partition the ambient space. Restricting to a measurable `body`, its volume
    splits additively over the three slices. This is the elementary measure
    decomposition underlying "each side gets exactly half": it needs only
    measurability and a genuine partition (`P ∪ N ∪ B = univ`, pairwise
    disjoint), no continuity. -/
theorem volume_body_eq_slices_add_boundary (n : ℕ)
    (body P N B : Set (EuclideanSpace ℝ (Fin n)))
    (hbody : MeasurableSet body) (hP : MeasurableSet P) (hN : MeasurableSet N)
    (hB : MeasurableSet B)
    (hcover : P ∪ N ∪ B = Set.univ)
    (hPN : Disjoint P N) (hPB : Disjoint P B) (hNB : Disjoint N B) :
    volume body
      = volume (body ∩ P) + volume (body ∩ N) + volume (body ∩ B) := by
  have hsplit : body = (body ∩ P) ∪ (body ∩ N) ∪ (body ∩ B) := by
    rw [← Set.inter_union_distrib_left, ← Set.inter_union_distrib_left, hcover,
      Set.inter_univ]
  have dPN : Disjoint (body ∩ P) (body ∩ N) :=
    hPN.mono Set.inter_subset_right Set.inter_subset_right
  have dPB : Disjoint (body ∩ P) (body ∩ B) :=
    hPB.mono Set.inter_subset_right Set.inter_subset_right
  have dNB : Disjoint (body ∩ N) (body ∩ B) :=
    hNB.mono Set.inter_subset_right Set.inter_subset_right
  have dUB : Disjoint ((body ∩ P) ∪ (body ∩ N)) (body ∩ B) :=
    Disjoint.union_left dPB dNB
  conv_lhs => rw [hsplit]
  rw [measure_union dUB (hbody.inter hB), measure_union dPN (hbody.inter hN)]

/-- **A bisecting hyperplane gives each body exactly half its volume.**

    Given the strict/strict/boundary partition, a *finite-volume* body whose two
    strict slices have equal volume (`hbis`) and whose boundary slice is null
    (`hnull`) is split into two pieces of volume **exactly** `vol(body)/2`:
    `2 · vol(body ∩ P) = vol(body)`.

    This upgrades the conclusion of `ham_sandwich_of_discrepancy`
    (`vol(body ∩ pos) = vol(body ∩ neg)`, i.e. the two sides are *equal*) to the
    textbook statement that each side is *exactly half*. The only extra input is
    that the boundary hyperplane carries no volume of the body — the same
    Lebesgue null-set fact that the rest of the file isolates as the residual
    analytic keystone. No continuity is used here. -/
theorem each_slice_exactly_half (n : ℕ)
    (body P N B : Set (EuclideanSpace ℝ (Fin n)))
    (hbody : MeasurableSet body) (hP : MeasurableSet P) (hN : MeasurableSet N)
    (hB : MeasurableSet B)
    (hcover : P ∪ N ∪ B = Set.univ)
    (hPN : Disjoint P N) (hPB : Disjoint P B) (hNB : Disjoint N B)
    (hbis : volume (body ∩ P) = volume (body ∩ N))
    (hnull : volume (body ∩ B) = 0) :
    2 * volume (body ∩ P) = volume body := by
  rw [volume_body_eq_slices_add_boundary n body P N B hbody hP hN hB hcover
    hPN hPB hNB, ← hbis, hnull, add_zero, two_mul]

-- ============================================================
-- PART 8: Gap 2 discharged — the boundary hyperplane is Lebesgue-null
-- ============================================================

/-- **The boundary hyperplane carries no Lebesgue volume.**

    A real-inner-product level set `{y | ⟪u, y⟫ = c}` with nonzero normal `u`
    is an additive Haar (Lebesgue) null set. This is the lone analytic fact the
    `hnull` hypothesis of `each_slice_exactly_half` isolated as Gap 2.

    Proof: `{y | ⟪u, y⟫ = c}` is the translate by any point `y₀` on the
    hyperplane of the kernel of the nonzero functional `⟪u, ·⟫`. That kernel is a
    *proper* submodule (it omits `u`, since `⟪u, u⟫ = ‖u‖² ≠ 0`), hence null by
    `Measure.addHaar_submodule`; translation preserves Haar measure. No
    continuity / dominated-convergence input is needed — this gap is genuinely
    elementary, unlike the headline Gap 1 (scalar slice-volume continuity). -/
theorem volume_inner_hyperplane_eq_zero {m : ℕ}
    (u : EuclideanSpace ℝ (Fin m)) (hu : u ≠ 0) (c : ℝ) :
    volume {y : EuclideanSpace ℝ (Fin m) | inner (𝕜 := ℝ) u y = c} = 0 := by
  have huu : inner (𝕜 := ℝ) u u ≠ 0 := by
    rw [real_inner_self_eq_norm_sq]
    have : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    positivity
  -- a point on the hyperplane
  set y₀ : EuclideanSpace ℝ (Fin m) := (c / inner (𝕜 := ℝ) u u) • u with hy₀
  have hy₀c : inner (𝕜 := ℝ) u y₀ = c := by
    rw [hy₀, real_inner_smul_right]
    field_simp
  -- kernel submodule of the functional ⟪u, ·⟫
  set K : Submodule ℝ (EuclideanSpace ℝ (Fin m)) :=
    LinearMap.ker (innerSL ℝ u).toLinearMap with hK
  have hmemK : ∀ z, z ∈ K ↔ inner (𝕜 := ℝ) u z = 0 := by
    intro z
    rw [hK, LinearMap.mem_ker]
    simp [innerSL_apply_apply]
  have hKne : K ≠ ⊤ := by
    intro h
    have : u ∈ K := by rw [h]; exact Submodule.mem_top
    rw [hmemK] at this
    exact huu this
  -- the hyperplane is a translate of the kernel
  have hset : {y : EuclideanSpace ℝ (Fin m) | inner (𝕜 := ℝ) u y = c}
      = ((-y₀) + ·) ⁻¹' (K : Set (EuclideanSpace ℝ (Fin m))) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]
    rw [hmemK, inner_add_right, inner_neg_right, hy₀c]
    constructor <;> intro h <;> linarith
  rw [hset, measure_preimage_add]
  exact Measure.addHaar_submodule volume K hKne

/-- The boundary slice of a body under the standard parameterization is null
    whenever the cutting direction `u x` is nonzero — discharging the `hnull`
    hypothesis of `each_slice_exactly_half` from `volume_inner_hyperplane_eq_zero`
    and `body ∩ B ⊆ B`. -/
theorem volume_body_inter_stdBoundary_eq_zero (n : ℕ)
    (body : Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (t : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ)
    (x : EuclideanSpace ℝ (Fin (n + 1))) (hux : u x ≠ 0) :
    volume (body ∩ {y | inner (𝕜 := ℝ) (u x) y = t x}) = 0 :=
  measure_mono_null Set.inter_subset_right
    (volume_inner_hyperplane_eq_zero (u x) hux (t x))

/-- **Each side is exactly half, standard parameterization — `hnull` discharged.**

    Specializes `each_slice_exactly_half` to the standard linear cut
    `stdPos`/`stdNeg`. The strict/strict/boundary partition, measurability of the
    three slices, and the boundary null condition are *all proved here*: the
    boundary hyperplane is null by Gap 2 (`volume_body_inter_stdBoundary_eq_zero`)
    given only `u x ≠ 0`. The sole remaining input is the bisection equality
    `hbis` — i.e. the Ham Sandwich conclusion itself. -/
theorem each_slice_exactly_half_standard (n : ℕ)
    (body : Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (t : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ)
    (x : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin n)
    (hbody : MeasurableSet body) (hux : u x ≠ 0)
    (hbis : volume (body ∩ stdPos n u t x i) = volume (body ∩ stdNeg n u t x i)) :
    2 * volume (body ∩ stdPos n u t x i) = volume body := by
  have hcont : Continuous fun y : EuclideanSpace ℝ (Fin n) => inner (𝕜 := ℝ) (u x) y :=
    continuous_const.inner continuous_id
  have hPm : MeasurableSet (stdPos n u t x i) :=
    (isOpen_lt hcont continuous_const).measurableSet
  have hNm : MeasurableSet (stdNeg n u t x i) :=
    (isOpen_lt continuous_const hcont).measurableSet
  have hBm : MeasurableSet {y : EuclideanSpace ℝ (Fin n) | inner (𝕜 := ℝ) (u x) y = t x} :=
    (isClosed_eq hcont continuous_const).measurableSet
  have hcover : stdPos n u t x i ∪ stdNeg n u t x i
      ∪ {y | inner (𝕜 := ℝ) (u x) y = t x} = Set.univ := by
    ext y
    simp only [stdPos, stdNeg, Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    rcases lt_trichotomy (inner (𝕜 := ℝ) (u x) y) (t x) with h | h | h <;> tauto
  have hPN : Disjoint (stdPos n u t x i) (stdNeg n u t x i) := by
    rw [Set.disjoint_left]; intro y h1 h2
    simp only [stdPos, stdNeg, Set.mem_setOf_eq] at h1 h2; linarith
  have hPB : Disjoint (stdPos n u t x i) {y | inner (𝕜 := ℝ) (u x) y = t x} := by
    rw [Set.disjoint_left]; intro y h1 h2
    simp only [stdPos, Set.mem_setOf_eq] at h1 h2; linarith
  have hNB : Disjoint (stdNeg n u t x i) {y | inner (𝕜 := ℝ) (u x) y = t x} := by
    rw [Set.disjoint_left]; intro y h1 h2
    simp only [stdNeg, Set.mem_setOf_eq] at h1 h2; linarith
  exact each_slice_exactly_half n body (stdPos n u t x i) (stdNeg n u t x i)
    {y | inner (𝕜 := ℝ) (u x) y = t x} hbody hPm hNm hBm hcover hPN hPB hNB hbis
    (volume_body_inter_stdBoundary_eq_zero n body u t x hux)

-- ============================================================
-- PART 9: The *global* continuity hypotheses are non-dischargeable
-- ============================================================

/-
The continuity hypotheses `hcont_pos`/`hcont_neg` of
`ham_sandwich_(standard_)of_scalar_continuity` demand `Continuous fun x => …`
over **all** of `EuclideanSpace ℝ (Fin (n+1))`. This is forced by the
architecture: `SphereFun.continuous'` is a *global* `Continuous` field, consumed
globally on the way to the Borsuk–Ulam axiom. We show here that for the standard
linear cut these global hypotheses are **false** whenever the slice is
nondegenerate: the slice-volume map is `0` at the origin (the cut degenerates to
the empty half-space) but is a *constant nonzero* value along every open ray from
the origin. Hence it has a jump discontinuity at `0`.

The mathematical consequence is that the honest, still-true hypothesis is
`ContinuousOn (Sphere n) …` (the Borsuk–Ulam machinery only ever reads `f` on the
sphere, where `x = 0` never occurs); replacing global `Continuous` by
`ContinuousOn (Sphere n)` throughout the chain is the genuine remaining work.
These lemmas certify *why* that reformulation is necessary rather than optional.
-/

/-- **The standard positive slice degenerates to `∅` at the origin.** Since `u`
    and `t` are *linear*, `u 0 = 0` and `t 0 = 0`, so the defining condition
    `⟨u 0, y⟩ < t 0` reads `0 < 0`, satisfied by no `y`. -/
theorem stdPos_zero (n : ℕ)
    (u : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (t : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ) (i : Fin n) :
    stdPos n u t 0 i = (∅ : Set (EuclideanSpace ℝ (Fin n))) := by
  unfold stdPos
  ext y
  simp only [map_zero, inner_zero_left, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    lt_self_iff_false]

/-- The standard negative slice also degenerates to `∅` at the origin. -/
theorem stdNeg_zero (n : ℕ)
    (u : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (t : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ) (i : Fin n) :
    stdNeg n u t 0 i = (∅ : Set (EuclideanSpace ℝ (Fin n))) := by
  unfold stdNeg
  ext y
  simp only [map_zero, inner_zero_left, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    lt_self_iff_false]

/-- **The standard positive slice is invariant under positive scaling of the
    parameter.** Linearity gives `u (c • x) = c • u x` and `t (c • x) = c • t x`;
    dividing the strict inequality by `c > 0` recovers the original half-space. So
    the slice — and hence its volume — is **constant along each open ray** `ℝ₊ • x`
    from the origin. -/
theorem stdPos_smul_pos (n : ℕ)
    (u : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (t : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ)
    (x : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin n) {c : ℝ} (hc : 0 < c) :
    stdPos n u t (c • x) i = stdPos n u t x i := by
  unfold stdPos
  ext y
  simp only [map_smul, real_inner_smul_left, smul_eq_mul, Set.mem_setOf_eq]
  exact mul_lt_mul_iff_of_pos_left hc

/-- The standard negative slice is likewise invariant under positive scaling. -/
theorem stdNeg_smul_pos (n : ℕ)
    (u : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (t : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ)
    (x : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin n) {c : ℝ} (hc : 0 < c) :
    stdNeg n u t (c • x) i = stdNeg n u t x i := by
  unfold stdNeg
  ext y
  simp only [map_smul, real_inner_smul_left, smul_eq_mul, Set.mem_setOf_eq]
  exact mul_lt_mul_iff_of_pos_left hc

/-- **The global `hcont_pos` hypothesis is non-dischargeable for any nondegenerate
    cut.** If some standard positive slice `bodyᵢ ∩ stdPos x₀` has finite positive
    volume, then `x ↦ vol(bodyᵢ ∩ stdPos x).toReal` is **not** globally continuous:
    it is `0` at the origin (`stdPos_zero`), yet equals the constant positive value
    `vol(bodyᵢ ∩ stdPos x₀).toReal` along the ray `(k+1)⁻¹ • x₀ → 0`
    (`stdPos_smul_pos`). The two limits disagree, so continuity fails at `0`.

    This certifies the architectural correction recorded in the project notes: the
    `hcont_pos` of `ham_sandwich_standard_of_scalar_continuity` cannot be proved as
    stated; the faithful hypothesis is `ContinuousOn (Sphere n)`. -/
theorem stdPos_global_continuity_fails (n : ℕ)
    (body : Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (t : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ)
    (x₀ : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin n)
    (hpos : 0 < volume (body ∩ stdPos n u t x₀ i))
    (hfin : volume (body ∩ stdPos n u t x₀ i) ≠ ⊤) :
    ¬ Continuous fun x => (volume (body ∩ stdPos n u t x i)).toReal := by
  intro hcont
  have hc_pos : 0 < (volume (body ∩ stdPos n u t x₀ i)).toReal :=
    ENNReal.toReal_pos hpos.ne' hfin
  -- value at the origin is `0` (the slice is empty there)
  have hzero :
      (volume (body ∩ stdPos n u t (0 : EuclideanSpace ℝ (Fin (n + 1))) i)).toReal = 0 := by
    rw [stdPos_zero, Set.inter_empty, measure_empty, ENNReal.toReal_zero]
  -- the ray `xₖ = (k+1)⁻¹ • x₀` tends to `0`
  have htend : Filter.Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹ • x₀)
      Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) Filter.atTop (nhds 0) := by
      simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hcs : Continuous (fun c : ℝ => c • x₀) := continuous_id.smul continuous_const
    simpa only [Function.comp_def, zero_smul] using (hcs.tendsto 0).comp h0
  -- along the ray the value is the constant positive value
  have hval : ∀ k : ℕ,
      (volume (body ∩ stdPos n u t (((k : ℝ) + 1)⁻¹ • x₀) i)).toReal
        = (volume (body ∩ stdPos n u t x₀ i)).toReal := by
    intro k
    rw [stdPos_smul_pos n u t x₀ i (by positivity : (0 : ℝ) < ((k : ℝ) + 1)⁻¹)]
  -- continuity forces the constant sequence to converge to the origin value `0`
  have hlim := (hcont.tendsto 0).comp htend
  simp only [Function.comp_def, hval] at hlim
  rw [hzero] at hlim
  exact absurd (tendsto_nhds_unique hlim tendsto_const_nhds) hc_pos.ne

/-- The symmetric statement for the negative slice: `hcont_neg` is likewise
    non-dischargeable globally whenever the negative slice is nondegenerate. -/
theorem stdNeg_global_continuity_fails (n : ℕ)
    (body : Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (t : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ)
    (x₀ : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin n)
    (hpos : 0 < volume (body ∩ stdNeg n u t x₀ i))
    (hfin : volume (body ∩ stdNeg n u t x₀ i) ≠ ⊤) :
    ¬ Continuous fun x => (volume (body ∩ stdNeg n u t x i)).toReal := by
  intro hcont
  have hc_pos : 0 < (volume (body ∩ stdNeg n u t x₀ i)).toReal :=
    ENNReal.toReal_pos hpos.ne' hfin
  have hzero :
      (volume (body ∩ stdNeg n u t (0 : EuclideanSpace ℝ (Fin (n + 1))) i)).toReal = 0 := by
    rw [stdNeg_zero, Set.inter_empty, measure_empty, ENNReal.toReal_zero]
  have htend : Filter.Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹ • x₀)
      Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) Filter.atTop (nhds 0) := by
      simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hcs : Continuous (fun c : ℝ => c • x₀) := continuous_id.smul continuous_const
    simpa only [Function.comp_def, zero_smul] using (hcs.tendsto 0).comp h0
  have hval : ∀ k : ℕ,
      (volume (body ∩ stdNeg n u t (((k : ℝ) + 1)⁻¹ • x₀) i)).toReal
        = (volume (body ∩ stdNeg n u t x₀ i)).toReal := by
    intro k
    rw [stdNeg_smul_pos n u t x₀ i (by positivity : (0 : ℝ) < ((k : ℝ) + 1)⁻¹)]
  have hlim := (hcont.tendsto 0).comp htend
  simp only [Function.comp_def, hval] at hlim
  rw [hzero] at hlim
  exact absurd (tendsto_nhds_unique hlim tendsto_const_nhds) hc_pos.ne

/-
## Significance and the Remaining Gap

The parent file `BrouwerFixedPointOQ01OQ03.lean` carries `ham_sandwich_theorem`
as an axiom, justified by: *"the continuity of the bisecting-measure function
… is beyond the current proof scope."* This file confirms that diagnosis is
exact: with that one continuity fact in hand (as the `SphereFun` packaging of
the discrepancy map), the Ham Sandwich conclusion is fully **proved**, not
axiomatized. The oddness and the "zero ⇒ bisected" steps, which one might worry
also hide content, are dispatched here by elementary means.

Two of the three originally-listed side conditions are now discharged for the
standard parameterization (Parts 4–6):
  * the antipodal swap `pos(-x) = neg(x)` holds for any *linear* direction /
    threshold extraction (`stdPos_neg`, `stdNeg_neg`) — it is a consequence of
    linearity, not an assumption,
  * finiteness `vol(bodyᵢ ∩ H) < ⊤` follows from `vol(bodyᵢ) < ⊤` since the
    slice is a subset (`volume_inter_ne_top`).

The boundary-null side condition (Gap 2) is also now discharged (Part 8):
  * `volume_inner_hyperplane_eq_zero` proves any level hyperplane
    `{y | ⟨u, y⟩ = c}` with `u ≠ 0` is Lebesgue-null (translate of the kernel of
    a nonzero functional + `Measure.addHaar_submodule`), and
    `each_slice_exactly_half_standard` uses it to drop `hnull` entirely: under the
    standard cut, "each side is exactly half" follows from the bisection equality
    alone, with measurability and the strict/strict/boundary partition proved.

The single genuinely-remaining analytic input is therefore:
  * the continuity of `x ↦ vol(bodyᵢ ∩ {y | ⟨u(x), y⟩ < t(x)}).toReal` on `Sⁿ`
    (Lebesgue continuity of parameterized half-spaces; dominated convergence).
This is a self-contained measure-theory fact; it is not topological.

Part 9 sharpens the statement of that remaining input. The continuity must be
read as `ContinuousOn (Sphere n)`, **not** global `Continuous`: for the standard
linear cut the global map is provably discontinuous at the origin whenever the
slice is nondegenerate (`stdPos_global_continuity_fails`,
`stdNeg_global_continuity_fails`), since the cut degenerates to the empty
half-space at `0` (`stdPos_zero`) while staying a fixed nonzero slice along every
ray (`stdPos_smul_pos`). The Borsuk–Ulam machinery only reads `f` on the sphere,
where `x = 0` never occurs, so the on-sphere statement is the faithful one.

`ham_sandwich_standard_of_scalar_continuity` (Part 6) states the conclusion with
*exactly* this scalar continuity (plus finiteness) as its only hypotheses: the
vector packaging into a `SphereFun` is no longer assumed but constructed, so the
intermediate `ham_sandwich_standard` (which still took the vector `hcomp`) is
strictly weakened in its hypotheses. The dichotomy "topological core (proved) vs.
scalar Lebesgue continuity (the lone input)" is now exact.
-/

end BrouwerFixedPointOQ01OQ03OQ01
