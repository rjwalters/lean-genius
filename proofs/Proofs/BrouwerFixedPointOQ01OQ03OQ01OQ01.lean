import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic
import Proofs.BorsukUlam
import Proofs.BrouwerFixedPoint
import Proofs.BrouwerFixedPointOQ01OQ03
import Proofs.BrouwerFixedPointOQ01OQ03OQ01

/-
# The Honest Continuity Hypothesis: `ContinuousOn (Sphere n)` Borsuk–Ulam
# (brouwer-fixed-point-oq-01-oq-03-oq-01-oq-01)

## The Open Question

The parent entry OQ-01-OQ-03-OQ-01 ("De-Axiomatizing the Ham Sandwich Theorem")
reduced the Ham Sandwich axiom to a single analytic input — the continuity of
the parameterized slice-volume map — and then, in its Part 9, **proved that the
continuity must be read on the sphere, not globally**: for the standard linear
cut, the global slice-volume map is provably discontinuous at the origin
(`stdPos_global_continuity_fails` / `stdNeg_global_continuity_fails`), since the
cut degenerates to the empty half-space there while staying a fixed nonzero slice
along every ray. The parent file therefore flagged, as the genuine remaining
work, *"replacing global `Continuous` by `ContinuousOn (Sphere n)` throughout the
chain."*

But the whole Borsuk–Ulam pipeline is built on `SphereFun`, whose continuity
field is **global** (`SphereFun.continuous' : Continuous toFun`), and the
underlying axiom `no_continuous_odd_nonzero_on_sphere` demands a *globally*
continuous odd map. So the on-sphere reformulation is not a free rephrasing: one
must show the global Borsuk–Ulam input actually *implies* the on-sphere version.

## Result

We carry out exactly that reduction, and it turns out to be a clean theorem of
analysis — no new topology, no new axiom.

1. `sphereExtend` — the **radial extension** of a map `h : Sⁿ → ℝⁿ`:
   `sphereExtend h x = ‖x‖ • h(‖x‖⁻¹ • x)`, with `sphereExtend h 0 = 0`. It
   reuses only the *values of `h` on the sphere* (the argument `‖x‖⁻¹ • x` always
   lies on `Sⁿ`).

2. `sphereExtend_eq_of_mem` / `sphereExtend_odd` / `sphereExtend_continuous` —
   the extension agrees with `h` on the sphere, is odd whenever `h` is, and is
   **globally continuous** as soon as `h` is merely `ContinuousOn (Sphere n)`.
   Global continuity at the origin is the only nontrivial point and follows from
   the squeeze `‖sphereExtend h x‖ ≤ M·‖x‖`, where `M` bounds `‖h‖` on the
   compact sphere.

3. `borsuk_ulam_antipodal_collapse_on` — the payoff: an **odd map that is only
   `ContinuousOn (Sphere n)`** still has a zero on the sphere. Proved by feeding
   its radial extension (a genuine `SphereFun`) to the parent
   `borsuk_ulam_antipodal_collapse`. This strictly generalizes the global
   statement (`borsuk_ulam_antipodal_collapse_of_sphereFun`).

4. `ham_sandwich_reduction_on`, `ham_sandwich_of_discrepancy_on`,
   `ham_sandwich_of_scalar_continuity_on`,
   `ham_sandwich_standard_of_scalar_continuity_on` — the entire Ham Sandwich
   chain of the parent file, re-derived with the continuity hypothesis stated as
   `ContinuousOn (Sphere n)` instead of global `Continuous`. The headline
   `ham_sandwich_standard_of_scalar_continuity_on` proves simultaneous bisection
   under the *honest* hypothesis Part 9 identified, with all side conditions
   (antipodal swap, finiteness) still discharged from `stdPos_neg`, `stdNeg_neg`,
   `volume_inter_ne_top`.

This closes the loop opened by the parent file: the global continuity it showed
to be *false* is replaced by the on-sphere continuity it showed to be *faithful*,
and that replacement is now proved sufficient — at no cost beyond a radial
extension argument.

## Summary: 0 sorries, 0 new axioms.
Depends on `BorsukUlam.lean` (1 axiom: `no_continuous_odd_nonzero_on_sphere`).
-/

set_option linter.unusedVariables false

namespace BrouwerFixedPointOQ01OQ03OQ01OQ01

open BorsukUlam BrouwerFixedPointOQ01OQ03 BrouwerFixedPointOQ01OQ03OQ01
open MeasureTheory Filter Topology

-- ============================================================
-- PART 1: The radial extension of a map defined on the sphere
-- ============================================================

/-- **Radial extension.** Given any `h : Sⁿ → ℝⁿ`, define
    `sphereExtend h x = ‖x‖ • h(‖x‖⁻¹ • x)` (and `0` at the origin). The argument
    `‖x‖⁻¹ • x` lies on `Sⁿ` for `x ≠ 0`, so the extension reads `h` only on the
    sphere. On the sphere itself `‖x‖ = 1`, so the extension reproduces `h`. -/
noncomputable def sphereExtend (n : ℕ)
    (h : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin (n + 1))) : EuclideanSpace ℝ (Fin n) :=
  ‖x‖ • h (‖x‖⁻¹ • x)

/-- The radial extension vanishes at the origin. -/
theorem sphereExtend_zero (n : ℕ)
    (h : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n)) :
    sphereExtend n h 0 = 0 := by
  simp [sphereExtend]

/-- The radial extension reproduces `h` on the sphere. -/
theorem sphereExtend_eq_of_mem (n : ℕ)
    (h : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin (n + 1))) (hx : x ∈ Sphere n) :
    sphereExtend n h x = h x := by
  have hnorm : ‖x‖ = 1 := by
    simpa [Sphere, Metric.mem_sphere, dist_zero_right] using hx
  simp [sphereExtend, hnorm]

/-- For `x ≠ 0`, the normalized argument `‖x‖⁻¹ • x` lies on `Sⁿ`. -/
theorem normalize_mem_sphere (n : ℕ) {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ≠ 0) :
    ‖x‖⁻¹ • x ∈ Sphere n := by
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  simp only [Sphere, Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm]
  rw [inv_mul_cancel₀ hxn]

/-- **Oddness of the radial extension.** If `h` is odd, so is its radial
    extension — the scale `‖x‖` is even and `‖x‖⁻¹ • (-x) = -(‖x‖⁻¹ • x)`. -/
theorem sphereExtend_odd (n : ℕ)
    (h : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n))
    (hodd : ∀ x, h (-x) = -h x) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    sphereExtend n h (-x) = -sphereExtend n h x := by
  simp only [sphereExtend, norm_neg]
  rw [show ‖x‖⁻¹ • (-x) = -(‖x‖⁻¹ • x) by rw [smul_neg], hodd, smul_neg]

/-- **The radial extension is globally continuous from on-sphere continuity.**

    This is the crux. Off the origin the extension is a composition of continuous
    maps (`x ↦ ‖x‖⁻¹ • x` into the sphere, then `h`, then scale by `‖x‖`). At the
    origin continuity follows from the squeeze `‖sphereExtend h x‖ ≤ M·‖x‖`, with
    `M` an upper bound for `‖h‖` on the **compact** sphere. -/
theorem sphereExtend_continuous (n : ℕ)
    (h : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n))
    (hcont : ContinuousOn h (Sphere n)) :
    Continuous (sphereExtend n h) := by
  -- `h` is bounded on the compact sphere.
  have hKcompact : IsCompact (Sphere n) := isCompact_sphere 0 1
  obtain ⟨M, hM⟩ := hKcompact.exists_bound_of_continuousOn hcont
  rw [continuous_iff_continuousAt]
  intro x₀
  rcases eq_or_ne x₀ 0 with rfl | hx₀
  · -- Continuity at the origin via the squeeze `‖sphereExtend h x‖ ≤ M·‖x‖`.
    have htend : Tendsto (sphereExtend n h) (𝓝 0) (𝓝 0) := by
      refine squeeze_zero_norm (a := fun x => M * ‖x‖) (fun x => ?_) ?_
      · rcases eq_or_ne x 0 with rfl | hx
        · simp [sphereExtend_zero]
        · show ‖sphereExtend n h x‖ ≤ M * ‖x‖
          rw [sphereExtend, norm_smul, norm_norm, mul_comm M ‖x‖]
          exact mul_le_mul_of_nonneg_left (hM _ (normalize_mem_sphere n hx)) (norm_nonneg x)
      · have h0 : Tendsto (fun x : EuclideanSpace ℝ (Fin (n + 1)) => ‖x‖) (𝓝 0) (𝓝 0) := by
          simpa using (continuous_norm.tendsto (0 : EuclideanSpace ℝ (Fin (n + 1))))
        simpa using h0.const_mul M
    simpa [ContinuousAt, sphereExtend_zero] using htend
  · -- Continuity at `x₀ ≠ 0` from continuity on the open set `{x ≠ 0}`.
    have hU : IsOpen {x : EuclideanSpace ℝ (Fin (n + 1)) | x ≠ 0} := isOpen_ne
    have hp : ContinuousOn (fun x : EuclideanSpace ℝ (Fin (n + 1)) => ‖x‖⁻¹ • x)
        {x | x ≠ 0} := by
      apply ContinuousOn.smul
      · exact (continuous_norm.continuousOn).inv₀ (fun x hx => norm_ne_zero_iff.mpr hx)
      · exact continuous_id.continuousOn
    have hmaps : Set.MapsTo (fun x : EuclideanSpace ℝ (Fin (n + 1)) => ‖x‖⁻¹ • x)
        {x | x ≠ 0} (Sphere n) := fun x hx => normalize_mem_sphere n hx
    have hConU : ContinuousOn (sphereExtend n h) {x | x ≠ 0} := by
      apply ContinuousOn.smul continuous_norm.continuousOn
      exact ContinuousOn.comp hcont hp hmaps
    exact hConU.continuousAt (hU.mem_nhds hx₀)

-- ============================================================
-- PART 2: Borsuk–Ulam from on-sphere continuity
-- ============================================================

/-- **Borsuk–Ulam antipodal collapse, on-sphere version.**

    An odd map `h : Sⁿ → ℝⁿ` that is merely `ContinuousOn (Sphere n)` still
    vanishes somewhere on the sphere. We extend `h` radially to a globally
    continuous odd map (a genuine `SphereFun`), apply the parent global collapse,
    and pull the zero back to `h` using `sphereExtend_eq_of_mem`. -/
theorem borsuk_ulam_antipodal_collapse_on (n : ℕ) (hn : n ≥ 1)
    (h : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n))
    (hcont : ContinuousOn h (Sphere n))
    (hodd : ∀ x, h (-x) = -h x) :
    ∃ x ∈ Sphere n, h x = 0 := by
  obtain ⟨x, hx, hHx⟩ := borsuk_ulam_antipodal_collapse n hn
    ⟨sphereExtend n h, sphereExtend_continuous n h hcont⟩
    (sphereExtend_odd n h hodd)
  exact ⟨x, hx, by rw [← sphereExtend_eq_of_mem n h x hx]; exact hHx⟩

/-- The global (`SphereFun`) collapse is the special case of the on-sphere
    collapse where continuity happens to hold everywhere — confirming the
    on-sphere statement is a genuine generalization. -/
theorem borsuk_ulam_antipodal_collapse_of_sphereFun (n : ℕ) (hn : n ≥ 1)
    (f : SphereFun n) (hodd : ∀ x, f.toFun (-x) = -f.toFun x) :
    ∃ x ∈ Sphere n, f.toFun x = 0 :=
  borsuk_ulam_antipodal_collapse_on n hn f.toFun f.continuous'.continuousOn hodd

-- ============================================================
-- PART 3: The Ham Sandwich chain, with on-sphere continuity
-- ============================================================

/-- **Ham Sandwich reduction (topological core), on-sphere version.** Identical
    to the parent `ham_sandwich_reduction` but consuming `ContinuousOn (Sphere n)`
    in place of a globally continuous `SphereFun`. -/
theorem ham_sandwich_reduction_on (n : ℕ) (hn : n ≥ 1)
    (F : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n))
    (hcont : ContinuousOn F (Sphere n))
    (hodd : ∀ x, F (-x) = -F x)
    (Bisected : EuclideanSpace ℝ (Fin (n + 1)) → Prop)
    (hbridge : ∀ x ∈ Sphere n, F x = 0 → Bisected x) :
    ∃ x ∈ Sphere n, Bisected x := by
  obtain ⟨x, hx, hFx⟩ := borsuk_ulam_antipodal_collapse_on n hn F hcont hodd
  exact ⟨x, hx, hbridge x hx hFx⟩

/-- **Ham Sandwich from a continuous-on-sphere discrepancy map.** The discrepancy
    of the parent file, realized by a map `F` that is only
    `ContinuousOn (Sphere n)`, still yields a simultaneous bisection. Oddness and
    "zero discrepancy ⇒ equal volumes" are unchanged from the parent; only the
    continuity hypothesis is weakened to the sphere. -/
theorem ham_sandwich_of_discrepancy_on (n : ℕ) (hn : n ≥ 1)
    (bodies : Fin n → Set (EuclideanSpace ℝ (Fin n)))
    (pos neg : EuclideanSpace ℝ (Fin (n + 1)) → Fin n → Set (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n))
    (hswap : ∀ x i, pos (-x) i = neg x i)
    (hswap' : ∀ x i, neg (-x) i = pos x i)
    (hfin_pos : ∀ x i, volume (bodies i ∩ pos x i) ≠ ⊤)
    (hfin_neg : ∀ x i, volume (bodies i ∩ neg x i) ≠ ⊤)
    (hcontF : ContinuousOn F (Sphere n))
    (hcomp : ∀ x i, F x i = discrepancy n bodies pos neg x i) :
    ∃ x ∈ Sphere n, ∀ i, volume (bodies i ∩ pos x i) = volume (bodies i ∩ neg x i) := by
  have hodd : ∀ x, F (-x) = -F x := by
    intro x
    have key : WithLp.ofLp (F (-x)) = WithLp.ofLp (-F x) := by
      funext i
      show (F (-x)).ofLp i = (-F x).ofLp i
      rw [hcomp (-x) i, discrepancy_odd_of_swap n bodies pos neg hswap hswap' x i,
        ← hcomp x i]
      simp
    exact WithLp.ofLp_injective _ key
  refine ham_sandwich_reduction_on n hn F hcontF hodd
    (fun x => ∀ i, volume (bodies i ∩ pos x i) = volume (bodies i ∩ neg x i))
    ?_
  intro x hx hFx i
  have hzero : discrepancy n bodies pos neg x i = 0 := by
    rw [← hcomp x i, hFx]; simp
  have hsub : (volume (bodies i ∩ pos x i)).toReal
      = (volume (bodies i ∩ neg x i)).toReal := by
    unfold discrepancy at hzero
    linarith [hzero]
  exact (ENNReal.toReal_eq_toReal_iff' (hfin_pos x i) (hfin_neg x i)).mp hsub

/-- **Ham Sandwich from scalar slice-volume continuity, on-sphere version.**

    The honest form of the parent's `ham_sandwich_of_scalar_continuity`: each of
    the `2n` scalar slice-volume maps is assumed continuous **on `Sⁿ`** (where the
    map is genuinely continuous — see the parent's Part 9, which shows the global
    version is *false*). The discrepancy assembles into a `ContinuousOn (Sphere n)`
    `EuclideanSpace`-valued map and the bisection follows. -/
theorem ham_sandwich_of_scalar_continuity_on (n : ℕ) (hn : n ≥ 1)
    (bodies : Fin n → Set (EuclideanSpace ℝ (Fin n)))
    (pos neg : EuclideanSpace ℝ (Fin (n + 1)) → Fin n → Set (EuclideanSpace ℝ (Fin n)))
    (hswap : ∀ x i, pos (-x) i = neg x i)
    (hswap' : ∀ x i, neg (-x) i = pos x i)
    (hfin_pos : ∀ x i, volume (bodies i ∩ pos x i) ≠ ⊤)
    (hfin_neg : ∀ x i, volume (bodies i ∩ neg x i) ≠ ⊤)
    (hcont_pos : ∀ i, ContinuousOn (fun x => (volume (bodies i ∩ pos x i)).toReal) (Sphere n))
    (hcont_neg : ∀ i, ContinuousOn (fun x => (volume (bodies i ∩ neg x i)).toReal) (Sphere n)) :
    ∃ x ∈ Sphere n, ∀ i, volume (bodies i ∩ pos x i) = volume (bodies i ∩ neg x i) := by
  have hcont : ContinuousOn (fun x => (EuclideanSpace.equiv (Fin n) ℝ).symm
      (fun i => discrepancy n bodies pos neg x i)) (Sphere n) := by
    refine (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous.comp_continuousOn' ?_
    refine continuousOn_pi.mpr (fun i => ?_)
    simpa only [discrepancy] using (hcont_pos i).sub (hcont_neg i)
  exact ham_sandwich_of_discrepancy_on n hn bodies pos neg
    (fun x => (EuclideanSpace.equiv (Fin n) ℝ).symm
      (fun i => discrepancy n bodies pos neg x i))
    hswap hswap' hfin_pos hfin_neg hcont (fun x i => rfl)

/-- **Ham Sandwich, standard linear cut, from on-sphere scalar continuity.**

    The headline result, and the honest counterpart of the parent's
    `ham_sandwich_standard_of_scalar_continuity`. Under the standard linear
    half-space assignment `stdPos`/`stdNeg`, the antipodal-swap and finiteness
    side conditions are theorems (`stdPos_neg`, `stdNeg_neg`,
    `volume_inter_ne_top`), and the vector-assembly is built internally. The only
    hypotheses are:
      * `hbody` — each body has finite volume, and
      * `hcont_pos`/`hcont_neg` — each scalar slice-volume map is continuous
        **on `Sⁿ`**.
    The latter is exactly the hypothesis the parent's Part 9 proved to be the
    faithful one (the global version is provably discontinuous at the origin).
    With it, simultaneous bisection of all `n` bodies is fully proved. -/
theorem ham_sandwich_standard_of_scalar_continuity_on (n : ℕ) (hn : n ≥ 1)
    (bodies : Fin n → Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (t : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ)
    (hbody : ∀ i, volume (bodies i) ≠ ⊤)
    (hcont_pos : ∀ i, ContinuousOn
      (fun x => (volume (bodies i ∩ stdPos n u t x i)).toReal) (Sphere n))
    (hcont_neg : ∀ i, ContinuousOn
      (fun x => (volume (bodies i ∩ stdNeg n u t x i)).toReal) (Sphere n)) :
    ∃ x ∈ Sphere n, ∀ i,
      volume (bodies i ∩ stdPos n u t x i) = volume (bodies i ∩ stdNeg n u t x i) :=
  ham_sandwich_of_scalar_continuity_on n hn bodies (stdPos n u t) (stdNeg n u t)
    (stdPos_neg n u t) (stdNeg_neg n u t)
    (fun x i => volume_inter_ne_top n (bodies i) _ (hbody i))
    (fun x i => volume_inter_ne_top n (bodies i) _ (hbody i))
    hcont_pos hcont_neg

/-
## Significance

The parent file isolated the lone analytic obstruction to a fully-formal Ham
Sandwich theorem — continuity of the parameterized slice-volume map — and then
proved (Part 9) that this continuity is *false* when read globally and only true
when read on the sphere `Sⁿ`. That left a structural worry: the entire
Borsuk–Ulam pipeline (`SphereFun`, `no_continuous_odd_nonzero_on_sphere`) is
phrased with *global* continuity, so the "honest" on-sphere hypothesis might not
even be usable.

This file removes that worry. The radial extension `sphereExtend` turns any
`ContinuousOn (Sphere n)` odd map into a globally continuous odd `SphereFun`
agreeing with it on the sphere, so the global Borsuk–Ulam input *implies* the
on-sphere collapse `borsuk_ulam_antipodal_collapse_on`. Re-running the parent's
reduction on top of it yields the full Ham Sandwich chain with the continuity
hypothesis stated exactly as Part 9 demanded — `ContinuousOn (Sphere n)`, the
faithful form — culminating in `ham_sandwich_standard_of_scalar_continuity_on`.

The dichotomy is now airtight: the genuinely-remaining analytic input is the
on-sphere Lebesgue continuity of a single real parameterized slice-volume, and
nothing more. Everything topological — including the bridge from the global axiom
to the on-sphere hypothesis — is proved.
-/

end BrouwerFixedPointOQ01OQ03OQ01OQ01
