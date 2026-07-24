/-
# Erdős #1215 (cyclotomic sub-question, OQ02) — exit paths in EVERY direction

  Slug: erdos-1215-oq-02
  Prior work (this OQ family):
    * OQ02OQ01  — lower/upper factor bounds, boundedness, openness of `{|Φ_n| < C}`.
    * OQ02OQ02  — sharp two-sided factor bounds `(‖z‖-1)^{φ(n)} ≤ |Φ_n(z)| ≤ (‖z‖+1)^{φ(n)}`.
    * OQ02OQ03–07 — radius/area sandwich, sharp inner/outer radius, origin interiority.
    * OQ02OQ08  — the FIRST path result: a radial exit along the positive real axis,
                  first crossing time `t* ≤ 1 + C^{1/φ(n)}`.
    * OQ02OQ09  — the far field `{R < ‖z‖}` is one path-connected escape region.

  ## What is genuinely open (parent #1215)

  Erdős #1215 asks whether every `P` with `P(0)=1` and unit-circle roots admits a path
  from `0` to the boundary of `{|P| < C}` of length `≤ C·deg P`, staying inside the set.
  Mac Lane (1953) answered **NO in general**: labyrinth polynomials force arbitrarily
  long detours (`Erdos1215Problem.maclane_labyrinth`, axiomatized).  OQ02 restricts to
  the rigid cyclotomic family `Φ_n` and asks whether the labyrinth can still appear.

  ## This file — the OQ08 exit ray holds in EVERY direction

  OQ02OQ08 exhibited a single short exit path, along `ℝ_{≥0}`.  Its recorded follow-up
  question was whether boundary reachability extends beyond that one ray.  This file
  answers the directional half of that question completely:

  > For EVERY unit direction `u` (`‖u‖ = 1`), the ray `t ↦ t·u` from the origin has a
  > first level-`C` crossing `t*` with the **two-sided sharp bound**
  > `C^{1/φ(n)} − 1 ≤ t* ≤ 1 + C^{1/φ(n)}`, and the open segment `[0, t*)·u` stays
  > strictly inside `{|Φ_n| < C}` (`ray_exit`).

  Consequences:
  * the level curve `{|Φ_n| = C}` meets every ray from the origin, inside the sharp
    annulus `C^{1/φ(n)} − 1 ≤ ‖z‖ ≤ 1 + C^{1/φ(n)}` (`levelCurve_meets_every_ray`) —
    the boundary *surrounds* the origin in all directions at `n`-uniformly bounded
    distance (both radii `→` the unit circle as `φ(n) → ∞`);
  * an explicit straight-segment path of Euclidean length `t* ≤ 1 + C^{1/φ(n)}` in
    each direction (`ray_exit_pathLength`).

  So not only does one radial ray escape (OQ08): seen from the origin, the cyclotomic
  sublevel set has NO labyrinthine direction at all — every direction exits after a
  bounded straight run.  OQ08's `radial_exit` is the special case `u = 1` (up to the
  extra sharp lower bound proved here, which is new even for that case).

  The mechanism is the OQ08 first-crossing argument run along an arbitrary ray:
  `‖t·u‖ = t` for `t ≥ 0`, so the OQ02OQ01 lower bound forces a crossing by
  `1 + C^{1/φ(n)}`, while the OQ02OQ07 sharp inner ball forbids one before
  `C^{1/φ(n)} − 1`.  No arc-length / rectifiable-path infrastructure is needed —
  a segment's length is its endpoint distance.

  Result status: `[propext, Classical.choice, Quot.sound]` — axiom-free relative to
  Mathlib.  The deep `maclane_labyrinth` axiom of the parent is untouched.
-/
import Mathlib
import Proofs.Erdos1215Problem
import Proofs.CyclotomicPolynomialsOQ02OQ01
import Proofs.CyclotomicPolynomialsOQ02OQ07

open Complex Polynomial

namespace CyclotomicPolynomialsOQ02OQ10

/-- `rayNorm n u t = |Φ_n(t·u)|`: the modulus of the cyclotomic polynomial restricted
to the ray through `u`, parameterized by real `t`. -/
noncomputable def rayNorm (n : ℕ) (u : ℂ) (t : ℝ) : ℝ :=
  ‖(cyclotomic n ℂ).eval ((t : ℂ) * u)‖

/-- `rayNorm n u` is continuous: it is `‖·‖ ∘ eval ∘ (t ↦ t·u)`. -/
lemma continuous_rayNorm (n : ℕ) (u : ℂ) : Continuous (rayNorm n u) :=
  continuous_norm.comp ((cyclotomic n ℂ).continuous.comp
    (Complex.continuous_ofReal.mul continuous_const))

/-- On the ray through a unit vector, the parameter is the norm: `‖t·u‖ = t` for `t ≥ 0`. -/
lemma norm_ofReal_mul (u : ℂ) (hu : ‖u‖ = 1) {t : ℝ} (ht : 0 ≤ t) :
    ‖(t : ℂ) * u‖ = t := by
  rw [norm_mul, hu, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]

/-- At the origin every ray starts at modulus `1`: `rayNorm n u 0 = |Φ_n(0)| = 1`. -/
lemma rayNorm_zero (n : ℕ) (hn : n ≠ 0) (u : ℂ) : rayNorm n u 0 = 1 := by
  simp only [rayNorm, Complex.ofReal_zero, zero_mul]
  exact CyclotomicPolynomialsOQ02OQ07.norm_cyclotomic_eval_zero n hn

/-- **The sharp outer radius forces a crossing in every direction.**
At `R = 1 + C^{1/φ(n)}` along any unit direction `u` we have `|Φ_n(R·u)| ≥ C`:
the point `R·u` has norm `R`, so the OQ02OQ01 lower bound
`(‖z‖-1)^{φ(n)} ≤ |Φ_n(z)|` evaluates to `(C^{1/φ(n)})^{φ(n)} = C`. -/
lemma le_rayNorm_outer (n : ℕ) (hn : n ≠ 0) (u : ℂ) (hu : ‖u‖ = 1)
    {C : ℝ} (hC : 1 < C) :
    C ≤ rayNorm n u (1 + C ^ ((n.totient : ℝ)⁻¹)) := by
  have hC0 : (0 : ℝ) < C := lt_trans one_pos hC
  have hk0 : n.totient ≠ 0 := (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)).ne'
  set r : ℝ := C ^ ((n.totient : ℝ)⁻¹) with hr
  have hr1 : 1 < r := by
    have h := CyclotomicPolynomialsOQ02OQ07.sharpInnerRadius_pos n hn hC
    rw [← hr] at h; linarith
  have hRnn : (0 : ℝ) ≤ 1 + r := by linarith
  have hnorm : ‖((1 + r : ℝ) : ℂ) * u‖ = 1 + r := norm_ofReal_mul u hu hRnn
  have h1le : (1 : ℝ) ≤ ‖((1 + r : ℝ) : ℂ) * u‖ := by rw [hnorm]; linarith
  have hlow := CyclotomicPolynomialsOQ02OQ01.pow_sub_one_le_norm_cyclotomic_eval
    n hn (((1 + r : ℝ) : ℂ) * u) h1le
  rw [hnorm] at hlow
  have hpoweq : (1 + r - 1) ^ n.totient = C := by
    have h1 : (1 + r - 1) = r := by ring
    rw [h1, hr, Real.rpow_inv_natCast_pow hC0.le hk0]
  rw [hpoweq] at hlow
  simpa [rayNorm] using hlow

/-- **No crossing before the sharp inner radius, in any direction.**
For `0 ≤ s < C^{1/φ(n)} − 1` the point `s·u` lies in the sharp inner ball of OQ02OQ07,
hence strictly inside the sublevel set: `|Φ_n(s·u)| < C`. -/
lemma rayNorm_lt_of_lt_sharpInner (n : ℕ) (hn : n ≠ 0) (u : ℂ) (hu : ‖u‖ = 1)
    {C : ℝ} (hC : 1 < C) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s < C ^ ((n.totient : ℝ)⁻¹) - 1) :
    rayNorm n u s < C := by
  have hmem : ((s : ℂ) * u) ∈ Metric.ball (0 : ℂ) (C ^ ((n.totient : ℝ)⁻¹) - 1) := by
    rw [Metric.mem_ball, dist_zero_right, norm_ofReal_mul u hu hs0]
    exact hs
  have hlevel := CyclotomicPolynomialsOQ02OQ07.ball_sharpInner_subset_levelSet
    n hn hC hmem
  simpa [Erdos1215.levelSet, Set.mem_setOf_eq, rayNorm] using hlevel

/-- **A short exit path in EVERY direction (positive answer, OQ02, directional form).**

For `n ≥ 1`, `C > 1`, and any unit direction `u`, there is a *first crossing time*
`t > 0` along the ray `t ↦ t·u` with

  * `C^{1/φ(n)} − 1 ≤ t ≤ 1 + C^{1/φ(n)}`  — two-sided sharp bound on the exit distance,
  * `|Φ_n(t·u)| = C`                        — the segment ends exactly on the boundary,
  * `∀ s ∈ [0, t), |Φ_n(s·u)| < C`          — the open segment stays inside `{|Φ_n| < C}`.

OQ02OQ08's `radial_exit` is the special case `u = 1` (the sharp lower bound on `t` is
new even there).  Since the direction `u` is arbitrary, the cyclotomic sublevel set has
no labyrinthine direction whatsoever: every ray from the origin exits after a straight
run of length `≤ 1 + C^{1/φ(n)}`, `n`-uniformly bounded (`→ 2` as `φ(n) → ∞`). -/
theorem ray_exit (n : ℕ) (hn : n ≠ 0) (u : ℂ) (hu : ‖u‖ = 1) {C : ℝ} (hC : 1 < C) :
    ∃ t : ℝ, 0 < t ∧ C ^ ((n.totient : ℝ)⁻¹) - 1 ≤ t ∧
      t ≤ 1 + C ^ ((n.totient : ℝ)⁻¹) ∧
      rayNorm n u t = C ∧ ∀ s ∈ Set.Ico (0 : ℝ) t, rayNorm n u s < C := by
  set R : ℝ := 1 + C ^ ((n.totient : ℝ)⁻¹) with hR
  have hcont : Continuous (rayNorm n u) := continuous_rayNorm n u
  have hg0 : rayNorm n u 0 = 1 := rayNorm_zero n hn u
  have hgR : C ≤ rayNorm n u R := le_rayNorm_outer n hn u hu hC
  have hrin_pos : 0 < C ^ ((n.totient : ℝ)⁻¹) - 1 :=
    CyclotomicPolynomialsOQ02OQ07.sharpInnerRadius_pos n hn hC
  have hRpos : 0 < R := by rw [hR]; linarith
  -- The closed, bounded-below, nonempty set of crossing times in `[0, R]`.
  set A : Set ℝ := Set.Icc 0 R ∩ (rayNorm n u ⁻¹' Set.Ici C) with hA
  have hAclosed : IsClosed A := isClosed_Icc.inter (isClosed_Ici.preimage hcont)
  have hAbdd : BddBelow A := ⟨0, fun x hx => hx.1.1⟩
  have hRmem : R ∈ A := ⟨⟨le_of_lt hRpos, le_refl R⟩, hgR⟩
  have hAne : A.Nonempty := ⟨R, hRmem⟩
  -- `t := sInf A` is the first crossing.
  set t : ℝ := sInf A with ht
  have htmem : t ∈ A := hAclosed.csInf_mem hAne hAbdd
  obtain ⟨⟨ht0, htR⟩, htC⟩ := htmem
  rw [Set.mem_preimage, Set.mem_Ici] at htC
  -- Sharp lower bound: before `C^{1/φ(n)} − 1` the ray is strictly inside the set.
  have hlow : C ^ ((n.totient : ℝ)⁻¹) - 1 ≤ t := by
    by_contra hlt
    push Not at hlt
    have := rayNorm_lt_of_lt_sharpInner n hn u hu hC ht0 hlt
    linarith
  have htpos : 0 < t := lt_of_lt_of_le hrin_pos hlow
  -- Stays strictly inside on `[0, t)`: any `s < t = sInf A` with `rayNorm s ≥ C`
  -- would sit in `A`, contradicting it being the infimum.
  have hbelow : ∀ s ∈ Set.Ico (0 : ℝ) t, rayNorm n u s < C := by
    intro s hs
    obtain ⟨hs0, hst⟩ := hs
    by_contra hge
    push Not at hge
    have hsA : s ∈ A := ⟨⟨hs0, le_trans (le_of_lt hst) htR⟩, hge⟩
    have hts : t ≤ s := csInf_le hAbdd hsA
    linarith
  -- Ends exactly on the boundary: `rayNorm t = C`.  We have `C ≤ rayNorm t`;
  -- if strict, IVT on `[0, t]` (from `1 < C < rayNorm t`) gives an earlier crossing
  -- `u' ≤ t` in `A`, so `t ≤ u' ≤ t`, forcing `rayNorm t = C` after all.
  have hboundary : rayNorm n u t = C := by
    rcases eq_or_lt_of_le htC with h | h
    · exact h.symm
    · exfalso
      have hmemIcc : C ∈ Set.Icc (rayNorm n u 0) (rayNorm n u t) := by
        rw [hg0]; exact ⟨le_of_lt hC, le_of_lt h⟩
      obtain ⟨v, hv_mem, hv⟩ :=
        intermediate_value_Icc ht0 hcont.continuousOn hmemIcc
      obtain ⟨hv0, hvt⟩ := hv_mem
      have hvA : v ∈ A := ⟨⟨hv0, le_trans hvt htR⟩, hv.ge⟩
      have htv : t ≤ v := csInf_le hAbdd hvA
      have hvt_eq : v = t := le_antisymm hvt htv
      rw [hvt_eq] at hv
      rw [hv] at h
      exact lt_irrefl C h
  exact ⟨t, htpos, hlow, htR, hboundary, hbelow⟩

/-- **The level curve surrounds the origin: it meets every ray, inside the sharp annulus.**

For every unit direction `u`, the level curve `{z : |Φ_n(z)| = C}` contains a point on
the open ray `{t·u : t > 0}`, and that point lies in the closed annulus
`C^{1/φ(n)} − 1 ≤ ‖z‖ ≤ 1 + C^{1/φ(n)}`.  As `φ(n) → ∞` the annulus radii tend to `0`
and `2` respectively, so the crossing stays `n`-uniformly at distance `≤ 2 + ε`.
The boundary of the cyclotomic sublevel set is radially visible from the origin in every
direction — the exact opposite of a Mac Lane labyrinth, whose boundary hides behind
long detours. -/
theorem levelCurve_meets_every_ray (n : ℕ) (hn : n ≠ 0) {C : ℝ} (hC : 1 < C)
    (u : ℂ) (hu : ‖u‖ = 1) :
    ∃ z : ℂ, ‖(cyclotomic n ℂ).eval z‖ = C ∧
      (∃ t : ℝ, 0 < t ∧ z = (t : ℂ) * u) ∧
      C ^ ((n.totient : ℝ)⁻¹) - 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 1 + C ^ ((n.totient : ℝ)⁻¹) := by
  obtain ⟨t, htpos, hlow, htR, hbdry, _⟩ := ray_exit n hn u hu hC
  have hznorm : ‖(t : ℂ) * u‖ = t := norm_ofReal_mul u hu htpos.le
  refine ⟨(t : ℂ) * u, by simpa [rayNorm] using hbdry, ⟨t, htpos, rfl⟩, ?_, ?_⟩
  · rw [hznorm]; exact hlow
  · rw [hznorm]; exact htR

/-- **The exit segment in direction `u` realises the length bound.**
Re-packaging `ray_exit` as an explicit Euclidean segment `γ : [0,1] → ℂ`,
`γ s = s · (t·u)`, from `0` to the boundary point `t·u`, whose length is
`dist (γ 0) (γ 1) = t ≤ 1 + C^{1/φ(n)}` — the same `n`-uniform bound in every
direction.  A segment's length is its endpoint distance, so no rectifiable-path
arc-length infrastructure is needed. -/
theorem ray_exit_pathLength (n : ℕ) (hn : n ≠ 0) (u : ℂ) (hu : ‖u‖ = 1)
    {C : ℝ} (hC : 1 < C) :
    ∃ (t : ℝ) (γ : ℝ → ℂ),
      γ = (fun s : ℝ => (s : ℂ) * ((t : ℂ) * u)) ∧ γ 0 = 0 ∧ γ 1 = (t : ℂ) * u ∧
      dist (γ 0) (γ 1) = t ∧ t ≤ 1 + C ^ ((n.totient : ℝ)⁻¹) ∧
      ‖(cyclotomic n ℂ).eval (γ 1)‖ = C := by
  obtain ⟨t, htpos, _hlow, htR, hbdry, _⟩ := ray_exit n hn u hu hC
  refine ⟨t, (fun s : ℝ => (s : ℂ) * ((t : ℂ) * u)), rfl, by simp, by simp, ?_, htR, ?_⟩
  · -- `dist 0 (t·u) = ‖t·u‖ = t` (t > 0, ‖u‖ = 1)
    simp only [Complex.ofReal_zero, Complex.ofReal_one, zero_mul, one_mul, dist_zero_left]
    exact norm_ofReal_mul u hu htpos.le
  · -- endpoint modulus equals `C`
    simpa [rayNorm] using hbdry

end CyclotomicPolynomialsOQ02OQ10
