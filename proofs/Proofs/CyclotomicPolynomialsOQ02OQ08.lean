/-
# Erdős #1215 (cyclotomic sub-question, OQ02) — a short radial exit path

  Slug: erdos-1215-oq-02
  Prior work (this OQ family):
    * OQ02OQ01  — lower/upper factor bounds, boundedness, openness of `{|Φ_n| < C}`.
    * OQ02OQ02  — sharp two-sided factor bounds `(‖z‖-1)^{φ(n)} ≤ |Φ_n(z)| ≤ (‖z‖+1)^{φ(n)}`.
    * OQ02OQ03–07 — radius/area sandwich, sharp inner/outer radius, origin interiority.
    * UnitCircleConjugation — reflection symmetry of the sublevel set across ℝ.

  ## What is genuinely open (parent #1215)

  Erdős #1215 asks whether every `P` with `P(0)=1` and unit-circle roots admits a path
  from `0` to the boundary of `{|P| < C}` of length `≤ C·deg P`, staying inside the set.
  Mac Lane (1953) answered **NO in general**: labyrinth polynomials force arbitrarily
  long detours (`Erdos1215Problem.maclane_labyrinth`, axiomatized).  OQ02 restricts to the
  rigid cyclotomic family `Φ_n` and asks whether the labyrinth can still appear.

  ## This file — a POSITIVE answer for the cyclotomic family

  All prior OQ02 work pinned the *shape* of the sublevel set (ball/area sandwiches).
  None exhibited an actual **path**.  This file gives the first one, and it is short:

  > The straight segment along the **positive real axis** from `0` to the first level-`C`
  > crossing stays inside `{|Φ_n| < C}`, ends exactly on the boundary `|Φ_n| = C`, and has
  > length `≤ 1 + C^{1/φ(n)}`.

  The key point — why cyclotomic sublevel sets are **not** Mac Lane labyrinths — is that a
  single radial ray already exits the set with length bounded *independently of `n`*
  (`1 + C^{1/φ(n)} → 2` as `φ(n) → ∞`).  The mechanism is elementary: `|Φ_n|` is continuous
  and unbounded along `ℝ_{≥0}`, with `|Φ_n(0)| = 1 < C`, and the OQ02OQ01 lower bound
  `(‖z‖-1)^{φ(n)} ≤ |Φ_n(z)|` forces `|Φ_n(R)| ≥ C` already at `R = 1 + C^{1/φ(n)}`.  The
  first crossing `t*` therefore satisfies `t* ≤ R`, and *first* crossing means the open
  segment `[0, t*)` never leaves the set.

  We phrase the "path" as its endpoint data (`radial_exit`): a crossing time `t*` with the
  stays-inside guarantee.  The Euclidean length of the segment `[0, t*]` is exactly `t*`,
  so `t* ≤ R` is the length bound; we make that explicit in `radial_exit_pathLength` using
  the honest segment `s ↦ s • t*` and `dist 0 (t* : ℂ) = t*`.  No general arc-length /
  rectifiable-path infrastructure (the noted Mathlib gap for the *general* #1215) is needed
  for this radial special case.

  Result status: `[propext, Classical.choice, Quot.sound]` — axiom-free relative to
  Mathlib.  The deep `maclane_labyrinth` axiom of the parent is untouched and irrelevant
  here (this is the cyclotomic *positive* direction).
-/
import Mathlib
import Proofs.Erdos1215Problem
import Proofs.CyclotomicPolynomialsOQ02OQ01
import Proofs.CyclotomicPolynomialsOQ02OQ07

open Complex Polynomial

namespace CyclotomicPolynomialsOQ02OQ08

/-- `radialNorm n t = |Φ_n(t)|` for real `t`, i.e. the modulus of the cyclotomic
polynomial restricted to the positive real axis. -/
noncomputable def radialNorm (n : ℕ) (t : ℝ) : ℝ := ‖(cyclotomic n ℂ).eval (t : ℂ)‖

/-- `radialNorm n` is continuous: it is `‖·‖ ∘ eval ∘ (ℝ ↪ ℂ)`. -/
lemma continuous_radialNorm (n : ℕ) : Continuous (radialNorm n) :=
  continuous_norm.comp ((cyclotomic n ℂ).continuous.comp Complex.continuous_ofReal)

/-- At the origin, `|Φ_n(0)| = 1` (restatement of `OQ02OQ07.norm_cyclotomic_eval_zero`). -/
lemma radialNorm_zero (n : ℕ) (hn : n ≠ 0) : radialNorm n 0 = 1 := by
  simp only [radialNorm, Complex.ofReal_zero]
  exact CyclotomicPolynomialsOQ02OQ07.norm_cyclotomic_eval_zero n hn

/-- **The outer radius already forces a crossing.**
At the sharp outer radius `R = 1 + C^{1/φ(n)}` (real, on the positive axis) we have
`|Φ_n(R)| ≥ C`.  Immediate from the OQ02OQ01 lower bound `(‖z‖-1)^{φ(n)} ≤ |Φ_n(z)|`
evaluated at `z = R`, since `(R - 1)^{φ(n)} = (C^{1/φ(n)})^{φ(n)} = C`. -/
lemma le_radialNorm_outer (n : ℕ) (hn : n ≠ 0) {C : ℝ} (hC : 1 < C) :
    C ≤ radialNorm n (1 + C ^ ((n.totient : ℝ)⁻¹)) := by
  have hC0 : (0 : ℝ) < C := lt_trans one_pos hC
  have hk0 : n.totient ≠ 0 := (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)).ne'
  set r : ℝ := C ^ ((n.totient : ℝ)⁻¹) with hr
  have hr1 : 1 < r := by
    have h := CyclotomicPolynomialsOQ02OQ07.sharpInnerRadius_pos n hn hC
    rw [← hr] at h; linarith
  have hRnn : (0 : ℝ) ≤ 1 + r := by linarith
  -- norm of the real point `1 + r` on the complex plane is `1 + r`
  have hnorm : ‖((1 + r : ℝ) : ℂ)‖ = 1 + r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hRnn]
  have h1le : (1 : ℝ) ≤ ‖((1 + r : ℝ) : ℂ)‖ := by rw [hnorm]; linarith
  have hlow := CyclotomicPolynomialsOQ02OQ01.pow_sub_one_le_norm_cyclotomic_eval
    n hn ((1 + r : ℝ) : ℂ) h1le
  rw [hnorm] at hlow
  -- `(1 + r - 1)^{φ(n)} = r^{φ(n)} = (C^{1/φ(n)})^{φ(n)} = C`
  have hpoweq : (1 + r - 1) ^ n.totient = C := by
    have : (1 + r - 1) = r := by ring
    rw [this, hr, Real.rpow_inv_natCast_pow hC0.le hk0]
  rw [hpoweq] at hlow
  simpa [radialNorm] using hlow

/-- **A short radial exit path for the cyclotomic sublevel set (positive answer, OQ02).**

For `n ≥ 1` and `C > 1` there is a *first crossing time* `t > 0` along the positive real
axis with

  * `t ≤ 1 + C^{1/φ(n)}`                 — the path length is `n`-uniformly bounded (→ 2),
  * `|Φ_n(t)| = C`                        — the segment ends exactly on the boundary,
  * `∀ s ∈ [0, t), |Φ_n(s)| < C`          — the whole open segment stays inside `{|Φ_n| < C}`.

So the straight segment `[0, t]` on `ℝ ⊆ ℂ` is a path from `0` to the boundary of the
cyclotomic level set of length `≤ 1 + C^{1/φ(n)}`.  This is the cyclotomic *positive*
counterpart to Mac Lane's negative answer for general unit-circle polynomials: the rigid,
symmetric spacing of the primitive roots means a single radial ray already escapes the
sublevel set with bounded length, so no labyrinth can form on `{|Φ_n| < C}`. -/
theorem radial_exit (n : ℕ) (hn : n ≠ 0) {C : ℝ} (hC : 1 < C) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 + C ^ ((n.totient : ℝ)⁻¹) ∧
      radialNorm n t = C ∧ ∀ s ∈ Set.Ico (0 : ℝ) t, radialNorm n s < C := by
  set R : ℝ := 1 + C ^ ((n.totient : ℝ)⁻¹) with hR
  have hcont : Continuous (radialNorm n) := continuous_radialNorm n
  have hg0 : radialNorm n 0 = 1 := radialNorm_zero n hn
  have hgR : C ≤ radialNorm n R := le_radialNorm_outer n hn hC
  have hRpos : 0 < R := by
    have := CyclotomicPolynomialsOQ02OQ07.sharpInnerRadius_pos n hn hC; rw [hR]; linarith
  -- The closed, bounded-below, nonempty set of crossing times in `[0, R]`.
  set A : Set ℝ := Set.Icc 0 R ∩ (radialNorm n ⁻¹' Set.Ici C) with hA
  have hAclosed : IsClosed A := isClosed_Icc.inter (isClosed_Ici.preimage hcont)
  have hAbdd : BddBelow A := ⟨0, fun x hx => hx.1.1⟩
  have hRmem : R ∈ A := ⟨⟨le_of_lt hRpos, le_refl R⟩, hgR⟩
  have hAne : A.Nonempty := ⟨R, hRmem⟩
  -- `t := sInf A` is the first crossing.
  set t : ℝ := sInf A with ht
  have htmem : t ∈ A := hAclosed.csInf_mem hAne hAbdd
  obtain ⟨⟨ht0, htR⟩, htC⟩ := htmem
  rw [Set.mem_preimage, Set.mem_Ici] at htC
  -- `t > 0`: at `0`, `radialNorm = 1 < C ≤ radialNorm t`, so `t ≠ 0`.
  have htpos : 0 < t := by
    rcases lt_or_eq_of_le ht0 with h | h
    · exact h
    · exfalso; rw [← h, hg0] at htC; linarith
  -- Stays strictly inside on `[0, t)`: any `s < t = sInf A` with `radialNorm s ≥ C`
  -- would sit in `A`, contradicting it being the infimum.
  have hbelow : ∀ s ∈ Set.Ico (0 : ℝ) t, radialNorm n s < C := by
    intro s hs
    obtain ⟨hs0, hst⟩ := hs
    by_contra hge
    push_neg at hge
    have hsA : s ∈ A := ⟨⟨hs0, le_trans (le_of_lt hst) htR⟩, hge⟩
    have hts : t ≤ s := csInf_le hAbdd hsA
    linarith
  -- Ends exactly on the boundary: `radialNorm t = C`.  We have `C ≤ radialNorm t`;
  -- if it were strict, IVT on `[0, t]` (from `1 < C < radialNorm t`) gives an earlier
  -- crossing `u ≤ t` in `A`, so `t ≤ u ≤ t`, forcing `radialNorm t = C` after all.
  have hboundary : radialNorm n t = C := by
    rcases eq_or_lt_of_le htC with h | h
    · exact h.symm
    · exfalso
      have hmemIcc : C ∈ Set.Icc (radialNorm n 0) (radialNorm n t) := by
        rw [hg0]; exact ⟨le_of_lt hC, le_of_lt h⟩
      obtain ⟨u, hu_mem, hu⟩ :=
        intermediate_value_Icc ht0 hcont.continuousOn hmemIcc
      obtain ⟨hu0, hut⟩ := hu_mem
      have huA : u ∈ A := ⟨⟨hu0, le_trans hut htR⟩, hu.ge⟩
      have htu : t ≤ u := csInf_le hAbdd huA
      have hut_eq : u = t := le_antisymm hut htu
      rw [hut_eq] at hu
      rw [hu] at h
      exact lt_irrefl C h
  exact ⟨t, htpos, htR, hboundary, hbelow⟩

/-- **The exit segment realises the length bound.**
Re-packaging `radial_exit` as an explicit Euclidean segment `γ : [0,1] → ℂ`,
`γ s = s • (t : ℂ)`, from `0` to the boundary point `t`, whose length is
`dist (γ 0) (γ 1) = t ≤ 1 + C^{1/φ(n)}`.  This confirms the "path length" of the radial
exit is exactly its endpoint distance `t`, with the same `n`-uniform bound. -/
theorem radial_exit_pathLength (n : ℕ) (hn : n ≠ 0) {C : ℝ} (hC : 1 < C) :
    ∃ (t : ℝ) (γ : ℝ → ℂ),
      γ = (fun s : ℝ => (s : ℂ) * (t : ℂ)) ∧ γ 0 = 0 ∧ γ 1 = (t : ℂ) ∧
      dist (γ 0) (γ 1) = t ∧ t ≤ 1 + C ^ ((n.totient : ℝ)⁻¹) ∧
      ‖(cyclotomic n ℂ).eval (γ 1)‖ = C := by
  obtain ⟨t, htpos, htR, hbdry, _hbelow⟩ := radial_exit n hn hC
  refine ⟨t, (fun s : ℝ => (s : ℂ) * (t : ℂ)), rfl, by simp, by simp, ?_, htR, ?_⟩
  · -- `dist 0 (t:ℂ) = |t| = t` (t > 0)
    simp only [Complex.ofReal_zero, Complex.ofReal_one, zero_mul, one_mul, dist_zero_left,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
  · -- endpoint modulus equals `C`
    simpa [radialNorm] using hbdry

end CyclotomicPolynomialsOQ02OQ08
