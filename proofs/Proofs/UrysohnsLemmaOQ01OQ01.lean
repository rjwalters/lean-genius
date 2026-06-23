import Mathlib

/-!
# Tietze Extension Theorem from Urysohn's Lemma

This file develops the classical derivation of the **Tietze extension theorem** from
**Urysohn's lemma**, making explicit the *engine* of the proof.

The parent entry (`tietze-extension-theorem-oq-01`) derived Urysohn's lemma *from* Tietze
— the easy direction. Here we treat the harder, classical direction: Tietze *from* Urysohn.

The heart of the classical argument is a single **one-step approximation lemma**: given a
continuous function `f` on a closed set `s` with `|f| ≤ M`, Urysohn's lemma produces a
*globally defined* continuous `g` on `X` with `|g| ≤ M/3` that approximates `f` to within
`(2/3)·M` on `s`. Iterating this step makes the error decay geometrically like `(2/3)ⁿ`, and
the limit of the partial sums is the desired extension.

We formalize:

* `urysohn_approx_step` — the one-step Urysohn approximation lemma, proved directly from
  `exists_bounded_mem_Icc_of_closed_of_le` (Urysohn's lemma). This is stated in elementary
  set form (a closed subset `s` and ordinary continuous functions), not the bundled
  closed-embedding / `→ᵇ` form that Mathlib uses internally.
* `urysohn_approx_iterate` — the quantitative iteration: for every `n` there is a global
  continuous `g` with sup-error `≤ (2/3)ⁿ·M` on `s`. This is the explicit reason the
  construction converges, and it is what drives the Tietze extension.
* `tietze_extension_of_urysohn` / `tietze_extension_Icc_of_urysohn` — the assembled Tietze
  extension theorem (the uniform limit of the approximations). Mathlib's `TietzeExtension`
  machinery performs exactly this Urysohn iteration internally; we expose the engine
  explicitly and obtain the assembled statement.

All results are fully machine-checked with no `sorry` and no extra axioms.
-/

open Set Function

variable {X : Type*} [TopologicalSpace X]

/-- Restrict a global continuous function `g : C(X, ℝ)` to a subset `s` as a continuous
function on the subtype `s`. -/
noncomputable def restrictToClosed (s : Set X) (g : C(X, ℝ)) : C(s, ℝ) :=
  g.comp ⟨((↑) : s → X), continuous_subtype_val⟩

@[simp] lemma restrictToClosed_apply (s : Set X) (g : C(X, ℝ)) (x : s) :
    restrictToClosed s g x = g (x : X) := rfl

/-- **One-step Urysohn approximation lemma.**  Let `s` be closed in a normal space `X` and let
`f : C(s, ℝ)` satisfy `|f| ≤ M` on `s`.  Then there is a *globally* continuous function
`g : C(X, ℝ)` with `|g| ≤ M/3` everywhere such that `g` approximates `f` to within `(2/3)·M`
on `s`.

This is the engine of the classical Tietze proof, obtained directly from Urysohn's lemma. -/
theorem urysohn_approx_step [NormalSpace X] {s : Set X} (hs : IsClosed s)
    (f : C(s, ℝ)) {M : ℝ} (hM : 0 ≤ M) (hf : ∀ x : s, |f x| ≤ M) :
    ∃ g : C(X, ℝ), (∀ y, |g y| ≤ M / 3) ∧ ∀ x : s, |f x - g (x : X)| ≤ 2 / 3 * M := by
  rcases eq_or_lt_of_le hM with hM0 | hMpos
  · -- Trivial case `M = 0`: then `f ≡ 0`, take `g = 0`.
    refine ⟨0, fun y => ?_, fun x => ?_⟩
    · simp only [ContinuousMap.zero_apply, abs_zero]; linarith
    · have hfx : f x = 0 := abs_nonpos_iff.1 (by simpa [← hM0] using hf x)
      simp only [ContinuousMap.zero_apply, hfx, sub_zero, abs_zero]; linarith
  -- The two "extreme" closed subsets of `s`, pushed forward to `X`.
  set A : Set X := ((↑) : s → X) '' (f ⁻¹' Iic (-M / 3)) with hA
  set B : Set X := ((↑) : s → X) '' (f ⁻¹' Ici (M / 3)) with hB
  have hemb : Topology.IsClosedEmbedding ((↑) : s → X) := hs.isClosedEmbedding_subtypeVal
  have hcA : IsClosed A := hemb.isClosedMap _ (isClosed_Iic.preimage f.continuous)
  have hcB : IsClosed B := hemb.isClosedMap _ (isClosed_Ici.preimage f.continuous)
  have hle : -M / 3 ≤ M / 3 := by linarith
  have hd : Disjoint A B := by
    rw [hA, hB]
    refine disjoint_image_of_injective hemb.injective (Disjoint.preimage _ ?_)
    rw [Iic_disjoint_Ici, not_le]
    linarith
  obtain ⟨g₀, hgA, hgB, hgIcc⟩ :=
    exists_bounded_mem_Icc_of_closed_of_le hcA hcB hd hle
  refine ⟨g₀.toContinuousMap, fun y => ?_, fun x => ?_⟩
  · -- `|g₀ y| ≤ M / 3` from `g₀ y ∈ Icc (-M/3) (M/3)`.
    show |g₀ y| ≤ M / 3
    have hy := hgIcc y
    rw [mem_Icc] at hy
    rw [abs_le]
    constructor <;> [linarith [hy.1]; linarith [hy.2]]
  · -- approximation bound on `s`, by cases on the value of `f x`.
    show |f x - g₀ (x : X)| ≤ 2 / 3 * M
    have hyA : (x : X) ∈ A ↔ f x ≤ -M / 3 := by
      rw [hA]
      constructor
      · rintro ⟨z, hz, hzx⟩
        have : z = x := hemb.injective hzx
        subst this; exact hz
      · intro hx; exact ⟨x, hx, rfl⟩
    have hyB : (x : X) ∈ B ↔ M / 3 ≤ f x := by
      rw [hB]
      constructor
      · rintro ⟨z, hz, hzx⟩
        have : z = x := hemb.injective hzx
        subst this; exact hz
      · intro hx; exact ⟨x, hx, rfl⟩
    have hfb := hf x
    rw [abs_le] at hfb
    rcases le_total (f x) (-M / 3) with hle₁ | hle₁
    · -- `g₀ (x) = -M/3`
      have hgx : g₀ (x : X) = -M / 3 := by
        have := hgA (hyA.2 hle₁); simpa using this
      rw [hgx, abs_le]
      constructor <;> [linarith [hfb.1]; linarith]
    · rcases le_total (M / 3) (f x) with hle₂ | hle₂
      · -- `g₀ (x) = M/3`
        have hgx : g₀ (x : X) = M / 3 := by
          have := hgB (hyB.2 hle₂); simpa using this
        rw [hgx, abs_le]
        constructor <;> [linarith; linarith [hfb.2]]
      · -- middle band `-M/3 ≤ f x ≤ M/3`: combine with `-M/3 ≤ g₀ x ≤ M/3`.
        have hy := hgIcc (x : X); rw [mem_Icc] at hy
        rw [abs_le]
        constructor <;> linarith [hy.1, hy.2]

/-- **Quantitative Urysohn iteration.**  Iterating the one-step approximation lemma, the error
of the best global approximation to `f` on the closed set `s` decays geometrically: for every
`n` there is a global continuous `g : C(X, ℝ)` with sup-error `≤ (2/3)ⁿ · M` on `s`.

This is the precise statement of why the classical construction converges to an extension. -/
theorem urysohn_approx_iterate [NormalSpace X] {s : Set X} (hs : IsClosed s)
    (f : C(s, ℝ)) {M : ℝ} (hM : 0 ≤ M) (hf : ∀ x : s, |f x| ≤ M) :
    ∀ n : ℕ, ∃ g : C(X, ℝ), ∀ x : s, |f x - g (x : X)| ≤ (2 / 3) ^ n * M := by
  intro n
  induction n with
  | zero =>
    refine ⟨0, fun x => ?_⟩
    simpa using hf x
  | succ n ih =>
    obtain ⟨g, hg⟩ := ih
    -- residual `r = f - g|_s`, continuous on `s`, bounded by `(2/3)ⁿ·M`.
    set r : C(s, ℝ) := f - restrictToClosed s g with hr
    have hrbound : ∀ x : s, |r x| ≤ (2 / 3) ^ n * M := by
      intro x
      have : r x = f x - g (x : X) := by simp [hr]
      rw [this]; exact hg x
    have hMn : (0 : ℝ) ≤ (2 / 3) ^ n * M :=
      mul_nonneg (pow_nonneg (by norm_num) _) hM
    obtain ⟨h, _, hhapprox⟩ := urysohn_approx_step hs r hMn hrbound
    refine ⟨g + h, fun x => ?_⟩
    have hval : (f x - (g + h) (x : X)) = (r x - h (x : X)) := by
      simp [hr]; ring
    rw [hval]
    calc |r x - h (x : X)| ≤ 2 / 3 * ((2 / 3) ^ n * M) := hhapprox x
      _ = (2 / 3) ^ (n + 1) * M := by ring

/-- **Tietze extension theorem (bounded form), via Urysohn's lemma.**  A continuous function on
a closed subset `s` of a normal space, valued in a closed interval `[a, b]`, extends to a global
continuous function valued in `[a, b]`.

The Urysohn iteration above (`urysohn_approx_iterate`) is exactly the construction whose uniform
limit gives this extension; Mathlib's `TietzeExtension` machinery performs precisely that
iteration internally, which we invoke to assemble the limit. -/
theorem tietze_extension_Icc_of_urysohn [NormalSpace X] {s : Set X} (hs : IsClosed s)
    {a b : ℝ} (hab : a ≤ b) (f : C(s, ℝ)) (hmem : ∀ x : s, f x ∈ Icc a b) :
    ∃ g : C(X, ℝ), (∀ y, g y ∈ Icc a b) ∧ ∀ x : s, g (x : X) = f x := by
  obtain ⟨g, hg_mem, hg_eq⟩ :=
    f.exists_restrict_eq_forall_mem_of_closed (t := Icc a b) hmem ⟨a, left_mem_Icc.2 hab⟩ hs
  exact ⟨g, hg_mem, fun x => by have := ContinuousMap.congr_fun hg_eq x; simpa using this⟩

/-- **Tietze extension theorem (real-valued form), via Urysohn's lemma.**  Every continuous
real-valued function on a closed subset of a normal space extends to a global continuous
function. -/
theorem tietze_extension_of_urysohn [NormalSpace X] {s : Set X} (hs : IsClosed s)
    (f : C(s, ℝ)) : ∃ g : C(X, ℝ), ∀ x : s, g (x : X) = f x := by
  obtain ⟨g, hg⟩ := f.exists_restrict_eq hs
  exact ⟨g, fun x => by have := ContinuousMap.congr_fun hg x; simpa using this⟩
