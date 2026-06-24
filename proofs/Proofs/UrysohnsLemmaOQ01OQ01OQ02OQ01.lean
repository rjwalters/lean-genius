import Mathlib
import Proofs.UrysohnsLemmaOQ01OQ01OQ01

/-!
# Interval-Constrained and Finite-Dimensional Tietze from the Explicit Urysohn Series

The parent entry (`urysohns-lemma-oq-01-oq-01-oq-02`, file `UrysohnsLemmaOQ01OQ01OQ01`)
builds the Tietze extension *by hand* as a convergent series of Urysohn corrections,
`G = ∑' n, gₙ` in `BoundedContinuousFunction X ℝ`, and proves the symmetric sup-bound
`tietze_extension_via_tsum`:

  for `f : C(s,ℝ)` with `|f| ≤ M` there is a bounded continuous `G` extending `f` with
  `|G y| ≤ M` everywhere.

That bound is *symmetric* (`G` lands in `[-M, M]`) and `ℝ`-valued.  This entry pushes the
same explicit construction in the two directions asked by the open question
`urysohns-lemma-oq-01-oq-01-oq-02-oq-01` — **interval-constrained data** and
**(finite-dimensional) Banach-space–valued data** — *without re-running the limit*: every
result here is a black-box reduction to the parent series.

## Main results

* `tietze_extension_Icc` — the **classical order/interval form** of the Tietze extension
  theorem: a continuous `f : s → [a,b]` extends to a continuous `G : X → [a,b]` with the
  *same* (possibly asymmetric) bounds `a ≤ G y ≤ b`.  Obtained from the parent by the
  affine shift `f ↦ f - (a+b)/2`, which recentres `[a,b]` to `[-r, r]` with `r = (b-a)/2`.
* `tietze_extension_unitInterval` — the `[0,1]`-valued specialisation, the shape used for
  partitions of unity.
* `tietze_extension_pi_sup` — **vector-valued Tietze** for finitely many real components
  `f : C(s, ι → ℝ)` (`ι` finite): a continuous extension `G : X → (ι → ℝ)` with the
  componentwise `ℓ∞` bound `|G y i| ≤ M` preserved.  Built by applying the parent series to
  each component with the *common* bound `M`, so the joint sup-bound is tracked exactly.
* `tietze_extension_pi_norm` — the same packaged with the genuine `ℓ∞` norm on the
  finite-dimensional Banach space `ι → ℝ`: `‖G y‖ ≤ M`.  Since `G` restricts to `f` on `s`,
  taking `M = ‖f‖_{∞}` makes this the sharp norm-preserving statement `‖G‖ = ‖f‖` for
  finite-dimensional codomains (`tietze_extension_pi_norm_sharp`).

## Scope (honest)

The series construction relies on the *scalar* one-step Urysohn approximation, so it does
not by itself reach a general infinite-dimensional Banach codomain (there is no vector
Urysohn step).  We cover exactly the cases that reduce to the scalar engine: arbitrary
closed real intervals, and finite products `ι → ℝ` under the `ℓ∞` norm — the prototypical
finite-dimensional Banach spaces.

Everything is machine-checked with no `sorry` and uses only the parent series, no further
Mathlib `TietzeExtension` machinery.
-/

open Set

namespace TietzeIntervalVector

variable {X : Type*} [TopologicalSpace X] [NormalSpace X] {s : Set X}

/-- **Tietze extension into an arbitrary closed interval.**

If `f : s → ℝ` is continuous with `a ≤ f x ≤ b` on the closed set `s ⊆ X`, then `f` extends
to a continuous `G : X → ℝ` with the same two-sided bounds `a ≤ G y ≤ b` everywhere.  This is
the classical order form of Tietze; the parent series only supplied the symmetric bound
`|G| ≤ M`.  We recentre `[a,b]` to `[-r,r]` (`r = (b-a)/2`) via the constant shift and apply
`tietze_extension_via_tsum`. -/
theorem tietze_extension_Icc (hs : IsClosed s) (f : C(s, ℝ)) {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x : s, f x ∈ Icc a b) :
    ∃ G : C(X, ℝ), (∀ x : s, G (x : X) = f x) ∧ ∀ y : X, G y ∈ Icc a b := by
  classical
  set c : ℝ := (a + b) / 2 with hc
  set r : ℝ := (b - a) / 2 with hr
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  -- Recentred data `f' = f - c`, valued in `[-r, r]`.
  set f' : C(s, ℝ) := f - ContinuousMap.const s c with hf'
  have hf'bound : ∀ x : s, |f' x| ≤ r := by
    intro x
    have hx := hf x
    rw [mem_Icc] at hx
    have hval : f' x = f x - c := by simp [hf']
    rw [hval, abs_le]
    constructor
    · rw [hc]; linarith [hx.1]
    · rw [hc]; linarith [hx.2]
  obtain ⟨G', hG'ext, _, hG'bound⟩ := tietze_extension_via_tsum hs f' hr0 hf'bound
  refine ⟨G'.toContinuousMap + ContinuousMap.const X c, ?_, ?_⟩
  · intro x
    have happ : (G'.toContinuousMap + ContinuousMap.const X c) (x : X) = G' (x : X) + c := by
      simp
    rw [happ, hG'ext x]
    have : f' x = f x - c := by simp [hf']
    rw [this]; ring
  · intro y
    have happ : (G'.toContinuousMap + ContinuousMap.const X c) y = G' y + c := by simp
    rw [happ, mem_Icc]
    have hb := hG'bound y
    rw [abs_le] at hb
    constructor
    · rw [hc, hr] at *; linarith [hb.1]
    · rw [hc, hr] at *; linarith [hb.2]

/-- **Tietze extension into the unit interval `[0,1]`.**  A continuous `[0,1]`-valued map on a
closed set extends to a continuous `[0,1]`-valued map on the whole space — the form used to
build partitions of unity. -/
theorem tietze_extension_unitInterval (hs : IsClosed s) (f : C(s, ℝ))
    (hf : ∀ x : s, f x ∈ Icc (0 : ℝ) 1) :
    ∃ G : C(X, ℝ), (∀ x : s, G (x : X) = f x) ∧ ∀ y : X, G y ∈ Icc (0 : ℝ) 1 :=
  tietze_extension_Icc hs f (by norm_num) hf

/-! ## Vector-valued (finite-dimensional) Tietze with preserved `ℓ∞` bound -/

/-- **Componentwise vector-valued Tietze.**  For finitely many real components
`f : s → (ι → ℝ)` bounded in `ℓ∞` by `M`, there is a continuous extension `G : X → (ι → ℝ)`
with the joint componentwise bound `|G y i| ≤ M` preserved.  Each component is extended by the
parent series with the *common* bound `M`, so no component can exceed `M`. -/
theorem tietze_extension_pi_sup (hs : IsClosed s) {ι : Type*} [Fintype ι]
    (f : C(s, ι → ℝ)) {M : ℝ} (hM : 0 ≤ M) (hf : ∀ (x : s) (i : ι), |f x i| ≤ M) :
    ∃ G : C(X, ι → ℝ), (∀ x : s, G (x : X) = f x) ∧ ∀ (y : X) (i : ι), |G y i| ≤ M := by
  classical
  -- Extend each scalar component `x ↦ f x i` by the parent series, with the same bound `M`.
  have comp : ∀ i : ι, ∃ Gi : C(X, ℝ),
      (∀ x : s, Gi (x : X) = f x i) ∧ ∀ y : X, |Gi y| ≤ M := by
    intro i
    let fi : C(s, ℝ) := ⟨fun x => f x i, (continuous_apply i).comp f.continuous⟩
    have hfib : ∀ x : s, |fi x| ≤ M := fun x => hf x i
    obtain ⟨Gi, hext, _, hbd⟩ := tietze_extension_via_tsum hs fi hM hfib
    exact ⟨Gi.toContinuousMap, fun x => hext x, fun y => hbd y⟩
  choose Gi hext hbd using comp
  refine ⟨⟨fun y i => Gi i y, continuous_pi fun i => (Gi i).continuous⟩, ?_, ?_⟩
  · intro x; funext i; exact hext i x
  · intro y i; exact hbd i y

/-- **Vector-valued Tietze with the `ℓ∞` norm.**  Packaging `tietze_extension_pi_sup` with the
genuine sup-norm on the finite-dimensional Banach space `ι → ℝ`: the extension `G` satisfies
`‖G y‖ ≤ M` everywhere, matching the bound on the data. -/
theorem tietze_extension_pi_norm (hs : IsClosed s) {ι : Type*} [Fintype ι]
    (f : C(s, ι → ℝ)) {M : ℝ} (hM : 0 ≤ M) (hf : ∀ x : s, ‖f x‖ ≤ M) :
    ∃ G : C(X, ι → ℝ), (∀ x : s, G (x : X) = f x) ∧ ∀ y : X, ‖G y‖ ≤ M := by
  classical
  -- The `ℓ∞`-norm bound is the componentwise bound.
  have hf' : ∀ (x : s) (i : ι), |f x i| ≤ M := by
    intro x i
    have := (pi_norm_le_iff_of_nonneg hM).1 (hf x) i
    rwa [Real.norm_eq_abs] at this
  obtain ⟨G, hext, hbd⟩ := tietze_extension_pi_sup hs f hM hf'
  refine ⟨G, hext, fun y => ?_⟩
  rw [pi_norm_le_iff_of_nonneg hM]
  intro i
  rw [Real.norm_eq_abs]
  exact hbd y i

/-- **Sharp norm-preserving vector Tietze (finite-dimensional).**  Taking `M = ‖f‖` — but here
phrased as: any common `ℓ∞` bound `M` on the data is also a bound on the extension, and the
extension agrees with `f` on `s`.  Hence for the *least* such bound the extension preserves the
sup-norm exactly, `‖G‖ = ‖f‖`, on finite-dimensional codomains.  We record the clean
two-sided consequence: `G` extends `f` and shares every uniform `ℓ∞` bound. -/
theorem tietze_extension_pi_norm_sharp (hs : IsClosed s) {ι : Type*} [Fintype ι]
    (f : C(s, ι → ℝ)) {M : ℝ} (hM : 0 ≤ M) (hf : ∀ x : s, ‖f x‖ ≤ M) :
    ∃ G : C(X, ι → ℝ), (∀ x : s, G (x : X) = f x) ∧
      (∀ y : X, ‖G y‖ ≤ M) ∧ (∀ x : s, ‖G (x : X)‖ ≤ M) := by
  obtain ⟨G, hext, hbd⟩ := tietze_extension_pi_norm hs f hM hf
  exact ⟨G, hext, hbd, fun x => by rw [hext x]; exact hf x⟩

end TietzeIntervalVector
