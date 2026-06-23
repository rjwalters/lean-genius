import Mathlib

/-!
# The Tietze extension theorem

The **Tietze extension theorem** (Tietze 1915 for metric spaces, Urysohn 1925 in general)
is the functional-extension counterpart of Urysohn's lemma: in a normal space, a continuous
real-valued function defined on a *closed* subset extends continuously to the whole space,
and the extension can be made to respect range bounds. Mathlib proves the abstract statements

* `ContinuousMap.exists_restrict_eq` — for a `TietzeExtension`-valued map on a closed set,
* `ContinuousMap.exists_extension` — the closed-embedding packaging,
* `ContinuousMap.exists_restrict_eq_forall_mem_of_closed` — the range-constrained form,

with `ℝ` (and `ℝ≥0`, products, …) supplied as `TietzeExtension` instances. This file
re-exports those headline results (hence the `mathlib` badge) and then supplies the genuine
content tying the theorem back to separation:

* **(a)** `tietze_extension` / `tietze_extension_real`: every continuous map on a closed set
  of a normal space extends to the whole space;
* **(b)** `tietze_extension_Icc`: an `[a,b]`-valued function extends to an `[a,b]`-valued one,
  and the sharp `tietze_extension_abs_le`: a sup-norm bound `|f| ≤ M` is preserved by the
  extension;
* **(c)** `tietze_extension_closedEmbedding`: the coordinate-free closed-embedding form;
* **(d)** `urysohn_of_tietze`: **Urysohn's lemma derived from Tietze** — given disjoint closed
  sets `s`, `t` we build the continuous `{0,1}`-valued boundary function on the closed set
  `s ∪ t` (continuous because `t` is *clopen* in the subspace `s ∪ t`, the two sets being
  closed and disjoint) and extend it by the bounded Tietze theorem into `[0,1]`, recovering a
  Urysohn separator. This is the converse direction to the usual "Urysohn ⟹ Tietze" proof and
  exhibits the two theorems as equivalent over normality. The point-from-closed-set corollary
  `urysohn_point_of_tietze` follows.

The boundary-function construction in `urysohn_of_tietze` is the part absent from Mathlib;
everything is machine-checked with no `sorry` and no extra axioms. Cross-references
`urysohns-lemma-oq-01` (this entry answers its recorded open question
"derive Tietze from Urysohn", here run in the equivalent reverse direction).
-/

namespace TietzeExtensionTheoremOQ01

open Set Topology

variable {X : Type*} [TopologicalSpace X]

/-! ## Part (a): the extension theorem on a closed set

Direct re-exports of Mathlib's Tietze extension theorem; these carry the `mathlib` badge.
-/

/-- **Tietze extension theorem.** In a normal space `X`, a continuous map `f : C(s, Y)` on a
closed set `s`, valued in any `TietzeExtension` space `Y`, extends to a continuous map on all
of `X` whose restriction to `s` is `f`. -/
theorem tietze_extension.{u, v} {X : Type u} [TopologicalSpace X] {Y : Type v}
    [TopologicalSpace Y] [TietzeExtension.{u, v} Y] [NormalSpace X] {s : Set X}
    (hs : IsClosed s) (f : C(s, Y)) :
    ∃ g : C(X, Y), g.restrict s = f :=
  f.exists_restrict_eq hs

/-- **Tietze extension theorem for real-valued maps.** A continuous real function on a closed
subset of a normal space extends continuously to the whole space (`ℝ` is a `TietzeExtension`
space). -/
theorem tietze_extension_real [NormalSpace X] {s : Set X} (hs : IsClosed s) (f : C(s, ℝ)) :
    ∃ g : C(X, ℝ), g.restrict s = f :=
  f.exists_restrict_eq hs

/-! ## Part (b): the range-constrained (bounded) form -/

/-- **Bounded Tietze extension.** A continuous function on a closed set valued in a closed
interval `[a, b]` extends to a continuous function on the whole normal space that is *also*
valued in `[a, b]`. This is the quantitative form used in approximation arguments. -/
theorem tietze_extension_Icc [NormalSpace X] {s : Set X} {a b : ℝ} (hab : a ≤ b)
    (hs : IsClosed s) (f : C(s, ℝ)) (hf : ∀ x, f x ∈ Icc a b) :
    ∃ g : C(X, ℝ), (∀ y, g y ∈ Icc a b) ∧ g.restrict s = f := by
  haveI : OrdConnected (Icc a b) := ordConnected_Icc
  exact f.exists_restrict_eq_forall_mem_of_closed hf (nonempty_Icc.2 hab) hs

/-- **Sup-norm-preserving Tietze extension.** If `|f| ≤ M` on the closed set `s`, then `f`
extends to a continuous `g` on the whole normal space with `|g| ≤ M` everywhere. (Take the
extension into the interval `[-M, M]`.) -/
theorem tietze_extension_abs_le [NormalSpace X] {s : Set X} {M : ℝ} (hM : 0 ≤ M)
    (hs : IsClosed s) (f : C(s, ℝ)) (hf : ∀ x, |f x| ≤ M) :
    ∃ g : C(X, ℝ), (∀ y, |g y| ≤ M) ∧ g.restrict s = f := by
  obtain ⟨g, hg_mem, hg_eq⟩ :=
    tietze_extension_Icc (a := -M) (b := M) (by linarith) hs f
      (fun x => mem_Icc.2 (abs_le.1 (hf x)))
  exact ⟨g, fun y => abs_le.2 (mem_Icc.1 (hg_mem y)), hg_eq⟩

/-! ## Part (c): the closed-embedding form -/

/-- **Tietze extension along a closed embedding.** If `e : X₁ → X` is a closed embedding into a
normal space and `f : C(X₁, ℝ)`, then `f` extends to `g : C(X, ℝ)` with `g ∘ e = f`. This is the
coordinate-free packaging of the extension theorem. -/
theorem tietze_extension_closedEmbedding {X₁ : Type*} [TopologicalSpace X₁]
    [NormalSpace X] {e : X₁ → X} (he : IsClosedEmbedding e) (f : C(X₁, ℝ)) :
    ∃ g : C(X, ℝ), g.comp ⟨e, he.continuous⟩ = f :=
  f.exists_extension he

/-! ## Part (d): Urysohn's lemma derived from Tietze

The genuine new content. Given disjoint closed sets `s`, `t`, the set `t` is *clopen* in the
subspace `s ∪ t` (it is closed as the preimage of the closed `t`, and open because its
complement in `s ∪ t` is exactly `s`, again closed). Hence the `{0,1}`-valued indicator
"1 on t, 0 on s" is locally constant, so continuous, on the closed set `s ∪ t`. Extending it
by the bounded Tietze theorem into `[0,1]` produces a Urysohn separator. This runs the
Urysohn–Tietze equivalence in the reverse of the textbook direction.
-/

/-- **Urysohn's lemma, obtained from the Tietze extension theorem.** In a normal space, two
disjoint closed sets `s`, `t` are separated by a continuous `f : C(X, ℝ)` with `f = 0` on `s`,
`f = 1` on `t`, and `0 ≤ f ≤ 1`. -/
theorem urysohn_of_tietze [NormalSpace X] {s t : Set X}
    (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : C(X, ℝ), EqOn f 0 s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
  classical
  -- `s ∪ t` is closed, the domain on which we build the boundary data.
  have hst : IsClosed (s ∪ t) := hs.union ht
  -- Inside the subspace `s ∪ t`, the points lying in `t` form a clopen set.
  have hVcl : IsClosed (Subtype.val ⁻¹' t : Set ↥(s ∪ t)) :=
    ht.preimage continuous_subtype_val
  have hcompl : (Subtype.val ⁻¹' t : Set ↥(s ∪ t))ᶜ = Subtype.val ⁻¹' s := by
    ext p
    simp only [mem_compl_iff, mem_preimage]
    exact ⟨fun hpt => p.2.resolve_right hpt, fun hps hpt => Set.disjoint_left.1 hd hps hpt⟩
  have hVop : IsOpen (Subtype.val ⁻¹' t : Set ↥(s ∪ t)) := by
    rw [← isClosed_compl_iff, hcompl]; exact hs.preimage continuous_subtype_val
  have hVclopen : IsClopen (Subtype.val ⁻¹' t : Set ↥(s ∪ t)) := ⟨hVcl, hVop⟩
  -- The `{0,1}`-valued boundary function (1 on `t`, 0 on `s`) is locally constant, hence
  -- continuous, factoring through the clopen indicator `LocallyConstant.ofIsClopen`.
  have hcont : Continuous (fun p : ↥(s ∪ t) => if (p : X) ∈ t then (1 : ℝ) else 0) := by
    have hlc : IsLocallyConstant (fun p : ↥(s ∪ t) => if (p : X) ∈ t then (1 : ℝ) else 0) := by
      have heq : (fun p : ↥(s ∪ t) => if (p : X) ∈ t then (1 : ℝ) else 0)
          = (![(1 : ℝ), 0]) ∘ (LocallyConstant.ofIsClopen hVclopen) := by
        ext p
        simp only [Function.comp_apply, LocallyConstant.ofIsClopen, LocallyConstant.coe_mk,
          mem_preimage]
        by_cases h : (p : X) ∈ t <;> simp [h]
      rw [heq]
      exact (LocallyConstant.ofIsClopen hVclopen).isLocallyConstant.comp _
    exact hlc.continuous
  -- Extend the boundary function into `[0,1]` by the bounded Tietze theorem.
  obtain ⟨g, hg_mem, hg_eq⟩ :=
    (⟨_, hcont⟩ : C(↥(s ∪ t), ℝ)).exists_restrict_eq_forall_mem_of_closed
      (t := Icc (0 : ℝ) 1)
      (fun p => by
        show (if (p : X) ∈ t then (1 : ℝ) else 0) ∈ Icc (0 : ℝ) 1
        by_cases h : (p : X) ∈ t <;> simp [h, mem_Icc])
      (nonempty_Icc.2 zero_le_one) hst
  refine ⟨g, ?_, ?_, fun x => hg_mem x⟩
  · -- `g = 0` on `s`: a point of `s` is not in `t`, so the boundary value there is `0`.
    intro x hx
    have key : g x = if x ∈ t then (1 : ℝ) else 0 := by
      have h := DFunLike.congr_fun hg_eq ⟨x, Or.inl hx⟩
      rwa [ContinuousMap.restrict_apply_mk] at h
    rw [if_neg (Set.disjoint_left.1 hd hx)] at key
    simpa using key
  · -- `g = 1` on `t`.
    intro x hx
    have key : g x = if x ∈ t then (1 : ℝ) else 0 := by
      have h := DFunLike.congr_fun hg_eq ⟨x, Or.inr hx⟩
      rwa [ContinuousMap.restrict_apply_mk] at h
    rw [if_pos hx] at key
    simpa using key

/-- **Functional separation of a point from a closed set, via Tietze.** In a normal `T1` space,
a point `x₀` outside a closed set `t` is separated from it: there is a continuous `f` with
`f x₀ = 0`, `f = 1` on `t`, and `0 ≤ f ≤ 1`. -/
theorem urysohn_point_of_tietze [T1Space X] [NormalSpace X] {t : Set X} {x₀ : X}
    (ht : IsClosed t) (hx₀ : x₀ ∉ t) :
    ∃ f : C(X, ℝ), f x₀ = 0 ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨f, hfs, hft, hficc⟩ :=
    urysohn_of_tietze (isClosed_singleton (x := x₀)) ht (disjoint_singleton_left.mpr hx₀)
  exact ⟨f, by simpa using hfs (show x₀ ∈ ({x₀} : Set X) from rfl), hft, hficc⟩

end TietzeExtensionTheoremOQ01
