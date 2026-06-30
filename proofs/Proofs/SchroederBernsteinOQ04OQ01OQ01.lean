import Mathlib.Tactic
import Proofs.SchroederBernsteinOQ04OQ01

/-
# Semi-Decidable (Σ⁰₁) Presentation of the CBS Orbit Classification

## Open Question (OQ-04 ▸ OQ-01 ▸ sub-question 1)
The parent file `SchroederBernsteinOQ04OQ01` proves Cantor–Bernstein–Schroeder for
*arbitrary* types via the union-of-iterates reachable set
`reachableSet f g = ⋃ₙ (step f g)^[n] (baseSet g)`, and observes in its header that
the price of dropping finiteness is that the orbit classification
`a ∈ reachableSet f g` is no longer decidable, only **semi-decidable (Σ⁰₁)** —
"there is no a-priori bound on how many `step` iterations one must unfold."

This file makes that observation precise and proves it.

## What is proved

* **Section A — the Σ⁰₁ logical form.** `reachableSet f g` is, *definitionally*, an
  existential over the stage family `stage f g n := (step f g)^[n] (baseSet g)`:
  `a ∈ reachableSet f g ↔ ∃ n, a ∈ stage f g n`, and `reachableSet f g = ⋃ n, stage f g n`.
  The stages are monotone increasing. This is exactly the shape of a `Σ⁰₁`
  (semi-decidable) predicate: an existential quantifier over a uniformly described
  family of "approximation stages".

* **Section B — semi-decision halts on members.** Every member has a *least*
  certifying stage (`exists_least_stage`). This is the positive half of
  semi-decidability: a search that enumerates the stages will, for any genuine
  member, terminate at a finite stage — but it is given no information about
  non-members.

* **Section C — the decidability criterion.** If the stages ever become stationary
  (`stage f g N = stage f g (N+1)`), the union collapses:
  `reachableSet f g = stage f g N` (`reachableSet_eq_stage_of_stationary`). So
  membership is decidable as soon as a fixed point is reached. For a `Fintype` a
  fixed point must occur (a strictly increasing chain of subsets of a finite type
  cannot run forever) — recovering the parent's finite, decidable case. The *only*
  obstruction to decidability is therefore the failure of stabilization, i.e. an
  unbounded search.

* **Section D — the search is genuinely unbounded.** With `α = β = ℕ` and
  `f = g = Nat.succ` (the shift embeddings of the parent header's example), the
  stages strictly grow forever: `stage Nat.succ Nat.succ N = {0, 2, …, 2N}`, so the
  least certifying stage of `2N` is exactly `N`. Hence:
  - `unbounded_search`: for every bound `N` there is a member (`2(N+1)`) not yet
    certified at stage `N`;
  - `stage_succ_ne`: no stage is ever stationary, so the criterion of Section C is
    *never* met here.
  This is the formal content of "no a-priori bound on the number of iterations":
  the Σ⁰₁ presentation cannot be collapsed to a single bounded (decidable-by-fixed-`N`)
  test.

## Honesty note
"Semi-decidable / Σ⁰₁" is captured here as its precise *logical form* — an
existential over a uniform stage family with the least-witness property — together
with the proof that the search is genuinely unbounded. A fully computability-theoretic
`RePred` statement would additionally require the injections `f`, `g` (and the
membership `· ∈ range g`) to be effectively given; that is an orthogonal hypothesis
not present in the parent's purely set-theoretic construction, and is *not* claimed
here. In the concrete `ℕ`-shift instance membership happens to be decidable (it is
the even numbers); what is unbounded — and what genuinely fails to stabilise — is the
*stage-bounded* search, which is the mechanism behind the Σ⁰₁ presentation.

## Status
- [x] Complete proof (0 sorries, 0 `axiom` declarations)
- [x] Builds on the parent's union-of-iterates construction with no new assumptions
-/

set_option linter.unusedSectionVars false

namespace CBSInfinite

variable {α β : Type*}

/-! ## Stage family: the finite approximations of the reachable set -/

/-- The `n`-th approximation stage: the reachable set unfolded to depth `n`.
    `reachableSet f g` is the union of all stages. -/
def stage (f : α → β) (g : β → α) (n : ℕ) : Set α :=
  (step f g)^[n] (baseSet g)

theorem stage_zero (f : α → β) (g : β → α) : stage f g 0 = baseSet g := rfl

/-- One stage is obtained from the previous by a single `step`. -/
theorem step_stage (f : α → β) (g : β → α) (n : ℕ) :
    stage f g (n + 1) = step f g (stage f g n) := by
  unfold stage
  rw [Function.iterate_succ_apply']

/-! ## Section A: the Σ⁰₁ logical form -/

/-- **The Σ⁰₁ presentation.** Membership in `reachableSet` is, definitionally, an
    existential over the uniformly described stage family. This is precisely the
    shape of a semi-decidable predicate. -/
theorem mem_reachable_iff_exists_stage (f : α → β) (g : β → α) (a : α) :
    a ∈ reachableSet f g ↔ ∃ n, a ∈ stage f g n := Iff.rfl

/-- The reachable set is the countable union of its stages. -/
theorem reachableSet_eq_iUnion (f : α → β) (g : β → α) :
    reachableSet f g = ⋃ n, stage f g n := by
  ext a
  simp only [reachableSet, stage, Set.mem_setOf_eq, Set.mem_iUnion]

/-- Consecutive stages are nested. -/
theorem stage_subset_succ (f : α → β) (g : β → α) (n : ℕ) :
    stage f g n ⊆ stage f g (n + 1) :=
  iter_subset_succ f g n

/-- The stage family is monotone in the depth. -/
theorem stage_mono (f : α → β) (g : β → α) : Monotone (stage f g) :=
  monotone_nat_of_le_succ (fun n => stage_subset_succ f g n)

/-! ## Section B: semi-decision halts on members -/

/-- **Positive half of semi-decidability.** Every member of the reachable set is
    certified at some *least* finite stage: a search enumerating the stages halts on
    every genuine member. (It is told nothing about non-members — that is the whole
    point of `Σ⁰₁`.) -/
theorem exists_least_stage {f : α → β} {g : β → α} {a : α}
    (h : a ∈ reachableSet f g) :
    ∃ N, a ∈ stage f g N ∧ ∀ m, a ∈ stage f g m → N ≤ m := by
  classical
  exact ⟨Nat.find h, Nat.find_spec h, fun m hm => Nat.find_min' h hm⟩

/-! ## Section C: the decidability criterion -/

/-- Once two consecutive stages coincide, the family is constant from there on. -/
theorem stage_const_of_stationary (f : α → β) (g : β → α) (N : ℕ)
    (h : stage f g N = stage f g (N + 1)) :
    ∀ k, stage f g (N + k) = stage f g N := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have e1 : N + (k + 1) = (N + k) + 1 := by ring
    rw [e1, step_stage f g (N + k), ih, ← step_stage f g N, ← h]

/-- A stationary point propagates to all later indices. -/
theorem stage_eq_of_ge (f : α → β) (g : β → α) (N : ℕ)
    (h : stage f g N = stage f g (N + 1)) {n : ℕ} (hn : N ≤ n) :
    stage f g n = stage f g N := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact stage_const_of_stationary f g N h k

/-- **Decidability criterion.** If the stages become stationary at `N`, the whole
    reachable set is just `stage f g N` — a single, bounded, decidable approximation.
    The unbounded existential collapses to a finite one exactly when a fixed point of
    `step` is reached. For a `Fintype` this always happens (the stages form a
    strictly increasing chain of subsets, which must terminate), recovering the
    parent's decidable finite case. -/
theorem reachableSet_eq_stage_of_stationary (f : α → β) (g : β → α) (N : ℕ)
    (h : stage f g N = stage f g (N + 1)) :
    reachableSet f g = stage f g N := by
  rw [reachableSet_eq_iUnion]
  apply Set.eq_of_subset_of_subset
  · apply Set.iUnion_subset
    intro n
    rcases le_total n N with hn | hn
    · exact stage_mono f g hn
    · exact (stage_eq_of_ge f g N h hn).le
  · exact Set.subset_iUnion (stage f g) N

/-! ## Section D: the search is genuinely unbounded (the `ℕ`-shift instance)

We instantiate the construction at the parent header's own example: `α = β = ℕ`,
`f = g = Nat.succ`. Here `baseSet = {0}` and `step S = S ∪ (·+2) '' S`, so the
stages are the truncated evens `{0, 2, …, 2N}`. The least certifying stage of `2N`
is exactly `N`, which grows without bound: the Σ⁰₁ search has no uniform cutoff. -/

/-- For the shift `g = Nat.succ`, the only element with no preimage is `0`. -/
theorem baseSet_succ : baseSet Nat.succ = {0} := by
  ext a
  simp only [baseSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · exact h0
    · exact absurd (by omega : Nat.succ (a - 1) = a) (h (a - 1))
  · rintro rfl b
    exact Nat.succ_ne_zero b

/-- Every element of stage `n` of the shift instance is at most `2n`. -/
theorem mem_stage_succ_le {n m : ℕ} (hm : m ∈ stage Nat.succ Nat.succ n) :
    m ≤ 2 * n := by
  induction n generalizing m with
  | zero =>
    rw [stage_zero, baseSet_succ, Set.mem_singleton_iff] at hm
    omega
  | succ n ih =>
    rw [step_stage] at hm
    simp only [step, Set.mem_union, Set.mem_image] at hm
    rcases hm with h | ⟨x, hx, rfl⟩
    · have := ih h; omega
    · have := ih hx; omega

/-- The even number `2n` is reached at stage `n`. -/
theorem two_mul_mem_stage (n : ℕ) : 2 * n ∈ stage Nat.succ Nat.succ n := by
  induction n with
  | zero =>
    rw [stage_zero, baseSet_succ]
    simp
  | succ n ih =>
    rw [step_stage]
    simp only [step, Set.mem_union, Set.mem_image]
    exact Or.inr ⟨2 * n, ih, by omega⟩

/-- Hence `2n` is in the reachable set. -/
theorem two_mul_mem_reachable (n : ℕ) :
    2 * n ∈ reachableSet Nat.succ Nat.succ :=
  ⟨n, two_mul_mem_stage n⟩

/-- **The search is genuinely unbounded.** For every bound `N` there is a member of
    the reachable set — namely `2(N+1)` — that is not yet certified at stage `N`. No
    fixed number of iterations suffices uniformly: this is the precise sense of "no
    a-priori bound" from the parent header. -/
theorem unbounded_search (N : ℕ) :
    ∃ a, a ∈ reachableSet Nat.succ Nat.succ ∧ a ∉ stage Nat.succ Nat.succ N := by
  refine ⟨2 * (N + 1), two_mul_mem_reachable (N + 1), ?_⟩
  intro h
  have := mem_stage_succ_le h
  omega

/-- **No stationary point ever occurs** in the shift instance: the criterion of
    `reachableSet_eq_stage_of_stationary` is never satisfied, so the reachable set is
    not equal to any single stage. The stages strictly grow forever. -/
theorem stage_succ_ne (N : ℕ) :
    stage Nat.succ Nat.succ N ≠ stage Nat.succ Nat.succ (N + 1) := by
  intro h
  have hmem : 2 * (N + 1) ∈ stage Nat.succ Nat.succ N := by
    rw [h]; exact two_mul_mem_stage (N + 1)
  have := mem_stage_succ_le hmem
  omega

/-- Consequently the reachable set of the shift instance differs from every stage:
    the unbounded union does not collapse. -/
theorem reachableSet_ne_stage (N : ℕ) :
    reachableSet Nat.succ Nat.succ ≠ stage Nat.succ Nat.succ N := by
  intro h
  obtain ⟨a, ha_mem, ha_not⟩ := unbounded_search N
  rw [h] at ha_mem
  exact ha_not ha_mem

end CBSInfinite
