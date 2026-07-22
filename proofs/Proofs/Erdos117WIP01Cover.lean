/-
  Erdős Problem #117 — Covering Groups by Abelian Subgroups:
  cyclic covers and the structure of the covering set (0-axiom).

  Companion to `Erdos117Problem.lean` / `Erdos117WIP01.lean` /
  `Erdos117WIP01Mono.lean`.  The parent defines
  `h(n) = abelianCoverNumber n = sInf {k | CoversWithAbelian k n}` where
  `CoversWithAbelian k n` (from the `Mono` companion) says `k` abelian subgroups
  cover *every* finite group with the `n`-commuting property; Pyber's exponential
  bounds `c₁ⁿ < h(n) < c₂ⁿ` are stated only in prose.  Prior companions pin
  `h(0) = 0`, `h(1) = 1`, the closure theory of the property, and monotonicity of
  `h` in `n`.

  This file adds two elementary pieces of the covering theory.

  **1. Every group is a union of abelian (cyclic) subgroups.**  The single-element
  subgroup `zpowers g` is abelian, and `g ∈ zpowers g`, so the family
  `g ↦ zpowers g` covers `G` by abelian subgroups — *unconditionally*, for any
  group.  This is the qualitative fact behind #117: the covering number `h(n)`
  measures only *how many* abelian subgroups are needed uniformly, never *whether*
  a cover exists for a fixed group (one always does, of size `≤ |G|`).

  **2. The covering set `{k | CoversWithAbelian k n}` is a terminal segment.**
  It is upward closed in `k` (pad a `k`-cover with copies of `⊥`), and — for
  `n ≥ 1` — never contains `0` (the empty family cannot cover the nontrivial
  witness `PUnit`).  Together with `Nat.sInf_mem` (the `Mono` companion) this
  characterises the set as `[h(n), ∞)` whenever it is nonempty, and gives the
  general lower bound `1 ≤ h(n)` for every `n ≥ 1` at which `h(n)` is
  well-defined.

  Main results (all axiom-free — `#print axioms` = propext/Classical.choice/Quot.sound):

  * `isAbelianSubgroup_zpowers`     : the cyclic subgroup `zpowers g` is abelian.
  * `exists_cyclic_abelian_cover`   : every group is covered by abelian (cyclic)
                                      subgroups (the family `g ↦ zpowers g`).
  * `coversWithAbelian_upward`      : `CoversWithAbelian · n` is upward closed in `k`.
  * `not_coversWithAbelian_zero`    : for `n ≥ 1`, `0` abelian subgroups never cover.
  * `one_le_abelianCoverNumber`     : for `n ≥ 1`, if `h(n)` is well-defined
                                      (the covering set is nonempty) then `h(n) ≥ 1`.

  The open Erdős #117 (the exact exponential base) and Pyber's bounds are untouched.

  0 axioms, 0 sorries.
-/

import Mathlib
import Proofs.Erdos117Problem
import Proofs.Erdos117WIP01
import Proofs.Erdos117WIP01Mono

universe u

/-- **Cyclic subgroups are abelian.**  Any two elements of `Subgroup.zpowers g`
    are powers `g ^ a, g ^ b` of the single generator `g`, and powers of a fixed
    element commute: `g ^ a * g ^ b = g ^ (a + b) = g ^ (b + a) = g ^ b * g ^ a`. -/
theorem isAbelianSubgroup_zpowers {G : Type*} [Group G] (g : G) :
    IsAbelianSubgroup G (Subgroup.zpowers g) := by
  intro x y hx hy
  rw [Subgroup.mem_zpowers_iff] at hx hy
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  rw [← zpow_add, ← zpow_add, add_comm]

/-- **Every group is covered by abelian (cyclic) subgroups.**  The family
    `g ↦ Subgroup.zpowers g` consists of abelian subgroups
    (`isAbelianSubgroup_zpowers`) and covers `G`, since `g ∈ Subgroup.zpowers g`
    for every `g`.  A cover therefore always exists for a *fixed* group — of size
    at most `|G|` when `G` is finite — so the content of `h(n)` is the *uniform*
    count over all groups with the `n`-commuting property, never mere existence. -/
theorem exists_cyclic_abelian_cover {G : Type*} [Group G] :
    ∃ H : G → Subgroup G,
      (∀ i, IsAbelianSubgroup G (H i)) ∧ ∀ g : G, ∃ i, g ∈ H i :=
  ⟨fun i => Subgroup.zpowers i, fun i => isAbelianSubgroup_zpowers i,
    fun g => ⟨g, Subgroup.mem_zpowers g⟩⟩

/-- **The covering set is upward closed in `k`.**  If `k` abelian subgroups cover
    every finite group with the `n`-commuting property, then so do any `k' ≥ k`:
    extend the covering family `H : Fin k → Subgroup G` to `Fin k'` by sending the
    extra indices to the (abelian) trivial subgroup `⊥`.  The original cover still
    reaches every element, and every subgroup in the extended family is abelian. -/
theorem coversWithAbelian_upward {k k' n : ℕ} (hk : k ≤ k')
    (h : CoversWithAbelian.{u} k n) : CoversWithAbelian.{u} k' n := by
  intro G _ _ hn
  obtain ⟨H, hAb, hCov⟩ := h G hn
  refine ⟨fun j => if hj : (j : ℕ) < k then H ⟨j, hj⟩ else ⊥, ?_, ?_⟩
  · intro j
    by_cases hj : (j : ℕ) < k
    · simp only [hj, dif_pos]; exact hAb _
    · simp only [hj, dif_neg, not_false_iff]; exact isAbelianSubgroup_bot
  · intro g
    obtain ⟨i, hi⟩ := hCov g
    have hlt : (i : ℕ) < k' := lt_of_lt_of_le i.2 hk
    refine ⟨⟨i, hlt⟩, ?_⟩
    -- beta-reduce the family application, then take the `< k` branch; the
    -- resulting index `⟨↑i, i.2⟩` is defeq to `i` (structure eta), so `hi` closes it.
    dsimp only
    rw [dif_pos i.2]
    exact hi

/-- **`0` abelian subgroups never cover, for any threshold `n ≥ 1`.**  The empty
    family `Fin 0 → Subgroup G` covers nothing, yet the commutative witness group
    `PUnit` has the `n`-commuting property for every `n ≥ 1`
    (`commGroup_hasNCommutingProperty`).  So `CoversWithAbelian 0 n` would force a
    cover of `PUnit.unit` by no subgroups — impossible. -/
theorem not_coversWithAbelian_zero {n : ℕ} (hn : 1 ≤ n) :
    ¬ CoversWithAbelian.{u} 0 n := by
  intro h
  obtain ⟨H, _, hCov⟩ := h PUnit (commGroup_hasNCommutingProperty hn)
  obtain ⟨i, _⟩ := hCov PUnit.unit
  exact i.elim0

/-- **General lower bound `h(n) ≥ 1` for `n ≥ 1`.**  Whenever `h(n)` is genuinely
    well-defined — i.e. the covering set is nonempty rather than the `sInf ∅ = 0`
    fallback — it is at least `1`, because `0` is never in the covering set
    (`not_coversWithAbelian_zero`).  This complements `h(0) = 0`: the covering
    number leaves `0` exactly at the `n = 0 → 1` step.  (For `n = 1` the set is
    nonempty, recovering `abelianCoverNumber_one`'s lower half; for larger `n`,
    nonemptiness of the set is exactly Pyber's unformalized upper bound.) -/
theorem one_le_abelianCoverNumber {n : ℕ} (hn : 1 ≤ n)
    (hne : ∃ k, CoversWithAbelian.{u} k n) :
    1 ≤ abelianCoverNumber.{u} n := by
  rw [abelianCoverNumber_eq_sInf, Nat.one_le_iff_ne_zero, Ne, Nat.sInf_eq_zero]
  push_neg
  exact ⟨not_coversWithAbelian_zero hn, hne⟩
