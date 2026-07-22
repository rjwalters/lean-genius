/-
  Erdős Problem #117 — Covering Groups by Abelian Subgroups: monotonicity of h(n).

  Companion to `Erdos117Problem.lean` / `Erdos117WIP01.lean`.  The parent defines
  `h(n) = abelianCoverNumber n = sInf {k | every finite group with the n-commuting
  property is covered by k abelian subgroups}` and states Pyber's exponential
  bounds `c₁ⁿ < h(n) < c₂ⁿ` only in prose.  `Erdos117WIP01.lean` pins the base
  values `h(0) = 0`, `h(1) = 1` and the closure theory of the property.

  This file adds the elementary **structural monotonicity** of `h` in `n`.  The
  `n`-commuting property is *weaker* for larger `n` (`hasNCommutingProperty_mono`),
  so the class of groups constrained by the covering condition *grows* with `n`.
  Hence a fixed budget of `k` abelian subgroups that covers every group with the
  `m`-property (`m ≥ n`) a fortiori covers every group with the `n`-property:
  `CoversWithAbelian k m → CoversWithAbelian k n`.  Passing to the `sInf`, `h` is
  monotone nondecreasing — **whenever the larger index admits a finite cover at
  all** (the honest hypothesis, since the unconditional well-definedness of `h(m)`
  is exactly Pyber's unformalized upper bound; with the `Nat.sInf ∅ = 0`
  convention, an ill-defined `h(m) = 0` would otherwise defeat monotonicity).

  Main results (all axiom-free — `#print axioms` = propext/Classical.choice/Quot.sound):

  * `CoversWithAbelian k n`          : the membership condition of `abelianCoverNumber`'s
                                       defining set, named for reuse.
  * `abelianCoverNumber_eq_sInf`     : `h(n) = sInf {k | CoversWithAbelian k n}` (`rfl`).
  * `coversWithAbelian_of_le`        : a cover for the `m`-property is a cover for the
                                       `n`-property when `n ≤ m` (the crux — uses
                                       `hasNCommutingProperty_mono`).
  * `abelianCoverNumber_mono`        : `n ≤ m` and a finite `m`-cover exists ⟹
                                       `h(n) ≤ h(m)`.

  The open Erdős #117 (the exact exponential base) and Pyber's bounds are untouched.

  0 axioms, 0 sorries.
-/

import Mathlib
import Proofs.Erdos117Problem
import Proofs.Erdos117WIP01

/- The universe of the ambient groups.  `abelianCoverNumber` is
   universe-polymorphic in this parameter (its body quantifies `∀ (G : Type*)`),
   and — because the value is an `sInf` over the class of groups in that universe
   — the statements below fix `u` explicitly so every occurrence lives in the
   *same* universe.  (Mixing universes yields the `abelianCoverNumber.{u_1}` vs
   `.{u_3}` application-type mismatch.) -/
universe u

/-- **The covering condition, named.**  `CoversWithAbelian k n` holds when `k`
    abelian subgroups suffice to cover *every* finite group (in universe `u`) with
    the `n`-commuting property.  This is exactly the membership predicate of the
    set whose `sInf` defines `abelianCoverNumber.{u} n`. -/
def CoversWithAbelian (k n : ℕ) : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G],
    HasNCommutingProperty G n →
    ∃ H : Fin k → Subgroup G,
      (∀ i, IsAbelianSubgroup G (H i)) ∧ ∀ g : G, ∃ i, g ∈ H i

/-- `abelianCoverNumber.{u} n` is the `sInf` of the `CoversWithAbelian.{u} · n`
    set — definitionally, since `CoversWithAbelian k n` unfolds to the set's
    condition at the same universe `u`. -/
theorem abelianCoverNumber_eq_sInf (n : ℕ) :
    abelianCoverNumber.{u} n = sInf {k | CoversWithAbelian.{u} k n} := rfl

/-- **A cover for the harder (larger `n`) constraint covers the easier one.**
    If `n ≤ m` and `k` abelian subgroups cover every finite group with the
    `m`-commuting property, then they cover every finite group with the
    `n`-commuting property: the `n`-property *implies* the `m`-property
    (`hasNCommutingProperty_mono`), so any `n`-property group is already handled. -/
theorem coversWithAbelian_of_le {k n m : ℕ} (hnm : n ≤ m)
    (h : CoversWithAbelian.{u} k m) : CoversWithAbelian.{u} k n := by
  intro G _ _ hn
  exact h G (hasNCommutingProperty_mono hnm hn)

/-- **Monotonicity of the covering number.**  For `n ≤ m`, if some finite budget
    of abelian subgroups covers every group with the `m`-commuting property
    (`∃ k, CoversWithAbelian k m` — the defining set is nonempty, i.e. `h(m)` is
    genuinely well-defined rather than the `sInf ∅ = 0` fallback), then
    `h(n) ≤ h(m)`.

    Proof: the defining set for `m` is `⊆` that for `n` (`coversWithAbelian_of_le`);
    `h(m)`, being its `sInf` and the set nonempty, is a member, hence a member of
    the `n`-set, so `h(n) = sInf(n-set) ≤ h(m)`. -/
theorem abelianCoverNumber_mono {n m : ℕ} (hnm : n ≤ m)
    (hne : ∃ k, CoversWithAbelian.{u} k m) :
    abelianCoverNumber.{u} n ≤ abelianCoverNumber.{u} m := by
  have hsub : {k | CoversWithAbelian.{u} k m} ⊆ {k | CoversWithAbelian.{u} k n} :=
    fun _ hk => coversWithAbelian_of_le hnm hk
  have hneSet : {k | CoversWithAbelian.{u} k m}.Nonempty := hne
  have hmem : abelianCoverNumber.{u} m ∈ {k | CoversWithAbelian.{u} k m} :=
    Nat.sInf_mem hneSet
  exact Nat.sInf_le (hsub hmem)
