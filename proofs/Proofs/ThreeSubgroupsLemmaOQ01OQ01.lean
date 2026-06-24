import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic
import Proofs.ThreeSubgroupsLemmaOQ01

/-
# Bilinear bound for the lower central series: `⁅γᵢ, γⱼ⁆ ≤ γ₍ᵢ₊ⱼ₎`

## What This Proves

For the lower central series `γ` of a group `G`, the commutator of two terms
sits inside a later term according to the **additive** rule

  `⁅γ_a, γ_b⁆ ≤ γ_{a+b+1}`   (Mathlib's `0`-indexed convention, `γ₀ = ⊤`).

In the classical `1`-indexed convention `G = G₁`, `G_{i+1} = ⁅G_i, G⁆`, where
`γ_n = G_{n+1}`, this is exactly the textbook statement

  `⁅G_i, G_j⁆ ≤ G_{i+j}`,

the central structural fact that makes the associated graded `⨁ γ_n / γ_{n+1}`
a graded Lie ring and underlies the theory of nilpotent groups.

## What Mathlib has — and what this adds

Mathlib (`Mathlib/GroupTheory/Nilpotent.lean`) develops the lower central series
and its basic API (`lowerCentralSeries_succ`, `lowerCentralSeries_antitone`,
the normality instance `lowerCentralSeries_normal`, …), but it does **not**
record this bilinear `⁅γ_a, γ_b⁆ ≤ γ_{a+b+1}` bound.  A search of the commutator
and nilpotency files turns up only the diagonal recursion `γ_{n+1} = ⁅γ_n, ⊤⁆`
and no cross-term estimate.

The proof is the classical induction on `b` (generalising `a`), whose engine is
the **three subgroups lemma**.  The base case is the defining recursion; the
inductive step writes `γ_{b+1} = ⁅γ_b, ⊤⁆`, applies the normal-subgroup form of
the three subgroups lemma proved in the parent entry
(`ThreeSubgroupsLemmaOQ01.commutator_le_of_rotate_symm`), and discharges its two
hypotheses from the induction hypothesis — one at `a`, one at the shifted index
`a + 1`.  This is precisely the use case for which the `≤ N` generalisation of
the three subgroups lemma (the parent's contribution over Mathlib's `= ⊥` form)
was built.

Verified: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/

namespace ThreeSubgroupsLemmaOQ01OQ01

open Subgroup ThreeSubgroupsLemmaOQ01

variable {G : Type*} [Group G]

/-- **Bilinear lower-central-series bound.**  In Mathlib's `0`-indexed convention
(`lowerCentralSeries G 0 = ⊤`), the commutator of the `a`-th and `b`-th terms of
the lower central series lands in the `(a+b+1)`-th term:

  `⁅γ_a, γ_b⁆ ≤ γ_{a+b+1}`.

Equivalently, in the classical `1`-indexed convention `γ_n = G_{n+1}` this is the
textbook filtration bound `⁅G_i, G_j⁆ ≤ G_{i+j}`.

Proved by induction on `b` (generalising `a`) using the parent entry's
three subgroups lemma (`commutator_le_of_rotate_symm`). -/
theorem commutator_lowerCentralSeries_le (a b : ℕ) :
    ⁅lowerCentralSeries G a, lowerCentralSeries G b⁆
      ≤ lowerCentralSeries G (a + b + 1) := by
  -- The defining recursion, in commutator form (`rfl`).  Mathlib's
  -- `lowerCentralSeries_succ` unfolds the bracket to a raw `closure` set, which
  -- does not rewrite against `⁅·, ⊤⁆`; this `rfl`-equation keeps it foldable.
  have hsucc : ∀ n : ℕ,
      lowerCentralSeries G (n + 1) = ⁅lowerCentralSeries G n, (⊤ : Subgroup G)⁆ :=
    fun _ => rfl
  induction b generalizing a with
  | zero =>
      -- `⁅γ_a, ⊤⁆ = γ_{a+1}`, and `a + 0 + 1 = a + 1` definitionally.
      rw [lowerCentralSeries_zero]
      exact le_of_eq (hsucc a).symm
  | succ b ih =>
      -- Unfold `γ_{b+1} = ⁅γ_b, ⊤⁆` and flip to outer-bracket form
      -- `⁅⁅γ_b, ⊤⁆, γ_a⁆ ≤ N`; the index `a + (b+1) + 1` is defeq `a + b + 1 + 1`.
      rw [hsucc b, commutator_comm (lowerCentralSeries G a) ⁅lowerCentralSeries G b, ⊤⁆]
      show ⁅⁅lowerCentralSeries G b, (⊤ : Subgroup G)⁆, lowerCentralSeries G a⁆
            ≤ lowerCentralSeries G (a + b + 1 + 1)
      -- Three subgroups lemma with `H = ⊤`, `K = γ_a`, `L = γ_b`,
      -- `N = γ_{a+b+1+1}` (normal as a lower-central-series term).
      refine commutator_le_of_rotate (H := ⊤) (K := lowerCentralSeries G a)
        (L := lowerCentralSeries G b) ?_ ?_
      · -- `⁅⁅⊤, γ_a⁆, γ_b⁆ ≤ N`: rewrite `⁅⊤, γ_a⁆ = γ_{a+1}`, then ih at `a+1`.
        rw [commutator_comm ⊤ (lowerCentralSeries G a), ← hsucc a]
        have e : (a + 1) + b + 1 = a + b + 1 + 1 := by omega
        exact e ▸ ih (a + 1)
      · -- `⁅⁅γ_a, γ_b⁆, ⊤⁆ ≤ N`: expand `N = ⁅γ_{a+b+1}, ⊤⁆`, monotonicity + ih at `a`.
        rw [hsucc (a + b + 1)]
        exact commutator_mono (ih a) le_rfl

end ThreeSubgroupsLemmaOQ01OQ01
