import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Tactic

/-
# The bilinear lower-central-series bound `⁅γᵢ, γⱼ⁆ ≤ γ₍ᵢ₊ⱼ₊₁₎`

## What This Proves

For the lower central series `γₖ = lowerCentralSeries G k` of an arbitrary group `G`,
the iterated commutator of two terms drops at least as far as the *sum* of their
indices:

  `⁅lowerCentralSeries G i, lowerCentralSeries G j⁆ ≤ lowerCentralSeries G (i + j + 1)`.

This is the classical bilinearity estimate for the lower central series.  It is the
multiplicative engine behind nilpotency arithmetic: it controls how commutators of
deep terms land even deeper, and it specialises to the standard `[γᵢ, γⱼ] ⊆ γ₍ᵢ₊ⱼ₎`
in the `γ₁ = G` indexing convention (Mathlib uses `γ₀ = G`, which shifts the bound
by one, hence the `+1`).

The proof is an induction on `j` (uniform in `i`) whose inductive step is *exactly*
the three subgroups lemma applied to `H = γⱼ`, `K = ⊤`, `L = γᵢ`, with the normal
subgroup `N = γ₍ᵢ₊ⱼ₊₂₎`.  This is the application for which the parent entry
`three-subgroups-lemma-oq-01` proved the normal-subgroup form
`commutator_le_of_rotate`; that lemma is reproduced here (its short quotient proof)
so the file is self-contained.

## What Mathlib has — and what this adds

Mathlib develops the lower central series (`Mathlib/GroupTheory/Nilpotent.lean`)
with `lowerCentralSeries_succ`, `lowerCentralSeries_antitone`, the normality
instance `lowerCentralSeries_normal`, and the *linear* bound
`derived_le_lower_central : derivedSeries G n ≤ lowerCentralSeries G n`.  It does
**not** record the *bilinear* estimate `⁅γᵢ, γⱼ⁆ ≤ γ₍ᵢ₊ⱼ₊₁₎`.  A search of the
group-theory commutator and nilpotency files turns up only the one-sided
`lowerCentralSeries_succ = ⁅γₙ, ⊤⁆` recursion, never the two-index product bound.

As a headline consequence we obtain the **exponentially sharp** derived-series
estimate

  `derivedSeries G n ≤ lowerCentralSeries G (2 ^ n - 1)`,

which strictly strengthens Mathlib's `derived_le_lower_central` (index `n`) to
index `2ⁿ − 1`.  The proof is a clean two-line induction once the bilinear bound is
available — illustrating exactly why the bound is worth isolating.

Verified: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/

namespace ThreeSubgroupsLemmaOQ0101

open Subgroup

variable {G : Type*} [Group G]

/-! ## The three subgroups lemma (normal-subgroup form)

This is the result proved in the parent entry `three-subgroups-lemma-oq-01`.  We
reproduce its short proof — project to `G ⧸ N`, where `X ≤ N ↔ X.map (mk' N) = ⊥`
and `map` distributes over the bracket, then apply Mathlib's `= ⊥` Hall–Witt lemma
`Subgroup.commutator_commutator_eq_bot_of_rotate`. -/

/-- **Three Subgroups Lemma (normal-subgroup form).**  If `N` is normal and both
`⁅⁅H, K⁆, L⁆` and `⁅⁅K, L⁆, H⁆` lie in `N`, then so does `⁅⁅L, H⁆, K⁆`. -/
private theorem commutator_le_of_rotate {H K L N : Subgroup G} [N.Normal]
    (h1 : ⁅⁅H, K⁆, L⁆ ≤ N) (h2 : ⁅⁅K, L⁆, H⁆ ≤ N) :
    ⁅⁅L, H⁆, K⁆ ≤ N := by
  rw [← QuotientGroup.ker_mk' N] at h1 h2 ⊢
  rw [← Subgroup.map_eq_bot_iff] at h1 h2 ⊢
  simp only [Subgroup.map_commutator] at h1 h2 ⊢
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

/-- Cyclic relabelling of `commutator_le_of_rotate`: from `⁅⁅K, L⁆, H⁆ ≤ N` and
`⁅⁅L, H⁆, K⁆ ≤ N` conclude `⁅⁅H, K⁆, L⁆ ≤ N`. -/
private theorem commutator_le_of_rotate₂ {H K L N : Subgroup G} [N.Normal]
    (h1 : ⁅⁅K, L⁆, H⁆ ≤ N) (h2 : ⁅⁅L, H⁆, K⁆ ≤ N) :
    ⁅⁅H, K⁆, L⁆ ≤ N :=
  commutator_le_of_rotate h1 h2

/-! ## The successor recursion of the lower central series

`lowerCentralSeries G (n + 1) = ⁅lowerCentralSeries G n, ⊤⁆` holds definitionally;
we name it for readable rewriting. -/

/-- The defining recursion `γ₍ₙ₊₁₎ = ⁅γₙ, ⊤⁆`. -/
theorem lowerCentralSeries_succ_def (n : ℕ) :
    lowerCentralSeries G (n + 1) = ⁅lowerCentralSeries G n, (⊤ : Subgroup G)⁆ := rfl

/-! ## The bilinear bound -/

/-- **Bilinear lower-central-series bound.**  The commutator of the `i`-th and
`j`-th terms of the lower central series lies in the `(i + j + 1)`-th term:

  `⁅γᵢ, γⱼ⁆ ≤ γ₍ᵢ₊ⱼ₊₁₎`.

Proof: induction on `j`, uniform in `i`.  The base case `j = 0` is the recursion
`⁅γᵢ, ⊤⁆ = γ₍ᵢ₊₁₎`.  The inductive step rewrites `γ₍ⱼ₊₁₎ = ⁅γⱼ, ⊤⁆` and applies the
three subgroups lemma with `H = γⱼ`, `K = ⊤`, `L = γᵢ`, `N = γ₍ᵢ₊ⱼ₊₂₎`: the two
hypotheses `⁅γ₍ᵢ₊₁₎, γⱼ⁆ ≤ N` and `⁅⁅γᵢ, γⱼ⁆, ⊤⁆ ≤ N` come from the inductive
hypothesis (at `i + 1` and at `i`, respectively), and the lemma delivers the
conclusion `⁅⁅γⱼ, ⊤⁆, γᵢ⁆ = ⁅γᵢ, γ₍ⱼ₊₁₎⁆ ≤ N`. -/
theorem commutator_lowerCentralSeries_le (i j : ℕ) :
    ⁅lowerCentralSeries G i, lowerCentralSeries G j⁆ ≤ lowerCentralSeries G (i + j + 1) := by
  induction j generalizing i with
  | zero =>
    rw [lowerCentralSeries_zero, Nat.add_zero]
    exact (lowerCentralSeries_succ_def i).ge
  | succ j ih =>
    -- `⁅⊤, γᵢ⁆ = γ₍ᵢ₊₁₎`.
    have e1 : ⁅(⊤ : Subgroup G), lowerCentralSeries G i⁆ = lowerCentralSeries G (i + 1) := by
      rw [commutator_comm]; exact (lowerCentralSeries_succ_def i).symm
    -- Rewrite the target commutator into the textbook `⁅⁅γⱼ, ⊤⁆, γᵢ⁆` orientation.
    have e2 : ⁅lowerCentralSeries G i, lowerCentralSeries G (j + 1)⁆
        = ⁅⁅lowerCentralSeries G j, (⊤ : Subgroup G)⁆, lowerCentralSeries G i⁆ := by
      rw [lowerCentralSeries_succ_def j, commutator_comm]
    have key : ⁅lowerCentralSeries G i, lowerCentralSeries G (j + 1)⁆
        ≤ lowerCentralSeries G (i + j + 2) := by
      rw [e2]
      refine commutator_le_of_rotate₂ ?_ ?_
      · -- `⁅⁅⊤, γᵢ⁆, γⱼ⁆ = ⁅γ₍ᵢ₊₁₎, γⱼ⁆ ≤ γ₍ᵢ₊ⱼ₊₂₎`  via the IH at `i + 1`.
        rw [e1, show i + j + 2 = (i + 1) + j + 1 by omega]
        exact ih (i + 1)
      · -- `⁅⁅γᵢ, γⱼ⁆, ⊤⁆ ≤ ⁅γ₍ᵢ₊ⱼ₊₁₎, ⊤⁆ = γ₍ᵢ₊ⱼ₊₂₎`  via the IH at `i`.
        calc ⁅⁅lowerCentralSeries G i, lowerCentralSeries G j⁆, (⊤ : Subgroup G)⁆
            ≤ ⁅lowerCentralSeries G (i + j + 1), (⊤ : Subgroup G)⁆ :=
              commutator_mono (ih i) le_rfl
          _ = lowerCentralSeries G (i + j + 2) := (lowerCentralSeries_succ_def (i + j + 1)).symm
    rw [show i + (j + 1) + 1 = i + j + 2 by omega]
    exact key

/-! ## Consequences -/

/-- The self-commutator special case `⁅γᵢ, γᵢ⁆ ≤ γ₍₂ᵢ₊₁₎`. -/
theorem sq_commutator_lowerCentralSeries_le (i : ℕ) :
    ⁅lowerCentralSeries G i, lowerCentralSeries G i⁆ ≤ lowerCentralSeries G (2 * i + 1) := by
  have h := commutator_lowerCentralSeries_le (G := G) i i
  rwa [show i + i + 1 = 2 * i + 1 by ring] at h

/-- **Exponentially sharp derived-series bound.**  Each term of the derived series
sits inside an *exponentially* deep term of the lower central series:

  `derivedSeries G n ≤ lowerCentralSeries G (2 ^ n - 1)`.

This strictly strengthens Mathlib's linear `derived_le_lower_central`
(`derivedSeries G n ≤ lowerCentralSeries G n`).  Proof: induction on `n`.  The step
uses `derivedSeries G (n+1) = ⁅derivedSeries G n, derivedSeries G n⁆`, monotonicity of
the bracket against the inductive hypothesis, and then the bilinear bound, which
sends index `(2ⁿ−1) + (2ⁿ−1) + 1 = 2ⁿ⁺¹ − 1`. -/
theorem derivedSeries_le_lowerCentralSeries_two_pow (n : ℕ) :
    derivedSeries G n ≤ lowerCentralSeries G (2 ^ n - 1) := by
  induction n with
  | zero => simp [derivedSeries_zero]
  | succ n ih =>
    have hpos : 0 < 2 ^ n := pow_pos (by norm_num) n
    have hidx : (2 ^ n - 1) + (2 ^ n - 1) + 1 = 2 ^ (n + 1) - 1 := by
      have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
      omega
    calc derivedSeries G (n + 1)
        = ⁅derivedSeries G n, derivedSeries G n⁆ := by rw [derivedSeries_succ]
      _ ≤ ⁅lowerCentralSeries G (2 ^ n - 1), lowerCentralSeries G (2 ^ n - 1)⁆ :=
            commutator_mono ih ih
      _ ≤ lowerCentralSeries G ((2 ^ n - 1) + (2 ^ n - 1) + 1) :=
            commutator_lowerCentralSeries_le _ _
      _ = lowerCentralSeries G (2 ^ (n + 1) - 1) := by rw [hidx]

/-! ## Consistency: recovering Mathlib's linear bound

Since `2 ^ n - 1 ≥ n` and the lower central series is antitone, the sharp bound
recovers `derived_le_lower_central`. -/

/-- Cross-check: the sharp bound recovers Mathlib's `derivedSeries G n ≤ γₙ`. -/
theorem derivedSeries_le_lowerCentralSeries (n : ℕ) :
    derivedSeries G n ≤ lowerCentralSeries G n :=
  (derivedSeries_le_lowerCentralSeries_two_pow n).trans
    (lowerCentralSeries_antitone (by
      have hpos : 0 < 2 ^ n := pow_pos (by norm_num) n
      have hn : n < 2 ^ n := Nat.lt_two_pow_self
      omega))

end ThreeSubgroupsLemmaOQ0101
