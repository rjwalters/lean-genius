import Mathlib
import Proofs.TwinPrimes

/-
# Twin Primes OQ-02: the growth rate of π₂(N)

## Open question
What is the true growth rate of the twin-prime counting function

  π₂(N) := #{ p ≤ N : p and p+2 are both prime } ?

The **Hardy–Littlewood Conjecture B** predicts the asymptotic

  π₂(N) ~ 2·C₂ · N / (log N)²,   C₂ = ∏_{p ≥ 3 prime} p(p−2)/(p−1)² ≈ 0.6601…

(the *twin prime constant*).  This is open: no unconditional proof of the
asymptotic — or even of `π₂(N) → ∞` — is known.

## What this file does (honestly)
The asymptotic itself is **axiomatized** (`hardy_littlewood_conjecture_B`), exactly
as the parent twin-prime entries axiomatize the conjecture.  Around it we prove a body
of genuinely **unconditional**, machine-checked facts about `π₂`:

* `piTwo_zero`, `piTwo_five`, `piTwo_thirteen` — concrete values by `decide`.
* `piTwo_mono` — `π₂` is monotone non-decreasing.
* `piTwo_le` — the trivial bound `π₂(N) ≤ N + 1`.
* `twinPrimeConjecture_of_piTwo_unbounded` — **growth controls existence**: if `π₂` is
  unbounded then the Twin Prime Conjecture holds.  (So Hardy–Littlewood, which forces
  `π₂(N) → ∞`, is strictly stronger than mere infinitude.)

## Axiom Count: 1  (`hardy_littlewood_conjecture_B`; the ordinary
propext / Classical.choice / Quot.sound are not counted).
-/

open Filter Topology
open TwinPrimes (IsTwinPrimePair)

namespace TwinPrimesSpecialOQ02

/-- The twin-prime counting function: the number of `p ≤ N` such that `(p, p+2)` is a
twin-prime pair (we count by the smaller member of each pair).  The filter predicate is
written out explicitly (`Nat.Prime p ∧ Nat.Prime (p+2)`, definitionally
`TwinPrimes.IsTwinPrimePair p`) so that it is decidable. -/
def piTwo (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (p + 2))).card

/-! ## Concrete values (unconditional, by `decide`) -/

theorem piTwo_zero : piTwo 0 = 0 := by decide

/-- `π₂(5) = 2`: the pairs `(3,5)` and `(5,7)` (heads `3, 5 ≤ 5`). -/
theorem piTwo_five : piTwo 5 = 2 := by decide

/-- `π₂(13) = 3`: heads `3, 5, 11` (pairs `(3,5), (5,7), (11,13)`). -/
theorem piTwo_thirteen : piTwo 13 = 3 := by decide

/-! ## Unconditional structural facts -/

/-- `π₂` is monotone non-decreasing: enlarging the search range can only add twin pairs. -/
theorem piTwo_mono : Monotone piTwo := by
  intro M N hMN
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact Finset.range_mono (by omega)

/-- Trivial upper bound: `π₂(N) ≤ N + 1` (the heads live in `range (N+1)`). -/
theorem piTwo_le (N : ℕ) : piTwo N ≤ N + 1 := by
  have h := Finset.card_filter_le (Finset.range (N + 1))
    (fun p => Nat.Prime p ∧ Nat.Prime (p + 2))
  simpa [piTwo, Finset.card_range] using h

/-! ## Growth controls existence -/

/-- **Growth controls existence.**  If the twin-prime counting function `π₂` is unbounded,
then the Twin Prime Conjecture holds (infinitely many twin-prime pairs).

This makes precise that any nontrivial *lower* bound on the growth of `π₂` — in particular
the Hardy–Littlewood asymptotic, which forces `π₂(N) → ∞` — is strictly stronger than the
bare infinitude statement. -/
theorem twinPrimeConjecture_of_piTwo_unbounded
    (h : ∀ M : ℕ, ∃ N : ℕ, M < piTwo N) :
    ∀ N : ℕ, ∃ p : ℕ, p > N ∧ IsTwinPrimePair p := by
  intro N
  obtain ⟨N', hlt⟩ := h (piTwo N)
  -- `N ≤ N'`, else the larger range would have fewer twins.
  have hNN' : N ≤ N' := by
    by_contra hc
    push_neg at hc
    have hsub' : (Finset.range (N' + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (p + 2)) ⊆
        (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (p + 2)) :=
      Finset.filter_subset_filter _ (Finset.range_mono (by omega : N' + 1 ≤ N + 1))
    have hle := Finset.card_le_card hsub'
    simp only [piTwo] at hlt
    omega
  -- The smaller range's twin set sits inside the larger one, strictly (cards differ).
  have hsub : (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (p + 2)) ⊆
      (Finset.range (N' + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (p + 2)) :=
    Finset.filter_subset_filter _ (Finset.range_mono (by omega : N + 1 ≤ N' + 1))
  have hssub : (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (p + 2)) ⊂
      (Finset.range (N' + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (p + 2)) := by
    refine Finset.ssubset_iff_subset_ne.2 ⟨hsub, ?_⟩
    intro heq
    have : piTwo N = piTwo N' := by simp only [piTwo, heq]
    omega
  -- Extract a twin head in the difference: it lies in `(N, N']`.
  obtain ⟨p, hpmem, hpnot⟩ := Finset.exists_of_ssubset hssub
  rw [Finset.mem_filter] at hpmem
  obtain ⟨_, hp_twin⟩ := hpmem
  refine ⟨p, ?_, hp_twin⟩
  -- `p ∉ filter over range (N+1)`, but `p` is twin, so `p ∉ range (N+1)`, i.e. `p > N`.
  by_contra hpN
  push_neg at hpN
  apply hpnot
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_range.2 ?_, hp_twin⟩
  omega

/-! ## The Hardy–Littlewood asymptotic (axiomatized open prediction) -/

/-- **Hardy–Littlewood Conjecture B** (axiomatized).  The twin-prime counting function
satisfies `π₂(N) ~ 2·C₂·N/(log N)²` for a positive constant; the conjectured value of the
constant is the twin prime constant `C₂ = ∏_{p≥3} p(p−2)/(p−1)² ≈ 0.6601`.  This is an
open problem — stated here as an explicit assumption, not proved.

The existential `C` records the conjectured leading constant `C₂` without committing to its
exact (infinite-product) value; the content is the growth *order* `N/(log N)²`. -/
axiom hardy_littlewood_conjecture_B :
    ∃ C : ℝ, 0 < C ∧
      Tendsto (fun N : ℕ => (piTwo N : ℝ) / ((N : ℝ) / Real.log N ^ 2))
        atTop (𝓝 (2 * C))

end TwinPrimesSpecialOQ02
