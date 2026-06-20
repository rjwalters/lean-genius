/-
# Erdős Divisibility Pigeonhole — extremal form: the largest divisibility-antichain
  in `{1, …, 2n}` has size exactly `n`

The parent entry (`Proofs/ErdosDivisibilityPigeonhole.lean`) proves two complementary
facts about subsets of `{1, …, 2n}`:

* `erdos_divisibility_pigeonhole` — any `n + 1` elements contain a pair `a ∣ b`
  (`a ≠ b`); and
* `erdos_divisibility_pigeonhole_sharp` — the block `{n+1, …, 2n}` has `n` elements
  and **no** such pair.

The first is an upper bound on "how big can a divisibility-free set be?"; the second
exhibits a set meeting it. This file packages the two into the single **extremal**
statement they jointly prove:

> The maximum size of a *divisibility-antichain* in `{1, …, 2n}` — a subset no two
> distinct members of which are related by `∣` — is exactly `n`.

This is the Sperner/Dilworth-flavoured optimum of the pigeonhole gem. A
divisibility-antichain is precisely an `IsAntichain (· ∣ ·)` set drawn from the
interval; we keep the explicit `Finset` predicate `IsDivAntichain` here for a clean
`IsGreatest` statement and record the `IsAntichain` reading in `isDivAntichain_iff`.

## Proof

* **Upper bound** (`antichain_card_le`): a divisibility-antichain `S ⊆ {1, …, 2n}`
  has `|S| ≤ n`. If instead `|S| ≥ n + 1`, the pigeonhole theorem produces a pair
  `a ∣ b` inside `S`, contradicting the antichain property.
* **Attained** (`erdos_divisibility_pigeonhole_sharp`): the block `{n+1, …, 2n}` is a
  divisibility-antichain of size `n`.

Together these give `IsGreatest` for the achievable antichain sizes
(`max_antichain_card`).

Axiom-free: the file is built entirely from the parent's verified theorems plus
foundational Mathlib lemmas (no `sorry`, no `axiom`, no `native_decide`).
-/
import Mathlib
import Proofs.ErdosDivisibilityPigeonhole

namespace ErdosDivisibilityPigeonhole

open Finset

/-- A **divisibility-antichain** in `{1, …, 2n}`: a finite set of integers drawn from
the interval `{1, …, 2n}` no two distinct members of which are related by divisibility. -/
def IsDivAntichain (n : ℕ) (S : Finset ℕ) : Prop :=
  S ⊆ Finset.Icc 1 (2 * n) ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬ a ∣ b

/-- `IsDivAntichain n S` is exactly "`S ⊆ {1, …, 2n}` and `S` is an `IsAntichain` for
the divisibility relation", connecting the bespoke predicate to Mathlib's general
order-theoretic notion. -/
theorem isDivAntichain_iff {n : ℕ} {S : Finset ℕ} :
    IsDivAntichain n S ↔
      S ⊆ Finset.Icc 1 (2 * n) ∧ IsAntichain (· ∣ ·) (S : Set ℕ) := by
  unfold IsDivAntichain
  refine and_congr_right fun _ => ?_
  constructor
  · intro h a ha b hb hab
    exact h a ha b hb hab
  · intro h a ha b hb hab
    exact h ha hb hab

/-- **Upper bound.** A divisibility-antichain in `{1, …, 2n}` has at most `n`
elements. Were it larger (`|S| ≥ n + 1`), the pigeonhole theorem
`erdos_divisibility_pigeonhole` would force a pair `a ∣ b` with `a ≠ b`, contradicting
the antichain hypothesis. -/
theorem antichain_card_le {n : ℕ} {S : Finset ℕ} (hS : IsDivAntichain n S) :
    S.card ≤ n := by
  by_contra h
  push_neg at h
  obtain ⟨a, ha, b, hb, hab, hdvd⟩ := erdos_divisibility_pigeonhole hS.1 h
  exact hS.2 a ha b hb hab hdvd

/-- **Extremal form of the Erdős divisibility pigeonhole.** The maximum size of a
divisibility-antichain in `{1, …, 2n}` is exactly `n`: the block `{n+1, …, 2n}`
attains it, and `antichain_card_le` shows nothing larger is possible. -/
theorem max_antichain_card (n : ℕ) :
    IsGreatest { k : ℕ | ∃ S : Finset ℕ, IsDivAntichain n S ∧ S.card = k } n := by
  constructor
  · -- `n` is achievable, witnessed by the sharp block `{n+1, …, 2n}`.
    obtain ⟨S, hsub, hcard, hanti⟩ := erdos_divisibility_pigeonhole_sharp n
    exact ⟨S, ⟨hsub, hanti⟩, hcard⟩
  · -- `n` is an upper bound for every achievable size.
    rintro k ⟨S, hS, rfl⟩
    exact antichain_card_le hS

/-- The extremal value stated for the canonical witness: `{n+1, …, 2n}` is a
divisibility-antichain of size `n`, so the maximum `n` of `max_antichain_card` is
genuinely attained by an explicit set. -/
theorem block_isDivAntichain (n : ℕ) :
    IsDivAntichain n (Finset.Icc (n + 1) (2 * n)) ∧
      (Finset.Icc (n + 1) (2 * n)).card = n := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro x hx
    rw [Finset.mem_Icc] at hx ⊢; omega
  · intro a ha b hb hab hdvd
    rw [Finset.mem_Icc] at ha hb
    have hble : a ≤ b := Nat.le_of_dvd (by omega) hdvd
    have hlt : a < b := lt_of_le_of_ne hble hab
    obtain ⟨c, hc⟩ := hdvd
    have hc2 : 2 ≤ c := by
      rcases c with _ | _ | c
      · simp at hc; omega
      · simp at hc; omega
      · omega
    have hba : 2 * a ≤ b := by
      rw [hc, mul_comm a c]; exact mul_le_mul_right' hc2 a
    omega
  · rw [Nat.card_Icc]; omega

-- Axiom audit: confirms the extremal result depends only on the standard
-- foundational axioms (propext, Classical.choice, Quot.sound) — no `Lean.ofReduceBool`
-- (no `native_decide`) and no `sorryAx`.
#print axioms max_antichain_card

end ErdosDivisibilityPigeonhole
