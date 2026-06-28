/-
  Erdős Problem #564 — verified tower-growth theory (erdos-564-incomplete-01)

  **Parent problem (OPEN, $500).**  For the 3-uniform hypergraph Ramsey number
  R₃(n) the known bounds (Erdős–Hajnal–Rado 1965) are
      2^{cn²}  <  R₃(n)  <  2^{2^n},
  i.e. a *singly* exponential lower bound and a *doubly* exponential upper bound.
  Erdős asked whether the lower bound can be raised to `2^{2^{cn}}` — whether
  R₃(n) reaches **tower height 2** from below.  `Erdos564Problem.lean` axiomatizes
  the Ramsey number `R` and the two EHR bounds and defines the iterated-exponential
  `tower` function, but develops almost no theory of `tower` (only the three
  unfoldings `tower_zero/one/two` and positivity).

  **This file.**  The phrase "tower height", on which the whole problem hinges, is
  only meaningful once one knows the tower genuinely *grows* with its height and
  with its base.  Here is that theory, fully verified and **0-axiom** (it touches
  none of the parent's axioms — `#print axioms` on every result lists only
  propext / Classical.choice / Quot.sound):

    * `tower_lt_succ_height` : `tower k n < tower (k+1) n`              (height ↑)
    * `tower_strictMono_height` : `StrictMono (k ↦ tower k n)`
    * `tower_strictMono_base`   : `StrictMono (tower k)`               (base ↑)
    * `self_le_tower`           : `n ≤ tower k n`
    * `tower_one_lt_tower_two`  : `1 ≤ n → tower 1 n < tower 2 n`
      — the *singly*-exponential known lower bound is strictly below the
        *doubly*-exponential conjectured one: the exact gap Erdős #564 asks to close.

  Nothing here resolves the open conjecture; this is the combinatorial scaffolding
  that makes its statement ("can R₃ reach tower height 2?") precise.

  Reference: https://erdosproblems.com/564
-/

import Mathlib
import Proofs.Erdos564Problem

open Erdos564

namespace Erdos564.Incomplete01

/-- One step of the tower is an exponential: `tower (k+1) n = 2 ^ tower k n`.
This is the recursion `tower` is defined by, recorded as a rewrite lemma. -/
theorem tower_succ (k n : ℕ) : tower (k + 1) n = 2 ^ tower k n := rfl

/-- **Each extra level strictly increases the tower.**  `tower k n < tower (k+1) n`
for every `k` and `n`, because `m < 2 ^ m` holds for every natural number `m`
(including `m = 0`, where `0 < 1`).  No positivity hypothesis on `n` is needed. -/
theorem tower_lt_succ_height (k n : ℕ) : tower k n < tower (k + 1) n := by
  rw [tower_succ]
  exact Nat.lt_two_pow_self

/-- **The tower is strictly increasing in its height.**  For fixed base `n` the
map `k ↦ tower k n` is strictly monotone — every additional `2^(·)` level makes
the value strictly larger. -/
theorem tower_strictMono_height (n : ℕ) : StrictMono (fun k => tower k n) :=
  strictMono_nat_of_lt_succ (fun k => tower_lt_succ_height k n)

/-- **The base is a lower bound for the whole tower.**  `n ≤ tower k n` for every
height `k`: the tower never drops below its base.  Immediate from height-monotonicity
applied to `0 ≤ k` together with `tower 0 n = n`. -/
theorem self_le_tower (k n : ℕ) : n ≤ tower k n := by
  have h := (tower_strictMono_height n).monotone (Nat.zero_le k)
  rwa [tower_zero] at h

/-- **The tower is strictly increasing in its base.**  For fixed height `k` the map
`n ↦ tower k n` is strictly monotone.  Induction on `k`: the base case is the
identity, and `2 ^ (·)` is strictly monotone on `ℕ`, so it preserves the inductive
strict inequality. -/
theorem tower_strictMono_base (k : ℕ) : StrictMono (tower k) := by
  induction k with
  | zero => intro a b h; simpa [tower_zero] using h
  | succ k ih =>
      intro a b h
      simp only [tower_succ]
      exact Nat.pow_lt_pow_right (by norm_num) (ih h)

/-- The tower is (non-strictly) monotone in its base, for fixed height. -/
theorem tower_mono_base (k : ℕ) : Monotone (tower k) :=
  (tower_strictMono_base k).monotone

/-- `tower 2 n = 2 ^ (2 ^ n)` — the doubly-exponential height appearing in both the
EHR upper bound and the conjectured lower bound. -/
theorem tower_two_eq (n : ℕ) : tower 2 n = 2 ^ (2 ^ n) := rfl

/-- **The crux of Erdős #564, made precise.**  The known *singly*-exponential
lower bound has tower height `1` (`tower 1 n = 2 ^ n`); the conjectured lower
bound has tower height `2` (`tower 2 n = 2 ^ (2 ^ n)`).  For every `n` the
former is strictly smaller than the latter:
    `tower 1 n < tower 2 n`.
So the conjecture genuinely asks to push R₃ up a whole tower level — closing the
height gap between the EHR lower and upper bounds. -/
theorem tower_one_lt_tower_two (n : ℕ) : tower 1 n < tower 2 n := by
  have h1 : tower 1 n = 2 ^ n := tower_one n
  have h2 : tower 2 n = 2 ^ (2 ^ n) := tower_two_eq n
  rw [h1, h2]
  -- 2 ^ n < 2 ^ (2 ^ n) since n < 2 ^ n for every n
  exact Nat.pow_lt_pow_right (by norm_num) Nat.lt_two_pow_self

/-! ### Concrete sanity checks -/

/-- `tower 2 3 = 256`. -/
theorem tower_two_three : tower 2 3 = 256 := by decide

/-- `tower 3 1 = 16`: `tower 3 1 = 2 ^ tower 2 1 = 2 ^ (2 ^ (2 ^ 1)) = 2 ^ 4 = 16`. -/
theorem tower_three_one : tower 3 1 = 16 := by decide

/-- The base bound in action: `5 ≤ tower 4 5`. -/
theorem self_le_tower_example : 5 ≤ tower 4 5 := self_le_tower 4 5

/-! ## Monotonicity of the Ramsey property

The parent axiomatizes the Ramsey number `R` but proves no theory of the underlying
predicate `HasHypergraphRamseyProperty k m n` ("every 2-colouring of the k-subsets of
`Fin m` has a monochromatic n-clique").  Two structural monotonicities hold for *any*
such Ramsey-type property and are exactly the facts that make `R k n` well-behaved as a
*threshold* (the least `m` with the property):

* **more vertices preserve the property** (`…_mono`) — so the set of good `m` is upward
  closed, which is what lets one speak of the *least* such `m`;
* **a smaller target clique is easier** (`…_antitone_clique`) — so `R k ·` is monotone in
  the clique size.

Both are verified and **0-axiom** (they do not touch `R` or the EHR bounds). They are the
first genuine theory of the property predicate itself, complementing the `tower`-growth
theory above. -/

/-- **Vertex monotonicity.**  If every 2-colouring on `m` vertices yields a monochromatic
`n`-clique and `m ≤ m'`, the same holds on `m'` vertices: restrict a colouring of `Fin m'`
along the embedding `Fin m ↪ Fin m'`, find the clique downstairs, and push it back up
(`Finset.map` preserves cardinality and subset structure). -/
theorem hasHypergraphRamseyProperty_mono {k m m' n : ℕ} (hmm : m ≤ m')
    (h : HasHypergraphRamseyProperty k m n) : HasHypergraphRamseyProperty k m' n := by
  intro c'
  set f : Fin m ↪ Fin m' := Fin.castLEEmb hmm with hf
  obtain ⟨S, colour, hScard, hSmono⟩ := h (fun e => c' (e.map f))
  refine ⟨S.map f, colour, ?_, ?_⟩
  · rw [Finset.card_map]; exact hScard
  · intro e' he'sub he'card
    obtain ⟨e, hesub, rfl⟩ := Finset.subset_map_iff.mp he'sub
    rw [Finset.card_map] at he'card
    simpa using hSmono e hesub he'card

/-- **Clique-size antitonicity.**  A monochromatic `n`-clique contains a monochromatic
`n'`-clique for every `n' ≤ n`: take any `n'`-element subset of the clique — its
`k`-subsets are still `k`-subsets of the original clique, hence still monochromatic. -/
theorem hasHypergraphRamseyProperty_antitone_clique {k m n n' : ℕ} (hnn : n' ≤ n)
    (h : HasHypergraphRamseyProperty k m n) : HasHypergraphRamseyProperty k m n' := by
  intro c
  obtain ⟨S, colour, hScard, hSmono⟩ := h c
  obtain ⟨T, hTsub, hTcard⟩ := Finset.le_card_iff_exists_subset_card.mp (hScard ▸ hnn)
  exact ⟨T, colour, hTcard, fun e hesub hecard => hSmono e (hesub.trans hTsub) hecard⟩

end Erdos564.Incomplete01
