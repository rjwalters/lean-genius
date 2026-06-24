/-
  Erdős Problem #105, Open Question 01 → 01:
  The avoidability set is a genuine threshold — `f(n)` is sharp, and the open
  `n-4` question is exactly `f(n) ≥ n-4`.

  **Background.** For a non-collinear `n`-point set `A` and an obstacle set `B`,
  call `B` *avoidable* if some rich line of `A` (a line through ≥2 points of `A`)
  misses all of `B`. The parent `Erdos105OQ01.lean` showed avoidability is
  *antitone* in `B` and, conditional on the open hypothesis `openProblem_n_minus_4`,
  derived a lower bound `f(n) ≥ n-4` — but only under an *ad hoc* extra hypothesis
  that the avoidability set is bounded above, and without showing `f` is a true
  threshold (that the set of always-avoidable counts is an initial segment).

  **What this entry contributes** (all *axiom-free*; the parent's `xichuan_counterexample`
  and `beck_szemeredi_trotter_positive` axioms are NOT used):

  1. `avoidSet n` — the set of obstacle counts `m` that are *always* avoidable for
     `|A| = n`. By construction `thresholdFunction n = sSup (avoidSet n)`
     (`thresholdFunction_eq_sSup`).

  2. `avoidSet_downwardClosed` — `avoidSet n` is an initial segment of `ℕ`: if `m` is
     always avoidable then so is every `m' ≤ m`. (Immediate from the `≤` in the
     definition — no padding needed.) And `zero_mem_avoidSet`: `0 ∈ avoidSet n` for
     `n ≥ 3`, since an empty obstacle set is avoided by any rich line, which exists
     by `many_rich_lines_exist`. So `avoidSet n` is always *nonempty*.

  3. `mem_avoidSet_iff_le_threshold` / `avoidSet_eq_Iic` — **`f` is a sharp threshold.**
     Whenever `avoidSet n` is bounded above, `m ∈ avoidSet n ↔ m ≤ f(n)`, i.e.
     `avoidSet n = Set.Iic (f n)` exactly. (The sup of a nonempty bounded set of
     naturals is attained, so `f(n)` itself is always avoidable, and downward-closure
     fills in everything below.) This *justifies calling `f` a threshold function* —
     avoidable for every `m ≤ f(n)`, blocked for some configuration at every
     `m > f(n)`.

  4. `openProblem_iff_mem` / `openProblem_iff_threshold_ge` — **the open boundary,
     pinned.** `openProblem_n_minus_4` is logically *equivalent* to
     `∀ n ≥ 5, (n-4) ∈ avoidSet n`, and (when each `avoidSet n` is bounded above)
     to `∀ n ≥ 5, f(n) ≥ n-4`. Combined with the known upper bound `f(n) ≤ n-4`
     (Xichuan), the open question is *exactly* `f(n) = n-4`.

  **Status**: the structural results are axiom-free and self-contained over the parent
  definitions. The boundedness hypothesis `BddAbove (avoidSet n)` is stated honestly as
  a hypothesis (it is open question 02 whether it holds for every `n`), NOT assumed as
  an axiom. Sorry count: 0. Axiom count: 0.

  Reference: https://erdosproblems.com/105
-/

import Proofs.Erdos105OQ01
import Mathlib

open Erdos105 Erdos105OQ01

namespace Erdos105OQ01OQ01

-- ════════════════════════════════════════════════════════════════
-- SECTION I: The avoidability set and the threshold function
-- ════════════════════════════════════════════════════════════════

/-- **The avoidability set at size `n`.** The obstacle counts `m` such that *every*
    non-collinear `A` with `|A| = n` admits a rich line avoiding *every* disjoint
    obstacle set `B` with `|B| ≤ m`. This is precisely the set whose supremum defines
    the parent's `thresholdFunction n`. -/
def avoidSet (n : ℕ) : Set ℕ :=
  {m | ∀ (A B : Finset Point), A.card = n → B.card ≤ m → Disjoint A B →
    NonCollinear (A : Set Point) →
    ∃ L : Line, L.richAndUnblocked (A : Set Point) (B : Set Point)}

/-- The threshold function is, by definition, the supremum of the avoidability set. -/
theorem thresholdFunction_eq_sSup (n : ℕ) : thresholdFunction n = sSup (avoidSet n) := rfl

-- ════════════════════════════════════════════════════════════════
-- SECTION II: The avoidability set is a nonempty initial segment
-- ════════════════════════════════════════════════════════════════

/-- **`avoidSet n` is downward closed** (an initial segment of `ℕ`): if `m` obstacles
    are always avoidable, so are any `m' ≤ m`. Immediate, since a configuration with
    `|B| ≤ m'` also has `|B| ≤ m`. -/
theorem avoidSet_downwardClosed {n m m' : ℕ} (hmm : m' ≤ m) (hm : m ∈ avoidSet n) :
    m' ∈ avoidSet n :=
  fun A B hA hB hdisj hncoll => hm A B hA (hB.trans hmm) hdisj hncoll

/-- **`0 ∈ avoidSet n` for `n ≥ 3`.** An empty obstacle set is avoided by *any* rich
    line, and a non-collinear set of `≥ 3` points has one (`many_rich_lines_exist`).
    Hence `avoidSet n` is always nonempty in the interesting regime. -/
theorem zero_mem_avoidSet {n : ℕ} (hn : 3 ≤ n) : 0 ∈ avoidSet n := by
  intro A B hA hB hdisj hncoll
  obtain ⟨k, hk, S, hScard, hrich⟩ := many_rich_lines_exist A hncoll (hA ▸ hn)
  have hSne : S.Nonempty := Finset.card_pos.mp (by rw [hScard]; omega)
  obtain ⟨L, hLmem⟩ := hSne
  have hBe : B = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hB)
  exact ⟨L, hrich L hLmem, fun b hb => by rw [hBe] at hb; simp at hb⟩

/-- `avoidSet n` is nonempty for `n ≥ 3`. -/
theorem avoidSet_nonempty {n : ℕ} (hn : 3 ≤ n) : (avoidSet n).Nonempty :=
  ⟨0, zero_mem_avoidSet hn⟩

-- ════════════════════════════════════════════════════════════════
-- SECTION III: `f` is a sharp threshold (under boundedness)
-- ════════════════════════════════════════════════════════════════

/-- **The threshold value is itself always avoidable.** The supremum of a nonempty
    bounded-above set of naturals is attained, so `f(n) ∈ avoidSet n`. -/
theorem threshold_mem_avoidSet {n : ℕ} (hn : 3 ≤ n) (hbdd : BddAbove (avoidSet n)) :
    thresholdFunction n ∈ avoidSet n :=
  Nat.sSup_mem (avoidSet_nonempty hn) hbdd

/-- **`f` is a sharp threshold.** Under boundedness, an obstacle count is always
    avoidable *iff* it is at most `f(n)`. -/
theorem mem_avoidSet_iff_le_threshold {n m : ℕ} (hn : 3 ≤ n) (hbdd : BddAbove (avoidSet n)) :
    m ∈ avoidSet n ↔ m ≤ thresholdFunction n := by
  constructor
  · intro hm
    exact le_csSup hbdd hm
  · intro hm
    exact avoidSet_downwardClosed hm (threshold_mem_avoidSet hn hbdd)

/-- **The avoidability set is exactly the initial segment `[0, f(n)]`.** -/
theorem avoidSet_eq_Iic {n : ℕ} (hn : 3 ≤ n) (hbdd : BddAbove (avoidSet n)) :
    avoidSet n = Set.Iic (thresholdFunction n) :=
  Set.ext fun _ => mem_avoidSet_iff_le_threshold hn hbdd

-- ════════════════════════════════════════════════════════════════
-- SECTION IV: The open `n-4` question, pinned to `f(n) ≥ n-4`
-- ════════════════════════════════════════════════════════════════

/-- The forward bridge: a positive answer to the open `n-4` question puts `n-4` in the
    avoidability set, for every `n ≥ 5` (the parent's `n_minus_4_avoidable_set`). -/
theorem n_minus_4_mem_avoidSet (h : openProblem_n_minus_4) {n : ℕ} (hn : 5 ≤ n) :
    (n - 4) ∈ avoidSet n :=
  n_minus_4_avoidable_set h n hn

/-- The reverse bridge: if `n-4` is always avoidable for every `n ≥ 5`, then the open
    `n-4` question holds (specialise from `|B| ≤ n-4` to `|B| = n-4`). -/
theorem openProblem_of_mem (h : ∀ n, 5 ≤ n → (n - 4) ∈ avoidSet n) :
    openProblem_n_minus_4 :=
  fun A B n hn hA hB hdisj hncoll => h n hn A B hA (le_of_eq hB) hdisj hncoll

/-- **The open `n-4` question is exactly membership of `n-4` in every avoidability set.** -/
theorem openProblem_iff_mem :
    openProblem_n_minus_4 ↔ ∀ n, 5 ≤ n → (n - 4) ∈ avoidSet n :=
  ⟨fun h n hn => n_minus_4_mem_avoidSet h hn, openProblem_of_mem⟩

/-- **The open `n-4` question is exactly the sharp lower bound `f(n) ≥ n-4`.**
    Under boundedness of each avoidability set, `openProblem_n_minus_4` holds iff
    `f(n) ≥ n-4` for all `n ≥ 5`. With the known upper bound `f(n) ≤ n-4`, this pins
    the open question to `f(n) = n-4`. -/
theorem openProblem_iff_threshold_ge
    (hbdd : ∀ n, 5 ≤ n → BddAbove (avoidSet n)) :
    openProblem_n_minus_4 ↔ ∀ n, 5 ≤ n → n - 4 ≤ thresholdFunction n := by
  rw [openProblem_iff_mem]
  constructor
  · intro h n hn
    exact (mem_avoidSet_iff_le_threshold (by omega) (hbdd n hn)).1 (h n hn)
  · intro h n hn
    exact (mem_avoidSet_iff_le_threshold (by omega) (hbdd n hn)).2 (h n hn)

-- ════════════════════════════════════════════════════════════════
-- SECTION V: Summary
-- ════════════════════════════════════════════════════════════════

/--
**Summary of Erdős #105, OQ-01 → 01.**

The avoidability set `avoidSet n` is a nonempty initial segment of `ℕ`
(`zero_mem_avoidSet`, `avoidSet_downwardClosed`), and whenever it is bounded above it
equals `Set.Iic (f n)` exactly (`avoidSet_eq_Iic`) — so `f = thresholdFunction` is a
*genuine sharp threshold*: every count `≤ f(n)` is always avoidable. The single open
boundary `openProblem_n_minus_4` is then logically equivalent to `f(n) ≥ n-4` for all
`n ≥ 5` (`openProblem_iff_threshold_ge`), which together with the known `f(n) ≤ n-4`
pins the open question to `f(n) = n-4`. All results are axiom-free. -/
theorem erdos_105_oq01oq01_summary :
    (∀ n, 3 ≤ n → (avoidSet n).Nonempty) ∧
    (∀ n m m', m' ≤ m → m ∈ avoidSet n → m' ∈ avoidSet n) ∧
    (∀ n, 3 ≤ n → BddAbove (avoidSet n) → avoidSet n = Set.Iic (thresholdFunction n)) ∧
    (openProblem_n_minus_4 ↔ ∀ n, 5 ≤ n → (n - 4) ∈ avoidSet n) :=
  ⟨fun n hn => avoidSet_nonempty hn,
   fun _ _ _ hmm hm => avoidSet_downwardClosed hmm hm,
   fun _ hn hbdd => avoidSet_eq_Iic hn hbdd,
   openProblem_iff_mem⟩

end Erdos105OQ01OQ01
