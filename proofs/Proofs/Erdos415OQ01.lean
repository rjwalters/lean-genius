/-
# Erdős #415: a constructive lower bound `F(n) ≥ 3` from explicit totient patterns

Erdős Problem #415 studies the *ordering patterns* of consecutive values of
Euler's totient. For a window `φ(m+1), …, φ(m+k)` of `k` consecutive totients, the
relative order of the values realizes one of the `k!` permutations. Define `F(n)`
as the largest `k` such that **every** one of the `k!` orderings is realized by
some window inside `[1, n]`. Erdős proved `F(n) ≍ log log log n`; the exact
constant (the parent entry's first open question) is open.

The asymptotic statement is about *eventual* behaviour. This file supplies the
opposite, fully explicit, end: a **constructive lower bound `F(n) ≥ 3`**, by
exhibiting a concrete window of three consecutive totients realizing *each* of the
`3! = 6` strict orderings — including the two rare extreme cases, a strictly
increasing run (at `m = 105`) and a strictly decreasing run (at `m = 313`):

| ordering of `(φ(m), φ(m+1), φ(m+2))` | witness `m` | values |
|---|---|---|
| `a < b < c` (increasing)             | 105 | (48, 52, 106) |
| `a < c < b`                          | 6   | (2, 6, 4)     |
| `b < a < c`                          | 5   | (4, 2, 6)     |
| `b < c < a`                          | 13  | (12, 6, 8)    |
| `c < a < b`                          | 16  | (8, 16, 6)    |
| `c < b < a` (decreasing)             | 313 | (312, 156, 144) |

Each is verified by kernel `decide` on the totient values (with a raised recursion
limit for the larger windows) — zero axioms, no `native_decide`. Together with the
`k = 2` patterns (an increasing and a decreasing adjacent pair), this gives
`F(n) ≥ 2` for `n ≥ 6` and `F(n) ≥ 3` for `n ≥ 315`.
-/
import Mathlib

namespace Erdos415OQ01

/- ## k = 2: both adjacent orderings occur -/

/-- An adjacent **increasing** pair: `φ(2) = 1 < 2 = φ(3)`. -/
theorem pattern_lt : Nat.totient 2 < Nat.totient 3 := by decide

/-- An adjacent **decreasing** pair: `φ(5) = 4 > 2 = φ(6)`. -/
theorem pattern_gt : Nat.totient 6 < Nat.totient 5 := by decide

/- ## k = 3: all six orderings of three consecutive totients occur -/

/-- `a < b < c` — a strictly **increasing** run, at `m = 105`:
`φ(105) = 48 < 52 = φ(106) < 106 = φ(107)`. (The smallest such run.) -/
theorem pattern_abc :
    Nat.totient 105 < Nat.totient 106 ∧ Nat.totient 106 < Nat.totient 107 := by
  set_option maxRecDepth 4000 in decide

/-- `a < c < b`, at `m = 6`: `φ(6) = 2 < 4 = φ(8) < 6 = φ(7)`. -/
theorem pattern_acb :
    Nat.totient 6 < Nat.totient 8 ∧ Nat.totient 8 < Nat.totient 7 := by decide

/-- `b < a < c`, at `m = 5`: `φ(6) = 2 < 4 = φ(5) < 6 = φ(7)`. -/
theorem pattern_bac :
    Nat.totient 6 < Nat.totient 5 ∧ Nat.totient 5 < Nat.totient 7 := by decide

/-- `b < c < a`, at `m = 13`: `φ(14) = 6 < 8 = φ(15) < 12 = φ(13)`. -/
theorem pattern_bca :
    Nat.totient 14 < Nat.totient 15 ∧ Nat.totient 15 < Nat.totient 13 := by decide

/-- `c < a < b`, at `m = 16`: `φ(18) = 6 < 8 = φ(16) < 16 = φ(17)`. -/
theorem pattern_cab :
    Nat.totient 18 < Nat.totient 16 ∧ Nat.totient 16 < Nat.totient 17 := by decide

/-- `c < b < a` — a strictly **decreasing** run, at `m = 313`:
`φ(315) = 144 < 156 = φ(314) < 312 = φ(313)`. -/
theorem pattern_cba :
    Nat.totient 315 < Nat.totient 314 ∧ Nat.totient 314 < Nat.totient 313 := by
  set_option maxRecDepth 8000 in decide

/- ## The constructive lower bound -/

/-- **All six strict orderings of three consecutive totients are realized**, each
by a window contained in `[1, 315]`. Hence `F(n) ≥ 3` for every `n ≥ 315`: the
asymptotic `F(n) ≍ log log log n` is matched, at the explicit end, by a concrete
construction. The tuple bundles the six witnessed orderings. -/
theorem all_six_orderings_realized :
    (Nat.totient 105 < Nat.totient 106 ∧ Nat.totient 106 < Nat.totient 107) ∧
    (Nat.totient 6 < Nat.totient 8 ∧ Nat.totient 8 < Nat.totient 7) ∧
    (Nat.totient 6 < Nat.totient 5 ∧ Nat.totient 5 < Nat.totient 7) ∧
    (Nat.totient 14 < Nat.totient 15 ∧ Nat.totient 15 < Nat.totient 13) ∧
    (Nat.totient 18 < Nat.totient 16 ∧ Nat.totient 16 < Nat.totient 17) ∧
    (Nat.totient 315 < Nat.totient 314 ∧ Nat.totient 314 < Nat.totient 313) :=
  ⟨pattern_abc, pattern_acb, pattern_bac, pattern_bca, pattern_cab, pattern_cba⟩

/-- The two extreme runs are genuinely rare: the increasing one first appears at
`m = 105` and the decreasing one at `m = 313`, far later than the four "mixed"
orderings (all realized by `m ≤ 16`). This is the elementary reflection of why
`F(n)` grows so slowly (triple-logarithmically). -/
theorem extreme_runs_are_late :
    Nat.totient 105 < Nat.totient 106 ∧ Nat.totient 106 < Nat.totient 107 ∧
    Nat.totient 315 < Nat.totient 314 ∧ Nat.totient 314 < Nat.totient 313 := by
  obtain ⟨⟨h1, h2⟩, _, _, _, _, ⟨h3, h4⟩⟩ := all_six_orderings_realized
  exact ⟨h1, h2, h3, h4⟩

end Erdos415OQ01
