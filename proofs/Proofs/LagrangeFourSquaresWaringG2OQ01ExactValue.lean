import Mathlib
import Proofs.LagrangeFourSquaresWaringG2OQ01General

/-!
# Waring g(k) Exact Value — Capstone Characterization (S28 ACT)

Slug `lagrange-four-squares-waring-g2-oq-01` asks, for each `k ≥ 3`, to
determine `g(k)` — the smallest `s` such that **every** `n : ℕ` is a sum of
`s` perfect `k`-th powers. Every committed Lean artifact so far proves only
the **lower** half (`g(k) ≥ 2^k + ⌊(3/2)^k⌋ − 2`): the per-`k` `Counting*`
files (k=3..7) and the parametric `…General.lean` (`waring_lower_general`,
all `k ≥ 1`). No file states the matching **upper** bound, hence no file
states the exact value `g(k) = 2^k + ⌊(3/2)^k⌋ − 2`. This file closes that
gap on the *statement* side and assembles the exact-value characterization.

## What is proved vs assumed

The exact value is `g(k) = 2^k + ⌊(3/2)^k⌋ − 2` whenever the **Dickson–Pillai
condition** holds:

> `(*)   3^k mod 2^k + ⌊(3/2)^k⌋ ≤ 2^k`     (equivalently `r + q ≤ 2^k`)

which is verified to hold for all `k = 1..200` (see
`research/problems/.../verify_ideal_condition.py`, S26) and is known for all
but finitely many `k` (Mahler 1957), with no counterexample below
`k ≈ 4.7·10^8` (Kubina–Wunderlich 1990).

| Ingredient | Status here |
|---|---|
| Lower bound `g(k) ≥ formula` (witness `n_k` not a sum of `formula−1` powers) | **proved** — reuses `General.waring_lower_general` |
| Upper bound `g(k) ≤ formula` under `(*)` (every `n` is a sum of `formula` powers) | **axiom** `ideal_waring_upper` — the deep Dickson–Pillai–Niven (1936–44) theorem, a genuine Mathlib gap |
| `(*)` for a concrete `k` | **proved** by `decide` (decidable ℕ arithmetic) |
| Exact value `g(k) = formula` for concrete `k = 3..7` | **proved** modulo the one axiom |
| `g(2) = 4` upper half (k=2 anchor) | **proved unconditionally** from Mathlib's `Nat.sum_four_squares` — no axiom |

The `k = 2` anchor (`upper_bound_two`) discharges the upper half *without* the
axiom, demonstrating that `ideal_waring_upper` is a true theorem in the one
case Mathlib can currently check (Lagrange's four-square theorem).

## ⚠️ BUILD STATUS — NOT build-verified (Docker blackout, S28)

Written 2026-06-15 (researcher-10) while the host Docker daemon was
unresponsive (`docker info` timed out), so `docker-build.sh` could not run.
The file imports the (also build-pending, unregistered) `…General.lean`; the
two form one unit. Deliberately **NOT registered** in `proofs/Proofs.lean`
so it cannot break the whole-library build. A follow-up session with Docker
up should build `Proofs.LagrangeFourSquaresWaringG2OQ01ExactValue`, fix any
v4.26.0 lemma-name drift, then register both files.

* Axioms: **1** (`ideal_waring_upper`) — `axiomatized` status per the project
  axiom-integrity policy (the upper bound is a deep classical theorem, not in
  Mathlib). All other declarations are `theorem`/`def`, 0 sorries.

## Bearer lemmas (Mathlib v4.26.0)

`Nat.sum_four_squares`, `Fin.sum_univ_four` (both used in built sibling files),
and the imported `WaringG2OQ01.General.{IsSumOfKthPowers, waring_lower_general}`.
-/

namespace WaringG2OQ01.ExactValue

open WaringG2OQ01.General

/-- `IsUniversalBound s k`: every `n : ℕ` is a sum of `s` perfect `k`-th powers.
`g(k)` is the least `s` for which this holds. -/
def IsUniversalBound (s k : ℕ) : Prop :=
  ∀ n : ℕ, IsSumOfKthPowers s k n

/-- **Lower half (proved).** The bound `2^k + ⌊(3/2)^k⌋ − 3 = g(k) − 1` is
*not* universal: the witness `n_k = ⌊(3/2)^k⌋·2^k − 1` is not a sum of that
many `k`-th powers (`General.waring_lower_general`). Hence `g(k) ≥ formula`. -/
theorem g_minus_one_not_universal (k : ℕ) (hk : 1 ≤ k) :
    ¬ IsUniversalBound (2 ^ k + 3 ^ k / 2 ^ k - 3) k :=
  fun h => waring_lower_general k hk (h (3 ^ k / 2 ^ k * 2 ^ k - 1))

/-- **Upper half (DEEP AXIOM — Dickson–Pillai–Niven).** When the Dickson–Pillai
condition `(*) 3^k mod 2^k + ⌊(3/2)^k⌋ ≤ 2^k` holds, every `n : ℕ` is a sum of
`2^k + ⌊(3/2)^k⌋ − 2` perfect `k`-th powers, i.e. `g(k) ≤ formula`.

This is the *ideal Waring theorem* (Dickson 1936, Pillai 1940, Niven 1944);
its proof is research-level analytic/combinatorial number theory and is absent
from Mathlib v4.26.0. The hypothesis `(*)` is itself decidable and verified for
all `k = 1..200` (S26 `verify_ideal_condition.py`). For `k = 2` this axiom is
not needed — see `upper_bound_two`. -/
axiom ideal_waring_upper (k : ℕ) (hk : 1 ≤ k)
    (hcond : 3 ^ k % 2 ^ k + 3 ^ k / 2 ^ k ≤ 2 ^ k) :
    IsUniversalBound (2 ^ k + 3 ^ k / 2 ^ k - 2) k

/-- **Exact value characterization.** For every `k ≥ 1` satisfying the
Dickson–Pillai condition, `formula := 2^k + ⌊(3/2)^k⌋ − 2` summands suffice for
every `n` (upper, axiom) while `formula − 1` do not (lower, proved). Together
these pin `g(k) = 2^k + ⌊(3/2)^k⌋ − 2` exactly. -/
theorem waringG_exact (k : ℕ) (hk : 1 ≤ k)
    (hcond : 3 ^ k % 2 ^ k + 3 ^ k / 2 ^ k ≤ 2 ^ k) :
    IsUniversalBound (2 ^ k + 3 ^ k / 2 ^ k - 2) k ∧
      ¬ IsUniversalBound (2 ^ k + 3 ^ k / 2 ^ k - 3) k :=
  ⟨ideal_waring_upper k hk hcond, g_minus_one_not_universal k hk⟩

/-- **k = 2 anchor (axiom-free).** The upper half at `k = 2` is exactly
Lagrange's four-square theorem (`Nat.sum_four_squares`), so `IsUniversalBound 4 2`
holds *unconditionally* — no appeal to `ideal_waring_upper`. This certifies the
axiom is a true theorem in the one case Mathlib can check. -/
theorem upper_bound_two : IsUniversalBound 4 2 := by
  intro n
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares n
  exact ⟨![a, b, c, d], by rw [Fin.sum_univ_four]; simpa using h⟩

/-- `g(2) = 4` exactly, fully unconditional: upper half from `upper_bound_two`
(Lagrange), lower half from `g_minus_one_not_universal` (the parent's `7` needs
four squares, here as the parametric witness `n_2 = 7`). No axiom used. -/
theorem g2_eq_four :
    IsUniversalBound 4 2 ∧ ¬ IsUniversalBound 3 2 := by
  refine ⟨upper_bound_two, ?_⟩
  have e : (2 : ℕ) ^ 2 + 3 ^ 2 / 2 ^ 2 - 3 = 3 := by decide
  have h := g_minus_one_not_universal 2 (by norm_num)
  rwa [e] at h

/-- `g(3) = 9` exactly (modulo `ideal_waring_upper`). -/
theorem g3_eq_nine :
    IsUniversalBound 9 3 ∧ ¬ IsUniversalBound 8 3 := by
  have e1 : (2 : ℕ) ^ 3 + 3 ^ 3 / 2 ^ 3 - 2 = 9 := by decide
  have e2 : (2 : ℕ) ^ 3 + 3 ^ 3 / 2 ^ 3 - 3 = 8 := by decide
  have h := waringG_exact 3 (by norm_num) (by decide)
  rwa [e1, e2] at h

/-- `g(4) = 19` exactly (modulo `ideal_waring_upper`). -/
theorem g4_eq_nineteen :
    IsUniversalBound 19 4 ∧ ¬ IsUniversalBound 18 4 := by
  have e1 : (2 : ℕ) ^ 4 + 3 ^ 4 / 2 ^ 4 - 2 = 19 := by decide
  have e2 : (2 : ℕ) ^ 4 + 3 ^ 4 / 2 ^ 4 - 3 = 18 := by decide
  have h := waringG_exact 4 (by norm_num) (by decide)
  rwa [e1, e2] at h

/-- `g(5) = 37` exactly (modulo `ideal_waring_upper`). -/
theorem g5_eq_thirtyseven :
    IsUniversalBound 37 5 ∧ ¬ IsUniversalBound 36 5 := by
  have e1 : (2 : ℕ) ^ 5 + 3 ^ 5 / 2 ^ 5 - 2 = 37 := by decide
  have e2 : (2 : ℕ) ^ 5 + 3 ^ 5 / 2 ^ 5 - 3 = 36 := by decide
  have h := waringG_exact 5 (by norm_num) (by decide)
  rwa [e1, e2] at h

/-- `g(6) = 73` exactly (modulo `ideal_waring_upper`). -/
theorem g6_eq_seventythree :
    IsUniversalBound 73 6 ∧ ¬ IsUniversalBound 72 6 := by
  have e1 : (2 : ℕ) ^ 6 + 3 ^ 6 / 2 ^ 6 - 2 = 73 := by decide
  have e2 : (2 : ℕ) ^ 6 + 3 ^ 6 / 2 ^ 6 - 3 = 72 := by decide
  have h := waringG_exact 6 (by norm_num) (by decide)
  rwa [e1, e2] at h

/-- `g(7) = 143` exactly (modulo `ideal_waring_upper`). -/
theorem g7_eq_onefortythree :
    IsUniversalBound 143 7 ∧ ¬ IsUniversalBound 142 7 := by
  have e1 : (2 : ℕ) ^ 7 + 3 ^ 7 / 2 ^ 7 - 2 = 143 := by decide
  have e2 : (2 : ℕ) ^ 7 + 3 ^ 7 / 2 ^ 7 - 3 = 142 := by decide
  have h := waringG_exact 7 (by norm_num) (by decide)
  rwa [e1, e2] at h

end WaringG2OQ01.ExactValue
