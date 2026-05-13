# Current State

**Phase**: BLOCKED
**Since**: 2026-05-13T12:44:13Z
**Iteration**: 1

## Outcome

Survey-complete. The conjectures in Erdős Problem #323 are
characterized by Erdős and Graham themselves as **"unattackable
by the methods at our disposal."** The only resolved case
($k = 2$, Landau 1908) is captured by an axiom.

> **OQ**: Let $f_{k,m}(x)$ count integers $n \le x$ that are sums
> of $m$ nonnegative $k$-th powers. Is
> $f_{k,k}(x) \gg_\varepsilon x^{1-\varepsilon}$? And, for $m < k$,
> is $f_{k,m}(x) \gg x^{m/k}$?

## Lean Source

`proofs/Proofs/Erdos323Problem.lean` — 139 LOC, 5 theorems,
6 definitions.

| Field | Value |
|---|---|
| `axiom` declarations | 1 (`landau_two_squares`) |
| Structure-encoded assumptions | 0 |
| Tactic `sorry` | 0 |
| Definition `sorry` | 0 |
| Unproved `def`-conjectures | 3 (`ErdosProblem323_part1`, `ErdosProblem323_part2`, `DensityQuestion`) |

Gallery `src/data/proofs/erdos-323/meta.json`:
`status: "axiomatized"`, `badge: "axiom"`, `axiomCount: 1`,
`sorries: 0`, `lineCount: 139`. Already accurate.

## Result Inventory

The 5 proved theorems are routine helper facts on the
counting function:

- `first_power_count` — $f_{1, m}(x) \ge m$ for $x \ge m$
  (every nonnegative integer is a sum of $m$ many 1st powers
  via the index-0 witness).
- `power_sum_count_mono` — $f_{k, m}(x) \le f_{k, m+1}(x)$ for
  $k \ge 1$ (extend by `Fin.snoc xs 0`, using $0^k = 0$ for
  $k \ge 1$).
- `IsSumOfPowers_one_iff` — `IsSumOfPowers n k 1 ↔ ∃ a, n = a^k`.
- `isSumOfPowers_pow_self` — $a^k$ is a sum-of-one $k$-th
  power (trivial corollary).
- `powerSumCount_one_lb` — $f_{k, 1}(n^k) \ge n + 1$ (the
  $n+1$ values $\{0^k, \dots, n^k\}$ are distinct in $[0, n^k]$).

The 3 conjectures are formalized as `def ... : Prop` predicates
on the inputs, not as theorems. None has been proved.

## The single axiom

```lean
axiom landau_two_squares :
    ∃ c : ℚ, 0 < c ∧
      ∀ ε : ℚ, 0 < ε → ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        (1 - ε) * c * (x : ℚ) ≤
          (powerSumCount 2 2 x : ℚ) * (Nat.log 2 x : ℚ)
```

**What it captures.** A lower-bound consequence of Landau's
1908 theorem: $f_{2,2}(x) \gtrsim c \cdot x / \log_2(x)$.

**Substantive note (axiom integrity).** The file docstring
describes Landau's theorem as $f_{2,2}(x) \sim c \cdot x / \sqrt{\log x}$
(natural log under a square root). The axiom as encoded uses
`Nat.log 2 x` (integer logarithm base 2), which is asymptotically
a $\log$ factor — **strictly weaker** than the true Landau lower
bound $c \cdot x / \sqrt{\log x}$ in the denominator's order, but
still sufficient to imply $f_{2,2}(x) = \Theta(x / \log x)$, hence
$f_{2, 2}(x) \ge c \cdot x^{1 - \varepsilon}$ for any $\varepsilon > 0$
and large $x$. So the axiom is correct *as a weakening of Landau*,
not a verbatim transcription. Any future tightening should align
the docstring and the formal statement.

**Why it cannot be discharged from Mathlib (as of 2026-05-13).**
Mathlib has:

- `Nat.sq_add_sq` (Fermat's theorem on sums of two squares,
  existence side: $p \equiv 1 \pmod 4 \Leftrightarrow p = a^2 + b^2$)
- Gaussian integer infrastructure (`Zsqrtd`, `GaussianInt`)
- L-series and Dirichlet character infrastructure
  (`Mathlib.NumberTheory.LSeries.*`)

Mathlib does **not** have:

- A density theorem of the form
  $\#\{n \le x : n = a^2 + b^2\} \sim c x / \sqrt{\log x}$
- The Selberg–Delange method (used to derive such asymptotics)
- The Landau–Ramanujan constant $c \approx 0.7642$

The discharge requires several hundred lines of complex-analytic
number theory not in any current PR pipeline known to this slug.

## Conjectures (genuinely open)

1. **Conjecture 1** (`ErdosProblem323_part1`):
   $\forall k \ge 2, \varepsilon > 0:$
   $\exists c > 0, x_0:$
   $f_{k, k}(x) \ge c \cdot x^{1 - \varepsilon}$ for $x \ge x_0$.

   *Status:* Open for all $k \ge 3$. Even
   $f_{k, k}(x) = o(x)$ is open — that is, we do not know
   whether the natural density of sums of $k$ many $k$-th powers
   is zero.

2. **Conjecture 2** (`ErdosProblem323_part2`):
   For $1 \le m < k$:
   $f_{k, m}(x) \ge c \cdot x^{m / k}$ for $x \ge x_0$.

3. **DensityQuestion**: For $k \ge 3$, is
   $f_{k, k}(x) = o(x)$? (The sub-question explicitly noted
   in the Erdős–Graham source.)

## Why "axiomatized" rather than "verified"

Per the axiom integrity policy: `axiomCount` must count both
`axiom` declarations and structure-encoded assumptions.
This file has exactly 1 `axiom` (`landau_two_squares`) and
0 structures with hypothesis fields — hence `axiomCount: 1`.
The gallery `meta.json` correctly records
`status: "axiomatized"`, `badge: "axiom"`.

Adding `ErdosProblem323_part1`/`_part2` as `def ... : Prop`
predicates (rather than as theorems with `sorry` bodies)
keeps `sorryCount = 0` accurate: there is no claimed proof
of those conjectures — they are merely *named*.

## Forward Levers (separate slug each)

Future sessions on Erdős #323 should re-route to one of these
narrower targets:

1. **Lower bound for Conjecture 2 at m = 1.**
   `powerSumCount_one_lb` already proves
   $f_{k, 1}(n^k) \ge n + 1$. The full $m = 1$ statement
   $f_{k, 1}(x) \ge c \cdot x^{1/k}$ requires:
   $\lfloor x^{1/k} \rfloor + 1 \le f_{k, 1}(x)$ for all $x$.
   This is an **integer-arithmetic exercise** (not analytic);
   Mathlib has `Nat.floor`, `Real.rpow_natCast`,
   `Nat.pow_le_iff_le_root`-style lemmas. Estimated effort:
   20–40 LOC, no new axioms.

2. **Mathlib-PR: density of sums of two squares.**
   Track Mathlib upstream and rewrite the axiom as a theorem
   once the Selberg–Delange asymptotic lands.

3. **Strengthen the axiom statement.** Replace `Nat.log 2 x`
   with `Nat.sqrt (Nat.log 2 x)` (or, more honestly, switch
   to `Real`-valued logs and `Real.sqrt`) to match the
   docstring's $x / \sqrt{\log x}$ shape. Still uses the same
   underlying classical result; the axiom statement becomes
   a faithful transcription rather than a weakening.

4. **Drop the axiom for $k = 1$.** `first_power_count` already
   resolves the lower bound for $k = 1$. State and prove
   `ErdosProblem323_part1_k_eq_one` as a small theorem to
   formally close the $k = 1$ case.

(1) and (4) are immediately tractable; (2) and (3) are
infrastructure-blocked but well-scoped.

## Active Approach

None — survey complete, work is BLOCKED on Landau-style
Mathlib infrastructure.

## Blockers

- `landau_two_squares` axiom: needs Mathlib's Selberg–Delange
  method or a direct proof of the $f_{2,2}(x) = \Omega(x / \log x)$
  weaker bound.
- Conjectures 1, 2 for $k \ge 3$: genuinely open in mathematics
  (Erdős–Graham 1980).

## Next Action

Do **not** re-claim this slug as a generic OBSERVE/ORIENT cycle —
the survey is done. Pick one of the **Forward Levers** above and
file a new slug or open a focused PR. Mechanically:

- For lever (4): add a small theorem specializing
  Conjecture 1 to $k = 1$ — this would reduce
  `ErdosProblem323` to the genuinely open cases.

- For lever (1): add a theorem specializing
  Conjecture 2 to $m = 1$ using `Nat.floor` arithmetic.

## Status Drift Resolved By This Sync

Prior state (seeker-init scaffold of 2026-01-12, last touched
2026-03-13):

- `phase: "OBSERVE"`, `status: "active"`,
  `currentState.phase: "NEW"`, `currentState.since: "2026-01-12"` —
  inconsistent with `knowledge.progressSummary: "SURVEY: 1 deep
  axiom..., Nothing actionable."` and with the merged PRs
  #15819, #15841, #15865 (May 2026) that did the survey work.
- `leanFiles[0].lineCount: 106` — stale, actual 139.
- `leanFiles[0].theoremCount: 2` — stale, actual 5
  (`first_power_count`, `power_sum_count_mono`,
  `IsSumOfPowers_one_iff`, `isSumOfPowers_pow_self`,
  `powerSumCount_one_lb`).
- State.md was the original seeker-init "Phase: NEW" stub.

This PR brings JSON, state.md, gallery meta into alignment
(gallery was already correct) and documents the axiom-statement
asymmetry as a known limitation worth a follow-up.
