# Knowledge Base: erdos-1004-oq-02

Optimal exponent `c₀` for totient run lengths `(log x)^c` (Erdős #1004).

---

## Problem Understanding

Erdős #1004 asks: for every `c > 0`, if `x` is large, does there exist `n ≤ x`
such that `φ(n+1), …, φ(n+⌊(log x)^c⌋)` are all distinct? The parent gallery
entry (`Proofs/Erdos1004Problem.lean`) already formalizes the two shapes of this
question:

```lean
def Erdos1004Conjecture : Prop :=          -- "holds for every c > 0"
  ∀ c : ℝ, c > 0 → ∀ᶠ x : ℕ in atTop, ∃ n ≤ x,
    IsDistinctTotientRun n ⌊(Real.log x) ^ c⌋₊

def SmallCaseConjecture : Prop :=          -- "holds for some band 0 < c < c₀"
  ∃ c₀ > 0, ∀ c : ℝ, 0 < c → c < c₀ → ∀ᶠ x : ℕ in atTop, ∃ n ≤ x,
    IsDistinctTotientRun n ⌊(Real.log x) ^ c⌋₊
```

The **"optimal exponent"** is the largest `c` for which the property holds. The
parent already names it (`c₀` inside `SmallCaseConjecture`) but never turns it
into a first-class, well-defined quantity. This investigation's contribution is
to do exactly that: define `c₀` as a genuine invariant of the problem and prove
the structural facts that make it well-posed.

## Feasibility split: the invariant `c₀` is tractable; its value is blocked

### TRACTABLE — well-definedness of `c₀` (0-axiom, no analysis; recommended target)

Define the **achievable-exponent set**

```lean
def AchievableExponent (c : ℝ) : Prop :=
  ∀ᶠ x : ℕ in atTop, ∃ n ≤ x, IsDistinctTotientRun n ⌊(Real.log x) ^ c⌋₊
```

The single mathematical fact that makes `c₀` meaningful is that this set is an
**interval** (downward-closed): if a long run is achievable, so is every shorter
one, at the *same* witness `n`.

**Lemma (prefix stability).** `IsDistinctTotientRun n K → K' ≤ K →
IsDistinctTotientRun n K'`. Immediate from the definition — the pairwise-distinct
condition on indices `[1,K]` restricts to the sub-block `[1,K'] ⊆ [1,K]`:

```lean
theorem run_prefix (n K K' : ℕ) (h : IsDistinctTotientRun n K) (hle : K' ≤ K) :
    IsDistinctTotientRun n K' := by
  intro i j hi hiK hj hjK hij
  exact h i j hi (hiK.trans hle) hj (hjK.trans hle) hij     -- ~1 line
```

**Lemma (downward closure of `AchievableExponent`).** For `0 ≤ c' ≤ c`,
`AchievableExponent c → AchievableExponent c'`.

*Proof.* Filter to `x` large enough that `Real.log x ≥ 1` **and** the `c`-run
exists (both are `∀ᶠ`). For such `x`, since the base `log x ≥ 1` and `c' ≤ c`,

```
(log x)^c' ≤ (log x)^c            -- Real.rpow_le_rpow_of_exponent_le
⌊(log x)^c'⌋₊ ≤ ⌊(log x)^c⌋₊       -- Nat.floor_le_floor
```

and the witness `n ≤ x` of the `c`-run gives, by `run_prefix`, a distinct run of
the shorter length `⌊(log x)^c'⌋₊` at the same `n ≤ x`. ∎

Key Mathlib API (all present in 4.26.0):
- `Real.rpow_le_rpow_of_exponent_le : 1 ≤ b → x ≤ y → b ^ x ≤ b ^ y`
- `Nat.floor_le_floor` (monotonicity of `⌊·⌋₊`)
- `Real.tendsto_log_atTop` / `Filter.eventually_atTop` for the `log x ≥ 1` tail
- `Filter.Eventually.and`, `filter_upwards`

**Definition of the invariant.** With `AchievableExponent` downward-closed and
`0 ∈` it (`(log x)^0 = 1`, `⌊1⌋₊ = 1`, `IsDistinctTotientRun n 1` always — see
`distinctRun_one`), the optimal exponent is a well-defined element of `[0,∞]`.
Use a **complete lattice codomain** so the supremum is total even if the set is
unbounded (which is the conjectured case):

```lean
noncomputable def c₀ : EReal :=
  sSup {(c : EReal) | ∃ r : ℝ, 0 ≤ r ∧ (c = (r : EReal)) ∧ AchievableExponent r}
```

(`ℝ≥0∞` works equally well; `EReal` avoids a nonneg coercion. Working in a
complete lattice sidesteps the `Real.sSup`-of-unbounded-set junk value, which
would otherwise silently collapse the conjectural `c₀ = ∞` case to `0`.)

**Structural theorems reframing the two conjectures as one invariant** — the
honest payoff of the entry, each provable from downward closure + order theory,
0 axioms, no number theory beyond the two lemmas above:

| Theorem | Statement |
|---|---|
| `achievable_downward_closed` | `0 ≤ c' ≤ c → AchievableExponent c → AchievableExponent c'` |
| `zero_achievable` | `AchievableExponent 0` |
| `conjecture_iff_c₀_top` | `Erdos1004Conjecture ↔ c₀ = ⊤` |
| `smallCase_iff_c₀_pos` | `SmallCaseConjecture ↔ 0 < c₀` |

The last two turn the qualitative parent Props into a single quantitative claim
about `c₀`: the full conjecture is "`c₀ = ∞`", the weak form is "`c₀ > 0`". Both
equivalences use only downward closure (to move from a witnessing exponent to a
whole band) and `sSup`/`lt_sSup`/`le_sSup` on `EReal`.

Estimated ~140–200 lines. Fully verifiable at 0 axioms once a Mathlib build is
available. **This is the substantive contribution for this investigation.**

### BLOCKED — the *value* of `c₀`

- **`c₀ > 0` (i.e. `SmallCaseConjecture`).** Requires exhibiting an actual
  positive achievable exponent: that runs of length `(log x)^c` genuinely occur
  below `x` for some fixed `c > 0`. This is the analytic heart of Erdős #1004 and
  needs distribution-of-totient-values / sieve input (Erdős–Pomerance–Sárközy
  1987 circle of ideas). Mathlib has **none** of this machinery, and the parent
  already records the relevant existence facts as axioms
  (`longer_runs_need_larger_n`, and the upper direction `eps87_theorem`).
- **`c₀ = ⊤` (the full conjecture).** Open mathematically — this *is* Erdős #1004.
- **Numeric relation to `1/3`.** The EPS87 **upper** bound `K ≤ n/exp(c(log n)^{1/3})`
  (parent axiom `eps87_theorem`) bounds absolute run length by ~`n`, not the
  `(log x)^c` scale, so it does **not** cap `c₀`; the `1/3` is heuristic only (the
  parent explicitly notes "not a formal implication"). No 0-axiom bound on `c₀`
  from either side is currently reachable.

## What the parent already provides (verified 2026-07-02)

- `IsDistinctTotientRun n K` (+ `IsDistinctTotientRun'` InjOn form and the
  equivalence `distinctRun_iff`), `distinctRun_zero`, `distinctRun_one`.
- `maxDistinctRunLength n := sSup {K | IsDistinctTotientRun n K}` — the **per-`n`**
  run length (fixed starting point). Distinct from the **per-`x`** reachability
  scale `AchievableExponent` above, which quantifies over all `n ≤ x`.
- `Erdos1004Conjecture`, `Erdos1004Negation`, `SmallCaseConjecture`.
- `eps87_theorem` (axiom), `run_length_sublinear` (proved: `maxDistinctRunLength n
  / n → 0`), `collision_ends_run`.

## Relationship to existing family entries

- `erdos-1004` (parent) — conjecture statements + EPS87 axiom (**axiomatized**).
- `erdos-1004-oq-02` **(gallery slug — NOTE)** — the *gallery* entry under this
  slug is a **different, complete** result ("totient fibers are finite",
  `n ≤ 2φ(n)²`, verified 0-axiom). This research investigation shares the slug id
  but targets the *optimal-exponent* sub-question; a verified Lean artifact for it
  should ship under a fresh child slug (e.g. `erdos-1004-oq-02-oq-01`) to avoid
  clobbering the existing entry.
- `erdos-1004-oq-03` — unconditional 0-axiom run bound `K ≤ n−1` via parity.
- `erdos-1004-oq-04` — concrete run witnesses (K = 3,5,7,9,10) + universal
  existence `∀ K, ∃ n, IsDistinctTotientRun n K` (unbounded run lengths, no
  `x`-constraint).

## Recommended next step

Build `Erdos1004OQ0201.lean` importing the parent: prove `run_prefix`,
`achievable_downward_closed`, `zero_achievable`, define `c₀ : EReal`, and prove
`conjecture_iff_c₀_top` + `smallCase_iff_c₀_pos`. Ship as a new child gallery
entry, `status: verified`, 0 axioms. Present `c₀`'s *value* (`> 0` / `= ⊤`) as the
open analytic core, blocked on Mathlib's absence of totient-distribution / EPS
machinery.

## Status

PARTIAL / IN-PROGRESS. The well-definedness of the optimal exponent `c₀` (an
interval-supremum invariant, with the two conjecture Props reframed as `c₀ = ⊤`
and `c₀ > 0`) is a concrete 0-axiom target, fully designed here with exact
Mathlib API. Verification deferred this iteration: no Mathlib olean cache is
present in the environment and disk is at 99%, so a heavy build cannot be run
safely (see state.md). The *value* of `c₀` is the open analytic problem.
