# S5 ACT — Polynomial-form bridges to qNumber for the polynomial sub-lattice

**Researcher**: researcher-1
**Date**: 2026-06-01
**Phase**: ACT (S5 ACT, scope-narrowed from Path C RatFunc migration to polynomial-form bridges; see §6)
**Outcome**: 3 theorems shipped, ~80 LOC added, Docker-verified 7745/7745 jobs

## §0 — TL;DR

Three new theorems bridge the **rational Macdonald presentation** of the
polynomial sub-lattice `{k ≤ 1} ∪ {(2, 2)}` (S4 ACT) to the **polynomial
qNumber presentation** from the parent gallery entry:

1. `qtBinom_one_right_eq_qNumber` — at `k = 1`, the rational form
   `(1 - q^N) / (1 - q)` equals `qNumber q N = 1 + q + q² + ⋯ + q^(N-1)`
   provided `1 - q ≠ 0`.
2. `qtMultichoose_one_right_eq_qNumber` — corollary at `qtMultichoose`
   level via the `n + 1 - 1 = n` index shift.
3. `qtMultichoose_two_two_eq_qNumber` — the unique non-trivial polynomial
   sub-lattice point evaluates to `qNumber q 3 = 1 + q + q²` under the
   two Path A guards `1 - q² t ≠ 0` and `1 - q ≠ 0`.

Together, every point in the polynomial sub-lattice is now formally
equated to a `qNumber` expression from the parent, completing the
polynomial-form bridge that was left implicit by the S4 ACT rational
form.

## §1 — Context: why a scope-narrowed S5 ACT

The state.md "Next Action" pointed at Path C (RatFunc.eval) migration
for the positive `qtMultichoose 1 1 n k = Nat.multichoose n k` recovery,
estimated at 80–120 LOC of `RatFunc` infrastructure overhead. That
remains the right *long-term* direction but is multi-session.

The same state.md flagged an **alternative**:

> Alternative: if Path C is too heavy, prove additional polynomial-sub-lattice
> cases (qtMultichoose_one_one_zero, qtMultichoose_one_n_zero_zero, etc.)
> — these are direct corollaries of the existing Section II / III / VI
> theorems but make the sub-lattice characterization fully concrete.
> ~10-20 LOC each.

This iteration takes that alternative one step further: instead of
proving *more* sub-lattice cases at the rational level, we **bridge the
existing ones** to the parent's polynomial form. This:

- Closes the rational-vs-polynomial gap that was implicit in S4 ACT
  (the rational form `(1 - q^N)/(1 - q)` was never explicitly equated
  to `qNumber q N`, even though the equality is obvious by
  `qNumber_geometric`).
- Adds 3 small, easily-verified theorems (~80 LOC total, including doc).
- Uses zero new Mathlib infrastructure — `qNumber_geometric` and
  `mul_div_cancel_left₀` are the only non-trivial lemmas needed.
- Does not commit to either Path A or Path C for the eventual S5
  positive-form recovery — the bridges hold under either ambient.

The bridges complement, rather than replace, the future Path C work:
they make the polynomial sub-lattice characterisation **fully
polynomial** from the parent's perspective, which is the natural
foundation for the eventual gallery integration (S7) whose `meta.json`
will reference `qNumber` rather than `(1 - q^_)/(1 - q)` for legibility.

## §2 — Mathematical content

### 2.1 The `qNumber_geometric` identity

The parent file `Proofs.CombinationsFormulaOQ03` proves
(line 94, attributed to `QBinomialCoefficients`):

```
theorem qNumber_geometric (q : R) (n : ℕ) :
    (q - 1) * qNumber q n = q ^ n - 1
```

This is the multiplicative form of the geometric-series identity. By
negation:

```
(1 - q) * qNumber q n = 1 - q^n         (*)
```

(Either side negated gives the other, and the `linear_combination`
tactic closes the algebraic identity in one step.)

### 2.2 Bridge for `k = 1`

Combining `qtBinom_one_right` (S2 ACT) — which says
`qtBinom q t N 1 = (1 - q^N) / (1 - q)` — with identity (*) and
`mul_div_cancel_left₀ : a ≠ 0 → a * b / a = b` gives:

```
qtBinom q t N 1 = (1 - q^N) / (1 - q)
                = ((1 - q) * qNumber q N) / (1 - q)        [by (*)]
                = qNumber q N                              [mul_div_cancel_left₀]
```

The hypothesis is just `1 - q ≠ 0`. No hypothesis on `t` (the LHS is
t-free at `k = 1` because the only product factor uses `t^0 = 1`).

This is `qtBinom_one_right_eq_qNumber`. The `qtMultichoose` corollary
is a one-line shift via `n + 1 - 1 = n`.

### 2.3 Bridge for `(n, k) = (2, 2)`

Same pattern, one layer up:

```
qtMultichoose q t 2 2 = (1 - q^3) / (1 - q)                [qtMultichoose_two_two, under 1 - q² t ≠ 0]
                     = ((1 - q) * qNumber q 3) / (1 - q)  [by (*) at n = 3]
                     = qNumber q 3                         [mul_div_cancel_left₀]
                     = 1 + q + q²
```

Two hypotheses needed: `1 - q² t ≠ 0` (Path A guard from
`qtMultichoose_two_two`) and `1 - q ≠ 0` (denominator of the i = 0
factor).

This is `qtMultichoose_two_two_eq_qNumber`.

## §3 — Lean proof details

Each of the three theorems is ~6 LOC of proof (excluding the docstring).
The proof skeleton is identical:

```lean
theorem ⟨name⟩ ⟨hypotheses⟩ : ⟨LHS rational form⟩ = qNumber q ⟨N⟩ := by
  rw [⟨rational-form theorem⟩]
  have h_geom : (1 - q ^ ⟨N⟩ : R) = (1 - q) * qNumber q ⟨N⟩ := by
    have hg := qNumber_geometric q ⟨N⟩
    linear_combination hg
  rw [h_geom, mul_div_cancel_left₀ _ hq]
```

The `linear_combination hg` step verifies:

```
(1 - q^N - (1 - q) · qNumber q N) - 1 · ((q - 1) · qNumber q N - (q^N - 1))
  = (1 - q^N) - (1 - q) · qNumber q N - (q - 1) · qNumber q N + (q^N - 1)
  = 0         [since -(1 - q) - (q - 1) = 0 and (1 - q^N) + (q^N - 1) = 0]
```

A `ring` would close this directly but is more expensive; the
`linear_combination` form is the standard Mathlib idiom for closed-form
algebraic identities derived from an existing hypothesis.

## §4 — Counts after S5 ACT

| File | Lines | Theorems | Axioms | Defs | Sorries |
|------|-------|----------|--------|------|---------|
| `ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03OQ02.lean` | 428 | 13 | 0 | 2 | 0 |

Delta from S6 ACT (PR #?, 2026-05-31, ~348 LOC, 10 theorems):
**+80 LOC, +3 theorems, 0 sorries, 0 axioms net.**

(Note: the S6 ACT memo says "9 → 10 theorems" but the S2 ACT (5) +
S3 ACT (2) + S4 ACT (3) + S6 ACT (1) sum is 11. Re-counting after
this iteration including the 1 private helper: 13 public theorems,
1 private lemma. The "10" in S6 ACT memo's count excluded the private
helper.)

## §5 — Build status

Build verified by Docker:

```
./proofs/scripts/docker-build.sh Proofs.ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03OQ02
=== Build succeeded ===
✔ [7745/7745] Built Proofs.ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03OQ02 (9.5s)
```

Mathlib v4.26.0, fresh cache, no warnings.

## §6 — Honesty

This iteration ships:
- **3 new theorems** (all polynomial-form bridges)
- **0 sorry deltas** (none introduced; net still 0)
- **0 axiom deltas** (none introduced; net still 0)
- **0 new definitions**
- ~80 LOC added (60 doc + 20 proof)

The mathematical content is **not novel** — the bridges are immediate
from the existing rational-form theorems and the parent's
`qNumber_geometric` identity. The novelty is the explicit Lean
formalisation pinning each polynomial sub-lattice point to its
`qNumber` form, which had been left implicit in S4 ACT.

The future Lean entry's status remains **axiomatized** (or
**formalized** with the open S5+ work flagged) until either Path C
(`RatFunc.eval`) substitution or an iterated-limit construction
delivers the positive `at_one_one` recovery. The S5 ACT here narrows
the gap to "what needs to be added", not "what is already provable":
the polynomial sub-lattice characterisation is now fully equated to
the parent's polynomial presentation.

## §7 — Forward-looking notes for S6+ ACT

**Next iteration options** (in decreasing order of immediacy):

1. **S7 PREP — gallery JSON scoping**: with the polynomial-form bridges
   in place, the eventual `meta.json` entry can quote `qNumber q n`
   and `qNumber q 3` directly (rather than the more opaque rational
   forms), making the gallery presentation more aligned with the
   parent entry.

2. **Path C (RatFunc) migration — S5 ACT v2**: still the canonical
   route to the positive `qtMultichoose 1 1 n k = Nat.multichoose n k`
   recovery. Estimated 80–120 LOC of `RatFunc.eval` infrastructure;
   multi-session. The S5 PREP #18639 lays out the strategy.

3. **More polynomial-sub-lattice bridges**: e.g., a `qtBinom_zero_right`
   bridge — but `qtBinom q t N 0 = 1 = qNumber q 1`? No, `qNumber q 1
   = 1` but the empty product is `1` for trivial reasons, not as a
   `qNumber`. The k=0 case has no useful polynomial bridge.

4. **S6 ACT — Macdonald polynomial axiomatisation**: unchanged
   recommendation from S1. Out of scope until Mathlib gets Macdonald
   theory.

The S5 ACT here keeps the cascade in a sustainable rhythm: 1 ACT per
session, all 0-sorry / 0-axiom, building incrementally on the rational
foundation laid by S2/S3/S4 ACTs. The polynomial-form bridges are a
natural intermediate step before Path C migration commits to a heavy
infrastructure change.
