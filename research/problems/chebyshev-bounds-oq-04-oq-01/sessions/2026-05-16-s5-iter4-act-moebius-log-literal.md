# S5 — Iter 4 ACT: literal Möbius–log identity (build verified 7744 jobs)

**Date**: 2026-05-16T02:55Z
**Researcher**: researcher-6
**Phase**: ACT (Iter 4)
**Scope**: 1 new Lean theorem (~24 lines) + bookkeeping (state.md + slug JSON + meta.json + this session doc); 0 sorries, 0 axioms added/removed; Docker-verified clean 7744 jobs.

## §0 Summary

This session ships **Iter 4**, closing the literal Möbius-inverted form of Selberg's auxiliary function on `n.divisors`:

```
selbergLambda2_eq_moebius_log_sq :
  ∀ {n : ℕ}, 0 < n →
    selbergLambda2 n =
      ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℝ) * (Real.log (n / d : ℕ)) ^ 2)
```

This is the dual of Iter 3's `sum_divisors_selbergLambda2_eq_log_sq` under the Möbius-inversion iff `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq`. With this iteration the algebraic core of Selberg-Erdős 1949 is complete; the next analytic step (Iter 5–6) is Selberg's symmetry formula `Σ_{n ≤ N} Λ₂(n) = 2N · log N + O(N)`.

## §1 Pre-claim survey

`gh pr list -R rjwalters/lean-genius --search "chebyshev-bounds-oq-04-oq-01 in:title" --state open` at session start returned **0** OPEN PRs:

| PR | Status | Merged at |
|---|---|---|
| #19092 (Iter 3 ACT) | MERGED | 2026-05-15T22:59:33Z |
| #19171 (S4 PREP, doc-only) | MERGED | 2026-05-15T22:56:46Z |
| #17689 (stale Iter 2 parallel) | CLOSED | — |

The 3-way coordination plan from S5 PREP (`sessions/2026-05-15-s5-prep-deployer-stall-coord.md`) has fully resolved: the deployer drain wave merged Iter 3 + S4 PREP and closed the stale parallel attempt.

`origin/main` HEAD at session start: `8a3cda556b6` (post-kepler-oq-04 audit tracker sync). The slug's Lean file `proofs/Proofs/ChebyshevBoundsOQ04OQ01.lean` was at 312 LOC / 15 theorems / 0 sorries / 0 axioms (Iter 3 state).

## §2 Plan execution (per S4 PREP §4.2)

S4 PREP #19171 (researcher-8, merged 2026-05-15T22:56:46Z) laid out a precise proof sketch with API pins at Mathlib v4.26.0 SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. This session implements that sketch verbatim modulo one elaboration adjustment (see §3 below).

**Iter 4 theorem statement** (matches S4 PREP §4.1 exactly):

```lean
/-- **Möbius–log identity (literal form, Iter 4)**: for `n > 0`,

      Λ₂(n) = Σ_{d ∣ n} μ(d) · log²(n/d).

    This is the Möbius-inverse of Iter 3's dual identity
    `sum_divisors_selbergLambda2_eq_log_sq`. The proof applies
    `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq` to the dual
    identity, then re-indexes `divisorsAntidiagonal → divisors` via
    `Nat.sum_divisorsAntidiagonal`. -/
theorem selbergLambda2_eq_moebius_log_sq {n : ℕ} (hn : 0 < n) :
    selbergLambda2 n =
      ∑ d ∈ n.divisors,
        ((ArithmeticFunction.moebius d : ℝ) * (Real.log (n / d : ℕ)) ^ 2) := by
  have hiter3 : ∀ m : ℕ, 0 < m → ∑ i ∈ m.divisors, selbergLambda2 i = (Real.log m) ^ 2 :=
    fun m hm => sum_divisors_selbergLambda2_eq_log_sq hm
  have hinv :=
    (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℝ)).mp hiter3 n hn
  have hbridge :
      ∑ x ∈ n.divisorsAntidiagonal,
          ((ArithmeticFunction.moebius x.fst : ℝ) * (Real.log x.snd) ^ 2)
        = ∑ d ∈ n.divisors,
          ((ArithmeticFunction.moebius d : ℝ) * (Real.log (n / d : ℕ)) ^ 2) :=
    Nat.sum_divisorsAntidiagonal
      (fun a b => (ArithmeticFunction.moebius a : ℝ) * (Real.log b) ^ 2)
  exact hinv.symm.trans hbridge
```

**Step trace** (~8 LOC body):

1. **`hiter3` lift**: rewrap Iter 3's signature `sum_divisors_selbergLambda2_eq_log_sq : {n : ℕ} → 0 < n → ...` as the `∀ m : ℕ, 0 < m → ...` form needed by Mathlib's iff (1 LOC).
2. **`hinv` (Möbius inversion `.mp`)**: instantiate `R := ℝ`, apply `.mp` to `hiter3`, then specialize to the target `n` with hypothesis `hn`. Yields `∑ x ∈ n.divisorsAntidiagonal, (μ x.fst : ℝ) · (Real.log x.snd)^2 = selbergLambda2 n` (2 LOC).
3. **`hbridge` (antidiagonal → divisors)**: invoke `Nat.sum_divisorsAntidiagonal` with `f := fun a b => (μ a : ℝ) · (Real.log b)^2`. Yields the LHS rewrite. The signature `f i.1 i.2 = f i (n/i)` matches `x.fst = x.1`, `x.snd = x.2` directly (4 LOC for the statement + 2 LOC for the discharge).
4. **Close**: `hinv.symm.trans hbridge` chains `selbergLambda2 n = LHS_anti = RHS_div` (1 LOC).

## §3 Build trap surfaced & recorded

Per S4 PREP §4.3 Pitfall A and Pitfall E, the lift `hiter3` was a risk point. The actual fault mode encountered was a **mixed coercion-vs-namespace** issue not exactly matching either pitfall:

**Initial draft** (omits ℕ annotation):
```lean
have hiter3 : ∀ m > 0, ∑ i ∈ m.divisors, selbergLambda2 i = (Real.log m) ^ 2 := ...
```

**Docker iter 1 output**:
```
error: Proofs/ChebyshevBoundsOQ04OQ01.lean:291:33:
  Invalid field `divisors`: The environment does not contain `Real.divisors`
  m
has type
  ℝ
error: Proofs/ChebyshevBoundsOQ04OQ01.lean:292:54:
  Application type mismatch: The argument `hm` has type `m > 0`
  but is expected to have type `0 < ?m.78`
  in the application `sum_divisors_selbergLambda2_eq_log_sq hm`
```

**Root cause**: `Real.log m` accepts both `m : ℕ` (via `Nat.cast`) and `m : ℝ` (directly). When the bound variable `m` is unannotated and the hypothesis body mentions `Real.log m`, Lean's elaborator prefers `m : ℝ` (no coercion needed). Then `m.divisors` becomes `Real.divisors` which doesn't exist, and downstream `sum_divisors_selbergLambda2_eq_log_sq hm` rejects `hm : m > 0` because it expects `0 < ?n : ℕ`.

**Fix** (1-token addition):
```lean
have hiter3 : ∀ m : ℕ, 0 < m → ∑ i ∈ m.divisors, selbergLambda2 i = (Real.log m) ^ 2 := ...
```

The Mathlib iff `sum_eq_iff_sum_mul_moebius_eq` takes `∀ n > 0, P n` which is definitionally `∀ n, 0 < n → P n` — so the explicit form unifies with `.mp`'s expectations without further coercion gymnastics.

**Docker iter 2**: `[7744/7744] Built Proofs.ChebyshevBoundsOQ04OQ01 (51s) — Build succeeded` against Mathlib v4.26.0 SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

**General pattern recorded in state.md**: any iff-form Möbius-inversion lift in this file (Iter 5–6 will need at least one more) should type-annotate the bound `ℕ` variable explicitly when the consequent of the implication coerces through `Real.log` (or any `ℕ → ℝ` function the elaborator could resolve as `ℝ → ℝ`).

## §4 Mathlib API used (verified at v4.26.0 SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

| Lemma | File:Line | Form | Role |
|---|---|---|---|
| `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq` | `Mathlib/NumberTheory/ArithmeticFunction/Moebius.lean:240` | `[NonAssocRing R]` iff between `∑ i ∈ n.divisors, f i = g n` and `∑ x ∈ n.divisorsAntidiagonal, (μ x.fst : R) * g x.snd = f n` | Möbius inversion |
| `Nat.sum_divisorsAntidiagonal` (via `@[to_additive]` on `prod_divisorsAntidiagonal`) | `Mathlib/NumberTheory/Divisors.lean:543` | `∑ i ∈ n.divisorsAntidiagonal, f i.1 i.2 = ∑ i ∈ n.divisors, f i (n / i)` | Antidiagonal → divisors re-index |

Both lemmas inherited via `import Mathlib` + `open ArithmeticFunction` (lines 68 + 73 of the slug Lean file). The `ArithmeticFunction.` prefix on `sum_eq_iff_sum_mul_moebius_eq` and `moebius` is explicit even after `open`, matching the local style (line 236 uses `ArithmeticFunction.mul_apply` similarly).

`sum_divisors_selbergLambda2_eq_log_sq` (the Iter 3 dependency) is provided by PR #19092 (merged 2026-05-15T22:59:33Z) at line 257 of the same file with signature `{n : ℕ} (hn : 0 < n) : ∑ d ∈ n.divisors, selbergLambda2 d = (Real.log n) ^ 2`.

## §5 File deltas

| Path | +/- | Role |
|---|---|---|
| `proofs/Proofs/ChebyshevBoundsOQ04OQ01.lean` | +24/-11 | new theorem `selbergLambda2_eq_moebius_log_sq` inserted after Iter 3's `sum_divisors_selbergLambda2_eq_log_sq`; Future Work docstring pruned (the now-closed Iter 4 entry removed; iteration tally updated from "Iteration 3 closes…" to "Iterations 3–4 are now closed…") |
| `research/problems/chebyshev-bounds-oq-04-oq-01/state.md` | +56/-46 | phase advance to `ACT (Iter 4 Möbius–log literal form verified)`, iteration 4 → 5, new Iter 4 log entry, Race awareness updated for this PR, Next Action pivoted to Iter 5a (Selberg's symmetry formula leading term), Blockers refreshed |
| `src/data/research/problems/chebyshev-bounds-oq-04-oq-01.json` | + +/- | top-level phase update, `currentState` phase/since/iteration/focus/nextAction/attemptCounts refresh, `knownResults.proven` += selbergLambda2_eq_moebius_log_sq entry (open Möbius–log entry removed), `knowledge.progressSummary` + `builtItems` + `insights` + `nextSteps` + `mathlibGaps` Iter 4 entries appended, `leanFiles[3]` lineCount 206 → 325 + theoremCount 10 → 16 (the Iter 1 staleness flagged in S4 PREP §1.3 now corrected) |
| `src/data/proofs/chebyshev-bounds-oq-04-oq-01/meta.json` | + +/- | description extended for Iter 3 + Iter 4, `lineCount` 230 → 325, `theoremCount` 12 → 16, `originalContributions` += Iter 3 + Iter 4 entries (open Möbius–log gap removed), `conclusion.summary`/`implications`/`openQuestions` refresh, sections list += sec-dual-identity + sec-moebius-log + Future Work line-range correction |
| `research/problems/chebyshev-bounds-oq-04-oq-01/sessions/2026-05-16-s5-iter4-act-moebius-log-literal.md` | + only (new) | this session doc |

No overlap with any current open PR for any slug (verified pre-push via `gh pr list -R rjwalters/lean-genius --search "chebyshev-bounds-oq-04-oq-01 in:title" --state open` returning `[]`).

## §6 Iteration tally

| Iter | Date | PR | Status | Deliverable |
|---|---|---|---|---|
| 1 | 2026-05-09 | #17658 | merged | Selberg-Erdős scaffold (Λ₂, S₂ defs + 10 routine lemmas) |
| 2 | 2026-05-12 | #17690 | merged | Prime-value lemmas |
| 3 | 2026-05-14 | #19092 | merged | Selberg dual identity `Σ_{d∣n} Λ₂(d) = (log n)²` |
| 4 | 2026-05-16 | **this PR** | open | Literal Möbius–log form `Λ₂(n) = Σ_{d∣n} μ(d)·log²(n/d)` |

## §7 Next action (Iter 5a — Selberg's symmetry formula, leading term)

Goal: prove `Σ_{n ≤ N} Λ₂(n) = 2N · log N + O(N)`.

Starting from Iter 4's `selbergLambda2_eq_moebius_log_sq`, sum both sides over `n ≤ N`:

```
Σ_{n ≤ N} Λ₂(n) = Σ_{n ≤ N} Σ_{d ∣ n} μ(d) · (log (n/d))²
```

Swap the sum order (Möbius hyperbola trick) to get

```
= Σ_{d ≤ N} μ(d) · Σ_{m ≤ N/d} (log m)²
```

The inner sum has explicit asymptotic (integration by parts on `log²`, cf. Tenenbaum I.6.2):

```
Σ_{m ≤ x} (log m)² = x · (log x)² − 2x · log x + 2x + O(log²x).
```

Scaling by `μ(d) / d` and using Mertens' bound `Σ_{d ≤ N} μ(d) / d = O(1)`, the leading-term contribution to `Σ_{n ≤ N} Λ₂(n)` is `−2N · log N · O(1)` — but with a coefficient computation that produces `+2N · log N` (sign cancellation; cf. Tenenbaum III.4 Theorem 4.1).

Estimated PR delta: +80–120 LOC for the leading term alone (one theorem + maybe two helper lemmas). The `O(N)` error-term cleanup is comparable and would be Iter 5b.

## §8 Honest scope statement

This PR delivers **one** new theorem (~8 LOC body, ~24 LOC with docstring + signature). It does NOT:

- Make any progress on the open `chebyshevPsi_asymptotic` axiom in the parent file — the elementary PNT proof's terminal goal — which remains exactly as Iter 3 left it.
- Touch `src/data/research/candidates/` or the candidate pool.
- Add any new axioms or sorries.
- Modify Aristotle companion files or any sibling slug's content.

Its value is the **dual** of Iter 3: combined, the two iterations now provide both forms of Selberg's identity (the dual `Σ Λ₂(d) = (log n)²` and the literal `Λ₂(n) = Σ μ(d) log²(n/d)`) — Iter 5 will use the literal form to launch the symmetry formula proof.

## §9 Pre-push re-check checklist

Per `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md`:

- [x] `gh pr list -R rjwalters/lean-genius --search "chebyshev-bounds-oq-04-oq-01 in:title" --state open` re-run immediately before push: 0 OPEN PRs (no race).
- [x] Docker build clean on final commit SHA.
- [x] All JSON files validate via `python3 -m json.tool`.
- [x] No untracked files outside the slug scope.
- [x] Worktree absolute paths used for all Edit/Write (per `feedback_researcher_main_repo_linter_reverts_edits_use_worktree_absolute_path`).
