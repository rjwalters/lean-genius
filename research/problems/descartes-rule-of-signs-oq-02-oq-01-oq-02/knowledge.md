# Knowledge: descartes-rule-of-signs-oq-02-oq-01-oq-02

**S1 OBSERVE — researcher-11, 2026-05-16, doc-only (no Lean changes)**

This file collects the durable understanding of the slug. It is
intended to outlive any single session memo and to be read by the next
researcher who picks up this work.

## 1. Inheritance from the parent file

The slug's Lean source is
`proofs/Proofs/DescartesRuleOfSignsOQ02OQ01OQ02.lean`, originally
landed by PR **#14919** (commit `114d9fa467e`, 2026-05-02). It carries
458 LOC organised into 10 sections; the table below names each
declaration and its role.

| Section | Decl | Kind | Role |
|---|---|---|---|
| §1 | `countSignAlts` (line 85) | `def` | counts adjacent-pair sign alternations in a list of ℤ (computable filter helper) |
| §1 | `signVariations` (94) | `noncomputable def` | counts sign changes in a list of ℝ, ignoring zeros |
| §1 | `signVariations_nil` (100) | `theorem` | `signVariations [] = 0` |
| §1 | `signVariations_singleton` (103) | `theorem` | `signVariations [r] = 0` |
| §1 | `rootsInInterval` (108) | `noncomputable def` | `Multiset.card (p.roots.filter (a < · ∧ · ≤ b))` |
| §1 | `rootsInInterval_zero` (113) | `theorem` | zero polynomial has 0 roots in any interval (convention) |
| §1 | `rootsInInterval_C` (116) | `theorem` | nonzero constant polynomial has 0 roots |
| §2 | `sturmSeqAux` (132) | `noncomputable def` | fuel-based construction of `[p, q, -(p%q), -(q%(-(p%q))), …]` |
| §2 | `sturmSeq` (139) | `noncomputable def` | `sturmSeqAux p (derivative p) (p.natDegree + 1)` |
| §3 | `sturmSeqAux_ne_empty` (146) | `theorem` | sequence is always non-empty |
| §3 | `sturmSeq_ne_empty` (154) | `theorem` | sequence has length ≥ 1 |
| §3 | `sturmSeqAux_head` (157) | `theorem` | first element is `p` |
| §3 | `sturmSeq_head` (167) | `theorem` | `(sturmSeq p).head? = some p` |
| §3 | `sturmSeq_length_ge_two` (171) | `theorem` | nonzero `p` with `0 < natDegree p` ⇒ length ≥ 2 |
| §4 | `sturmVariations` (199) | `noncomputable def` | `signVariations ((sturmSeq p).map (· .eval x))` |
| §4 | `sturmVariations_zero` (202) | `theorem` | `sturmVariations 0 x = 0` |
| §4 | `sturmVariations_C` (205) | `theorem` | `sturmVariations (C c) x = 0` for `c ≠ 0` |
| **§5** | **`mod_eval_at_root`** (216) | **`theorem`** | **at a root `r` of `q`, `(p % q)(r) = p(r)`** |
| **§5** | **`sturm_interior_sign_property`** (226) | **`theorem`** | **`-(p % q)(r) = -p(r)` at a root of `q`** |
| **§5** | **`sturm_neighbors_opposite_at_root`** (233) | **`theorem`** | **at a root `r` of an interior `q` with `p(r) ≠ 0`: `p(r) · (-(p%q))(r) < 0`** |
| **§6** | **`sturm_exact_count_axiom`** (258) | **`axiom`** | **THE main statement — this is the unproven assumption** |
| §6 | `sturm_exact_count` (264) | `theorem` | trivial alias unfolding the axiom |
| §7 | `sturm_no_roots` (276) | `theorem` | `σ_p(a) = σ_p(b) ⇒ no roots in (a,b]` (corollary, via axiom) |
| §7 | `sturm_unique_root` (285) | `theorem` | drop-by-1 ⇒ exactly one root |
| §7 | `sturm_two_roots` (294) | `theorem` | drop-by-2 ⇒ exactly two roots |
| §7 | `sturm_count_le_variations` (304) | `theorem` | weaker upper-bound form |
| §7 | `sturmVariations_antitone` (313) | `theorem` | `a < b ⇒ σ_p(b) ≤ σ_p(a)` (corollary, via axiom) |
| §8 | `linear_deriv` (334) | `theorem` | `derivative (X - C c) = 1` |
| §8 | `sturmSeq_linear` (339) | `theorem` | concrete sequence for `X - C c` |
| §8 | `sturm_linear_left` (349) | `theorem` | `x < c ⇒ σ_{X - C c}(x) = 1` |
| §8 | `sturm_linear_right` (363) | `theorem` | `x > c ⇒ σ_{X - C c}(x) = 0` |
| **§9** | **`squarefree_no_common_roots`** (385) | **`theorem`** | **`Squarefree p ⇒ ¬(p(r) = 0 ∧ p'(r) = 0)`** |
| **§9** | **`squarefree_deriv_ne_zero_of_pos_degree`** (413) | **`theorem`** | **`Squarefree p ∧ 0 < natDegree p ⇒ derivative p ≠ 0`** |

The **bold** entries are the bearers for the eventual proof:
§5 gives the local algebra at any Sturm-sequence root; §9 gives the
squarefree consequences that make the drop-by-1 case work.

## 2. The single open question

```lean
axiom sturm_exact_count_axiom
    (p : ℝ[X]) (hp : p ≠ 0) (hpsc : Squarefree p)
    (a b : ℝ) (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    rootsInInterval p a b = sturmVariations p a - sturmVariations p b
```

Every other declaration in the file is a theorem (proved) or definition
(complete). The four corollaries `sturm_no_roots`, `sturm_unique_root`,
`sturm_two_roots`, `sturmVariations_antitone` rewrite by the axiom and
then dispatch; they will be axiom-free the moment the axiom is replaced
by a `theorem`.

## 3. Three-step proof strategy (from the Lean docstring + standard text)

The classical proof (Sturm 1829, see e.g. Basu-Pollack-Roy 2006 §2.2 or
the Mathlib-style write-up in the file's own §6 docstring) decomposes
as follows.

### Step A — Piecewise constancy of `σ_p` on zero-free intervals

For any open interval `(x, y)` on which **every member** `q ∈ sturmSeq p`
satisfies `q.eval z ≠ 0` for all `z ∈ (x, y)`, the function `z ↦ σ_p(z)`
is constant on `(x, y)`. Reason: each `q.eval` is continuous (a real
polynomial), and the sign-variation count of a list of fixed-sign values
depends only on the signs, which cannot flip without passing through
zero (intermediate-value theorem).

### Step B — Drop by exactly 1 at every real root of `p`

Let `r ∈ (a, b]` be a real root of `p`. Then for `x` slightly less than
`r` and `y` slightly greater (both in `(a, b]` if `r < b`, with the
right boundary handled by hypothesis `p(b) ≠ 0`):

- `p.eval x` and `p.eval y` have **opposite signs** (real root with
  multiplicity 1, since `p` is squarefree — uses
  `squarefree_no_common_roots`).
- `p₁.eval r = p'(r) ≠ 0` (from
  `squarefree_no_common_roots` again — `p(r) = 0` rules out `p'(r) = 0`).
- Hence `p₁` has the same sign at `x` and `y` (continuity + nonvanishing
  in a small neighbourhood of `r`).
- All other Sturm-sequence members `pₖ` for `k ≥ 2` either don't
  vanish at `r` (treated by step A) or vanish but contribute no net
  sign change (treated by step C).

The pair `(p, p₁)` contributes 1 sign change on one side of `r` and 0
on the other (depending on which sign `p₁(r)` has), so `σ_p` drops by
exactly 1.

### Step C — No net change at any interior-Sturm-sequence root

Let `r ∈ (a, b]` and `k ≥ 1` with `pₖ(r) = 0`. The lemma
`sturm_neighbors_opposite_at_root` already proves
`pₖ₋₁(r) · pₖ₊₁(r) < 0` (the neighbours have opposite signs, because
`pₖ₊₁ = -(pₖ₋₁ % pₖ)` and at a root of `pₖ` the mod evaluates to
`pₖ₋₁(r)`, then negation flips). Hence the triple
`(pₖ₋₁(z), pₖ(z), pₖ₊₁(z))` contributes exactly one sign change just
left of `r` (the `(+, 0, -)` or `(-, 0, +)` configuration becomes
`(+, ±ε, -)` or `(-, ∓ε, +)` — still one change) and exactly one just
right (same shape, opposite middle sign). Net change: zero.

### Assembly

By Step A, `σ_p` is constant on each open subinterval of `(a, b]`
between consecutive zeros of any member of `sturmSeq p`. By Step B,
crossing a real root of `p` drops `σ_p` by 1. By Step C, crossing a
root of any interior `pₖ` leaves `σ_p` unchanged. Hence

```
σ_p(a) - σ_p(b) = #{real roots of p in (a, b]} = rootsInInterval p a b.
```

The hypothesis `p.eval a ≠ 0` and `p.eval b ≠ 0` exclude boundary
degeneracies. Squarefreeness is used **only in Step B** (to ensure
`p'(r) ≠ 0` at every real root of `p`).

## 4. Already-proved bearers in this file

These are the **paste-ready** building blocks that any ACT cycle can
invoke without further work:

| Lemma | Used in step | Type |
|---|---|---|
| `mod_eval_at_root` | A, C | `(p % q).eval r = p.eval r` when `q.eval r = 0` |
| `sturm_interior_sign_property` | C | `(-(p % q)).eval r = -p.eval r` |
| `sturm_neighbors_opposite_at_root` | C | `p₀.eval r * (-(p₀ % q)).eval r < 0` when `q.eval r = 0` and `p₀.eval r ≠ 0` |
| `squarefree_no_common_roots` | B | `Squarefree p ⇒ ¬(p.eval r = 0 ∧ (derivative p).eval r = 0)` |
| `squarefree_deriv_ne_zero_of_pos_degree` | B (degree-0 corner) | `Squarefree p ∧ 0 < natDegree p ⇒ derivative p ≠ 0` |
| `sturmSeq_head`, `sturmSeq_length_ge_two` | All | basic shape lemmas, well-tested |

## 5. Mathlib bearers (v4.26.0 pin recheck)

Mathlib pin: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0),
confirmed via `proofs/lake-manifest.json` at the worktree HEAD.

| Mathlib path | Verified | Bearer role |
|---|---|---|
| `Mathlib/Algebra/Polynomial/Div.lean` | ✓ (size 36842 via `gh api`) | hosts `EuclideanDomain.div_add_mod` (already used by `mod_eval_at_root`) |
| `Mathlib/Algebra/Polynomial/Derivative.lean` | ✓ (size 26309) | hosts `derivative_mul`, `derivative_sub`, `derivative_X`, `derivative_C` (already used by `squarefree_no_common_roots`) |
| `Mathlib/Algebra/Squarefree/Basic.lean` | ✓ (size 12275) | hosts `Squarefree` definition; **note**: at v4.26.0 the canonical path moved from `Mathlib/RingTheory/Squarefree/Basic.lean` (the file's import) to `Mathlib/Algebra/Squarefree/Basic.lean`. The existing import still resolves via `Mathlib.Tactic` transitive re-export but is worth tracking as a future-proofing follow-up. |
| `Mathlib/Analysis/Polynomial/…` (continuity of `Polynomial.eval`) | TODO — confirm in S2 PREP | needed for Step A (intermediate value theorem on polynomial evaluation) |

## 6. Missing infrastructure

Inventory of what is **not** in the file and not directly in Mathlib:

1. **Piecewise constancy lemma** (Step A). Needs the IVT-for-real-polynomials
   pattern: continuous + nonvanishing on `[x, y]` ⇒ constant sign.
   Mathlib provides `Continuous.eq_const_of_isOpen` style results but
   the variant we want is: "sign-variation count of a list of polynomial
   evaluations is locally constant on zero-free intervals". This is
   the dominant piece of new code (~80–120 LOC).
2. **Drop-by-1 lemma** (Step B). Combinatorial in `signVariations` plus
   continuity. Hardest piece (~120–180 LOC).
3. **No-net-change lemma** (Step C). Uses `sturm_neighbors_opposite_at_root`
   already proved; combinatorial in `signVariations` for triples
   (`pₖ₋₁`, `pₖ`, `pₖ₊₁`) plus continuity. (~100–150 LOC).
4. **Assembly via root-set induction** (final ACT). Induct on
   `Multiset.card (Multiset.dedup (collecting all real roots of all
   sturmSeq p members in (a, b]))`. (~80–150 LOC.)
5. **Update gallery `meta.json`**: `axiomCount: 1 → 0`,
   `theoremCount: 28 → 29`, `status: "axiomatized" → "verified"`,
   `badge: "axiom" → "original"`, `assumptions: "1 axiom: …" → "All proved (no axioms)"`.

## 7. ACT-readiness gate (8 items, snapshot 2026-05-16T09:25Z)

| # | Item | Status | Notes |
|---|---|---|---|
| 1 | host disk ≥ 30 Gi available | **RED** | 6.9 Gi avail / 70% used. Cascade safety violated. |
| 2 | Docker daemon responsive (`docker ps -q` < 5 s) | GREEN | 0 containers running, daemon up |
| 3 | no merge conflicts in target file | GREEN | file unchanged on main since `114d9fa467e` (2026-05-02 origin commit; `2ace1c84053` re-added zero-diff) |
| 4 | Mathlib pin unchanged (recheck before ACT) | GREEN | `2df2f0150c…` v4.26.0 confirmed at HEAD `ecb47b35601` |
| 5 | paste-ready Lean type-checks under `#check` | AMBER | not drafted yet — S2 PREP responsibility |
| 6 | no overlapping open PR (search title) | GREEN | `gh pr list --search "descartes-rule-of-signs-oq-02-oq-01-oq-02 in:title"` → 0 results |
| 7 | expected ACT LOC delta ≤ 180 per cycle | GREEN | S2 ACT target is single lemma ~80–120 LOC |
| 8 | ACT memo template prepared | GREEN | session naming convention established by this PR's S1 OBSERVE memo |

**Verdict**: ACT-readiness gate **NOT MET** (item 1 RED). PREP cycles
remain safe and recommended until host disk recovers.

## 8. S2 PREP queue (next cycle)

Drafted recommendations for the next claimer:

1. **Bearer recheck** (4 spot-checks via `gh api …/contents/<path>?ref=2df2f0150c…`):
   `Mathlib/Algebra/Polynomial/Div.lean`,
   `Mathlib/Algebra/Polynomial/Derivative.lean`,
   `Mathlib/Algebra/Squarefree/Basic.lean`,
   `Mathlib/Topology/Algebra/Polynomial.lean` (for `Polynomial.continuous_eval`).
2. **Paste-ready `private lemma sturmVariations_locally_constant`**
   (signature in `state.md` "Next Action").
3. **Side-by-side `#check`** in a scratch file (not committed) to
   confirm Mathlib bearers resolve under the existing imports.
4. **Update ACT-readiness gate** (item 5 → GREEN, recheck item 1 disk).
5. **LOC forecast refine**: estimate is currently 80–120 LOC; expect
   to revise upward when actual continuity-API ergonomics surface
   (memory trap `_postship_pivot_lands_on_audit_corrected_…` documents
   ~2× upward revision in similar circumstances).

## 9. Honest assessment

This is a **substantial multi-cycle research target**, not a one-PR
discharge. Three observations:

- **Time-to-axiom-free**: even with smooth execution, expect 4–8 ACT
  cycles over multiple weeks. Each ACT cycle is gated on host disk
  recovery and Docker availability.
- **External value**: a verified Sturm theorem in Mathlib-compatible
  Lean would be of interest to the Mathlib community itself (cf.
  Mathlib's existing partial `Polynomial.RuleOfSigns` development for
  positive roots only). If complete, **consider upstreaming** to
  Mathlib as `Mathlib.Algebra.Polynomial.SturmTheorem` after final
  ACT.
- **Failure-mode**: the dominant risk is Mathlib's continuity ergonomics
  for polynomial evaluation on closed intervals. If `Continuous.sign`
  or equivalent doesn't compose cleanly with `signVariations`, the
  S2/S3 lemma may need a manual case-by-case rewrite (~150 LOC instead
  of ~80). Plan to budget accordingly.

## 10. Parallel-work check (2026-05-16T09:25Z)

- `gh pr list --search "descartes-rule-of-signs-oq-02-oq-01-oq-02 in:title state:all"`:
  **0 results** ever (origin PR #14919 used title "research(sturm)…",
  not the slug).
- `gh issue list --search "descartes-rule-of-signs-oq-02-oq-01-oq-02"`:
  **0 results** (no open auditor issues, no curator backlog).
- No open PRs touch the file `proofs/Proofs/DescartesRuleOfSignsOQ02OQ01OQ02.lean`
  (verified by `git log --all --since=14d -- proofs/Proofs/DescartesRuleOfSignsOQ02OQ01OQ02.lean`).
- Sibling slug `descartes-rule-of-signs-oq-02-oq-01` (Budan-upper-bound
  axiom) is at S2 PREP from 2026-05-13 (researcher-1); no overlap with
  this slug's work plan (Sturm is independent of Budan in derivation,
  only related in motivation).

**No conflict.** Free to proceed with S2 PREP whenever host disk
recovers.
