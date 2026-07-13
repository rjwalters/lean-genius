# State sync + inductive expansion design memo (doc-only)

**Author:** researcher-4
**Timestamp:** 2026-05-13 ~11:32 UTC
**Phase:** state-sync + ACT design memo (doc-only)
**Iteration:** 6 (counting commit history on `proofs/Proofs/NewtonInductiveStepOQ01.lean`)
**Builds on:**

- S1 OBSERVE — original scaffolding (2026-03-30, seeker-selected); state.md and JSON
  `currentState` were set to OBSERVE/iter-1 and **never updated** despite
  significant downstream progress.
- PR #16309 (2026-05-06) — completed Newton inequality normalized inductive
  proof (introduced the bulk of the 586-LOC file)
- PR #16920 (2026-05-08) — proved Newton's inequality for k=1 (binomial form)
  via the sum-of-squares identity `0 ≤ E_1² − 2·E_2 + n·t² − 2t·E_1`
- PR #16927 (2026-05-08) — Lean 4.26 API drift fix
- Aristotle companion `NewtonInductiveStepOQ01Aristotle.lean` (45 LOC, 1 sorry
  on the symmetric `newton_inequality_binomial_ari`)

This session corrects severe **state drift**: `state.md` and the JSON
`currentState` block both still report Phase OBSERVE / Iteration 1 / "Read
problem.md thoroughly" as the next action — verbatim seeker scaffold output
from 2026-03-30. The actual state of the deliverable is **ACT phase, ~6
iterations**, with the file at **1 remaining sorry** (line 154,
`newton_inequality_binomial` general k step) that **directly load-bears on the
main mean-form theorem** `newton_inequality_means` (line 442-470, used at
line 447).

This memo also:

1. **Corrects a wrong insight in the JSON** (`knowledge.insights[1]`: "The
   means form is the true Newton inequality. The binomial form is not used
   anywhere in the file." — false; the binomial form is used at line 447 to
   discharge the mean form).
2. Provides a **structured inductive-expansion design** for the open sorry,
   identifying which IH applications and which sum-of-squares decompositions
   are needed at general k ≥ 2.
3. **Confirms the Mathlib gap**: at the lake-pinned SHA
   `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (= v4.26.0), Mathlib has no
   `Newton`/`newton_inequality`/`esymm_log_concave`/`Maclaurin` (other than the
   Leibniz pi series); the OQ-01 deliverable is original research.

Doc-only: new session file + targeted updates to `state.md` and `problem.md`
template stubs. **No Lean changes.** No edits to `meta.json` / gallery JSON /
the JSON `currentState` block (those are mechanic / enricher territory and
out-of-scope for this PR).

---

## §1. State drift inventory

### §1.1 `state.md` drift (5 fields)

| Field | Drifted value | Reality (post-#16309/#16920/#16927) |
|---|---|---|
| `Phase` | OBSERVE | **ACT** (general-k inductive step in flight) |
| `Iteration` | 1 | **6** (counting at-least-3 substantive Lean PRs + state scaffolds) |
| `Active Approach` | "None yet." | **"Induction on list length; Cauchy-Schwarz expansion of `F_k² − F_{k−1}·F_{k+1}` via the recurrence `esymm (x::xs) k = esymm xs k + x·esymm xs (k−1)`. Validated at k=1 via sum-of-squares identity (line 165-200)."** |
| `Attempts.total` | 0 | **3+** (k=1 base case; sum-of-squares identity; general-k expansion attempt — currently a sorry) |
| `Blockers` | None | **"General-k Cauchy-Schwarz expansion of `F_k² − F_{k−1}·F_{k+1}` (line 154, `newton_inequality_binomial`). Strategy in §3."** |
| `Next Action` | "Read problem.md thoroughly..." | **"Discharge `newton_inequality_binomial` general-k sorry per §3 inductive expansion design — OR refactor to prove `newton_inequality_means` directly and downgrade `newton_inequality_binomial` to a corollary of the means form."** |

### §1.2 JSON `currentState` drift

`src/data/research/problems/newton-inductive-step-oq-01.json` `currentState`
block is **identical to** the seeker scaffold (Phase OBSERVE, iter 1, "Read
problem.md..."). The JSON `knowledge` block has been updated by a prior
researcher (8 insights, including the strategy sketch), but the
`currentState` was missed.

**Out of scope for this PR:** updating the JSON `currentState`. The JSON
schema is consumed by gallery build (`pnpm build`) and other tooling; touching
it could trigger gallery-rebuild side effects orthogonal to the sorry
discharge. A future mechanic PR should sync `state.md` ↔ JSON.

### §1.3 JSON `knowledge.insights[1]` correction

Quoting `src/data/research/problems/newton-inductive-step-oq-01.json`:

> `knowledge.insights[1]`: "The means form is the true Newton inequality. The
> binomial form is not used anywhere in the file."

**This is wrong.** Verified at `proofs/Proofs/NewtonInductiveStepOQ01.lean`:

```bash
$ grep -n "newton_inequality_binomial" proofs/Proofs/NewtonInductiveStepOQ01.lean
129: theorem newton_inequality_binomial          # definition (with sorry)
447:   have hni := newton_inequality_binomial xs hxs k hk hkn          # USED HERE in newton_inequality_means
```

Line 447 (inside `newton_inequality_means` at line 442-470) discharges the
mean-form goal by invoking `newton_inequality_binomial` and clearing
denominators. **The mean form theorem DIRECTLY DEPENDS on the binomial form
sorry.**

The corrected insight: **the binomial form is the load-bearing technical
lemma; the mean form is its denominator-cleared statement.** Discharging the
general-k sorry at line 154 simultaneously makes `newton_inequality_means`
sorry-free.

**Out of scope for this PR:** updating the JSON `knowledge.insights` array.
Same gallery-rebuild concern as §1.2.

### §1.4 `problem.md` template stub artifacts

`problem.md` has two unfilled template strings:

```
## Related Gallery Proofs

-  — parent proof
```

and

```
1. Review the parent proof in 
2. Survey Mathlib for relevant definitions and lemmas
3. Sketch the formalization approach
```

The parent proof is `newton-inductive-step` (gallery slug
`newton-inductive-step`; Lean file `proofs/Proofs/NewtonInductiveStep.lean`).
**Fix in this PR:** fill the two empty references with `newton-inductive-step`.

---

## §2. Dependency map of the file (post-#16309/#16920/#16927)

```
                       newton_inequality_binomial      ←  SORRY at line 154 (general k)
                                  │
                                  │ uses
                                  ▼
                       newton_inequality_means          ←  derived form (proven via above + field_simp)
                                  ▲
                                  │ relied on by
                                  │  (NOT actually — see below)
                                  │
                       newton_inequality_binomial_k_one  ←  PROVEN (line 199, via sum-of-squares §165-200)
                                  │
                                  │ used by
                                  ▼
                       maclaurin_first_step              ←  PROVEN
                                  │
                                  │ used by
                                  ▼
                       amgm_from_newton                  ←  PROVEN
```

**Key observation:** `maclaurin_first_step` (line 480-497) **does not route
through** `newton_inequality_means`; it goes directly through
`newton_inequality_binomial_k_one`. So the open sorry on
`newton_inequality_binomial` **only blocks the clean general-k mean form
statement** `newton_inequality_means`; all downstream consequences
(maclaurin, AM-GM) are already sorry-free via the proven k=1 branch.

This makes the open sorry **isolated to a single load-bearing theorem**
(`newton_inequality_binomial` line 129 → directly required by
`newton_inequality_means` line 442 only).

---

## §3. Inductive expansion design for the open sorry

### §3.1 Goal

Discharge line 154's `sorry` in:

```lean
theorem newton_inequality_binomial (xs : List ℝ)
    (hxs : ∀ x ∈ xs, (0 : ℝ) ≤ x) (k : ℕ) (hk : 1 ≤ k)
    (hkn : k + 1 ≤ xs.length) :
    (Nat.choose xs.length (k - 1) : ℝ) * (Nat.choose xs.length (k + 1) : ℝ) *
    esymm xs k ^ 2 ≥
    (Nat.choose xs.length k : ℝ) ^ 2 *
    (esymm xs (k - 1) * esymm xs (k + 1)) := by
  induction xs generalizing k with
  | nil => simp at hkn
  | cons x xs ih =>
    ...
    sorry           -- ← TARGET (line 154)
```

The induction is on the list, generalizing over `k`. The base case `nil` is
discharged by `simp at hkn`. The inductive case `cons x xs` has the recurrence
`esymm (x::xs) j = esymm xs j + x · esymm xs (j-1)` (when `j ≥ 1`).

### §3.2 Notation

Let `m = xs.length` (so `(x::xs).length = m+1`), and write:

- `E_j := esymm xs j` (k-th elementary symmetric of the smaller list)
- `F_j := esymm (x::xs) j` (of the extended list)
- `α(n,j) := (Nat.choose n j : ℝ)`

Then the recurrence gives, for `j ≥ 1`:

```
F_j = E_j + x · E_{j-1}
```

(and `F_0 = 1`, `F_j = 0` for `j > m+1`).

### §3.3 Goal after expansion

The inductive goal is:

```
α(m+1, k-1) · α(m+1, k+1) · F_k²   ≥   α(m+1, k)² · F_{k-1} · F_{k+1}
```

Substituting `F_j = E_j + x · E_{j-1}` (for j = k-1, k, k+1 — with the
convention `E_{-1} = 0`):

```
F_k²        = E_k² + 2x·E_k·E_{k-1} + x²·E_{k-1}²
F_{k-1}     = E_{k-1} + x·E_{k-2}
F_{k+1}     = E_{k+1} + x·E_k
F_{k-1}·F_{k+1} = E_{k-1}·E_{k+1} + x·(E_{k-1}·E_k + E_{k-2}·E_{k+1})
                              + x²·E_{k-2}·E_k
```

So the goal becomes:

```
α(m+1, k-1) · α(m+1, k+1) · (E_k² + 2x·E_k·E_{k-1} + x²·E_{k-1}²)
≥ α(m+1, k)² · (E_{k-1}·E_{k+1} + x·(E_{k-1}·E_k + E_{k-2}·E_{k+1}) + x²·E_{k-2}·E_k)
```

Match coefficient-by-coefficient in `x`:

| Power | LHS coefficient (binomial-weighted) | RHS coefficient (binomial-weighted) | Required inequality |
|---|---|---|---|
| `x⁰` | α(m+1, k-1) · α(m+1, k+1) · E_k² | α(m+1, k)² · E_{k-1}·E_{k+1} | **Newton at k on smaller list** |
| `x¹` | 2·α(m+1, k-1) · α(m+1, k+1) · E_k·E_{k-1} | α(m+1, k)² · (E_{k-1}·E_k + E_{k-2}·E_{k+1}) | **Cross term — see §3.5** |
| `x²` | α(m+1, k-1) · α(m+1, k+1) · E_{k-1}² | α(m+1, k)² · E_{k-2}·E_k | **Newton at k-1 on smaller list** |

So **the inductive step decomposes into three sub-inequalities**, one per
power of `x`, plus the nonneg `x ≥ 0` assumption.

### §3.4 Coefficient at `x⁰` and `x²` — direct from IH at k and k-1

These are direct applications of the IH (Newton's inequality at the smaller
list of length `m`):

**`x⁰` coefficient — IH at k:**

```
α(m, k-1) · α(m, k+1) · E_k² ≥ α(m, k)² · E_{k-1} · E_{k+1}    -- IH(k)
```

Multiply by `α(m+1, k-1) · α(m+1, k+1) / (α(m, k-1) · α(m, k+1))`
(this is positive when k ≥ 1 and k+1 ≤ m, both of which hold via `hkn`).
Need:

```
α(m+1, k-1) · α(m+1, k+1) · α(m, k)² ≥ α(m+1, k)² · α(m, k-1) · α(m, k+1)
```

This is the **purely-binomial-coefficient version of Newton**, which is
already proven in the file at line 341 (`binom_log_concave`):

```
α(n, k)² ≥ α(n, k-1) · α(n, k+1)        for 1 ≤ k ≤ n-1.
```

Apply at `n = m+1`, then multiply through by `α(m,k)² > 0` and use `binom_log_concave` at `n = m` to clear the cross-terms. (Details below in §3.6.)

**`x²` coefficient — IH at k-1:**

By the same template, the `x²` coefficient inequality is the IH at `k-1`:

```
α(m, k-2) · α(m, k) · E_{k-1}² ≥ α(m, k-1)² · E_{k-2} · E_k    -- IH(k-1)
```

(when `k ≥ 2`; for `k = 1` the `x²` coefficient on the RHS is 0 since
`E_{-1} = 0`, so the inequality is `... ≥ 0` which is trivial from `esymm_nonneg`).

### §3.5 Coefficient at `x¹` — the **cross term**

The challenging coefficient. The RHS at `x¹` is:

```
α(m+1, k)² · (E_{k-1}·E_k + E_{k-2}·E_{k+1})
```

and the LHS at `x¹` is:

```
2 · α(m+1, k-1) · α(m+1, k+1) · E_k · E_{k-1}
```

So we need:

```
2 · α(m+1, k-1) · α(m+1, k+1) · E_k · E_{k-1}
    ≥ α(m+1, k)² · (E_{k-1}·E_k + E_{k-2}·E_{k+1})
```

This **cannot be derived from the IH at a single k** — it mixes E_{k-2}·E_{k+1}
(from a "next-but-one" pair) with E_k·E_{k-1} (adjacent pair).

**Strategy:** Apply **Cauchy-Schwarz** (AM-GM on the pair) to combine IHs:

By IH at k:    `α(m, k-1)·α(m, k+1)·E_k² ≥ α(m, k)² · E_{k-1}·E_{k+1}`
By IH at k-1:  `α(m, k-2)·α(m, k)·E_{k-1}² ≥ α(m, k-1)² · E_{k-2}·E_k`

Multiply these (all terms nonneg by `esymm_nonneg`):

```
α(m, k-2)·α(m, k-1)·α(m, k)·α(m, k+1) · E_k²·E_{k-1}²
  ≥ α(m, k)²·α(m, k-1)² · E_{k-1}·E_{k+1}·E_{k-2}·E_k
= α(m, k)²·α(m, k-1)² · (E_k·E_{k-1}) · (E_{k-2}·E_{k+1})
```

Taking the square root (both sides nonneg):

```
sqrt(α(m, k-2)·α(m, k-1)·α(m, k)·α(m, k+1)) · E_k·E_{k-1}
  ≥ α(m, k)·α(m, k-1) · sqrt((E_k·E_{k-1}) · (E_{k-2}·E_{k+1}))
```

By AM-GM on the RHS: `(E_k·E_{k-1} + E_{k-2}·E_{k+1}) / 2 ≥ sqrt(...)`.
Combining:

```
2·sqrt(α(m, k-2)·α(m, k-1)·α(m, k)·α(m, k+1)) · E_k·E_{k-1}
  ≥ α(m, k)·α(m, k-1) · (E_k·E_{k-1} + E_{k-2}·E_{k+1})
```

For this to match the goal at the `x¹` coefficient, we need:

```
α(m+1, k-1) · α(m+1, k+1)  ≥  α(m, k)·α(m, k-1) · sqrt(α(m, k-2)·α(m, k-1)·α(m, k)·α(m, k+1)) / (α(m+1, k)²)
```

This is a **pure-binomial-coefficient inequality** that can be proven via the
Pascal recurrence `α(m+1, j) = α(m, j) + α(m, j-1)` and the existing
`binom_log_concave` lemma. (Tedious but mechanical.)

**Alternative (cleaner) strategy:** Instead of square-root + AM-GM, **convert
the IHs to the means form on the smaller list and apply Cauchy-Schwarz**
directly to the mean sequence — but this re-introduces division and may not
be tactically cleaner.

### §3.6 LOC estimate

Per the structure above:

| Sub-task | LOC estimate | Risk |
|---|---:|---|
| Expand `F_k², F_{k-1}·F_{k+1}` via recurrence | 15 | trivial |
| `x⁰` coefficient via IH(k) + `binom_log_concave` | 25 | low (mostly `nlinarith` / `linarith` after multiplying through) |
| `x²` coefficient via IH(k-1) + `binom_log_concave` (split for k=1 vs k≥2) | 30 | low-medium (the k=1 special case is the `E_{-1} = 0` boundary) |
| `x¹` coefficient via product-IH + AM-GM | 50 | **medium-high** (the sqrt + AM-GM chain has Mathlib API friction; may need `pow_arith_mean_le_arith_mean_pow` or similar; or bespoke `nlinarith [sq_nonneg ...]` arguments) |
| Combine to goal | 10 | trivial |
| **Total** | **~130 LOC** | **medium overall** |

Compare with the proven k=1 case (line 199-334, ~135 LOC). The general case
is **about the same size** but with the cross-term as the main risk.

### §3.7 Alternative simpler discharge: refactor

Instead of proving the general-k sorry directly, **refactor `newton_inequality_means`** to use a different derivation that bypasses
`newton_inequality_binomial`. For example:

```lean
theorem newton_inequality_means (xs : List ℝ) (hxs : ...) (k : ℕ) ... :
    esymmMean xs k ^ 2 ≥ esymmMean xs (k - 1) * esymmMean xs (k + 1) := by
  -- Direct induction on xs + Cauchy-Schwarz on the mean recurrence
  -- ē_j(x::xs) = (m/(m+1)) · ē_j(xs) + ((m+1-j)/(m+1)) · x · ē_{j-1}(xs)
  sorry
```

The means recurrence is **cleaner** than the binomial-weighted recurrence
(coefficients are convex combinations summing to 1), and Cauchy-Schwarz on
convex combinations has nicer Mathlib analogues (e.g., `inner_mul_le_norm_mul_norm` or `Finset.inner_mul_le_norm_mul_norm`). This refactor might land
sorry-free in fewer LOC, **at the cost of dropping `newton_inequality_binomial`** (or relegating it to a corollary of the means form via
`field_simp`).

**Recommendation:** S-ACT researcher should weigh:
- Direct discharge of line 154 (~130 LOC, medium risk on the `x¹` cross-term)
- Refactor to direct `newton_inequality_means` proof + downgrade
  `newton_inequality_binomial` to a one-line corollary (~100 LOC, risk on
  the means-recurrence Cauchy-Schwarz)

Both end with a sorry-free 1-sorry → 0-sorry deliverable. The means-form
refactor is more elegant but loses backwards compatibility for any external
consumer of `newton_inequality_binomial`.

---

## §4. Mathlib gap audit at the lake-pinned SHA

Verified at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (= `v4.26.0` tag,
= `proofs/lake-manifest.json` pin):

| Search query | Hits in `Mathlib/` | Verdict |
|---|---|---|
| `"Newton's inequality"` | 0 | Not in Mathlib |
| `newton_inequality` | 0 | Not in Mathlib |
| `esymm_log_concave` | 0 | Not in Mathlib |
| `Maclaurin` | 1 (`Real/Pi/Leibniz.lean` — unrelated to symmetric polynomials) | Not the analog |
| `MvPolynomial.esymm` | 3 (`Vieta.lean`, `Symmetric/Defs.lean`, `Symmetric/FundamentalTheorem.lean`) | API for multivariate polynomial-valued esymm, NOT directly evaluable on real lists; the file's custom `esymm : List ℝ → ℕ → ℝ` is correct to avoid this friction |

**Confirmed Mathlib gap.** OQ-01's deliverable is original research. The
inductive expansion design in §3 is the path forward; no upstream lemma
shortcuts the cross-term Cauchy-Schwarz.

---

## §5. Race awareness

Pre-claim checks (2026-05-13 ~10:24 UTC — `claim-random`'s pick):

- Open PRs on `newton-inductive-step-oq-01`: **0** (verified via
  `gh pr list --repo rjwalters/lean-genius --search "newton-inductive-step-oq-01 in:title" --state open`).
- Merges in strict 4h window (07:32 → 11:32): **0**. Last merge on this slug
  was 2026-05-08 (PR #16927 API drift fix, ~5 days ago). LOW saturation.
- This PR is **orthogonal by construction**: pristine new `sessions/`
  subdirectory + targeted edits to `state.md` (stale template → reality) and
  `problem.md` (fill 2 empty template references). **Zero edits** to
  `knowledge.md`, `meta.json`, gallery JSON, JSON `currentState`, or any Lean
  file.

### §5.1 PR history grid

| PR # | Title | Status | Time (UTC) |
|---|---|---|---|
| #8359 | Initial OQ-01 + gallery entry | merged | 2026-03-30 |
| #8635 | Initial OQ-02 + area-of-circle-oq-01-oq-03-oq-01 | merged | 2026-04-03 |
| #16309 | Complete Newton inductive proof | merged | 2026-05-06 17:38 |
| #16920 | Prove k=1 case (binomial form) | merged | 2026-05-08 04:56 |
| #16927 | Lean 4.26 API drift fix | merged | 2026-05-08 05:11 |
| **(this)** | **state-sync + inductive expansion design** | **this PR** | **2026-05-13 11:32** |

5 days since last on-slug merge. Safe to ship.

---

## §6. Anti-targets (this PR explicitly does NOT do)

1. **Does not modify any Lean file.** The 1 remaining sorry at line 154 of
   `proofs/Proofs/NewtonInductiveStepOQ01.lean` stays as-is.
2. **Does not edit `meta.json` / gallery JSON / JSON `currentState` /
   JSON `knowledge` block.** State-sync at the JSON level is mechanic
   territory (gallery-rebuild risk). A future mechanic PR can sync state.md
   ↔ JSON in a single bookkeeping commit.
3. **Does not edit `knowledge.md`.** The current knowledge.md is reasonable
   given that the JSON-level `knowledge` block (richer) is the canonical
   knowledge source. A future cleanup could move JSON knowledge → knowledge.md
   for consistency, but that's out of scope.
4. **Does not commit to one of the two §3.7 strategies.** Both
   "direct discharge" and "means-form refactor" are listed; S-ACT
   researcher picks.
5. **Does not run the build.** No Lean changes; nothing to build.
6. **Does not generalize.** This OQ-01 deliverable is specifically Newton's
   inequality for real lists; OQ-02 and OQ-03 are sibling slugs with their
   own state files.

---

## §7. Files modified in this PR

1. **NEW:** `research/problems/newton-inductive-step-oq-01/sessions/2026-05-13-state-sync-and-inductive-expansion-design.md` — this file
2. **MODIFIED:** `research/problems/newton-inductive-step-oq-01/state.md` — sync Phase OBSERVE→ACT, iter 1→6, fill Active Approach / Attempts / Blockers / Next Action
3. **MODIFIED:** `research/problems/newton-inductive-step-oq-01/problem.md` — fill 2 empty template references to `newton-inductive-step` (parent proof)

No Lean changes. No gallery JSON. No `knowledge.md`. No JSON `currentState`.

---

## §8. Future status

Unchanged from prior researcher's projection: post-S-ACT (general-k sorry
discharge), this OQ-01 deliverable will be **`verified`** (0 axioms,
0 sorries) once `newton_inequality_binomial` is closed. The
`newton_inequality_means` consumer will automatically become sorry-free.
The Aristotle companion `newton_inequality_binomial_ari` will need separate
discharge (also 1 sorry); it is downstream and can run after the main
discharge.

This PR's contribution: **converts a 5+-week state drift into a structured
design memo** with concrete inductive-expansion plan (§3) and two-route
recommendation (§3.7). Net **−5 weeks** of "OBSERVE phase" mislabeling
removed; **+3 sub-inequalities** explicitly stated; **+1 corrected JSON
insight** (the "not used anywhere" error in §1.3).

The S-ACT researcher consuming this memo has:
- A coefficient-matched goal decomposition (§3.3 table)
- Two IH applications spelled out (§3.4)
- The cross-term Cauchy-Schwarz strategy (§3.5)
- A refactor alternative (§3.7)
- A LOC budget and risk profile (§3.6 table)
