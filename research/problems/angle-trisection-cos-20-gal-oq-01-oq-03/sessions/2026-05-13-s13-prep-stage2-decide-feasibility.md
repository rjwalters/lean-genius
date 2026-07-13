# S13 PREP — Stage 2 `decide`-tactic feasibility audit + corrected proof template

**Date**: 2026-05-13
**Researcher**: researcher-9
**Mode**: PREP (doc-only design memo, audit of S11 PREP Stage 2)
**Status**: pristine, orthogonal to in-flight #17906 (S4 build-pending);
companion to merged #18571 (S12 PREP, Stage 1 audit, merged 2026-05-13 05:06)

## 1. Why this PREP

S11 PREP (#18410, merged 2026-05-13 02:09) §2 ships **two** sketched
theorems for the next ACT iteration:

- **Stage 1**: `cyclotomic_two_mul_prime_subLeadingCoeff_uniform`
  (the cyclotomic side; for every odd prime `p`, the sub-leading
  coefficient of `Φ_{2 p}` is `-1`).
- **Stage 2**: `r_subLeadingCoeff_via_moebius_uniform`
  (the trace bridge; quantified over `p ∈ ({5, 7, 11, 13} : Finset ℕ)`,
  asserts `(r p).coeff ((p-1)/2 - 1) = -((p:ℤ) - 1) + (cyclotomic (2*p) ℤ).coeff (p - 2)`).

S12 PREP (#18571, opened 2026-05-13 04:32) audits **Stage 1**:
corrects the Mathlib name `Finset.sum_coeff` → `Polynomial.finsetSum_coeff`,
revises the Stage 1 LOC estimate from ~10 to ~25, and supplies a
verified Lean proof tree.

This S13 PREP audits **Stage 2**. The S11 PREP §2 Stage 2 sketch
proposes a per-prime `decide` proof:

```lean
rcases Finset.mem_insert.mp hp with rfl | hp
· -- p = 5
  decide  -- ← bare `decide` on (r 5).coeff 1 = -4 + (cyclotomic 10 ℤ).coeff 3
```

**Bare `decide` will not close the per-prime goals.** The RHS contains
`(cyclotomic (2 * p) ℤ).coeff ((p : ℕ) - 1 - 1)`, and `cyclotomic`
is *not* reducible to a normal form by the kernel — Mathlib's
`Polynomial.cyclotomic` is defined recursively via Möbius-style
products of integer-coefficient polynomials, gated through
`Polynomial.cyclotomic'` over `ℂ` and integer-coercion
infrastructure. There is no `Decidable` instance for the equation
`(cyclotomic 22 ℤ).coeff 9 = -1` that bypasses unfolding the recursive
definition, and the unfolding chain blows up well before yielding a
normal form (in particular, `cyclotomic 22 ℤ` is built from
`cyclotomic 1, 2, 11, 22` via the standard
`X^n - 1 = ∏_{d ∣ n} Φ_d(X)` decomposition).

The corrected Stage 2 proof must first **rewrite** each
`cyclotomic (2*p) ℤ` using the explicit ring expressions already
proved in the file (`cyclotomic_ten_eq`, `cyclotomic_fourteen_eq`,
`cyclotomic_22_eq`, `cyclotomic_26_eq`), at which point
`coeff` simp lemmas + `decide` (or `norm_num`) can finish.

This PREP records the corrected per-prime proof template so the
future Stage 2 ACT does not waste cycles on a `decide` that won't
fire.

## 2. In-file precedent for the corrected pattern

Every existing per-prime cyclotomic-coefficient lemma in
`AngleTrisectionCos20GalOQ01OQ03.lean` follows the same
**`rw [explicit cyclotomic form]; simp only [coeff_*]; (decide | norm_num)`**
shape. Two examples:

### (a) Norm side — `(cyclotomic 10 ℤ).eval (-1) = 5` (line 532)

```lean
theorem cyclotomic_ten_eval_neg_one : (cyclotomic 10 ℤ).eval (-1) = 5 := by
  rw [cyclotomic_ten_eq]                                     -- ← rewrite first
  simp only [eval_add, eval_sub, eval_pow, eval_X, eval_one]
  norm_num
```

The pattern `rw [cyclotomic_2p_eq]` is **mandatory**: bare `decide`
or `norm_num` on `(cyclotomic 10 ℤ).eval (-1) = 5` does not close.

### (b) Trace half (existing) — `r_subLeadingCoeff_eq_neg_p` (line 365)

```lean
theorem r_subLeadingCoeff_eq_neg_p :
    (r 5).coeff 1 = -5
    ∧ (r 7).coeff 2 = -7
    ∧ (r 11).coeff 4 = -11
    ∧ (r 13).coeff 5 = -13 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [r_5_eq]                                              -- ← rewrite r p first
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    decide
  ...
```

The S4 ACT (PR #17913) trace lemma proves the LHS-only fingerprint
(no cyclotomic on the RHS), so a single `rw [r_p_eq]` is enough.
Stage 2 of S11 PREP introduces `cyclotomic` on the RHS, so it needs
**two** rewrites per prime: `rw [r_p_eq, cyclotomic_2p_eq]`.

## 3. Corrected Stage 2 proof template

```lean
/-- For `p` in the verified prime set `{5, 7, 11, 13}`, the
    sub-leading coefficient of `r p` matches the Möbius-driven
    Vieta-trace expression. -/
theorem r_subLeadingCoeff_via_moebius_uniform :
    ∀ p ∈ ({5, 7, 11, 13} : Finset ℕ),
      (r p).coeff ((p - 1) / 2 - 1)
        = -((p : ℤ) - 1) + (cyclotomic (2 * p) ℤ).coeff ((p : ℕ) - 1 - 1) := by
  intro p hp
  rcases Finset.mem_insert.mp hp with rfl | hp
  · -- p = 5  ⇒  (r 5).coeff 1 = -4 + (cyclotomic 10 ℤ).coeff 3
    rw [r_5_eq, show (2 * 5 : ℕ) = 10 from rfl, cyclotomic_ten_eq]
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    decide
  rcases Finset.mem_insert.mp hp with rfl | hp
  · -- p = 7  ⇒  (r 7).coeff 2 = -6 + (cyclotomic 14 ℤ).coeff 5
    rw [r_7_eq, show (2 * 7 : ℕ) = 14 from rfl, cyclotomic_fourteen_eq]
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    decide
  rcases Finset.mem_insert.mp hp with rfl | hp
  · -- p = 11 ⇒  (r 11).coeff 4 = -10 + (cyclotomic 22 ℤ).coeff 9
    rw [r_11_eq, show (2 * 11 : ℕ) = 22 from rfl, cyclotomic_22_eq]
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    decide
  · -- p = 13 ⇒  (r 13).coeff 5 = -12 + (cyclotomic 26 ℤ).coeff 11
    rcases Finset.mem_singleton.mp hp with rfl
    rw [r_13_eq, show (2 * 13 : ℕ) = 26 from rfl, cyclotomic_26_eq]
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    decide
```

### Why each piece

- `rw [r_p_eq]`: unfolds the parametric `r p` to its explicit ring
  expression. Without this, `(r 5).coeff 1` is stuck on the
  `noncomputable def r` pattern-match.
- `show (2 * p : ℕ) = (2p) from rfl`: makes the literal cyclotomic
  index visible. The kernel reduces `2 * 5 = 10` definitionally, but
  inserting the `show` ensures `rw [cyclotomic_2p_eq]` matches the
  literal form `cyclotomic 10 ℤ` (not the meta-form
  `cyclotomic (2 * 5) ℤ` that may or may not be what Lean's display
  shows).
- `rw [cyclotomic_2p_eq]`: substitutes the explicit polynomial form
  proved in S5+S6.
- `simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]`:
  pushes `coeff` through the polynomial algebra, leaving an
  `if-then-else` cascade in `ℤ`.
- `decide`: resolves the integer arithmetic + the `if-then-else`
  branches at the literal index (e.g. `coeff 3` of a degree-4
  polynomial).

### Substitution check (per prime, post-`rfl`-reduction)

For `p = 5`, after `rcases ... rfl`:

```
goal:  (r 5).coeff ((5 - 1) / 2 - 1) = -((5 : ℤ) - 1) + (cyclotomic (2 * 5) ℤ).coeff ((5 : ℕ) - 1 - 1)
       └──────────┬───────────┘     └────────┬─────┘    └───────┬─────────┘     └──────────┬─────────┘
              (r 5).coeff 1               -4 (in ℤ)        cyclotomic 10 ℤ              3 (in ℕ)
```

After `rw [r_5_eq, _, cyclotomic_ten_eq]` the goal is

```
((X : ℤ[X])^2 - C 5 * X + C 5).coeff 1
  = -((5 : ℤ) - 1) + ((X : ℤ[X])^4 - X^3 + X^2 - X + 1).coeff 3
```

After `simp only [coeff_*]`:

```
(if 2 = 1 then 1 else 0) - 5 * (if 1 = 1 then 1 else 0) + 5 * (if 0 = 1 then 1 else 0)
  = -((5 : ℤ) - 1)
    + ((if 4 = 3 then 1 else 0) - (if 3 = 3 then 1 else 0) + (if 2 = 3 then 1 else 0)
       - (if 1 = 3 then 1 else 0) + (if 0 = 3 then 1 else 0))
```

After `decide`:

```
0 - 5 + 0 = -4 + (0 - 1 + 0 - 0 + 0)
↔ -5 = -5  ✓
```

Identical machinery handles `p = 7, 11, 13` after the parallel
rewrites. The only LOC delta vs. `r_subLeadingCoeff_eq_neg_p`
(existing S4 ACT theorem) is the extra `, cyclotomic_2p_eq` rewrite
and the `show (2 * p : ℕ) = ...` literal-form bridge (~1 token each).

## 4. Cross-validation against the §5 table of S11 PREP

S11 PREP §5 (line 254) cross-validates the *arithmetic statement*:

| `p` | `(p-1)/2 - 1` | `(r p).coeff` | `(p:ℕ) - 2` | `Φ_{2p}.coeff` | RHS |
|----:|--------------:|--------------:|------------:|---------------:|-----:|
| 5   | 1             | -5            | 3           | -1             | -5 ✓ |
| 7   | 2             | -7            | 5           | -1             | -7 ✓ |
| 11  | 4             | -11           | 9           | -1             | -11 ✓ |
| 13  | 5             | -13           | 11          | -1             | -13 ✓ |

This table is **mathematically correct** and unchanged by this PREP.
What changes is the *Lean tactic* used to discharge each row:

| Row | S11 PREP §2 sketch | Corrected (this PREP §3) |
|-----|--------------------|--------------------------|
| `p = 5`  | `decide` only | `rw [r_5_eq, _, cyclotomic_ten_eq]; simp only [coeff_*]; decide` |
| `p = 7`  | `decide` only | `rw [r_7_eq, _, cyclotomic_fourteen_eq]; simp only [coeff_*]; decide` |
| `p = 11` | `decide` only | `rw [r_11_eq, _, cyclotomic_22_eq]; simp only [coeff_*]; decide` |
| `p = 13` | `decide` only | `rw [r_13_eq, _, cyclotomic_26_eq]; simp only [coeff_*]; decide` |

Each corrected row is ~3 tactic lines instead of 1; the per-prime
arithmetic conclusion is unchanged.

## 5. LOC re-estimate for the full Stage 2 deliverable

S11 PREP §2 estimates **~35 LOC for Stage 2 trace bridge**
(`r_subLeadingCoeff_via_moebius_uniform`) plus ~25 for the main
corollary `r_subLeadingCoeff_eq_neg_p_uniform`. Substituting the
corrected per-prime proof:

| Component | S11 PREP estimate | Corrected estimate |
|-----------|-------------------:|-------------------:|
| Theorem statement (4-prime Finset)             |  4 |  4 |
| `intro p hp` + first `rcases`                  |  2 |  2 |
| Per-prime proof block (×4) — S11 used `decide` only | 4×1 = 4 | 4×4 = 16 |
| `rcases ... rfl` between primes (×3)            | 3×1 = 3 | 3×1 = 3 |
| Closing `· decide` after final `rcases ... rfl` |  2 |  2 |
| Doc-comment                                    | 5 | 5 |
| Blank lines / spacing                          | 5 | 5 |
| **Stage 2 trace bridge total**                 | **~25** | **~37** |

For the main S11 corollary `r_subLeadingCoeff_eq_neg_p_uniform`
(which composes Stage 1 + Stage 2 trace bridge), the S11 PREP §2
sketch (~25 LOC) is unchanged by this audit — it does not introduce
any new `cyclotomic` arithmetic; it just composes the bridge with the
Stage 1 lemma via `ring`.

**Combined Stage 2 deliverable**: ~37 + ~25 = **~62 LOC**, vs. S11
PREP's ~60. The delta is small; the audit's value is in *correctness
of tactic*, not LOC.

## 6. Why the Stage 1 `Finset.sum_coeff` audit (#18571) is orthogonal

#18571 audits Stage 1's bearer name (`Finset.sum_coeff` does not
exist; correct is `Polynomial.finsetSum_coeff`, with `finset_sum_coeff`
being a deprecated alias as of 2026-04-08). That audit operates on
the *cyclotomic-side* lemma and its *Mathlib API*.

This S13 PREP audits Stage 2's *r-side trace bridge* and its *file-internal
tactic structure*. The two audits touch disjoint Stage{1,2} lemmas
and disjoint Mathlib-vs-internal-rewrite concerns:

| Audit | Lemma | Concern | Bearer |
|-------|-------|---------|--------|
| #18571 (S12 PREP) | Stage 1 (cyclotomic-only) | wrong Mathlib decl name | upstream Mathlib |
| this S13 PREP    | Stage 2 (trace bridge)    | bare `decide` on `cyclotomic.coeff` won't fire | local `cyclotomic_2p_eq` lemmas |

A future S(N) ACT iteration that implements both Stages will need
*both* corrections: the Stage 1 name fix from #18571 and the Stage 2
rewrite-template fix from this PREP.

## 7. Anti-targets

The following are **out of scope** for this audit and remain S(N+) work:

1. **Implementing Stage 1 or Stage 2.** This is doc-only PREP. The
   ACT implementation is an independent ~60-LOC Lean PR.
2. **Lifting Stage 2 to *every* odd prime** (S11 PREP §7 anti-target #1).
   Same status as before this audit: a future S11b candidate via the
   S9 uniform anchor; not affected by the tactic correction here.
3. **Extending Stage 2 to use `Polynomial.subLeadingCoeff` directly**
   (S11 PREP §4 discussion). The corrected template here uses
   explicit `coeff` indices, matching the S4 ACT style.
4. **The HARD half of the Eisenstein conjecture**
   (sub-leading divisibility for `0 < k < (p-1)/2`). State.md §312–316
   blocker; ramification calculation, ~200–400 LOC. Unaffected by
   this PREP.

## 8. No-edit guarantee

This PREP **does not** touch:

- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean` (1166 lines after S10)
- `proofs/Proofs.lean` (manifest)
- `research/problems/angle-trisection-cos-20-gal-oq-01-oq-03/{problem, knowledge, state}.md`
- `src/data/research/problems/angle-trisection-cos-20-gal-oq-01-oq-03.json`
- `src/data/proofs/angle-trisection-cos-20-gal-oq-01-oq-03/` (gallery)
- The existing `sessions/2026-05-12-s11-prep-trace-moebius-bridge.md`
- Any other research-slug files

Only the new `sessions/2026-05-13-s13-prep-stage2-decide-feasibility.md`
file is added.

## 9. Race awareness

At PREP-push time (2026-05-13, 05:00–05:15 UTC):

- `gh pr list --search "angle-trisection-cos-20-gal-oq-01-oq-03 in:title" --state open`
  shows **one** open PR:
  - **#17906** (S4 — irreducibility round-out, build pending,
    opened 2026-05-12 06:22). Modifies the same Lean file
    (`proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean`); does
    *not* touch `sessions/`. Disjoint from this PREP.
- The existing `sessions/2026-05-12-s11-prep-trace-moebius-bridge.md`
  is unmodified.
- Most recent merges (verified via `gh pr list --search ... --state all`):
  - 2026-05-13 05:06: #18571 S12 PREP (Stage 1 audit, doc-only).
    Just merged at PREP-write time; this PREP rebases onto the
    post-merge `main` and adds a sibling `sessions/2026-05-13-s13-…`
    file. No file-level conflict — different Stage focus, different
    filename.
  - 2026-05-13 02:09: #18410 S11 PREP (trace-Möbius bridge,
    doc-only). 3 hours ago — beyond the 30-min-post-merge release
    threshold.
  - 2026-05-12 23:20: #18204 S10 ACT (uniform constant-coefficient
    corollary, build pending). >5 hours ago.

**Conflict surface**: zero. Strictly additive single-file PR
creating a new entry in the existing `sessions/` subdirectory.

## 10. Hand-off checklist for the future Stage 2 ACT iteration

When the next researcher implements Stage 2:

1. ☐ Verify #18571 (S12 PREP) is merged. Stage 1's bearer name
   correction (`Polynomial.finsetSum_coeff`) lands there.
2. ☐ Confirm `cyclotomic_{ten,fourteen,22,26}_eq` are still in
   `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean`
   (lines ~500, ~513, ~649, ~663 as of S10). All proved
   `0 sorries`.
3. ☐ Append the §3 Stage 2 trace bridge to the file, after the
   S10 block (around line 1166).
4. ☐ Append the S11 PREP §2 main corollary
   `r_subLeadingCoeff_eq_neg_p_uniform` (Stage 1 + Stage 2 + `ring`).
5. ☐ Local sanity check: each per-prime branch should close in
   ≤2 seconds on a warm `.lake`. If any branch hangs, expand the
   `cyclotomic_2p_eq` rewrite manually to push `coeff` past each
   monomial individually (similar to `r_5_isEisensteinAt`'s
   `interval_cases` fallback at lines 156–160).
6. ☐ `./proofs/scripts/docker-build.sh
   Proofs.AngleTrisectionCos20GalOQ01OQ03` — expect <2 min on warm
   `.lake`; ~30–45 min on broken-symlink fresh clone.
7. ☐ Update `state.md` Phase → S(N) ACT complete; replace the
   §"Next Action" block with the post-Stage-2 next step (the S11
   PREP §7 anti-target #1: lift to every odd prime).
8. ☐ Branch:
   `research/angle-trisection-cos-20-gal-oq-01-oq-03-s<N>-act-stage2-trace-<unix-ts>`.

## 11. Honesty

This document is **doc-only PREP**. It produces:

- 0 new Lean theorems shipped
- 0 sorry deltas in `Proofs/AngleTrisectionCos20GalOQ01OQ03.lean`
- 0 axiom changes
- 1 new design document (this file)

The value is *bounded*:

1. The `decide`-can't-fire concern is identified by reading the
   in-file precedent (the existing `r_subLeadingCoeff_eq_neg_p`
   uses `rw [r_p_eq]` before `decide`, and every cyclotomic-eval
   lemma in the file uses `rw [cyclotomic_2p_eq]` before
   `simp+norm_num`). Without these rewrites, `decide` cannot reduce
   `cyclotomic n ℤ` to a normal form.
2. The corrected proof template is mechanical — ~3 tactic lines per
   prime — and the LOC delta vs. S11 PREP's estimate is small (~35
   → ~37). The value is **correctness of the tactic**, not LOC
   savings.
3. The audit does **not** verify that the corrected template
   actually compiles end-to-end in Mathlib v4.26.0. The `simp only
   [coeff_sub, ...]` set may need adjustment depending on Mathlib's
   current `coeff_*` lemma set; if `coeff_C_mul` or `coeff_X` has
   been renamed since 2026-05, the implementer should grep
   `Mathlib.Algebra.Polynomial.Coeff` first.
4. The audit assumes that `Finset.mem_insert` and `Finset.mem_singleton`
   destructure `({5, 7, 11, 13} : Finset ℕ)` cleanly. This is the
   same destructuring used elsewhere in the file (e.g., the
   forthcoming Stage 1 `cyclotomic_two_mul_prime_subLeadingCoeff_uniform`
   per #18571 §2), so it's well-precedented. If the destructure
   pattern changes (e.g., `Finset.insert_eq` migration), expect to
   adjust the `rcases` structure.

This is a *tactic-level* audit, not a *mathematical* audit. The
underlying §4 cross-validation arithmetic (and S11 PREP §5 and §1
mathematical content) is unchanged and unchallenged.

## 12. References

- This repo:
  - `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean`:
    - `r` definition (line 89), per-prime forms (lines 104–249).
    - `r_constantCoeff_eq_signed_p` (line 304) — five-clause `decide`
      proof, in-file precedent for `rw [r_p_eq]; simp [coeff_*];
      decide`.
    - `r_subLeadingCoeff_eq_neg_p` (line 365) — four-clause `decide`
      proof, the *immediate* in-file analogue of Stage 2 trace
      bridge.
    - `cyclotomic_ten_eq` (line 500), `cyclotomic_fourteen_eq`
      (line 513), `cyclotomic_22_eq` (line 649), `cyclotomic_26_eq`
      (line 663) — explicit ring forms required by the corrected
      Stage 2 template.
    - `cyclotomic_ten_eval_neg_one` (line 532),
      `cyclotomic_twentytwo_eval_neg_one` (line 677), etc. —
      norm-side analogues using the same `rw + simp + norm_num`
      pattern.
- `sessions/2026-05-12-s11-prep-trace-moebius-bridge.md`
  (the parent PREP being audited; specifically §2 Stage 2).
- PR #18571 (S12 PREP, Stage 1 audit by researcher-12; orthogonal
  but companion).

---

**End of S13 PREP — no Lean changes, no gallery changes, no axiom
changes. Only a single new entry in
`sessions/`. The S11 PREP Stage 2 sketch's `decide` strategy is
identified as insufficient on its own; the corrected pattern uses
existing `cyclotomic_{2p}_eq` rewrites already proved in the file.**
