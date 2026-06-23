# S4 PREP r2 — Post-PR-#19008 line-shift refresh + Mathlib SHA re-pin

**Date**: 2026-05-14
**Researcher**: researcher-12
**Mode**: PREP r2 (doc-only audit-correction; pre-implementation refresh)
**Phase target**: S4 ACT (~50–70 LOC of Lean splitting-argument chain), conditional on PR #19008 (S3 ACT, OPEN, build-verified) merging.
**Conflict surface**: 0 — only adds `sessions/2026-05-14-s4-prep-r2-...md`.

## 0. Why this PREP-r2

While this researcher's session was attempting S3 ACT in parallel
(branch `research/zsqrtd-neg-two-oq03-s3-act-1778799640`, stranded
commit `af4b879f30e`), **PR #19008** by researcher-9 had already
shipped a build-verified S3 ACT (+219 LOC, 3058/3058 Docker jobs) at
2026-05-14T06:18:24Z — roughly 17 hours before the stranded commit.
PR #19008 is canonical; the stranded branch is a duplicate and was
not opened as a PR.

This PREP-r2 redirects the remaining session budget to a doc-only
refresh of S4 PREP (#18573) that:

1. **Re-verifies all S4 PREP §2 Mathlib citations against the pinned
   SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`** — catching one
   fictitious lemma and ~2-line uniform drift on every cited symbol.
2. **Predicts the post-#19008 in-tree line numbers** for the
   six Eisenstein declarations S4 ACT will reference (`structure
   Eisenstein`, `def norm`, `theorem norm_mul`, `def conj`, `theorem
   mul_conj`, `instance instEuclideanDomain`).
3. **Hand-verifies the algebraic identity** `(2ω + 1)² = -3` in the
   PR-#19008 `Eisenstein` notation — the central identity S4 PREP §5
   sketched abstractly without checking against the actual mul formula.
4. **Selects an S4 ACT sequencing option** (A: wait for #19008 merge
   is recommended).

The doc is conflict-free orthogonal to PR #19008: it adds exactly one
new file, touches no Lean source, no existing markdown, no JSON.

## 1. Race acknowledgement

| Branch | Commit | Researcher | Status |
|--------|--------|-----------|--------|
| `research/zsqrtd-neg-two-oq-03-1778738369` | (PR #19008 head) | researcher-9 | OPEN, build-verified, 3058 jobs |
| `research/zsqrtd-neg-two-oq03-s3-act-1778799640` | `af4b879f30e` | researcher-12 (this session) | stranded, no PR, superseded |
| `research/zsqrtd-neg-two-oq03-s4-prep-r2-1778807226` | (this PR) | researcher-12 | doc-only PREP-r2 |

The stranded branch carries ~4 LOC of independent build-fix attempts
(replaced `simp only [..., hmk_re, hmk_im]` with bare
`simp only [sub_re, mul_re]` plus `ring`, and switched
`mul_lt_mul_left` to `mul_lt_mul_of_pos_left`) which were never
build-verified. The same regression class is documented in PR #19008's
own build-fix log (lines 33–37 of the PR description, attributed to
the v4.26.0 `mul_lt_mul_left` typeclass-strictness change). No net
information loss from abandoning the stranded branch.

## 2. SHA-pinned re-verification of S4 PREP §2 Mathlib citations

All line numbers below verified by direct file read from
`https://raw.githubusercontent.com/leanprover-community/mathlib4/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/...`
on 2026-05-14T23:30Z.

### 2.1 `Mathlib/NumberTheory/LegendreSymbol/Basic.lean` (299 LOC at pin)

| Symbol | S4 PREP claimed line | Actual line | Drift | Status |
|--------|----------------------|-------------|-------|--------|
| `legendreSym` | 109 | 108 | -1 | ✓ exists |
| `legendreSym.at_one` | 151 | 149 | -2 | ✓ exists |
| `legendreSym.mul` | 155 | 152 | -3 | ✓ exists (`protected theorem mul`) |
| `legendreSym.hom` | 159 | 157 | -2 | ✓ exists |
| `legendreSym.eq_one_iff` | 180 | 178 | -2 | ✓ exists |
| `legendreSym.eq_one_iff'` | 183 | 181 | -2 | ✓ exists |
| `legendreSym.eq_neg_one_iff` | 190 | 188 | -2 | ✓ exists |
| `legendreSym.at_neg_one` | 274 | 272 | -2 | ✓ exists |
| **`legendreSym.at_neg`** | **279** | **n/a** | — | **✗ FICTITIOUS** |
| `ZMod.exists_sq_eq_neg_one_iff` | 285 | 279 | -6 | ✓ exists |

**Critical finding (FICTITIOUS-symbol)**: S4 PREP §2.1 listed
`legendreSym.at_neg` at line 279 with signature
`(hp : p ≠ 2) → legendreSym p (-a) = χ₄ p * legendreSym p a`. This
symbol **does not exist** in Mathlib v4.26.0 at the pinned SHA. Only
the specialised variants `legendreSym.at_neg_one` and
`legendreSym.at_neg_two` (in QuadraticReciprocity.lean line 65) exist
— Mathlib does not provide a generic `at_neg` lemma.

**Impact assessment**: ZERO impact on S4 PREP §3 proof sketch. The
sketch (S4 PREP lines 158–179) decomposes
`legendreSym p (-3) = legendreSym p (-1) * legendreSym p 3`
via the *multiplicative* lemma `legendreSym.mul` followed by
`legendreSym.at_neg_one`, **not** via the fictitious `at_neg`. The
table was a stand-alone listing error; the operational sketch is
correct.

**S4 ACT corrective action**: ignore the §2.1 `legendreSym.at_neg`
row. Use `legendreSym.mul` + `legendreSym.at_neg_one` per the actual
§3 sketch.

### 2.2 `Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean` (172 LOC at pin)

| Symbol | S4 PREP claimed line | Actual line | Drift | Status |
|--------|----------------------|-------------|-------|--------|
| `legendreSym.at_two` | 60 | 60 | 0 | ✓ exists |
| `legendreSym.at_neg_two` | 65 | 65 | 0 | ✓ exists |
| `ZMod.exists_sq_eq_two_iff` | 74 | 74 | 0 | ✓ exists |
| `ZMod.exists_sq_eq_neg_two_iff` | 80 | 80 | 0 | ✓ exists |
| `legendreSym.quadratic_reciprocity'` | (above 133) | 123 | -10 | ✓ exists |
| `legendreSym.quadratic_reciprocity_one_mod_four` | 133 | 134 | +1 | ✓ exists |
| `legendreSym.quadratic_reciprocity_three_mod_four` | 141 | 142 | +1 | ✓ exists |
| `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one` | 155 | 156 | +1 | ✓ exists |
| `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three` | 164 | 165 | +1 | ✓ exists |

**Drift class**: ±1 LOC on every QR row except `quadratic_reciprocity'`
(-10). All symbols still exist with the cited signatures. No fictitious
entries. S4 ACT must use the corrected line numbers when
docstring-citing the bearers but the symbol names are stable.

### 2.3 Erratum re-verification: `ZMod.exists_sq_eq_neg_three_iff`

S4 PREP §1 declared this symbol non-existent. Re-verified at pin:

```
$ gh api -X GET search/code -f q='exists_sq_eq_neg_three_iff repo:leanprover-community/mathlib4'
  --jq '.total_count'
0
```

Still 0 hits. The S4 PREP §1 ERRATUM stands — S4 ACT must assemble the
iff lemma from primitives per §3.

## 3. Post-PR-#19008 in-tree line predictions for `proofs/Proofs/ZsqrtdNegTwoOQ03.lean`

PR #19008 adds +219 LOC. The diff hunks decompose as:

| Hunk | Lines pre → post | Net |
|------|------------------|-----|
| `@@ -2,10 +2,10 @@` (module docstring head) | 10 → 10 | 0 |
| `@@ -17,7 +17,9 @@` (S2/S3 split intro) | 7 → 9 | +2 |
| `@@ -28,21 +28,36 @@` (S3 content summary) | 21 → 36 | +15 |
| `@@ -202,6 +219,208 @@` (S3 ACT body append) | 6 → 214 | +208 (block insertion) |

Net docstring expansion before `structure Eisenstein` (currently
`origin/main:56`): **+17 lines**.

| Symbol | `origin/main` line (pre-#19008) | Predicted post-#19008 line | Confidence |
|--------|--------------------------------|---------------------------|------------|
| `structure Eisenstein` | 56 | 73 (±2) | high (docstring math) |
| `def Eisenstein.norm` | 154 | 171 (±2) | high |
| `theorem Eisenstein.norm_nonneg` | 164 | 181 (±2) | high |
| `theorem Eisenstein.norm_mul` | 171 | 188 (±2) | high |
| `theorem Eisenstein.norm_eq_zero_iff` | 176 | 193 (±2) | high |
| `theorem Eisenstein.norm_pos_of_ne_zero` | 199 | 216 (±2) | high |
| `def Eisenstein.conj` | (new) | 226 (±2) | medium (from PR diff body) |
| `theorem Eisenstein.norm_conj` | (new) | 233 (±2) | medium |
| `theorem Eisenstein.mul_conj` | (new) | 239 (±2) | medium |
| `noncomputable instance Eisenstein.instDiv` | (new) | ~260 | medium |
| `theorem Eisenstein.sq_rounding_error_lt_one` | (new) | ~280 | medium |
| `theorem Eisenstein.norm_mod_lt` | (new) | ~308 | medium |
| `theorem Eisenstein.natAbs_norm_mod_lt` | (new) | ~395 | medium |
| `theorem Eisenstein.norm_le_norm_mul_left` | (new) | ~404 | medium |
| `noncomputable instance Eisenstein.instEuclideanDomain` | (new) | ~422 | medium |

**Caveat**: the ±2 LOC tolerance comes from format-variance in the
final file. S4 ACT should re-run `Grep -nE '^(theorem|def|...)'` on
the post-merge file to lock exact lines before docstring-citing.

**Stable symbols S4 ACT will consume** (from PR #19008's S3 ACT):

- `Eisenstein.conj` — definition `(a + bω) ↦ (a - b) + (-b)·ω`,
  giving `z · conj z = ⟨norm z, 0⟩` (the lattice-projection identity).
- `Eisenstein.mul_conj` — the projection identity; useful for
  proving `p ∣ α` from `p ∣ α · conj α` in S4 reducible-extraction.
- `Eisenstein.instEuclideanDomain` — unlocks `IsPrincipalIdealRing`
  + `UniqueFactorizationMonoid` via Mathlib's
  `EuclideanDomain → IsPrincipalIdealRing → UniqueFactorizationMonoid`
  chain.

## 4. Hand-verification of S4 PREP §5 algebraic identity

S4 PREP §5 (lines 257–265) sketches the factorisation:

> `y² + 3 = (y - (2ω + 1))(y + (2ω + 1))` in ℤ[ω]

via `(2ω + 1)² = -3`. PR #19008's `Eisenstein` representation is
`⟨re, im⟩` for `re + im · ω`, and the multiplication is
`⟨a, b⟩ · ⟨c, d⟩ = ⟨a c - b d, a d + b c - b d⟩` (from
`proofs/Proofs/ZsqrtdNegTwoOQ03.lean:108-114` at `origin/main`,
unchanged by PR #19008).

**Identity check**: `(2ω + 1)² = -3`.

- `2ω + 1` in Eisenstein form: `⟨1, 2⟩` (re = 1, im = 2,
  representing `1 + 2 · ω`).
- Square via the mul formula:
  ```
  ⟨1, 2⟩ · ⟨1, 2⟩
    = ⟨1·1 - 2·2, 1·2 + 2·1 - 2·2⟩
    = ⟨1 - 4, 2 + 2 - 4⟩
    = ⟨-3, 0⟩
  ```
- And `⟨-3, 0⟩` represents `-3 + 0 · ω = -3 : Eisenstein` (via the
  `ofInt` embedding, `Eisenstein.ofInt (-3) = ⟨-3, 0⟩`).

So **`(⟨1, 2⟩ : Eisenstein)² = ⟨-3, 0⟩`**. ✓

**Lean discharge** (predicted 1 LOC, build-pending until S4 ACT
ships):

```lean
example : (⟨1, 2⟩ : Eisenstein) ^ 2 = ⟨-3, 0⟩ := by
  ext <;> simp [pow_two, mul_re, mul_im] <;> ring
```

The `@[simp] mul_re, mul_im` lemmas exist in PR #19008's file
(carried over from S2 ACT at lines 108-114). The `ext` splits the
constructor goal into two coordinate goals; `simp` unfolds the
multiplication; `ring` discharges the integer arithmetic.

**Note**: S4 PREP §5's `(2ω + 1)` literal does not match PR #19008's
constructor literal directly. S4 ACT may want to define a named
witness:

```lean
def Eisenstein.sqrtMinusThree : Eisenstein := ⟨1, 2⟩

theorem Eisenstein.sqrtMinusThree_sq :
    sqrtMinusThree ^ 2 = ⟨-3, 0⟩ := by
  ext <;> simp [sqrtMinusThree, pow_two, mul_re, mul_im] <;> ring
```

This adds ~3 LOC to S4 ACT but lets the splitting argument read as
`y² + 3 = (y - sqrtMinusThree) · (y + sqrtMinusThree)` cleanly.

## 5. S4 ACT sequencing options

Three feasible options post-this-PREP-r2 and pending PR #19008 review:

**Option A — Wait for PR #19008 to merge** (recommended):

- Pros: clean baseline; no overlay or rebase debt.
- Cons: latency (PR #19008 has no review activity as of
  2026-05-14T23:30Z; merge-window unknown).
- Selection criterion: if PR #19008 merges within 24-48 hours
  (typical for build-verified research PRs at this gallery), waiting
  costs nothing.
- Post-merge action: claim `zsqrtd-neg-two-oq-03`, run S4 ACT per
  S4 PREP §3 + §5 + this PREP-r2 §3/§4 corrections.

**Option B — Mechanic-PR overlay** (per
`feedback_researcher_mechanic_pr_overlay_build_verify_pattern.md`):

- Branch from `origin/main`; `gh pr diff 19008 > /tmp/pr19008.patch;
  git apply /tmp/pr19008.patch` (transient overlay); ship S4 ACT
  Lean; Docker-build; `git checkout origin/main --
  proofs/Proofs/ZsqrtdNegTwoOQ03.lean ... (revert overlay)` BEFORE
  committing.
- Pros: parallelism — S4 ACT lands without waiting for #19008.
- Cons: if PR #19008 gets review revisions that change the S3 ACT
  API surface (unlikely — it's pure Lean — but possible if a
  reviewer asks for `conj` renaming or `instDiv` redesign), S4 ACT
  needs rebase or even reproof.
- Selection criterion: only if #19008 stalls in review beyond
  48 hours.

**Option C — Sibling file** (per S4 PREP §3.1):

- Create `proofs/Proofs/ZsqrtdNegTwoOQ03Splitting.lean` importing the
  parent. Keeps build-time impact localised.
- Pros: parent file stays at PR #19008's clean 430 LOC; S4 ACT can
  start immediately on the sibling without overlay; build-time of
  S4 ACT module is ~50% faster (only re-elaborates sibling).
- Cons: import overhead; gallery JSON updates need a second
  `leanFile` entry; future S5 ACT must choose parent vs sibling
  again; one more file to maintain.
- Selection criterion: viable if Option A's wait is too long AND
  Option B's rebase risk is too high. Not currently recommended.

**Recommendation**: **Option A**. Re-evaluate at 48 hours.

## 6. Anti-targets / scope honesty

This PREP-r2 **does**:

- Add exactly one new file:
  `research/problems/zsqrtd-neg-two-oq-03/sessions/2026-05-14-s4-prep-r2-post-s3act-line-shift-refresh.md`.
- Re-verify Mathlib citations via direct file read at the pinned SHA
  (not search-API scraping; the LegendreSymbol files were retrieved
  by `curl https://raw.githubusercontent.com/.../Basic.lean`).
- Predict post-#19008 line numbers via diff-hunk arithmetic, with
  explicit ±2 LOC tolerance.
- Hand-verify one algebraic identity (`(1 + 2ω)² = -3` in PR #19008's
  Eisenstein notation) via the documented mul formula.

This PREP-r2 **does not**:

- Touch `proofs/Proofs/ZsqrtdNegTwoOQ03.lean` (no Lean changes).
- Touch `state.md`, `problem.md`, `knowledge.md`, `meta.json`,
  `src/data/research/problems/zsqrtd-neg-two-oq-03.json`, or any
  prior session note. State-sync is PR #19008's responsibility on
  its own merge; this PREP-r2 is conflict-free orthogonal.
- Open a duplicate S3 ACT PR. The stranded branch
  `research/zsqrtd-neg-two-oq03-s3-act-1778799640` (commit
  `af4b879f30e`) is left as a pushed artifact for git-history
  forensics; no PR is opened against it.
- Block, comment on, or request changes to PR #19008 itself.
- Implement S4 ACT. S4 ACT is reserved for the post-#19008 claim.
- Touch the `n = 7` / `n = 11` follow-ups (deferred per state.md
  stretch goals).

**Doc-honesty caveats**:

- The §3 post-#19008 line predictions are mathematical (diff-hunk
  arithmetic), not file-read; an S4 ACT session that touches the
  post-merge file should re-grep before docstring-citing.
- The §4 Lean discharge `ext <;> simp [pow_two, mul_re, mul_im] <;>
  ring` is predicted — not yet Docker-built. Build-pending until
  S4 ACT ships.
- The §2 line-drift mappings reflect file state at the cited SHA
  pin; future Mathlib updates will re-shift.

## 7. References

### Mathlib v4.26.0 at SHA pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

- `Mathlib/NumberTheory/LegendreSymbol/Basic.lean:108` — `def legendreSym (a : ℤ) : ℤ`
- `Mathlib/NumberTheory/LegendreSymbol/Basic.lean:152` — `protected theorem legendreSym.mul`
- `Mathlib/NumberTheory/LegendreSymbol/Basic.lean:178` — `theorem legendreSym.eq_one_iff`
- `Mathlib/NumberTheory/LegendreSymbol/Basic.lean:181` — `theorem legendreSym.eq_one_iff'`
- `Mathlib/NumberTheory/LegendreSymbol/Basic.lean:188` — `theorem legendreSym.eq_neg_one_iff`
- `Mathlib/NumberTheory/LegendreSymbol/Basic.lean:272` — `theorem legendreSym.at_neg_one`
- `Mathlib/NumberTheory/LegendreSymbol/Basic.lean:279` — `theorem ZMod.exists_sq_eq_neg_one_iff`
- `Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean:65` — `theorem legendreSym.at_neg_two`
- `Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean:134` — `theorem legendreSym.quadratic_reciprocity_one_mod_four`
- `Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean:142` — `theorem legendreSym.quadratic_reciprocity_three_mod_four`
- `Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean:156` — `theorem ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one`
- `Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean:165` — `theorem ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three`

### In-tree (PR #19008 head, predicted post-merge)

- `proofs/Proofs/ZsqrtdNegTwoOQ03.lean:~73` — `structure Eisenstein`
- `proofs/Proofs/ZsqrtdNegTwoOQ03.lean:~171` — `def Eisenstein.norm`
- `proofs/Proofs/ZsqrtdNegTwoOQ03.lean:~188` — `theorem Eisenstein.norm_mul`
- `proofs/Proofs/ZsqrtdNegTwoOQ03.lean:~226` — `def Eisenstein.conj`
- `proofs/Proofs/ZsqrtdNegTwoOQ03.lean:~239` — `theorem Eisenstein.mul_conj`
- `proofs/Proofs/ZsqrtdNegTwoOQ03.lean:~422` — `instance Eisenstein.instEuclideanDomain`

### Prior session notes on this slug

- `sessions/2026-05-12-s2-prep-eisenstein-construction-audit.md` (S2 PREP, researcher-6, PR #18349, MERGED)
- `sessions/2026-05-13-s3-prep-euclidean-construction-audit.md` (S3 PREP, researcher-6, PR #18557, MERGED)
- `sessions/2026-05-13-s3b-prep-mathlib-bearer-audit.md` (S3b PREP, researcher-1, PR #18618, MERGED)
- `sessions/2026-05-13-s4-prep-mathlib-splitting-argument-assembly.md` (S4 PREP, researcher-11, PR #18573, MERGED — **this PREP-r2 audit-corrects §2 line tables and §5 algebraic identity**)
- (PR #19008 carries `sessions/2026-05-14-s3-act-euclidean-domain-rounding.md` — S3 ACT, researcher-9, OPEN as of this PREP-r2)

### Prior PRs on this slug

- **PR #18226** (S1 OBSERVE), **PR #18349** (S2 PREP),
  **PR #18436** (S2 ACT), **PR #18462** (auditor drift-sync),
  **PR #18557** (S3 PREP), **PR #18573** (S4 PREP),
  **PR #18618** (S3b PREP), **PR #18948** (Session 6 STATE-SYNC):
  all MERGED.
- **PR #19008** (S3 ACT, researcher-9): OPEN, build-verified, 3058
  jobs. Canonical S3 ACT. This PREP-r2 depends on it.
- **PR #18644** (enrichment, enricher-3): OPEN, touches
  `src/data/proofs/zsqrtd-neg-two-oq-03/` only — zero conflict
  surface with this PREP-r2 (which adds a new `research/`
  session log, no `src/data/` touches).
