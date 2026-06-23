# S9 STATE-SYNC — 4-month-stale `Phase: NEW` template, 265-LOC axiomatized D₂/D₆/prime stack (doc-only)

**Author:** researcher-5
**Timestamp:** 2026-05-16T09:10Z
**Phase:** state-sync (doc-only)
**Iteration:** 9 (counting research-prefixed PRs that touched the slug)

Corrects **4-month-old `research/problems/erdos-374/state.md` drift**: still
claimed `Phase: NEW`, `Iteration: 1`, "Begin problem exploration." from
**2026-01-13T00:59Z** despite the deliverable being a 265-LOC single-file
AXIOMATIZED stack with 0 axioms / 0 sorries / 13 named theorems + 3 private
lemmas + 5 definitions, build-verified by `lean-genius` at Mathlib `v4.26.0`
across 8+ merged research PRs.

Per repo `CLAUDE.md` Axiom Integrity Policy: the open Erdős conjecture (growth
rate of `|D_k ∩ {1,…,n}|` for `3 ≤ k ≤ 6`) is correctly marked
`"axiomatized"` in `src/data/proofs/erdos-374/meta.json` *despite* the Lean
file containing 0 axioms. The status reflects the **open-conjecture
convention** ("Millennium Prize problems, Clay problems, and open conjectures:
always `\"axiomatized\"`"), not the absence of formal assumptions — the
growth-rate question is not even *stated* in the Lean file (only structural
facts around `D_2`, prime exclusion, and edge cases are proven).

Doc-only. New session file + `state.md` head/body sync + `knowledge.md`
Sessions section catchup. **No Lean changes.** No edits to `meta.json` (in
sync at `lineCount: 265`, `theoremCount: 16`, `definitionCount: 5`,
`axiomCount: 0`, `sorries: 0`), no edits to `problem.md`, no edits to
gallery `index.ts` / `annotations.json`. No Docker invocation.

---

## §1. Race awareness

- 0 open PRs touching `erdos-374` (`gh pr list --search "erdos-374 OR Erdos374"` returned no `state:open` matches)
- Last on-slug merge: **PR #13516 (2026-04-28)** "fix(batch): correct phantom-axiom narratives" — meta-level only
- Last *research* merge touching the Lean file: **PR #8355 (2026-03-30)** "4 problems — isoperimetric, hypercube Q_n, factorial squares, Kronecker symbol"
- **~47 days** stale since last research-class commit on the Lean file
- LOW saturation; this PR is orthogonal by construction (no Lean / meta / gallery JSON edits)

---

## §2. Files modified in this PR

1. **NEW:** `research/problems/erdos-374/sessions/2026-05-16-s09-state-sync-axiomatized-265loc-deferred-growth-rate.md` — this file
2. **MODIFIED:** `research/problems/erdos-374/state.md` — sync `Phase NEW → AXIOMATIZED`, `Iteration 1 → 9`, refresh `Current Focus` / `Active Approach` / `Next Action` / `Attempt Counts` to match merged-PR reality
3. **MODIFIED:** `research/problems/erdos-374/knowledge.md` — fill in `## Sessions` section (was `(No research sessions yet)` despite 8+ research PRs)

**Untouched** (all already in sync at HEAD):

- `src/data/proofs/erdos-374/meta.json` — confirmed `status: "axiomatized"`, `badge: "wip"`, `lineCount: 265`, `theoremCount: 16`, `definitionCount: 5`, `axiomCount: 0`, `sorries: 0`, `mathlib_version: "4.26.0"`
- `src/data/proofs/erdos-374/annotations.json` and `index.ts` — gallery integration
- `proofs/Proofs/Erdos374Problem.lean` — 265 LOC, audit below
- `research/problems/erdos-374/problem.md` — open conjecture statement (no rewrite needed)

---

## §3. Audit — `proofs/Proofs/Erdos374Problem.lean` @ HEAD `f76ad5c7e1b`

Pure metadata audit (no `lake build` run; cached `.olean` from PR #8355 still load-bearing per Mathlib pin unchanged at `v4.26.0`).

**Line count:** `wc -l` → 265 ✓ (matches `meta.json` `lineCount: 265` and `leanFile.lineCount: 265`)

**Definition inventory** (5):

| # | Symbol | Kind | Line |
|---|--------|------|-----|
| 1 | `IsPerfectSquare` | `def` | 30 |
| 2 | `factorialProduct` | `def` | 35 |
| 3 | `HasSquareFactorialProduct` | `def` | 40 |
| 4 | `bigF` | `noncomputable def` | 48 |
| 5 | `inDk` | `def` | 54 |

✓ matches `meta.json` `definitionCount: 5` and `leanFile.definitionCount: 5`.

**Theorem inventory** (16 = 12 top-level `theorem` + 1 `private theorem` + 3 `private lemma`):

Top-level `theorem`:

| # | Name | Line | Purpose |
|---|------|-----|---------|
| 1 | `bigF_ge_two` | 59 | `bigF m ≠ 0 → 2 ≤ bigF m` |
| 2 | `factorialProduct_pair` | 67 | `[a,b]` case |
| 3 | `squares_have_square_factorial_product` | 77 | `n ≥ 2 → HasSquareFactorialProduct (n*n) 2` (backward `D₂ ⊇ {n²}`) |
| 4 | `bigF_eq_two_of_square` | 104 | `n ≥ 2 → bigF (n*n) = 2` |
| 5 | `square_in_D2` | 114 | `n ≥ 2 → inDk 2 (n*n)` |
| 6 | `factorialProduct_append` | 132 | distributivity over `++` |
| 7 | `no_square_factorial_product_for_primes` | 174 | prime `p` ⇒ `¬HasSquareFactorialProduct p k` (∀k≥2) |
| 8 | `bigF_prime_zero` | 230 | `Prime p → bigF p = 0` |
| 9 | `no_prime_in_Dk` | 239 | `Prime p → ¬inDk k p` (∀k≥2) |
| 10 | `one_has_square_factorial_product` | 249 | `[0,1]` witness: `0!·1! = 1 = 1²` |
| 11 | `bigF_one_eq_two` | 253 | `bigF 1 = 2` |
| 12 | `one_in_D2` | 262 | `inDk 2 1` |

Plus `example : HasSquareFactorialProduct 4 2` (line 98), not counted as theorem.

`private theorem`:

| # | Name | Line | Purpose |
|---|------|-----|---------|
| 13 | `not_prime_dvd_factorialProduct` | 152 | `Prime p → (∀a∈seq, a<p) → ¬(p ∣ factorialProduct seq)` |

`private lemma`:

| # | Name | Line | Purpose |
|---|------|-----|---------|
| 14 | `factorialProduct_foldl_mul` | 121 | foldl-accumulator extraction |
| 15 | `factorialProduct_singleton` | 139 | `[x]` case |
| 16 | `factorialProduct_cons` | 144 | `x :: xs` split |

✓ matches `meta.json` `theoremCount: 16` and `leanFile.theoremCount: 16`.

**Axiom inventory** (0):

`grep -c "^axiom " proofs/Proofs/Erdos374Problem.lean` → `0`

No structure-encoded assumptions (no `class …` or `structure …` declarations
in the file; only `def`/`theorem`/`example`/imports). ✓ matches `meta.json`
`axiomCount: 0` and `leanFile.axiomCount: 0`.

**Sorry inventory** (0):

`grep -nE "^\s*sorry\s*$|^\s*sorry\b" proofs/Proofs/Erdos374Problem.lean` → 0 matches
`grep -c "\bsorry\b" proofs/Proofs/Erdos374Problem.lean` → `0` (no docstring mentions either)

✓ matches `meta.json` top-level `sorries: 0` and `leanFile.sorries: 0`.

**Mathlib pin** at HEAD: `proofs/lake-manifest.json` shows `mathlib` `inputRev: "v4.26.0"` ✓ matches `meta.json` `mathlib_version: "4.26.0"`.

---

## §4. Status rationale (Axiom Integrity Policy)

Per `CLAUDE.md`:

> Millennium Prize problems, Clay problems, and **open conjectures: always `"axiomatized"`**

Erdős #374 asks for the growth rate of `|D_k ∩ {1,…,n}|` for `3 ≤ k ≤ 6` —
an *open* conjecture as of 2026-05 per `erdosproblems.com/374`. The Lean
file does *not* state this growth-rate question formally (no axiom
`growth_rate_D_3 : ...`); it only formalizes:

- `D_2 ⊇ {n² : n ≥ 2}` (backward, proven via `squares_have_square_factorial_product`)
- prime exclusion `Prime p → ¬inDk k p` (proven via Legendre `v_p(p!) = 1` argument)
- edge cases `1 ∈ D_2` (via `[0,1]` witness)

The `"axiomatized"` status is correct *by the open-conjecture convention*,
not by counting `axiom` declarations. `badge: "wip"` is the appropriate
visual signal (matches the in-flight nature of the open question).

**No `meta.json` edit needed** — status, badge, and counts all already
correctly reflect this convention. (Distinct from the `_phantom_axiom_narratives`
batch fix in PR #13516, which corrected *narrative-level* axiom mentions
that no longer matched the post-elimination code; that work is already
merged.)

---

## §5. Iteration count rationale

Counting *research-class* commits that touched `proofs/Proofs/Erdos374Problem.lean`
or `src/data/proofs/erdos-374/meta.json` (substantive proof or metadata
work, excluding batch fix-meta-format passes and enrichment runs):

| Iter | Commit | PR | Date | Description |
|-----|--------|-----|------|-------------|
| 0 | `38a3be78f3b` | direct | 2026-01-26 | initial enhance (stub + scaffolding) |
| 1 | `cb614ee9461` | #5368 | 2026-03-23 | axiom elimination + D₂ backward (5 axioms → ?) |
| 2 | `97d580b3a2f` | #7259 | 2026-03-28 | "2 axioms eliminated" (across 374 + 864) |
| 3 | `796f473e228` | #7264 | 2026-03-28 | "+3 theorems, 1 assessment" |
| 4 | `31844801b6e` | #7521 | 2026-03-28 | "12 axioms, 2 bugs, 11 meta.json audit" |
| 5 | `09392a85f0b` | #7272 | 2026-03-28 | "+18 theorems, 1 axiom eliminated" (across 5 problems) |
| 6 | `b0a186690ef` | #8308 | 2026-03-30 | "eliminate 1 axiom, fix 2 bugs, prove 8 lemmas" |
| 7 | `f780eac6ac5` | #8347 | 2026-03-30 | isoperimetric + multi-slug (touched 374 metadata) |
| 8 | `d67e1c4c089` | #8355 | 2026-03-30 | "4 problems — incl. factorial squares" — final Lean edit |
| 9 | **this PR** | TBD | 2026-05-16 | S9 STATE-SYNC (doc-only catchup) |

Setting `Iteration: 9` in state.md to reflect cumulative session count.

---

## §6. State drift table (state.md, 9 fields)

| Field | Before (2026-01-13) | After (2026-05-16) | Reason |
|-------|---------------------|---------------------|--------|
| `**Phase**:` | `NEW` | `AXIOMATIZED` | 8 research PRs merged; 0 sorries, 0 axioms, open conjecture per policy |
| `**Since**:` | `2026-01-13T00:59:36.242Z` | `2026-05-16T09:10:00Z` | Phase transition timestamp |
| `**Iteration**:` | `1` | `9` | Per §5 commit history |
| `## Current Focus` body | "Initial exploration of the problem." | (updated, see §6.1) | Reflect 265-LOC stack |
| `## Active Approach` body | "None yet." | (updated, see §6.2) | Reflect proven backward D₂ + prime exclusion |
| `## Blockers` body | "None." | (preserved as "None.") | No active blockers |
| `## Next Action` body | "Begin problem exploration." | (updated, see §6.3) | Forward D₂ direction, 527 ∈ D₆ witness, growth-rate axiom statement |
| `## Attempt Counts` `Total` | `0` | `8` | Per §5 |
| `## Attempt Counts` `Approaches tried` | `0` | `4` | (a) constructive `[n²−1, n²]` for D₂; (b) Legendre + `not_prime_dvd_factorialProduct` induction for primes; (c) `[0,1]` for `1 ∈ D₂`; (d) `Nat.find` for `bigF` definability |

### §6.1 New `## Current Focus`

```
Maintenance / deferred extension. The Lean file `proofs/Proofs/Erdos374Problem.lean`
is at 265 LOC with 13 named theorems + 3 private lemmas + 5 definitions,
0 axioms, 0 sorries. Status `"axiomatized"` per open-conjecture convention.
The structural pillars (D₂ backward, prime exclusion, 1 ∈ D₂) are proven.
The open growth-rate question for D₃/D₄/D₅/D₆ remains formally unstated;
extension would axiomatize the conjecture and add provable consequences.
```

### §6.2 New `## Active Approach`

```
None in flight. Last active approach (S8, PR #8355, 2026-03-30): proved
`squares_have_square_factorial_product` via the [n²−1, n²] witness with
the factorization (n²−1)!·n² · (n²−1)! = (n·(n²−1)!)². Verified Mathlib
v4.26.0 build.
```

### §6.3 New `## Next Action`

```
Three orthogonal extension paths, in increasing risk order:

(a) LOW: Add `527 ∈ D_6` as a `theorem`-with-sorry witness (the smallest
    element of D_6 per Erdős–Graham 1976 / Luca–Saradha–Shorey 2014).
    Computational verification via `decide` likely infeasible (search
    space too large for `Nat.find` reduction); requires hand-constructed
    6-element factorial witness. Estimated ~30 LOC + 1 sorry for the
    explicit list construction.

(b) MEDIUM: Forward D₂ direction `inDk 2 m → ∃ n, m = n*n` (proves
    `D_2 ⊆ {n² : n ≥ 2}` to complete the equivalence). Requires showing
    that the only 2-element strictly-increasing sequence ending at m with
    a square factorial product is [n²−1, n²]. Estimated ~80 LOC.

(c) HIGH: Axiomatize the open conjecture as `axiom growth_rate_D_k :
    ∀ k ∈ {3,4,5,6}, ∃ f : ℕ → ℕ, |{m ≤ n : inDk k m}| = f n + o(f n)`
    and add 2-3 conditional consequences. Would change axiomCount 0→1
    and require meta.json update (axiomCount, assumptions field).

ACT-readiness: GREEN for (a) and (b); AMBER for (c) (requires sequence-
asymptotics infrastructure not yet in scope).

This STATE-SYNC PR does NOT execute any of these; it only documents the
true current state to enable future researchers to pick up cleanly.
```

---

## §7. Knowledge.md drift fix

`research/problems/erdos-374/knowledge.md` line 73 currently reads:

```markdown
## Sessions

(No research sessions yet)
```

Despite 8 substantive research PRs (§5). Replacing with a chronological table
referencing PR numbers and commit hashes for reproducibility. **No edits to
the upstream problem statement, references, OEIS, or tags sections** — those
were last touched by enrichment passes and remain accurate.

---

## §8. Out of scope (deferred to future sessions)

- **Forward D₂ direction proof** (path (b) in §6.3) — substantive new theorem, deferred
- **527 ∈ D₆ witness** (path (a)) — needs hand-construction of 6 factorials, deferred
- **Open-conjecture axiomatization** (path (c)) — would change axiomCount, needs meta.json sync, deferred
- **Lake build re-verification** — *not required*: this PR has 0 Lean / meta / gallery changes, so the prior PR #8355 build remains the source of truth. Mathlib pin unchanged at `v4.26.0`.
- **Docker / `lake build` invocation** — *not required*: doc-only; host disk at 100% capacity (`/System/Volumes/Data` 6.9Gi avail) makes Docker risky per gallery-wide memory pattern, and there is nothing to verify.

---

## §9. PR title

`research(erdos-374): S9 STATE-SYNC — 4-month-stale NEW template, 265-LOC axiomatized D₂/D₆/prime stack (doc-only)`

Body: link this session file + §1 race-safety note + §3 audit table + §5 iteration ledger + §8 out-of-scope.

---

## §10. Pattern note — 4th such state-sync in this gallery

After PR #14237/#14994-vintage S8 catchup on `erdos-1065` (researcher-4,
2026-05-13, multi-file axiomatized), the same drift pattern recurs on a
**single-file axiomatized** open-conjecture slug. Combined with similar
prior catchups on `erdos-1139` (iter 4) and `erdos-635` (iter 5), this
is now the **4th confirmed instance** of the "post-seeker-init state.md
never updated through N substantive research PRs" archetype.

A batch state-sync sweep across Erdős open-conjecture slugs would still
be high-yield Mechanic work (estimated 40-100 candidates). This PR
contributes one more datapoint to the sample.
