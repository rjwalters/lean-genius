# Current State

**Phase**: ACT
**Since**: 2026-06-12 (researcher-2, S8 sharper popcount bound)
**Iteration**: 8

## S8 ACT 2026-06-12 (researcher-2) — sharper popcount factor-count bound

**Mode**: ACT — proved the long-deferred sharper factor-count bound. Prior
state (S5–S7) shipped the elementary `squareKrylovProd_factor_count_le :
j.bitIndices.length ≤ j` and repeatedly deferred the asymptotically tight
`≤ Nat.size j` form as "blocked pending a missing Mathlib `Nat.bitIndices`
length API." That blocker was incorrect: the bound is provable in Mathlib
v4.26.0 today with no new API.

### What shipped

`proofs/Proofs/CayleyHamiltonMinpolyOQ03OQ02.lean` gains one public theorem:

```lean
theorem squareKrylovProd_factor_count_le_size (j : ℕ) :
    j.bitIndices.length ≤ Nat.size j
```

`Nat.size j = ⌈log₂ (j+1)⌉`, so this is the genuinely O(log j) Keller–Gehrig
matrix-multiplication factor count — exponentially sharper than the prior
`≤ j` bound. Added `import Mathlib.Data.Nat.Size`. File 333 → 383 LOC,
11 → 12 theorems, 3 axioms unchanged, 0 sorries.

### Proof shape

1. Each set-bit index `i ∈ j.bitIndices` contributes a summand `2^i` to
   `(j.bitIndices.map (2^·)).sum = j` (`Nat.twoPowSum_bitIndices`), so
   `2^i ≤ j` via `List.single_le_sum`, hence `i < Nat.size j`
   (`Nat.lt_size`).
2. `j.bitIndices` is `Nodup` (strictly sorted: `Nat.bitIndices_sorted`
   → `List.Pairwise.nodup`).
3. A Nodup list with all entries `< Nat.size j` embeds into
   `Finset.range (Nat.size j)`; `List.toFinset_card_of_nodup` +
   `Finset.card_le_card` + `Finset.card_range` close the count.

### Gotchas (for the technique index)

* `List.Sorted.nodup` is **deprecated** → use `List.Pairwise.nodup`
  (a `List.Sorted` term is accepted directly, since `Sorted` reduces to
  `Pairwise`).
* `Nat.bitIndices_sorted` takes its `n` **implicitly** — `Nat.bitIndices_sorted j`
  is a type error; rely on expected-type unification.

### Build

`./proofs/scripts/docker-build.sh Proofs.CayleyHamiltonMinpolyOQ03OQ02` —
**Build succeeded**, 0 errors, 0 warnings (mathlib v4.26.0 / lean v4.26.0,
3063 jobs).

### Docs synced

* Gallery `src/data/proofs/.../meta.json`: lineCount 383, theoremCount 12,
  Layer 2.5 section summary + endLine, Layer 3 section line range, new
  `originalContributions` bullet, `Mathlib.Data.Nat.Size` import, and the
  now-answered sharper-popcount `openQuestion` removed.
* `src/data/research/problems/cayley-hamilton-minpoly-oq-03-oq-02.json`:
  leanFiles[9] counts, currentState (iter 8, focus, nextAction, attemptCounts),
  knowledge (progressSummary, builtItems, insights, nextSteps[2] marked
  RESOLVED), blockers (sharper-bound entry removed), lastUpdate.

### Next action

Problem is at a genuine completion-ready state: the only remaining layer
(full O(n^ω) operation count) is gated on upstream Mathlib (complexity
monad + fast-matmul oracle) and is not a single-problem research target.
Recommend marking the slug `completed`.

---

## S7 STATE-SYNC 2026-06-10 (researcher-1, doc-only JSON catch-up)

**Mode**: STATE-SYNC — research-JSON catch-up after S5 + S6 shipped Lean / state.md / gallery content but did not update `src/data/research/problems/cayley-hamilton-minpoly-oq-03-oq-02.json`. The JSON last touched `currentState` at S4 (2026-05-30); since then on-disk reality moved through S5 (matvec-count + ω axioms, PR #22531) and S6 (gallery promotion, PR #22595). S7 syncs the JSON to match.

### Drift table

| Surface | On-disk reality | Stale JSON read | Δ |
|---------|------------------|------------------|----|
| `proofs/Proofs/CayleyHamiltonMinpolyOQ03OQ02.lean` | 333 LOC / 11 theorems / 3 axioms / 0 sorries | (JSON is lagging) | — |
| Gallery `meta.json` `leanFile` | `lineCount: 333, axiomCount: 3, theoremCount: 11, sorries: 0` | (no on-disk Δ) | — |
| state.md header (pre-S7) | `Phase: ACT, Since: 2026-06-06, Iteration: 6` | (no on-disk Δ) | — |
| JSON `currentState.iteration` | 7 (6 prior + S7) | `4` | **+3** |
| JSON `currentState.focus` | S5 + S6 + S7 narrative | `S4 ACT (build verified, researcher-1, 2026-05-30) — Layer 2 vector form shipped…` | rewrite |
| JSON `currentState.nextAction` | "problem at completion-ready state…" | `S5 — matvec-count bound + axiomatized Layer 3 placeholder…` (now done) | rewrite |
| JSON `attemptCounts.total` | 7 | `4` | **+3** |
| JSON `knowledge.progressSummary` | prepend S5 + S6 + S7 | starts at S3 ACT | prepend |
| JSON `knowledge.builtItems` | append S5 (axioms) + S6 (gallery entry) | ends at S4 ACT | append 2 |
| JSON `knowledge.nextSteps[0..6]` | re-order: optional follow-ups + Mathlib upstream | starts with done S5 matvec-count | rewrite |
| JSON `leanFiles[9].lineCount` | 333 | `200` | **+133** |
| JSON `leanFiles[9].theoremCount` | 11 | `7` | **+4** |
| JSON `leanFiles[9].axiomCount` | 3 | `0` | **+3** |
| JSON top-level `lastUpdate` | 2026-06-10 | `2026-05-30` | bump |

### Axiom Integrity recheck (per CLAUDE.md policy)

```text
$ grep -nE "^axiom " proofs/Proofs/CayleyHamiltonMinpolyOQ03OQ02.lean
240:axiom omegaMM : ℝ
247:axiom omegaMM_two_le : (2 : ℝ) ≤ omegaMM
253:axiom omegaMM_lt_three : omegaMM < (3 : ℝ)
$ grep -nE "^structure |^class " proofs/Proofs/CayleyHamiltonMinpolyOQ03OQ02.lean
(no matches)
$ grep -nE ":= by sorry|:= sorry|^[[:space:]]+sorry$" proofs/Proofs/CayleyHamiltonMinpolyOQ03OQ02.lean
(no matches)
```

Three axioms (Layer 3 ω placeholder), zero structure/class encoding, zero sorries. Status `axiomatized` / badge `axiom` is correct per CLAUDE.md.

### Mathlib pin recheck (no drift)

`proofs/lake-manifest.json` mathlib `rev` = `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) — 28-day byte-identical pin since 2026-05-13.

### What changed (concise)

| File | Δ | Note |
|------|---|------|
| `src/data/research/problems/cayley-hamilton-minpoly-oq-03-oq-02.json` | currentState + attemptCounts + knowledge.{progressSummary,builtItems,nextSteps} + leanFiles[9] + top-level lastUpdate | S5 + S6 + S7 catch-up |
| `research/problems/cayley-hamilton-minpoly-oq-03-oq-02/state.md` | this S7 header prepend + drift table | Prior S6 / S5 / S4 / earlier content preserved verbatim below |
| `research/problems/cayley-hamilton-minpoly-oq-03-oq-02/sessions/2026-06-10-s7-state-sync-json-catchup.md` | NEW | Session log with drift table + axiom-integrity recheck + race-safety probe |

**No Lean files modified. No gallery `meta.json` / `annotations.json` modified.**

### Race-safety probe

Pre-PR probe 2026-06-10 ~16:40Z: no in-flight researcher PR for this slug; most recent merged PR is #22595 (S6 gallery promotion) 4 days ago. S7 is doc-only / strictly orthogonal to any concurrent Lean edit.

### Revised current focus / next action

Unchanged in substance from S6 §"Next Action": **Problem at completion-ready state**. Layers 1 + 2 + 2.5 + axiomatized Layer 3 all build-verified and gallery-promoted. Further work (sharper popcount bound via `Nat.size j`; full operation-count theorem via complexity monad) is gated on Mathlib upstream infrastructure that does not yet exist.

After this S7 PR lands, the next picker (or this session) may issue `scripts/research/claim-problem.sh update cayley-hamilton-minpoly-oq-03-oq-02 completed` to formally drop the slug into the `completed` pool bucket.

---

## Current Focus (S6 — preserved verbatim from prior state.md)

S6 ACT — **Gallery promotion shipped** (researcher-3, 2026-06-06).
`src/data/proofs/cayley-hamilton-minpoly-oq-03-oq-02/meta.json` created with
`status = "axiomatized"`, `badge = "axiom"`, `axiomCount = 3`,
`theoremCount = 11`, `definitionCount = 2`, `lineCount = 333`. Five sections
(Layer 1, Layer 2 matrix, Layer 2 vector, Layer 2.5 factor-count, Layer 3
axiomatized ω); overview/historicalContext/keyInsights/conclusion all
populated; cross-references to parent OQ-03, sibling OQ-03-OQ-01, and
foundational `cayley-hamilton-minpoly`; references include Keller-Gehrig 1985,
Strassen 1969, Giesbrecht 1995, Storjohann 2000, Williams-Xu-Xu-Zhou 2024,
von zur Gathen & Gerhard 2013, and Mathlib's `Data.Nat.BitIndices`. Gallery
build verified: `pnpm annotations:build` clean, `pnpm research:build`
registers the entry in `listings.json` and `data-manifest.json` with
hash `meta: 419c79cf`. Session note in
`sessions/2026-06-06-iter6-s6-gallery-promotion.md`.

This closes Layers 1 + 2 + 2.5 + axiomatized Layer 3 as a public gallery
entry. Layer 3 (full operation count) and the sharper popcount bound
remain deferred pending Mathlib complexity-monad infrastructure.

## Previous Focus (S5 — carried for hand-off)

S5 ACT — **Matvec-count bound + Layer 3 ω axioms shipped** (researcher-1, 2026-06-05).
`proofs/Proofs/CayleyHamiltonMinpolyOQ03OQ02.lean` extended with:

* **Layer 2.5** — `length_le_twoPow_sum` (private helper) and
  `squareKrylovProd_factor_count_le : j.bitIndices.length ≤ j`. The
  matrix-multiplication factor count for assembling `M^j` is bounded
  by `j` itself (and asymptotically by `⌈log₂ j⌉ + 1`).
* **Layer 3 (axiomatized)** — three axioms `omegaMM : ℝ`,
  `omegaMM_two_le : 2 ≤ ω`, `omegaMM_lt_three : ω < 3`, with
  `omegaMM_mem_Ico` sanity corollary.

File now: ~333 LOC, **11 theorems** (3 Layer 1 + 4 Layer 2 matrix +
2 Layer 2 vector + 1 Layer 2.5 factor-count + 1 Layer 3 ω-sanity),
**0 sorries**, **3 axioms** (all in Layer 3 ω placeholder).

The sharper bound `j.bitIndices.length ≤ Nat.size j` (≤ `⌈log₂ (j+1)⌉`)
is deferred pending Mathlib API exploration; the `≤ j` bound is the
immediately verifiable version using only `Nat.twoPowSum_bitIndices`
and `Nat.one_le_two_pow`.

The full operation-count theorem (Keller–Gehrig recovers `μ_M` in
`O(n^ω)` field operations) is *deferred*: it requires Mathlib to grow
a complexity monad first.

**Build status:** ✅ **verified** (researcher-1, 2026-06-05).
`./proofs/scripts/docker-build.sh Proofs.CayleyHamiltonMinpolyOQ03OQ02`
on lockfile (mathlib v4.26.0 / lean v4.26.0): 3062/3062 jobs clean
(8.0 s of compile after Mathlib cache warm-up).

## Previous Focus (S4 — carried for hand-off)

S4 ACT — **Layer 2 vector form shipped** (researcher-1, 2026-05-30).
`proofs/Proofs/CayleyHamiltonMinpolyOQ03OQ02.lean` extended with 2
vector-level corollaries built on S3's matrix-level Layer 2 bridge:
* `squareKrylovProd_mulVec` — `(squareKrylovProd M j).mulVec v = (M^j).mulVec v`
* `krylov_in_squareKrylov_range` — every Krylov vector lies in the
  range of the squared-Krylov product matrix-vector map.

Both proofs are 1-line corollaries of `squareKrylovProd_eq_pow`
(S3); file 200 → ~228 LOC, 9 theorems total (3 Layer 1 + 4 Layer 2
matrix-level + 2 Layer 2 vector-level), 0 sorries, 0 axioms.

## Active Approach

Three-layer decomposition (unchanged):

1. **Structural layer** (squared-Krylov sequence) — ✅ **Layer 1 shipped
   in S2 (build pending → verified in S3).**
2. **Correctness layer** (Krylov power as product of squared-Krylov
   matrices) — ✅ **Layer 2 shipped in S3.** Vector-level corollaries
   shipped in S4.
3. **Complexity layer** — split into:
   * **Layer 2.5** (factor-count bound) — ✅ shipped in S5 (this iteration).
   * **Layer 3** (full `O(n^ω)` operation count) — **axiomatized in
     S5**: `ω` and its bounds declared as axioms; full
     operation-count theorem deferred until Mathlib grows a
     complexity-monad framework.

## Blockers

* Mathlib has no complexity-monad / cost-counting framework — blocks the
  *full* `O(n^ω)` operation-count theorem. (Mitigated in S5: the ω
  exponent itself is axiomatized; only the operation-count predicate
  remains to be supplied.)
* Mathlib's `Matrix.mul` is the naive cubic algorithm; there is no
  Strassen or abstract fast-matmul oracle.
* The sharper factor-count bound `j.bitIndices.length ≤ Nat.size j`
  needs Mathlib `Nat.bitIndices` / `Nat.size` API exploration; the
  current `≤ j` bound is the verifiable elementary version.

## Next Action

**Problem can be marked `completed` in the research pool.**

The structural side is done (Layers 1 + 2 + 2.5 + axiomatized Layer 3,
all build-verified, all gallery-promoted). Further work — the sharper
popcount bound `Nat.size j` and the full operation-count theorem — is
gated on Mathlib upstream infrastructure (a `Nat.bitIndices` length API
and a complexity monad respectively) that does not yet exist. These
are not single-problem research targets but Mathlib-side projects.

Optional follow-ups if the problem is reopened later:
* Add `src/data/proofs/cayley-hamilton-minpoly-oq-03-oq-02/annotations.json`
  with inline highlights — meta.json `sections` already cover the
  per-section content so this is cosmetic.
* Refine `squareKrylovProd_factor_count_le` to use `Nat.size j` once
  the Mathlib API exists.

## Attempt Counts

- Total attempts: 6 (S1 + S2 + S3 + S4 + S5 + S6; this iteration completes S6)
- Current approach attempts: 6 (3-layer decomposition + gallery promotion;
  Layers 1 + 2 + vector + factor-count + Layer 3 axioms + gallery entry shipped)
- Approaches tried: 1 (the planned 3-layer decomposition)

## Findings Summary

* **S6 (new):** Gallery promotion is mechanical: parent OQ-03 supplied a
  drop-in schema for the meta.json. Five sections, four axiom-status
  fields, two cross-references, and six references — all derivable from
  the Lean file's structure and the existing problem/knowledge documents.
  The build pipeline (`pnpm annotations:build` + `pnpm research:build`)
  picked up the new entry automatically; `listings.json` and
  `data-manifest.json` were regenerated without issues.
* **S5 (carried):** The matvec-count bound `j.bitIndices.length ≤ j` is a
  2-line proof: combine `Nat.twoPowSum_bitIndices` with the elementary
  lemma `(L.length ≤ (L.map (2^·)).sum)` (proved by induction +
  `Nat.one_le_two_pow`). The Layer 3 ω axioms are minimal: `ω : ℝ`
  with `2 ≤ ω < 3`, both bounds with citations in their docstrings
  (folklore + Strassen 1969).
* The full operation-count theorem cannot be stated cleanly today;
  S5 ships the *minimum honest commitment* — naming ω and its known
  bounds — leaving the operation-count predicate to a future Mathlib
  upgrade. This avoids both over-claiming with a vague `True`
  placeholder and under-committing with no Layer 3 at all.
* **S4 (carried):** The vector-level corollaries are 1-line proofs
  from the matrix-level Layer 2 bridge; they're the bridge from
  Keller–Gehrig matrix arithmetic into the OQ-03 matvec ladder.
* **S3 (carried):** Layer 2 has a 3-rewrite proof. After unfolding
  `squareKrylovProd`, the list `j.bitIndices.map (squareKrylov M)` is
  rewritten to `j.bitIndices.map (fun i => M^(2^i))` via the Layer 1
  bridge; the list product collapses to a single matrix power via
  `prod_pow_of_list`; finally `Nat.twoPowSum_bitIndices` identifies
  the exponent sum as `j` itself.
* The product-formula bridge `M^j = ∏ T_i` is exactly the algebraic
  content of the Keller-Gehrig outer loop: `⌈log₂ j⌉` squarings produce
  `T_0, …, T_{k-1}`, and `popcount(j)` multiplications then yield `M^j`.
* **Mathlib leverage:** `Nat.bitIndices` (Peter Nelson, 2024) +
  `Nat.twoPowSum_bitIndices` were perfect drop-ins. No bit-manipulation
  lemmas had to be re-proved.
* The Keller-Gehrig speed-up is *structural*: $n$ cheap matvecs vs.
  $\log n$ expensive matmuls. The structural and correctness claims
  formalise today (Layers 1 + 2: done; factor-count: done).
* The *quantitative* speed-up is gated on Mathlib infrastructure that does
  not exist (complexity monad). The ω exponent is now axiomatized
  (Layer 3 placeholder); the operation-count predicate awaits.
* Numerical breakeven: Strassen wins around $n \approx 256$;
  CW-Williams wins from $n \approx 64$. Mathlib's choice of naive
  cubic `Matrix.mul` is defensible at typical $n$.
* OQ-03 already provides 90% of the algebraic infrastructure (Krylov
  recurrence, annihilator theory, iteration bound).
