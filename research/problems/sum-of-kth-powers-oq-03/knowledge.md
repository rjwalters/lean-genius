# Knowledge Base: sum-of-kth-powers-oq-03

Combinatorial (odd-number partition) proof of Nicomachus's theorem
∑_{i=1}^n i³ = (∑_{i=1}^n i)² = T_n², independent of the parent's algebraic proof.

---

## STATUS UPDATE 2026-06-15 (researcher-4) — ACT IS DONE; this slug is COMPLETE

**The ORIENT spec below is superseded.** `proofs/Proofs/SumOfKthPowersOQ03.lean` **exists, is
complete (0 sorries / 0 axioms / 10 theorems / 1 def), and is registered** in
`proofs/Proofs.lean` (`import Proofs.SumOfKthPowersOQ03`). A prior session implemented the full
proof using an even cleaner route than the spec below: define `T n := ∑ i ∈ range n, i` (the
Gauss sum **as a sum**, NOT `n(n+1)/2`), which sidesteps ALL ℕ-division and ℕ-subtraction. The
triangular recurrence is the division-free `two_T_add : 2·T i + i = i²`; `block_sq` then gives
`T i² + i³ = T (i+1)²` by `ring` over the ℕ semiring; `block_eq_cube`, `tiling`, and
`sum_cubes_eq_sum_squared_via_odds` follow. Bonus corollary `cube_eq_sum_consecutive_odds`
(`i³ = ∑_{k<i} (2(T i + k)+1)`). The file uses `import Mathlib` + `Finset.sum_Ico_consecutive`
+ `Finset.range_eq_Ico` + `Finset.sum_range_succ` + one `Nat.add_left_cancel`.

**Only remaining gap = a green deployer Docker build to flip gallery status formalized/wip →
verified/original.** Build is blocked locally (worktree `proofs/.lake` is the circular
self-symlink ⇒ 0 oleans ⇒ Mathlib-from-source OOM; Aristotle MCP "Resource not found"). The
file header claims a prior docker-build succeeded, but that is not independently confirmed this
session, so status stays conservative.

researcher-4 fixed gallery meta: `theoremCount` 9→10 (the `^theorem`-grep undercounts
`@[simp] theorem T_zero`) and `lineCount` 144→155 (file grew after the corollary was added).
**Do NOT re-claim this as ORIENT or re-implement the Lean — it is already written and registered.**

---

## Problem Understanding

The parent entry `sum-of-kth-powers` (`Proofs/SumOfKthPowers.lean`) already proves the
identity **algebraically** as `sum_cubes_eq_sum_squared` (line 232), by composing the closed
forms `sum_cubes_classical` and `sum_first_powers_classical`. This OQ asks for a **second,
structurally different** proof via the classical odd-number partition:

- each cube i³ is a block of i consecutive odd numbers, and
- stacking the blocks for i = 1..n reproduces exactly the first T_n odd numbers, whose sum is T_n².

This is a finite-combinatorics target (a reindexing / tiling argument), not an analytic one. It
is fully elementary and should be < 100 LOC of Lean with no missing Mathlib infrastructure.

---

## Math resolved on paper (ORIENT)

Let T_i = i(i+1)/2 (the i-th triangular number), T_0 = 0.

**Block identity.** The odds assigned to index i are
  i² − i + 1, i² − i + 3, …, i² + i − 1   (i terms).
The smallest is i²−i+1 = 2·T_{i−1}+1 and the largest is i²+i−1 = 2·T_i−1. So index i occupies
odd-sequence **positions T_{i−1} … T_i−1** (0-indexed), i.e. the odds {2j+1 : T_{i−1} ≤ j < T_i}.
Verified: ∑_{j=0}^{i−1}(i²−i+1+2j) = i(i²−i+1) + i(i−1) = i³.  ✓

**Tiling.** The half-open position ranges [T_{i−1}, T_i) for i = 1..n are consecutive and tile
[0, T_n) exactly (T_i − T_{i−1} = i). Hence
  ∑_{i=1}^n i³ = ∑_{i=1}^n ∑_{T_{i−1}≤j<T_i}(2j+1) = ∑_{0≤j<T_n}(2j+1) = T_n².  ✓

**Sum-of-odds.** ∑_{j=0}^{m−1}(2j+1) = m² (trivial induction).

**Closing the loop.** T_n = ∑_{i=0}^n i (Gauss), so T_n² = (∑ i)², matching the parent's RHS.

The `problem.md` statement and its displayed formula i³ = ∑_{j=0}^{i−1}(i²−i+1+2j) are
**mathematically correct** (checked).

---

## Formalizable core (build-free spec — ready for a Docker-up session)

Target file: `proofs/Proofs/SumOfKthPowersOQ03.lean` (does **not yet exist** — see Doc Integrity).
Work over ℕ, mirroring the parent's `Finset.range` conventions. Let `T i := i * (i+1) / 2`.

- **L1 `sum_odds`** : `∑ j ∈ Finset.range m, (2*j+1) = m^2`.
  Proof: `induction m` + `Finset.sum_range_succ` + `ring`/`omega`. (~5 LOC.)
- **L2 `block_eq_cube`** : `∑ j ∈ Finset.Ico (T (i-1)) (T i), (2*j+1) = i^3`, for i ≥ 1.
  Proof: split as `sum_odds (T i) − sum_odds (T (i-1))` via `Finset.sum_Ico_eq_sub`
  (or `Finset.range_eq_Ico` + subtraction), then `T i ^2 − T (i-1)^2 = i^3` from
  `T i = T (i-1) + i` and `ring`. Prefer the additive form `T (i-1)^2 + i^3 = T i ^2`
  (or stating over ℤ) to avoid ℕ-subtraction pitfalls. (~10–15 LOC.)
- **L3 tiling/telescope** : the per-index Ico ranges concatenate via
  **`Finset.sum_Ico_consecutive`** (`a ≤ b → b ≤ c → (∑ Ico a b) + (∑ Ico b c) = ∑ Ico a c`),
  giving `∑ i ∈ range (n+1), (∑ j ∈ Ico (T (i-1)) (T i), (2*j+1)) = ∑ j ∈ Ico 0 (T n), (2*j+1)`.
  This is the lemma that formalizes "the odd blocks tile the first T_n odds." (~15–25 LOC.)
- **Main `sum_cubes_eq_sum_squared_via_odds`** :
  `∑ i ∈ range (n+1), i^3 = (∑ i ∈ range (n+1), i)^2`.
  Assemble L2 (each i³ as its block) → L3 (tiling) → L1 (= T_n²) → Gauss
  (`Finset.sum_range_id` / `Finset.sum_range_id_mul_two`) to rewrite T_n = ∑ i. (~15 LOC.)

**Mathlib gaps: none.** All of `Finset.sum_range_succ`, `Finset.sum_Ico_consecutive`,
`Finset.sum_Ico_eq_sub`, `Finset.range_eq_Ico`, `Finset.sum_range_id` are present. Total estimate
~60–100 LOC, no axioms, no sorries expected.

### ℕ-subtraction-free reindex (recommended Lean formulation — de-risks the port)

The spec above writes blocks as `Ico (T (i-1)) (T i)` for `i ≥ 1`, which introduces ℕ-subtraction
(`i-1`) and an `i ≥ 1` side condition. A cleaner, side-condition-free formulation indexes blocks by
`i ∈ range n` mapping to cube `(i+1)^3` on positions `[T i, T (i+1))` (with `T k = k*(k+1)/2`,
`T 0 = 0`), so **no `i-1` appears anywhere**:

- **L2′ `block_eq_cube`** : `∑ j ∈ Finset.Ico (T i) (T (i+1)), (2*j+1) = (i+1)^3`.
  Derive additively from L1 via `Finset.sum_Ico_consecutive` (with `Finset.range_eq_Ico`):
  `(T i)^2 + (∑ Ico (T i) (T (i+1)) (2j+1)) = (T (i+1))^2`, then close with the verified ring
  identity `(T i)^2 + (i+1)^3 = (T (i+1))^2`. To use `ring` despite the `/2` in `T`, clear the
  division first: prove `2 * T k = k*(k+1)` (i.e. `Finset.sum_range_id_mul_two` / `omega` on the
  evenness of `k*(k+1)`), or work the squared identity through the `*4` form
  `4*(T k)^2 = (k*(k+1))^2`. This division-clearing is the one genuinely build-fiddly step and is
  why M1 is Docker-gated rather than paste-port-trivial.
- **L3′ tiling** : `∑ i ∈ range n, (∑ j ∈ Ico (T i) (T (i+1)), (2*j+1)) = ∑ j ∈ Ico 0 (T n), (2*j+1)`
  by induction on `n` + `Finset.sum_range_succ` + `Finset.sum_Ico_consecutive` (needs `T i ≤ T (i+1)`,
  immediate since `T` is monotone). `Ico 0 (T n) = range (T n)`, so the RHS is `(T n)^2` by L1.
- **Main′** : `∑ i ∈ range n, (i+1)^3 = (T n)^2`. Then shift the index
  (`∑ i ∈ range n, (i+1)^3 = ∑ i ∈ range (n+1), i^3`, via `Finset.sum_range_succ'` or the `0^3 = 0`
  bump) and rewrite `T n = ∑ i ∈ range (n+1), i` (`sum_first_powers_classical` from the parent file,
  or `Finset.sum_range_id`) to land on `(∑ i ∈ range (n+1), i)^2` — matching the parent's exact RHS
  shape `sum_cubes_eq_sum_squared`.

### Build-free verification (durable, this session — researcher-1, S3)

All M1 arithmetic is now independently certified by a committed, reproducible script,
`research/problems/sum-of-kth-powers-oq-03/verify_m1.py` (sympy symbolic + brute force, exits
non-zero on any mismatch). It re-derives — not plugs in — every identity the M1 lemmas encode:
`sum_odds = m²`; the additive telescope `T(i-1)² + i³ = T(i)²`; `block = T(i)² − T(i-1)² = i³`; block
geometry (size `i`, smallest odd `i²−i+1`, largest `i²+i−1`); the ℕ-sub-free reindex
`T(i)² + (i+1)³ = T(i+1)²`; Gauss `T(n)=∑i`; and an end-to-end brute-force chain
`blocks == cubes == firstOdds == T_n² == (∑i)²` for `n = 0..60`. **All checks pass.** This makes the
M1 spec machine-checkable build-free, so the only remaining work is the Lean transcription (the
division-clearing in L2′ being the sole non-mechanical step). The eventual `.lean` is cross-checkable
against the parent, which already proves the same theorem algebraically (`sum_cubes_eq_sum_squared`).

**Milestone split**
- M1 (formalizable now): L1 + L2′ + L3′ + Main′ above (ℕ-sub-free reindex). Pure Mathlib, no gaps —
  Docker-gated only; arithmetic certified by `verify_m1.py`.
- M2 (pedagogical, optional): an explicit `Finset` **bijection** between the Σ-type {(i,j) : block}
  and `range (T n)` (via `Finset.sum_sigma`/`Finset.sum_biUnion` over a `Finset.disjiUnion`),
  to surface the "blocks ↔ initial segment of odds" bijection literally rather than by telescope.
  Strictly stronger pedagogy, same theorem; defer unless the gallery wants the explicit bijection.

---

## Doc Integrity (fixed this session)

The seeker registry `src/data/research/problems/sum-of-kth-powers-oq-03.json` (untracked local
state in main) listed `leanFiles` = [SumOfKthPowers, …OQ01, …OQ02, …OQ04, …OQ04Aristotle] — i.e.
the **parent and sibling** files, all 0-sorry. There is **no** `SumOfKthPowersOQ03.lean`. Left as
is, this misattribution makes an unsolved OQ look solved. Cleared `leanFiles` to `[]` and seeded
the `knowledge` fields. (Recurring misattribution vein: slug-prefix matching pulls in siblings'
complete files.)

---

## Decision

**ORIENT** (build-free). OQ resolved on paper; formalizable core pinned to existing Mathlib
lemmas with a milestone split; no Mathlib gap. The only blocker to ACT is the verification
blackout (Docker down + Aristotle "Resource not found"). A Docker-up session can type M1 directly.

---

## Insights

- Cleanest Lean route is **telescoping** (`Finset.sum_Ico_consecutive`), not an explicit
  bijection: `T_i² − T_{i−1}² = i³` reduces the whole proof to sum-of-odds + range concatenation.
- The block-vs-cube identity is equivalent to `T_i² − T_{i−1}² = i³`; prove it additively
  (`T (i-1)^2 + i^3 = T i^2`) to dodge ℕ-subtraction.
- Independence from the parent is genuine: parent uses closed forms (`sum_cubes_classical`),
  this uses a tiling of odds — no shared lemma beyond Gauss.

## Dead Ends

- (none yet — no proof attempt could run during the backend blackout)

---

## Session 2026-06-14 (S2, researcher-4) — build-free ℕ-spec verification

Still backend blackout (Docker `docker info` timeout; Aristotle `prove` → "Resource not found").
Re-verified the **entire formalizable core exactly as Lean would evaluate it in ℕ** (emulating
truncated subtraction `i-1` and `T i = i*(i+1)/2`), to catch off-by-one / ℕ-truncation hazards in
the spec *before* it is typed:

- **L1** `∑_{j<m}(2j+1)=m²` holds for all `m ≤ 50`.
- **L2** `∑_{j∈Ico(T(i-1),T i)}(2j+1)=i³` holds for all `1 ≤ i ≤ 40`.
- **i=0 edge (the subtle one):** in `Main` the sum runs over `range (n+1)`, which *includes* `i=0`.
  With ℕ-truncated `i-1`, the `i=0` block is `Ico (T 0) (T 0) = Ico 0 0 = ∅`, summing to `0 = 0³`.
  So including `i=0` is harmless and L2 need only be proved for `i ≥ 1` — **confirmed**, no special
  casing of `i=0` is required in `Main`.
- **L3 tiling + Main** `∑_{i<n+1} i³ = ∑_{i<n+1}(block i) = ∑_{j<T n}(2j+1) = T n² = (∑_{i<n+1} i)²`
  holds as a 5-way exact equality for all `n ≤ 40`; `T i − T(i-1) = i` confirmed (ranges tile `[0,T n)`).

Conclusion: the spec is ℕ-sound as written; M1 carries no hidden off-by-one. No spec changes needed
— this only raises confidence for the Docker-up ACT. (Verified with `python3` emulating ℕ semantics.)

---

## Session 2026-06-14 (S5, researcher-5) — bearer-lemma pin-confirmation at v4.26.0

Still backend blackout (Docker `docker info` timeout; Aristotle `prove` → "Resource not found";
probed both this session). No build/ACT possible. Closed the last *asserted-but-unconfirmed* item:
knowledge.md previously stated "Mathlib gaps: none" but never confirmed the load-bearing lemmas'
**exact signatures at the pinned rev**. Confirmed directly against the Mathlib source at the lake
pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (`v4.26.0`) via `gh api .../contents?ref=<rev>`:

- **`Finset.sum_Ico_consecutive`** — the `@[to_additive]` image of
  `Finset.prod_Ico_consecutive` at `Mathlib/Algebra/BigOperators/Intervals.lean:56`. Exact shape:
  `sum_Ico_consecutive (f : ℕ → M) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :`
  `(∑ i ∈ Ico m n, f i) + (∑ i ∈ Ico n k, f i) = ∑ i ∈ Ico m k, f i`.
  **Transcription note:** `f` is **explicit**, `m n k` are **implicit**, and the two `≤` hyps are
  **explicit positional** args — so L3′ must supply them as `Finset.sum_Ico_consecutive _ hmn hnk`
  (or name `f`), not as a bare rewrite. This is exactly the form L3′ needs to glue blocks.
- **`Finset.range_eq_Ico`** — `Mathlib/Order/Interval/Finset/Nat.lean:68`, stated **point-free**:
  `Finset.range_eq_Ico : range = Ico 0`. So `range (T n) = Ico 0 (T n)` is `congrFun … _` /
  `by rw [Finset.range_eq_Ico]`; it rewrites the L1 RHS `range (T n)` into the `Ico 0 (T n)` shape
  L3′ produces (and vice-versa). Confirmed in active use at Intervals.lean:86.
- **Bonus cleaner L3′ step:** `Finset.sum_Ico_succ_top (hab : a ≤ b) (f : ℕ → M) :`
  `∑ k ∈ Ico a (b+1), f k = (∑ k ∈ Ico a b, f k) + f b` (Intervals.lean, `@[to_additive]` of
  `prod_Ico_succ_top`) is also present — an alternative to `sum_Ico_consecutive` for the induction
  step if a single-step top-extension is preferred.
- `Finset.sum_range_id`, `Finset.sum_range_succ`, and the parent's `sum_first_powers_classical`
  are already exercised in `Proofs/SumOfKthPowers.lean` at this same pin → presence is implied by a
  green parent build; not re-fetched.

**Net effect:** "Mathlib gaps: none" is now **pin-confirmed for the two non-trivial bearers**, with
their exact argument order recorded (the one thing the prose spec omitted and the transcriber would
otherwise have to discover at build time). No spec change; the ACT plan stands. Still Docker-gated:
no `.lean` written (an unbuildable file under `Proofs/` would break the shared build), exactly as
S1–S4 deferred. Decision: **ORIENT** — pin-confirmation only, zero churn to spec.

## Session 2026-06-15 (S6, researcher-5) — complete Lean transcription (division-free reformulation)

Dual blackout still LIVE (`docker info` timeout; Aristotle `prove` → "Resource not found",
re-probed this session). No build/typecheck possible. After 5 ORIENT sessions the spec was fully
pinned; this session produced the **complete paste-ready Lean file** — but with a cleaner
formulation that removes the spec's sole documented hazard.

**Key simplification — `T` as a Gauss SUM, not the closed form.** The prior spec used
`T k := k*(k+1)/2`, whose `/2` forced the "division-clearing" step (multiply by 4, prove evenness
via `Nat.even_mul_succ_self`, etc.) flagged as "the one genuinely build-fiddly step". Defining
instead

  `def T (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, i`

makes `T 0 = 0` (`rfl`), `T (n+1) = T n + n` (`Finset.sum_range_succ`), and the triangular
recurrence becomes the **division-free, subtraction-free** identity `2 * T i + i = i^2`
(`two_T_add`, one-line induction). The block-square identity `T i^2 + i^3 = T (i+1)^2` (`block_sq`)
then follows by a 3-step `calc` using only `ring` (valid on the ℕ *semiring* — no
`linear_combination`, which needs a ring) plus `rw [← two_T_add i]`. **No ℕ-division and no
ℕ-subtraction appear anywhere in the file.** This is a strict improvement over the M1/M1′ specs
and should be the formulation that gets built.

**File:** `research/problems/sum-of-kth-powers-oq-03/SumOfKthPowersOQ03.lean` (kept in the research
dir, NOT under `Proofs/`, to avoid degrading the shared safe-subset build before a typecheck —
`build-safe-subset.sh` globs `Proofs/*.lean`). 0 axioms, 0 sorries (build-pending). Lemma chain:
`sum_odds` (L1) → `two_T_add` → `block_sq` → `block_eq_cube` (L2, via `Finset.sum_Ico_consecutive`
+ `range_eq_Ico` + `Nat.add_left_cancel`) → `tiling` (L3, induction) →
`sum_cubes_eq_sum_squared_via_odds` (Main, closes by `rfl` since `T (n+1)` is *definitionally*
`∑ i ∈ range (n+1), i`, matching the parent's RHS shape `(∑ i ∈ range (n+1), i)^2`).

**Verification:** new durable script `verify_div_free.py` certifies every identity exactly as the
Lean file evaluates them in ℕ (n = 0..199, exits non-zero on mismatch): L1, T_succ, two_T_add,
block_sq, block_eq_cube, tiling, Main, and `T (n+1)^2 = RHS`. All pass.

**Transcription risk notes for the Docker-up session:**
- `Finset.sum_Ico_consecutive _ (Nat.zero_le _) (T_le_succ i)` — `f` explicit (pass `_`),
  `m n k` implicit (inferred from goal), two `≤` hyps explicit positional (S5 pin).
- `rw [Finset.range_eq_Ico]` (point-free `range = Ico 0`) rewrites ALL `range` occurrences in one
  shot — use a SINGLE `rw`, not two (a second errors "no occurrence").
- `block_eq_cube`'s `sum_congr` goal is `i^3 = block i`, closed by `rw [block_eq_cube]` (rewrites
  the block RHS to `i^3`).
- If Main's final `rfl` is finicky on the `T (n+1)` defeq, fall back to `simp only [T]` or
  `show (∑ i ∈ range (n+1), i)^2 = _; rfl`.

**Next:** Docker-up session — `cp` the draft to `proofs/Proofs/SumOfKthPowersOQ03.lean`, build,
register in `Proofs.lean`, add gallery entry `src/data/proofs/sum-of-kth-powers-oq-03/`.

---

## Session 2026-06-15 (S7, researcher-3) — gallery entry created (Lean side already complete)

State at claim: the Lean proof `proofs/Proofs/SumOfKthPowersOQ03.lean` (division-free Nicomachus,
0 axioms / 0 sorries) is **on main and registered** in `Proofs.lean` (promoted by PR #24537, built
on S6 draft #24492). No open PRs. The one remaining gap was the **gallery entry**: oq-03 was the
only member of the family (parent, oq-01, oq-02, oq-04 all have `src/data/proofs/<slug>/`) without
one, so the completed proof was not surfaced on the website.

**This session (ACT, build-free):** created `src/data/proofs/sum-of-kth-powers-oq-03/meta.json`
modelled on the sibling entries — accurate metrics (144 lines, 9 theorems, 1 def, 0 axioms,
0 sorries), historical context (Nicomachus, squared-triangular-number), proof strategy, section
map, key insights, `alternative-proof` cross-reference to the parent, and follow-up open questions
(explicit Finset bijection / figurate-tiling generalization). JSON validated.

**Honesty / status:** badge `wip`, status `formalized`, with the `assumptions` field stating
plainly that the file is **build-pending** (authored under the Docker + Aristotle outage, not yet
machine-checked) and pointing at the two committed numeric certs. Did NOT claim `verified`/`original`
— that flip should wait for a green `docker-build.sh Proofs.SumOfKthPowersOQ03`.

**Re-verified this session:** both `verify_div_free.py` (n=0..199) and `verify_m1.py` (n=0..60)
still exit 0. Docker still down (`docker info` 25s timeout), so no typecheck possible.

**Next (Docker-up session):** `./proofs/scripts/docker-build.sh Proofs.SumOfKthPowersOQ03`; on green,
flip the meta `badge` to `original` / `status` to `verified` and drop the build-pending note from
`assumptions` and from the `.lean` header. Optionally add `annotations.json` (enricher territory).

## Session 2026-06-15 (researcher-1) — FIX broken build + ACT corollary, DOCKER-VERIFIED

**Mode**: ACT (Docker UP). **Critical finding**: `SumOfKthPowersOQ03.lean` was
registered in `proofs/Proofs.lean` (via #24537/#24561, both authored under a
blackout) but **never actually compiled** — the module docstring contained the
literal `-/` inside the phrase "division-/subtraction-free form" (line 31), which
prematurely **closes the `/- … -/` block comment**, so everything from there on
was parsed as code (`error: unexpected identifier`, `invalid 'import' command`).
Lean block comments nest, but an unbalanced `-/` with no matching inner `/-`
closes the outer comment. The file was merged broken because the deployer's build
gate did not catch it (blackout) — main carried a non-compiling registered file.

**Fix**: reworded to "division- and subtraction-free" (no `-/`). Confirmed no
other stray `-/` in the file. After the fix the file builds clean (7743 jobs,
`Built Proofs.SumOfKthPowersOQ03`).

**Added** (genuine, distinct, classical): `cube_eq_sum_consecutive_odds (i) :
i^3 = ∑ k ∈ range i, (2*(T i + k) + 1)` — "each cube is a sum of `i` consecutive
odd numbers" (1³=1, 2³=3+5, 3³=7+9+11, …). This is the per-cube decomposition
that `block_eq_cube` proves over `Ico (T i) (T (i+1))`, restated standalone over
`range i` with no ℕ-subtraction (first odd = 2·T i + 1). Proof: `block_eq_cube i`
+ `Finset.sum_Ico_eq_sum_range` + `T_succ` + `Nat.add_sub_cancel_left`, then
`.symm`. One line.

**Also**: corrected the now-false "NOT yet machine-checked" provenance note to
record the passing Docker build.

**Status**: 0 axioms, 0 sorries, **Docker build PASSED**. The slug's Lean side is
now genuinely verified (was previously a phantom registration).
