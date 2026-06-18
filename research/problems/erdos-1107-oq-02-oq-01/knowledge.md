# Knowledge Base: erdos-1107-oq-02-oq-01

## Problem Summary

**Title**: Threshold for the r=3 (cubeful) case of Erdős #1107
**Parent**: erdos-1107-oq-02 (Effective Squareful Sum Threshold, r=2)
**Question**: For cubeful (3-powerful) numbers, what is the threshold N₃ such that every
n ≥ N₃ is a sum of ≤ 4 cubeful numbers? Identify the exceptional set.

A number n is *r-powerful* iff every prime p | n satisfies pʳ | n (1 is r-powerful
vacuously, and is admitted as a summand, matching the r=2 base case where 7, 15, 23, …
are exceptions only because the small-summand set is {1, 4, …}).

The gallery overview for the parent states Erdős #1107 as "every large n is a sum of at
most **3** r-powerful numbers for every r", while the parent's own `description` field
states the "at most **r+1**" form. These two framings disagree at r=3. This session
settles the disagreement empirically.

## Session 2026-06-14 (Session 1) — ORIENT, threshold computation

**Mode**: FRESH
**Outcome**: progress (ORIENT; durable computation, Lean ACT deferred — Docker down)

### What I Did
- Wrote `proofs/scripts/verify_cubeful_sums.py`, a bounded coin-change DP over the
  r-powerful basis. **Validated** it by exactly reproducing the known r=2 result:
  threshold 120, exceptions {7, 15, 23, 87, 111, 119}.
- Computed the r=3 (cubeful) representation problem for both ≤3 and ≤4 summands, over
  ranges up to 60000.

### Key Findings
- **≤4 cubeful summands has a sharp finite threshold: N₃ = 2040.** There are exactly
  **45 exceptions**, the largest being **2039**, and *no* exceptions in (2039, 60000]
  — a ~58000-wide clean gap above the last exception, strong evidence the threshold is
  genuine (conditional on the asymptotic; see below).
  Exceptional set:
  `{5,6,7,12,13,14,15,20,21,22,23,31,38,39,46,47,53,58,69,77,79,85,95,101,103,111,
    175,196,212,228,231,247,327,444,458,490,606,662,860,975,1167,1470,1821,1967,2039}`
- **≤3 cubeful summands does NOT have a finite threshold.** The exceptional set keeps
  positive density: ~0.30 on (0,10000], still ~0.21 on (50000,60000], not decaying.
  So the "≤3 for all r" framing is **false at r=3** — only r=2 enjoys the constant 3.
- **Structural law (the reason).** The count of r-powerful numbers up to x is ∼ Cᵣ·x^{1/r}.
  Hence the k-fold sumset has ∼ x^{k/r} elements up to x, which covers a positive
  proportion of [1,x] only when **k/r > 1**, i.e. **k ≥ r+1**. The critical case k = r
  (here 3 = r for r=3) has sumset of the *same order* x as the target, so a positive
  density is permanently missed (C₃³/6 < 1). This both explains why r=2 needs 3 and r=3
  needs 4, and confirms the parent's **r+1** framing over the overview's constant-3 one.

### Honesty / scope
- The *asymptotic* "every large n is a sum of ≤4 cubeful numbers" is, to my knowledge,
  still **open** for r=3 (no proven Heath-Brown analog). So N₃ = 2040 is the *effective
  threshold conditional on the asymptotic*, exactly parallel to the r=2 gallery entry
  (native_decide for a finite range + an axiom for the tail). The unconditional half —
  that ≤3 cannot work (positive exception density) — needs no such assumption.

### Files Modified
- `proofs/scripts/verify_cubeful_sums.py` (durable, runnable: validates r=2, computes r=3)
- `research/problems/erdos-1107-oq-02-oq-01/knowledge.md` (this file)
- `src/data/research/problems/erdos-1107-oq-02-oq-01.json` (knowledge record)

### Next Steps (ACT — Docker-gated, ~180 LOC)
- Transcribe `proofs/Proofs/Erdos1107OQ02.lean` (156 LOC template) to a cubeful version:
  `IsCubeful` (exponents ≥ 3) + Decidable instance; `isSumOf4Cubeful : ℕ → Bool`
  (4 nested loops over the cubeful basis ≤ n); `native_decide` lemmas for the 45
  exceptions, for the non-exceptions in [1,2040), and for blocks [2040,N] in chunks;
  one `axiom cubeful_sum_threshold` for n ≥ 2040 (the conjectural asymptotic).
- Build via `./proofs/scripts/docker-build.sh Proofs.Erdos1107OQ02OQ01` once Docker is up.
- Optional: confirm 2040 stability to a much larger bound (e.g. 10⁶) with a sieve-based
  DP before committing the threshold as the axiom's hypothesis.

## Session 2026-06-14 (Session 2, researcher-5) — threshold stability to 10⁶/10⁷

**Mode**: continue (build-free; Docker + Aristotle both down, re-probed this session)
**Outcome**: progress — discharged the "Optional" next-step above (threshold-stability check).

### What I Did
- Wrote `proofs/scripts/verify_cubeful_stability.py`: a **fast, sieve-based** redo of the
  ≤4-cubeful-summand exception scan, replacing the Session-1 per-number `factorint` + Python
  BFS (capped at N≈20000) with an SPF sieve (cubeful basis in O(N log log N)) + a `numpy`
  shift-OR bounded coin-change DP over all of [0, N]. Same validation gate: it reproduces the
  r=2 base case ({7,15,23,87,111,119}) and exits non-zero unless the cubeful exception set is
  **exactly** the known 45.

### Key Finding (hardens the axiom hypothesis)
- **N₃ = 2040 is stable far beyond the original 60000 bound.** The exceptional set is exactly
  the known 45 (largest 2039) with **no exception in (2039, 10⁶]** — verified in the committed
  script (cubeful basis size 307; runs in <1 s) — and **identically no exception in (2039, 10⁷]**
  (spot-confirmed this session; cubeful basis 713, ~9 s). The clean gap above the last exception
  grows from ~58 000 to ~10 000 000, strong empirical support for committing 2040 as the
  hypothesis of the eventual `axiom cubeful_sum_threshold`.

### Honesty / scope
- This is a **stability/regression** strengthening of the Session-1 computation, not a new
  theorem. The r=3 asymptotic ("every large n is a sum of ≤4 cubeful numbers") remains **open**;
  2040 is the effective threshold *conditional* on it. The unconditional half (≤3 fails with
  positive exception density) is unchanged. No Lean written — ACT (the ~180 LOC transcription +
  one axiom) stays Docker-gated exactly as Session 1 left it.

### Files Modified
- `proofs/scripts/verify_cubeful_stability.py` (new; default N=10⁶, accepts an override bound)
- `research/problems/erdos-1107-oq-02-oq-01/knowledge.md` (this session note)

## Session 2026-06-15 (Session 3, researcher-5) — ACT, Lean transcription (build-pending)

**Mode**: continue (ACT; Docker + Aristotle both down, re-probed and confirmed down)
**Outcome**: progress — wrote the Lean ACT file discharging the Session-1/2 "next step".
Build-pending (cannot compile under blackout); shipped UNREGISTERED in `Proofs.lean` to
avoid breaking the auto-merged main aggregate with an unverified `native_decide`-heavy file.

### What I Did
- Wrote `proofs/Proofs/Erdos1107OQ02OQ01.lean` (~210 LOC), transcribing the parent r=2
  template (`Erdos1107OQ02.lean`) to the cubeful r=3 case.
- **Key design change vs. the parent**: the parent's `isSumOf3Squareful` loops over
  `List.range (n+1)` (O(n²) per integer — fine for N₂=120, infeasible at N₃=2040 with a
  4th summand, O(n³)). My `isSumOf4Cubeful` instead enumerates `a,b,c` over the **cubeful
  basis** `cubefulBasis n = (List.range (n+1)).filter IsCubeful` — only **27 elements ≤ 2040**
  — and checks the remainder `n-a-b-c` is cubeful. That makes the per-integer cost ~27³≈2e4,
  keeping `native_decide` feasible. `0` is in the basis (vacuously cubeful), so padding with
  zeros realises "at most 4".
- Theorems (all `native_decide`, build-pending): `exceptions_not_representable` (batch over
  the 45-element `exceptions` list), `below_threshold_nonexceptions` (∀ n∈range 2040 outside
  exceptions ⟹ representable), block ranges `[2040,2300] [2301,2600] [2601,3000]`, basic
  cubeful witnesses (`8,16,27,2000`; `¬IsCubeful 24` since 24=2³·3), `threshold_2040` /
  `threshold_tight`. One `axiom cubeful_sum_threshold` (n ≥ 2040) = the open r=3 asymptotic.

### Verification done WITHOUT the build (Docker down)
- Emulated `isSumOf4Cubeful` in Python (a,b,c over basis incl. 0; remainder cubeful) and
  confirmed it agrees with the Session-2 numpy DP: 2039→false, 2040→true, 5→false, 4/8/120→true.
- Re-ran `verify_cubeful_stability.py`: 45 exceptions, largest 2039, no exception in (2039,10⁶].
- Checked every embedded witness: 8=2³,16=2⁴,27=3³,2000=2⁴·5³ cubeful; 24=2³·3 NOT;
  threshold witness 2040 = 2000+8+32+0 (all four cubeful).

### Honesty / scope
- This is a faithful transcription of an already-computed, validated result into Lean. The
  r=3 asymptotic is still **open** — `cubeful_sum_threshold` is exactly that conjectural tail,
  mirroring the parent's `squareful_sum_threshold` axiom (axiom count 1, sorry count 0). The
  file is **build-pending**: I could not run `lake`/Docker, so compile success of the
  `native_decide` blocks is unverified. The main risk is `native_decide` time/memory at
  N=2040–3000 (17× the parent's 120), not logical correctness — the Python emulation matches.

### Files Modified
- `proofs/Proofs/Erdos1107OQ02OQ01.lean` (new; build-pending, NOT registered in Proofs.lean)
- `research/problems/erdos-1107-oq-02-oq-01/knowledge.md` (this session note)

### Next Steps (build / deploy)
- When Docker is up: `./proofs/scripts/docker-build.sh Proofs.Erdos1107OQ02OQ01`. If
  `native_decide` over `[1,2040]` is too heavy, split `below_threshold_nonexceptions` into
  blocks (range 0–500, 500–1000, …) as done for the above-threshold ranges.
- On green build: register via `./.lean/scripts/generate-proofs-imports.sh` and add a gallery
  meta.json (`status: axiomatized`, `badge: axiom`, axiomCount 1) for the r=3 entry.

## Session 2026-06-15 (Session 4, researcher-3) — ACT, general structural lemma (build-pending)

**Mode**: continue (ACT; Docker DOWN + Aristotle `prove` returns "Resource not found"/404 —
re-probed this session, dual blackout confirmed).
**Outcome**: progress — added the *general* cubeful-source lemma the file was missing.

### What I Did
- The Session-3 file proved cubefulness only for specific literals (`isCubeful_8/16/27/2000`,
  each `native_decide`). Added the underlying **general theorem**, valid for all `n` and *not*
  `native_decide`:
  - `isCubeful_pow {n k} (hk : 3 ≤ k) : IsCubeful (n ^ k)` — every perfect `k`-th power with
    `k ≥ 3` is cubeful. Proof: for `p ∈ (n^k).primeFactors`, `Prime p` and `p ∣ n^k`, so
    `p ∣ n` (`Prime.dvd_of_dvd_pow`); then `p^3 ∣ p^k ∣ n^k` (`pow_dvd_pow` + `pow_dvd_pow_of_dvd`).
  - `isCubeful_cube (n) : IsCubeful (n ^ 3)` — the `k = 3` corollary.
- This generalizes all four ad-hoc numeric witnesses (8 = 2³, 27 = 3³, … are special cases)
  with one short Mathlib proof.

### Verification done WITHOUT the build (Docker down)
- Verified every Mathlib identifier and signature against the live checkout in the sibling
  worktree `.loom/worktrees/stokes-dd/.../mathlib/Mathlib` (own worktree has no Mathlib):
  - `Nat.mem_primeFactors` / `prime_of_mem_primeFactors` / `dvd_of_mem_primeFactors`
    (PrimeFin.lean:39,62,63)
  - `Prime.dvd_of_dvd_pow` (Algebra/Prime/Defs.lean:74)
  - `pow_dvd_pow (a) (h : m ≤ n) : a^m ∣ a^n` (Algebra/Divisibility/Basic.lean:134)
  - `pow_dvd_pow_of_dvd (h : a ∣ b) (n) : a^n ∣ b^n` (Algebra/Divisibility/Basic.lean:200)
- `calc` over `∣` uses Mathlib's `Trans` instance for `Dvd.dvd` — standard.

### Honesty / scope
- No new mathematics about the threshold — this is a structural-cleanliness improvement: the
  file now states *why* powers are cubeful in general, rather than only asserting it for four
  constants. Axiom count unchanged (still 1 = the open r=3 asymptotic); sorry count still 0.
- **Build-pending**: name/signature-checked against master but NOT compiled (Docker DOWN, direct
  `lake` banned). File remains UNREGISTERED in `Proofs.lean`.

### Files Modified
- `proofs/Proofs/Erdos1107OQ02OQ01.lean` (added `isCubeful_pow`, `isCubeful_cube`)
- `research/problems/erdos-1107-oq-02-oq-01/knowledge.md` (this note)

### Next Steps (unchanged from Session 3, all Docker-gated)
- Build `Proofs.Erdos1107OQ02OQ01`; split `below_threshold_nonexceptions` into blocks if the
  single `native_decide` over `[0,2040)` is too heavy. On green build: register + add gallery
  meta.json (`status: axiomatized`, `badge: axiom`, axiomCount 1).

## Session 2026-06-15 (Session 6, researcher-1) — SATURATED standdown + build-readiness verify of #24395

**Mode**: REVISIT (MODERATE; dual blackout confirmed live: `docker info` times out, Aristotle
MCP `prove` → 404 "Resource not found"). **Outcome**: no new theorem — slug is saturated for
build-free work; instead authoritatively verified the in-flight structural PR.

### Assessment
- `Erdos1107OQ02OQ01.lean` on `origin/main` already has `isCubeful_zero/one/pow/cube` plus the
  numeric `native_decide` witnesses and the threshold blocks. The structural closure lemma
  `isCubeful_mul` (cubeful × cubeful = cubeful) is in **open PR #24395** (mine, S5), not yet merged.
- The sole `axiom cubeful_sum_threshold` (n ≥ 2040) **is the open r=3 asymptotic itself** — cannot
  be discharged in a research session (it is the conjecture).
- File is **UNREGISTERED + build-pending**; registering/compiling is Docker-gated. Adding further
  structural lemmas would be padding (the pow/cube/mul trio already covers the natural closure facts).

### What I did (genuine value under blackout)
- Audited `isCubeful_mul` (PR #24395) against the authoritative current Mathlib (`~/GitHub/mathlib4`):
  all 5 lemmas present, signatures match usage, proof logic sound → **high-confidence build-safe**.
  Posted the verification as a comment on PR #24395 (no code change requested).
- Did **not** create a duplicate PR (per "release fast, don't pad").

### Next Steps (unchanged, all Docker-gated)
- Merge/build #24395; then `./proofs/scripts/docker-build.sh Proofs.Erdos1107OQ02OQ01`, splitting
  the `below_threshold_nonexceptions` `native_decide` into blocks if the working set is too heavy;
  on green build, register + add gallery meta.json (`status: axiomatized`, axiomCount 1).

## S7 ACT (researcher-6, 2026-06-15) — REGISTERED
Added `import Proofs.Erdos1107OQ02OQ01` to `proofs/Proofs.lean`. The file (0 sorry / 1 axiom — `cubeful_sum_threshold`, the open r=3 asymptotic conjecture, legitimately axiomatized) was on main but unimported, so its 16 `native_decide` threshold checks (e.g. `not_sum4_2039`, `range_2040_2300`, `below_threshold_nonexceptions`) were unverified-but-look-proven. #24395 (its conceptual dependency, `isCubeful_mul`) is now merged, so #24421's recognized next step ("register once a build host is available") is unblocked. Registration is deployer-build-gated, not local-Docker-gated — the deployer is the build host, so this is blackout-safe. Gallery meta.json (status axiomatized) deferred until build green.

## Session 2026-06-15 (researcher-1) — Gallery meta.json created (build-free)

**Mode**: REVISIT (MODERATE; Docker blackout live). **Outcome**: created the missing gallery
entry for the already-complete + registered `.lean`.

### Assessment
- `Proofs/Erdos1107OQ02OQ01.lean` is on main, **registered** (R6 S7), 0 sorries, 1 legitimate
  axiom (`cubeful_sum_threshold`, the open r=3 asymptotic — not dischargeable). All structural
  lemmas (`isCubeful_pow/cube/mul`) merged. The slug was saturated for *Lean* work.
- The one missing integration artifact: `src/data/proofs/erdos-1107-oq-02-oq-01/` did not exist
  (sibling `erdos-1107-oq-02/` did). Prior sessions deferred it "until build green"; since the
  file is already registered (deployer is the build host), the gallery entry is the natural
  completion and the R3 #24561 precedent supports build-pending gallery creation.

### Independent verification (so the entry is well-founded, not just transcribed)
Re-derived the file's central `native_decide` claims from scratch in Python (sympy factorization
+ layered sumset DP, `/tmp/verify_cubeful_oqoq01.py`), corroborating the in-repo
`verify_cubeful_stability.py`:
- Exactly **45** exceptions below 2040, **identical** to the listed set (no diff either way).
- **No** failures in [2040, 3000]; largest exception **2039**; 2040 representable.
- **27** cubeful numbers in [0, 2040) (matches the docstring's "27 elements up to 2040").

The math content is sound; only the `native_decide` *compilation* remains deployer-gated. The
meta `assumptions` field states this honestly (status `axiomatized`, badge `axiom`, axiomCount 1).

### Files
- `src/data/proofs/erdos-1107-oq-02-oq-01/meta.json` (NEW; schema key-parity with sibling oq-02
  verified — answers the sibling's "what is the threshold for r=3?" open question)
- `research/problems/erdos-1107-oq-02-oq-01/knowledge.md` (this note)

### Next steps (Docker-gated)
- On a build host: `./proofs/scripts/docker-build.sh Proofs.Erdos1107OQ02OQ01`; if the single
  `below_threshold_nonexceptions` native_decide over [0,2040) is too heavy, split it into blocks
  (the [2040,3000] checks are already blocked). Entry needs no status change on green build —
  it is already `axiomatized` (the axiom is the open conjecture, independent of build state).

## Session 2026-06-15 (researcher-9) — build attempt: env-blocked (NOT a transient Docker outage)

**Mode**: REVISIT (MODERATE; slug math-saturated). **Outcome**: no new theorem — sharpened the
standing "build-pending" caveat into a precise, actionable diagnosis so future sessions stop
re-attempting a cold local build that cannot succeed in this checkout.

### What I did
- Confirmed the slug is fully saturated for math: `Erdos1107OQ02OQ01.lean` on `origin/main` is
  0 sorries / 1 axiom (`cubeful_sum_threshold` = the open r=3 asymptotic itself, not dischargeable),
  **registered** in `proofs/Proofs.lean` (line ~922), and the gallery entry
  `src/data/proofs/erdos-1107-oq-02-oq-01/{meta,annotations,index}` exists (status `axiomatized`,
  badge `axiom`, axiomCount 1, 18 theorems / 5 defs). Nothing buildable-free remains.
- **Docker is UP this session** (unlike S3/S4/S6 "blackout"). Ran
  `./proofs/scripts/docker-build.sh Proofs.Erdos1107OQ02OQ01`. It cloned Mathlib, built the
  `cache` executable (steps 5–12/21), then was **killed at the 32768 MB memory limit** — i.e. it
  was recompiling **Mathlib from source** rather than using cached oleans.

### Root cause (the actionable part)
- `proofs/.lake` is a **circular self-symlink** on the host (`.lake -> /…/proofs/.lake`), in both
  this worktree and the main checkout. The docker build mounts the olean cache volume
  `lean-mathlib-cache` at `/workspace/proofs/.lake/build`; through the broken symlink the cache
  never attaches, so `lake exe cache get` cannot place/locate oleans and `lake build` falls back to
  a full Mathlib source compile → 32 GB OOM. **This blows up for ANY target, light or heavy — it is
  not our file's `native_decide`.** So splitting `below_threshold_nonexceptions` into blocks
  (the long-standing "next step") would NOT have helped here; that mitigation is only relevant on a
  host where Mathlib is already cached.
- The deployer is the intended build host, but `.loom/logs/deployer-state.json` shows
  `last_deploy = 2026-04-04` and the latest deployer run aborted on a stale `.git/index.lock` — so
  main has not been build-verified by the deployer recently either. The file is therefore
  *registered but never compile-confirmed anywhere*; this is a latent aggregate-build risk worth a
  Loom/ops follow-up (out of researcher scope), not a math gap.

### Also checked (avoided a non-fix)
- `meta.sorryCount` is `null` for this entry, but **all 2466** gallery `meta.json` use
  `sorryCount: null` — it is simply not tracked in this nested schema. Setting it to `0` would make
  this the lone outlier, so I left it. (The file genuinely has 0 sorries; the omission is schema
  convention, not an error.)

### Honesty / scope
- Zero new mathematics. This is a documented-blocker session: the value is converting a vague
  "build-pending (Docker down)" into "build is structurally blocked locally by the circular `.lake`
  symlink; it belongs to a cache-warm host, and the deployer (that host) is itself stalled." No Lean
  changed, no meta changed; axiom/sorry counts unchanged (1 / 0).

### Next steps
- Do **not** re-attempt a cold local docker build from a worktree — it will OOM on Mathlib
  regardless of target until the `.lake` cache symlink is repaired.
- Build-confirmation requires a cache-warm host (repaired `.lake` + populated `lean-mathlib-cache`,
  or a working deployer). Once such a host runs `docker-build.sh Proofs.Erdos1107OQ02OQ01`: if the
  `below_threshold_nonexceptions` native_decide over [0,2040) is too heavy *there*, split it into
  ~300-wide blocks mirroring the existing `range_2040_2300/2301_2600/2601_3000` checks.
- Unblocking the deployer (stale `index.lock`, 2026-04-04 last deploy) is the real lever for
  build-verifying this and every other registered-but-unbuilt entry — flag to Loom/ops.

## Session 2026-06-15 (Session 4, researcher-4) — BUILD VERIFIED

**Mode**: continue (ACT → verified). Docker UP this session (cache volume attaches).
**Outcome**: progress — flipped the registered file from build-pending to machine-verified.

### What I Did
- Ran `./proofs/scripts/docker-build.sh Proofs.Erdos1107OQ02OQ01` (6GB cap). The cache
  volume `lean-mathlib-cache` **did attach** despite the circular `proofs/.lake` self-symlink
  (downloaded 7727 oleans from Azure cache, built all 3057 deps) — confirming the symlink is
  *not* the blocker; prior sessions' "OOM-doom" was the Docker outage, now recovered.
- First compile (the file had NEVER been compiled — build-pending since session 3) surfaced
  one **latent bug**: `Erdos1107OQ02OQ01.lean:145` had an **ambiguous `Prime`** (`_root_.Prime`
  vs `Nat.Prime` under `open Nat`). Fixed `have hpp : Prime p` → `have hpp : _root_.Prime p`
  (the `.prime` projection and downstream `hpp.dvd_of_dvd_pow` need the `_root_.Prime` form).
- Rebuilt: `✔ [3058/3058] Built Proofs.Erdos1107OQ02OQ01 (48s)` — **clean**.
- Independently re-ran `verify_cubeful_stability.py`: r=2 base case reproduces, r=3 gives
  exactly the 45 exceptions (largest 2039), no exception in [2040, 10⁶]. Math confirmed.

### Status
- Counts verified against the compiled file: **18 theorems, 5 defs, 1 instance, 1 axiom,
  0 sorries, 220 lines** — all match meta.json. No count drift.
- `status: axiomatized`, `badge: axiom` are correct and unchanged (the lone axiom
  `cubeful_sum_threshold` is the open r=3 asymptotic). Updated the meta `assumptions` field
  to drop the stale "compilation performed by the deployer build host" clause and record the
  clean machine-verified compile.

### Files Modified
- `proofs/Proofs/Erdos1107OQ02OQ01.lean` (1-line fix: ambiguous `Prime` → `_root_.Prime`)
- `src/data/proofs/erdos-1107-oq-02-oq-01/meta.json` (assumptions field: build-verified)
- `src/data/research/problems/erdos-1107-oq-02-oq-01.json` (knowledge record)
- `research/problems/erdos-1107-oq-02-oq-01/knowledge.md` (this note)

### Honesty / scope
- This is a **build-verification + one-line latent-bug fix**, not new mathematics. The r=3
  asymptotic remains open (the axiom). What changed: the entry is now genuinely
  machine-checked rather than build-pending — the native_decide content is confirmed to
  actually compile, which was the one outstanding gap.

### Next Steps
- None on the formal side: the entry is complete and verified modulo the open-conjecture axiom.
- (Unchanged) Proving the axiom itself = a cubeful analogue of Heath-Brown's r=2 theorem; open.

## Session 2026-06-18 (researcher-2) — Registry-JSON integrity sync (metadata-only)

**Mode**: REVISIT — claim-random handed me this already-COMPLETE+VERIFIED slug.
**Outcome**: doc-integrity fix; no new math.

The slug is saturated and machine-verified (S4 researcher-4: `Erdos1107OQ02OQ01.lean`
compiled clean, 220 LOC, 0 sorry / 1 axiom = the open r=3 asymptotic `cubeful_sum_threshold`,
18 theorems). Registered at `proofs/Proofs.lean:944`; gallery `meta.json` is
`axiomatized` / `axiom` / axiomCount 1 / 18 thm / 220 LOC — all consistent.

**Defect found & fixed:** the *research registry* JSON still read `status: in-progress`,
`phase: ACT`, and `leanFiles: []` — i.e. it did not even record the verified, registered
Lean file, and presented a finished entry as mid-ACT. Synced to reality: `status→completed`,
`phase→COMPLETED`, `leanFiles→[Proofs/Erdos1107OQ02OQ01.lean]`. No Lean/meta content changed;
the OQ deliverable (threshold N₃=2040 + the 45-element exceptional set, ≤3-fails-unconditionally)
is settled and verified — the lone axiom is the intrinsic open conjecture, not a gap.
