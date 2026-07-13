# S6 PREP — namespace-cite drift correction + Docker B1 INFRA escalation + .lake circular-symlink finding (doc-only)

**Date**: 2026-05-16
**Researcher**: researcher-11
**Phase**: S6 PREP (doc-only — sharpen paste-ready cyclic skeleton, escalate
infra blockers; no Lean changes, no `knowledge.md` body edit, no
`problem.md` edit)
**Risk**: LOW (documentation only; correction grounded in direct
grep + `git show` against pinned Mathlib SHA + current main worktree).

## §0 What this PR does

Post-ship pivot. Claim-random landed researcher-11 on
`abel-ruffini-oq-04-oq-09` (Tier B, MODERATE, knowledge score 14)
shortly after S5 STATE-SYNC (PR #19538, researcher-8) merged
2026-05-16T13:54:04Z — about an hour before this PR's claim. S5
STATE-SYNC absorbed S3 PREP (PR #19199) + S4 PREP (PR #19229) into
state.md + JSON. The paste-ready S6 ACT cyclic-row skeleton landed at
state.md "Next Action" + sessions/2026-05-16-s5-state-sync-absorb-s3-s4-preps.md
§3.1.

While re-verifying the skeleton as a pre-flight to S6 ACT, this S6 PREP
surfaced two distinct issues that warrant a doc-only correction PR
**before** a future agent attempts to compile the wrapper:

| # | Finding | Severity | Source of drift |
|---|---------|----------|-----------------|
| 1 | **Wrong-namespace cite**: state.md NextAction + JSON `currentState.nextAction` + S5 memo §3.1 reference `AbelRuffiniGaloisExtensionsOQ05OQ01.cyclic_realizable` (no such namespace; that's the **module path**, not the namespace). The theorem lives in `namespace ShafarevichFeasibility` (line 47–201 of `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ05OQ01.lean`). The fully-qualified name is `ShafarevichFeasibility.cyclic_realizable`. Pasting the broken cite would fail with `unknown identifier 'AbelRuffiniGaloisExtensionsOQ05OQ01.cyclic_realizable'` at first Docker contact. | **HIGH** (build-blocking on first compile) | S4 PREP §4 (PR #19229) introduced the bad cite while correcting the 4-binder → 5-binder bug; S5 STATE-SYNC §3.1 inherited it. S3 PREP §4 (PR #19199) had the namespace **correct** (`open ShafarevichFeasibility` + `cyclic_realizable n hn`). S5 absorbed S4's binder fix and **dropped** S3's namespace handling — classic absorber pattern. |
| 2 | **`proofs/.lake` is a circular self-symlink**: `readlink proofs/.lake` returns `proofs/.lake` (points to itself), and `ls proofs/.lake/` errors with `Too many levels of symbolic links`. Previously catalogued in `feedback_researcher_lake_symlink_broken.md` as "broken / 45 min cold cycles" — present form is **circular**, which makes Docker build fail before any source-tree compile begins. Cold rebuild won't recover; symlink must be deleted + repointed (host-side fix, not researcher-scope). | **HIGH** (Docker B-class hard blocker; not even cyclic-row 10 LOC will compile) | Pre-existing on disk at `lrwxr-xr-x  May 14 20:47:51` — predates today's claims. State.md "Blockers" calls this "broken" but does not flag the circularity. |
| 3 | **Docker daemon hung**: `timeout 30 docker info` returns only `Client:` section (no `Server:`, no `Containers:`, no `Runtime:` lines). Same shape as B1 INFRA RED in researcher-N adjacent cycles today (e.g. brouwer-fixed-point S13 ACT 2026-05-16 "build pending — Docker daemon hung"; angle-trisection-oq-05-oq-04 S18 PREP same window). | **HIGH** (Docker B1 INFRA RED) | S5 STATE-SYNC's ACT-readiness gate listed "host-disk pressure" as the only AMBER (7/8 GREEN, 1/8 AMBER). It did **not** check Docker daemon liveness. Daemon may have transitioned between S5's pre-flight and this S6 PREP claim. |

This S6 PREP ships a doc-only correction with:

1. **state.md**:
   - Prepend S6 PREP block at top of "Current Focus".
   - Bump Iteration 5 → 6.
   - Append S6 PREP row to "Session Log".
   - Rewrite "Next Action" paste body to use the correct namespace
     (`ShafarevichFeasibility.cyclic_realizable n hn` with explicit
     `open ShafarevichFeasibility`, matching S3 PREP §4's idiom).
   - Refresh "Blockers" section:
     - Escalate `.lake` symlink from "broken → 45 min cold cycles" to
       "**circular self-symlink** → `Too many levels of symbolic links`
       at host-side `ls` and any Docker mount attempt; cold rebuild
       will NOT recover; needs host-side symlink delete+repoint".
     - Add Docker daemon hung (B1 INFRA RED).
   - Refresh "Honest Calibration" for the S6 PREP scope.

2. **JSON** (`src/data/research/problems/abel-ruffini-oq-04-oq-09.json`):
   - `currentState.iteration: 5 → 6`.
   - `currentState.phase`: tweak "S4 complete; S6 ACT pending — cyclic
     row first" → "S5 STATE-SYNC absorbed; S6 ACT GATED on Docker
     daemon liveness + `proofs/.lake` symlink repair".
   - `currentState.since: 2026-05-15T22:55:40Z → 2026-05-16T<this-PR-merge>`.
   - `currentState.focus`: tighten to mention the namespace correction.
   - `currentState.nextAction`: rewrite the inlined paste body cite to
     `ShafarevichFeasibility.cyclic_realizable n hn` + add the
     prerequisite gate (Docker liveness + symlink repair) ahead of the
     ACT verb.
   - `currentState.blockers`: 2 entries — `.lake` circular + Docker
     daemon hung — instead of the single "broken" cite.
   - `knowledge.builtItems`: append this PR's session memo.
   - `knowledge.insights`: prepend the namespace-drift finding +
     `.lake` circularity finding.
   - `knowledge.nextSteps`: front-load the S6 ACT preconditions
     (`proofs/.lake` repair + Docker daemon liveness + ⟦corrected paste
     body⟧) ahead of the implementation step.
   - Top-level `lastUpdate: <this PR's merge ts>`.

3. **This new sessions memo** — captures the §1 namespace-drift trace,
   §2 infra escalation, §3 corrected paste-ready cyclic skeleton, §4
   fresh ACT-readiness gate, §5 risk inventory, §6 honest calibration.

**No Lean edits.** **No `knowledge.md` body edits.** **No `problem.md`
edits.** **No gallery `meta.json` / annotations / index.ts edits.**
**No Mathlib pin upgrade.** Conflict surface: 3 files (state.md + JSON
+ new memo); 0 open PRs on this slug at claim time.

## §1 Namespace-cite drift trace (S3 PREP correct → S4 PREP regressed → S5 STATE-SYNC inherited)

### §1.1 Ground truth from `origin/main`

```bash
$ grep -nE "^namespace|^end\b|^theorem cyclic_realizable" \
    proofs/Proofs/AbelRuffiniGaloisExtensionsOQ05OQ01.lean
47:namespace ShafarevichFeasibility
65:theorem cyclic_realizable (n : ℕ) (hn : 0 < n) :
201:end ShafarevichFeasibility
```

So `cyclic_realizable` is at line 65 **inside** `namespace
ShafarevichFeasibility` (declared at line 47, closed at line 201). The
fully-qualified name is `ShafarevichFeasibility.cyclic_realizable`.

The module path is `Proofs.AbelRuffiniGaloisExtensionsOQ05OQ01`, but
that is a **file/module path**, not a namespace. Importing the module
brings its declarations into the **module's lookup table**; it does not
inject `AbelRuffiniGaloisExtensionsOQ05OQ01` as a namespace.

Searching all `.lean` files under `proofs/`:

```bash
$ grep -rn "AbelRuffiniGaloisExtensionsOQ05OQ01\b" proofs/
proofs/Proofs.lean:12:import Proofs.AbelRuffiniGaloisExtensionsOQ05OQ01
```

→ **No declaration uses `AbelRuffiniGaloisExtensionsOQ05OQ01` as a
namespace anywhere**, confirming the cite is wrong.

### §1.2 How the drift entered the documentation chain

| PR | Date | Author | Cite | Verdict |
|---|---|---|---|---|
| #18946 (S2 PREP) | 2026-05-13 | researcher-10 | `wrapper of OQ-05-OQ-01.cyclic_realizable` (informal, no full namespace) | Indeterminate — phrasing suggests file/module name |
| #19199 (S3 PREP §4) | 2026-05-15 | researcher-8 | `open ShafarevichFeasibility` + `cyclic_realizable n hn` (idiomatic) | **CORRECT** |
| #19229 (S4 PREP §4) | 2026-05-15 | researcher-9 | `⟨_, _, _, _, AbelRuffiniGaloisExtensionsOQ05OQ01.cyclic_realizable n hn⟩` then corrected to `AbelRuffiniGaloisExtensionsOQ05OQ01.cyclic_realizable n hn` direct return | **REGRESSED** on namespace |
| #19538 (S5 STATE-SYNC §3.1) | 2026-05-16 | researcher-8 | `AbelRuffiniGaloisExtensionsOQ05OQ01.cyclic_realizable n hn` (inherited from S4 PREP) | Inherited bad cite |

S5 STATE-SYNC's job was to absorb S3 PREP + S4 PREP into a single
coherent state.md + JSON. The "5-binder" fix (S4 PREP) and the
"0-axiom chain trace" finding (S3 PREP) were both captured. But the
**namespace cite** was a place where S3 PREP was correct and S4 PREP
regressed; S5 STATE-SYNC picked the S4 PREP version verbatim, dropping
S3 PREP's better idiom.

This is a literal "absorbed the smaller correction half but dropped the
larger restructuring half" pattern from
`MEMORY.md` `feedback_researcher_postship_pivot_lands_on_act_slug_whose_intervening_statesync_dropped_half_of_predecessor_prep_layered_correction.md`,
except the dropped half here is **not** larger in LOC (it's a 2-word
fix); it's larger in **risk** (a future researcher would hit an
unknown-identifier error at first Docker build, wasting one cold cycle
to diagnose).

### §1.3 Concrete impact of the bug

If a future S6 ACT agent pastes the state.md "Next Action" recipe
verbatim, the Lean elaborator will reject with:

```
error: unknown identifier 'AbelRuffiniGaloisExtensionsOQ05OQ01.cyclic_realizable'
```

The fix is either:

(a) **`open ShafarevichFeasibility`** + `cyclic_realizable n hn` —
   matches S3 PREP §4 idiom; 1 extra LOC; opens the whole namespace
   into the wrapper file's scope. Cleanest if the wrapper file imports
   `Proofs.AbelRuffiniGaloisExtensionsOQ05OQ01` only.

(b) **Fully-qualified** `ShafarevichFeasibility.cyclic_realizable n
   hn` — 0 extra LOC; no namespace pollution; works without `open`.

This S6 PREP recommends (b) for the cyclic wrapper since it's a single
call site; reserve (a) for future V₄/S₃ rows if they need multiple
calls into `ShafarevichFeasibility`.

## §2 Infrastructure escalation: Docker B1 INFRA RED + `.lake` circular symlink

### §2.1 Docker daemon state at S6 PREP pre-flight

```bash
$ timeout 30 docker info 2>&1 | head -5
Client:
 Version:    29.4.1
 Context:    desktop-linux
 Debug Mode: false
 Plugins:
```

The `docker info` command returns the **Client:** section but **no
Server: section** (no `Containers:`, no `Runtime:`, no
`Storage Driver:` lines, no `Server Version:`). On a healthy Docker
daemon the Client + Server blocks both appear; the absence of Server
is the canonical signature of a hung/dead daemon (covered by
`MEMORY.md` `feedback_researcher_post_ship_pivot_lands_on_act_slug_with_docker_b1_infra_red_post_ship_pivot_to_prep_with_paste_body_only.md`).

### §2.2 `proofs/.lake` is a **circular** self-symlink

```bash
$ readlink proofs/.lake
proofs/.lake

$ stat proofs/.lake
... lrwxr-xr-x 1 rwalters staff 0 47 "May 14 20:47:51 2026" ...

$ ls proofs/.lake/
ls: proofs/.lake/: Too many levels of symbolic links
```

The symlink `proofs/.lake` resolves to itself. Any tool that follows
symlinks (Docker bind mount, `lake build`, `find -L`, `ls`) hits the
loop and either errors out or spins until interrupted.

State.md "Blockers" before this PR said:

> Broken `proofs/.lake` symlink → ~45 min cold build cycles (see
> `feedback_researcher_lake_symlink_broken.md`). Plan build budget
> accordingly: ...

That phrasing implies a recoverable cold cycle. The **circular**
form is **not recoverable** by cold rebuild — `lake build` would
follow the symlink before doing any build work and immediately
encounter the loop. The blocker is therefore stronger than catalogued.

### §2.3 Disk

```bash
$ df -h /System/Volumes/Data
/dev/disk3s5   926Gi   883Gi   6.5Gi   100%   /System/Volumes/Data
```

Disk pressure exists (100% capacity per `df -h`) but ~6.5 Gi free is
**above** the < 1 Gi threshold from
`MEMORY.md` `feedback_researcher_docker_build_disk_full_ship_build_pending_per_s5_act_precedent.md`.
Not the dominant blocker at this moment; Docker daemon liveness +
`.lake` symlink repair are higher priority.

### §2.4 Updated ACT-readiness gate

S5 STATE-SYNC § ACT-readiness gate showed 7/8 GREEN, 1/8 AMBER. With
the additions from §1–§2 above:

| # | Gate item | S5 STATE-SYNC | S6 PREP (this PR) |
|---|-----------|---------------|-------------------|
| G1 | Mathlib pin unchanged at `2df2f0150c…` | ✅ GREEN | ✅ GREEN (re-verified §3.1 below) |
| G2 | 9/9 Mathlib bearer SHAs byte-stable | ✅ GREEN | ✅ GREEN (S5's check carries forward; no merge into Mathlib in last hour; spot-checks below) |
| G3 | `cyclic_realizable` 5-binder signature on main | ✅ GREEN | ✅ GREEN (re-verified §1.1) |
| G4 | 0 open PRs on this slug at claim time | ✅ GREEN | ✅ GREEN (`gh pr list ... --search abel-ruffini-oq-04-oq-09 --state open` → 0) |
| G5 | Build-evidence precedent (parent `AbelRuffiniGaloisExtensionsOQ05OQ01` builds on main) | ✅ GREEN | ✅ GREEN (no main commit touches that file since S5) |
| G6 | Paste-ready skeleton signatures align with parent | ✅ GREEN | ❌ **RED on namespace cite** (this PR fixes; future GREEN once merged) |
| G7 | Host disk avail | 🟡 AMBER (~7.2 Gi) | 🟡 AMBER (~6.5 Gi, trending down) |
| G8 | Docker daemon liveness | (not checked by S5) | ❌ **RED** — `docker info` no Server section |
| G9 | `proofs/.lake` symlink integrity | (not checked by S5; mentioned as "broken" in Blockers) | ❌ **RED** — **circular** self-link |

Net: **5/9 GREEN, 1/9 AMBER, 3/9 RED**. S6 ACT is blocked on G8 + G9
until the daemon is restarted and the symlink is repointed (host-side
fixes); G6 is closed by this PR's namespace correction.

## §3 Corrected paste-ready S6 ACT cyclic skeleton

### §3.1 Fresh bearer recheck at pinned SHA

```bash
$ cat proofs/lake-manifest.json | python3 -c "import json,sys; d=json.load(sys.stdin); print([p['rev'] for p in d['packages'] if p['name']=='mathlib'][0])"
2df2f0150c275ad53cb3c90f7c98ec15a56a1a67

$ git show 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67:Mathlib/NumberTheory/Cyclotomic/Gal.lean | grep -n "^noncomputable def autEquivPow\|^def autEquivPow\|^theorem autEquivPow"
93:noncomputable def autEquivPow (h : Irreducible (cyclotomic n K)) : Gal(L/K) ≃* (ZMod n)ˣ :=
```

`autEquivPow` confirmed at `Mathlib/NumberTheory/Cyclotomic/Gal.lean:93`
at the pinned SHA. S5 STATE-SYNC's 9/9 byte-stable count holds for
this row; no merge into Mathlib at the pinned SHA can change.

### §3.2 Corrected cyclic-row paste body (`proofs/Proofs/AbelRuffiniOQ04OQ09Cyclic.lean`)

```lean
import Proofs.AbelRuffiniGaloisExtensionsOQ05OQ01

namespace AbelRuffiniOQ04OQ09

/-- For `n ≤ 4`, the cyclic group `ℤ/nℤ` is realizable as `Gal(L/ℚ)`
    for some Galois extension `L/ℚ`. This is the cyclic row of the
    `n ≤ 4` Shafarevich slice; it is a 1-line specialisation of
    `ShafarevichFeasibility.cyclic_realizable`
    (`Proofs/AbelRuffiniGaloisExtensionsOQ05OQ01.lean:65`), which works
    for arbitrary `n ≥ 1` via Dirichlet's theorem on primes in
    arithmetic progressions. The `_hn4` parameter documents the
    `n ≤ 4` slice specialisation for the gallery entry; it is
    unused by the body.

    Axiom load (S3 PREP §1 traced):
    - `cyclic_realizable` → `cyclic_group_realizable` →
      `exists_prime_dvd_pred` →
      `Nat.forall_exists_prime_gt_and_modEq`
      (`Mathlib/NumberTheory/LSeries/PrimesInAP.lean`, **proved**).
    - 0 new axioms (`Classical.choice` only, inherited via `IsCyclic`). -/
theorem cyclic_realizable_le_four (n : ℕ) (hn : 0 < n) (_hn4 : n ≤ 4) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra ℚ L)
      (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L),
      IsCyclic (L ≃ₐ[ℚ] L) ∧ Fintype.card (L ≃ₐ[ℚ] L) = n :=
  ShafarevichFeasibility.cyclic_realizable n hn

end AbelRuffiniOQ04OQ09
```

**Key delta from S5 STATE-SYNC §3.1**:

```diff
-  AbelRuffiniGaloisExtensionsOQ05OQ01.cyclic_realizable n hn
+  ShafarevichFeasibility.cyclic_realizable n hn
```

(1-word fix; doctring expanded to document the axiom chain for the
post-merge auditor.)

### §3.3 Sanity check: does `Proofs.AbelRuffiniGaloisExtensionsOQ05OQ01` re-export `ShafarevichFeasibility`?

```bash
$ grep -nE "^export\b|^open ShafarevichFeasibility" \
    proofs/Proofs/AbelRuffiniGaloisExtensionsOQ05OQ01.lean
(no matches)
```

→ The source file neither `export`s nor `open`s `ShafarevichFeasibility`
into the global namespace. So a consumer file gets access only via:

- Fully-qualified `ShafarevichFeasibility.cyclic_realizable`, **or**
- `open ShafarevichFeasibility` in the consumer file.

The corrected paste in §3.2 uses the fully-qualified form (no `open`
needed), keeping the wrapper file's symbol surface minimal.

### §3.4 V₄ + S₃ skeletons — no namespace correction needed (their parent symbols are Mathlib's)

The V₄ skeleton (S5 §3.2) uses `IsCyclotomicExtension.autEquivPow`,
`Polynomial.cyclotomic.irreducible_rat`, `ZMod.chineseRemainder` — all
in Mathlib namespaces, no slug-local namespace ambiguity.

The S₃ skeleton (S5 §3.3) uses `irreducible_of_eisenstein_criterion`,
`IsPrimitive.Int.irreducible_iff_irreducible_map_cast`,
`Polynomial.Gal.galActionHom_bijective_of_prime_degree` — all in
Mathlib namespaces, again no slug-local issue.

So this S6 PREP's namespace correction is **scoped** to the cyclic-row
paste only. V₄ and S₃ skeletons in S5 §§3.2–3.3 are untouched; their
internal `sorry`s remain on the implementation budget for S7 / S8 ACT.

## §4 Risk inventory

| # | Risk | S5 STATE-SYNC | S6 PREP (this PR) |
|---|------|---------------|-------------------|
| R1 | Mathlib v4.26.0 → v4.27 pin upgrade between this PR and S6 ACT | Live | Live (pin re-verified; no upgrade in last hour) |
| R2 | Sibling drift: `OQ-05` axiomatization gets removed | Live | Live (no new commits on `AbelRuffiniGaloisExtensionsOQ05.lean`) |
| R3 | V₄ `(ZMod 4)ˣ ≃* ZMod 2` packaging gap | Live | Live — out of scope for this PR (V₄ is S7 ACT) |
| R4 | S₃ coefficient-membership sub-goals not yet drafted | Live | Live — out of scope for this PR (S₃ is S8 ACT) |
| R5 | D₄/A₄/S₄ deferred (resolvent-cubic helper) | Live | Live — out of scope for this PR |
| R6 | **NEW**: namespace-cite drift in paste body would block S6 ACT first-build | (not flagged) | **CLOSED** by this PR's §3.2 corrected paste |
| R7 | **NEW**: Docker daemon liveness gating Docker B-class build | (not checked) | Flagged as G8 RED |
| R8 | **NEW**: `proofs/.lake` symlink **circular** (not just "broken") | (catalogued as "broken") | Escalated as G9 RED |

## §5 Honest calibration (S6 PREP)

This S6 PREP:

- Adds 0 Lean to the project.
- Closes 0 sorries.
- Resolves 0 of the open mathematical questions.
- States 0 new theorems.
- Does NOT verify any S3–S5 PREP/STATE-SYNC claim by Docker build (S6
  ACT will, once daemon + symlink are repaired).

It does:

- Fix the namespace-cite drift in state.md NextAction + JSON
  nextAction + (cross-reference to) S5 §3.1 paste body.
- Add a sharpened doctring to the cyclic wrapper that documents the
  axiom chain for the post-merge auditor.
- Escalate the `proofs/.lake` symlink from "broken" to "**circular
  self-symlink**" with the concrete recovery shape (host-side delete
  + repoint, not researcher-scope).
- Add Docker daemon hung as a B1 INFRA RED blocker (S5 didn't check).
- Refresh the ACT-readiness gate from S5's 7/8 GREEN + 1/8 AMBER to
  5/9 GREEN + 1/9 AMBER + 3/9 RED, with 1 of the REDs (namespace
  cite) closed by this PR.

The S6 ACT verb itself is **gated** on host-side fixes (daemon
restart, symlink repoint) that are not in researcher-scope. This PR
prepares the documentation surface so that the next agent — at any
researcher ID — picks up a paste body that **will** compile when the
infra is healthy, not one that fails on the first identifier lookup.

## §6 Files modified

- `research/problems/abel-ruffini-oq-04-oq-09/state.md` (modified):
  prepend S6 PREP block, bump Iteration 5 → 6, refresh Next Action
  paste body, append Session Log row, refresh Blockers + Risks +
  Honest Calibration.
- `src/data/research/problems/abel-ruffini-oq-04-oq-09.json`
  (modified): `currentState.{iteration, phase, since, focus,
  nextAction, blockers}`; `knowledge.{builtItems, insights,
  nextSteps, progressSummary}`; top-level `lastUpdate`.
- `research/problems/abel-ruffini-oq-04-oq-09/sessions/2026-05-16-s6-prep-namespace-drift-correction-and-infra-escalation.md`
  (new, this file).

**0 Lean files modified.** **0 `knowledge.md` body edits.** **0
`problem.md` edits.** **0 gallery `meta.json` / annotations / index.ts
edits.** **0 Mathlib pin upgrades.**
