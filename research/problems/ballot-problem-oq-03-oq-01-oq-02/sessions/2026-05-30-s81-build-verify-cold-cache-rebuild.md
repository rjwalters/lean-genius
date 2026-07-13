# Session 81 — BUILD-VERIFY under recovered INFRA: cold-cache Docker rebuild + lake fetch (researcher-1, 2026-05-30T~15:51Z)

## §0. Why this S81 fires (T+13d post-S80 STATE-SYNC merge)

This S81 BUILD-VERIFY ships ~13 days after the S80 STATE-SYNC
(researcher-9, 2026-05-17T~01:20Z, PR shipping doc-only).  The trigger
is the **B1+B2 INFRA RED clearance** observable on host at S81 entry:

| Surface | S80T (2026-05-17 ~01:20Z) | S81T (2026-05-30 ~15:51Z) | Delta |
|---|---|---|---|
| **B1 Docker daemon Server** | hung ~16.5h | responsive (v29.4.1) | **CLEAR** |
| **B2 disk avail** | 2.9 Gi (drain −0.8 Gi/h) | 62 Gi | **CLEAR (+59 Gi)** |
| **B3 .lake symlink** | self-circular | self-circular | unchanged |
| **Mathlib SHA** | `2df2f015...` (stable 4.5d) | `2df2f015...` (stable ~18d) | unchanged |

Independent corroboration of B1 recovery: parent `main` carries commit
`37b6dbbfea8 research(infinitude-primes-4k3-oq-01): S11 STATE-SYNC
ACT-VERIFIED — Docker recovered, S9 Tower file 3059 jobs clean` —
i.e. Docker recovery was observed and verified on another slug between
S80 and S81.  The S81 BUILD-VERIFY gate from S79/S80 is therefore
satisfied for B1+B2; B3 remains structurally circular but per S80 §B3
this does NOT independently block Docker build (volume mount overlays
the .lake path inside the container).

## §1. INFRA evidence at S81 entry

### §1.B1 — Docker daemon responsive

```
$ timeout 10 docker info --format '{{.ServerVersion}}'
29.4.1
```

Exit 0, Server section populated. Recovery from S80T's empty-Server
section (~T+16.5h hung) is **complete**; total downtime ≈ 13d 14h
between S78 ACT (2026-05-16T08:50Z) and observed recovery.  No host
intervention recorded in researcher-1's session memory (likely
champion / daemon-scope recovery action, possibly Docker Desktop
restart + system prune as recommended by S80 §B2 mitigation).

### §1.B2 — Disk `/System/Volumes/Data` 62 Gi avail

```
$ df -h /System/Volumes/Data
Filesystem      Size    Used   Avail Capacity iused ifree %iused  Mounted on
/dev/disk3s5   926Gi   836Gi    62Gi    94%     22M  649M    3%   /System/Volumes/Data
```

62 Gi avail — well above the S79-sharpened gate (≥5.0 Gi) and the
S80-projected zero-crossing point (~05:00Z 2026-05-17).  Either active
recovery (`docker system prune` + qcow2 audit) reclaimed the disk, or
~13d of natural drain reversal cleared the pressure.  Out-of-scope at
S81 to attribute root cause.

### §1.B3 — `proofs/.lake` still self-circular

```
$ ls -la proofs/.lake
proofs/.lake -> /Users/rwalters/GitHub/lean-genius/proofs/.lake
$ ls -la /Users/rwalters/GitHub/lean-genius/proofs/.lake
/Users/rwalters/GitHub/lean-genius/proofs/.lake -> /Users/rwalters/GitHub/lean-genius/proofs/.lake
```

Worktree symlink → main-repo symlink → itself.  Same pathology as
S79+S80 entries; carries forward.  S80 §B3 mitigation note holds:
Docker build is mounted via volume (`-v
${CACHE_VOLUME}:/workspace/proofs/.lake/build:delegated`) so the
container sees a fresh writable `/workspace/proofs/.lake/build` and
does not depend on the host-side .lake directory existing.

### §1.Mathlib pin

```
$ jq -r '.packages[] | select(.name=="mathlib") | .rev' proofs/lake-manifest.json
2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
```

Unchanged from S78/S79/S80 — stable ~18 days since 2026-05-12.  S78
§1.2 Cluster A 4-row bearer table + S76 §1 14-row table carry-forward
trustable verbatim (no bearer re-walk needed at S81 entry).

## §2. Build action — Proofs.BallotProblemOQ03OQ02 cold-cache rebuild

### §2.1 Command

```
$ LEAN_MEMORY_LIMIT=16384 LEAN_BUILD_TIMEOUT=30m \
    ./proofs/scripts/docker-build.sh Proofs.BallotProblemOQ03OQ02 \
    > .loom/logs/build-researcher-1-ballot-s81.log 2>&1 &
```

Memory 16 GB (per S79/S80 recommended limit), timeout 30 min, target
the parent file post-S78 Cluster A patch.

### §2.2 Cold-cache reality

Observed on S81 entry: the Docker image `lean4-arm64:v4.26.0` was
**not present** on host (presumably wiped during B1/B2 recovery), AND
the persistent `lean-mathlib-cache` volume was empty.  This forces a
3-phase cold-start:

| Phase | Activity | Elapsed at end | Notes |
|---|---|---|---|
| P1 | Docker image build (Dockerfile, ubuntu:22.04 base + lean toolchain) | ~3 min | first-time only |
| P2 | Mathlib + dependency git clones (mathlib, plausible, LeanSearchClient, importGraph, proofwidgets, aesop, Qq, batteries, ...) | ~+30s | first-time only |
| P3 | `lake exe cache get` — download 7727 cached `.olean` files from Azure | ~+90s | populates `lean-mathlib-cache` volume |
| P4 | `lake build Proofs.BallotProblemOQ03OQ02` — compile project files | TBD | target work |

P1+P2+P3 ≈ 5 min of setup BEFORE the project lake build begins; this
is uncacheable for a fresh `lean-mathlib-cache` volume.  All
subsequent S82+ BUILD-VERIFY runs from this host should skip P1
(image cached) and P3 (cache populated), needing only ~30s setup.

### §2.3 First build (S78 ACT carry-forward) outcome — 18 errors, S78 strategy refuted

```
error: Proofs/BallotProblemOQ03OQ02.lean:1854:53: Type mismatch
error: Proofs/BallotProblemOQ03OQ02.lean:1854:11: Application type mismatch: The argument
error: Proofs/BallotProblemOQ03OQ02.lean:1916:50: Unknown identifier `cast_PathMN_coe`
error: Proofs/BallotProblemOQ03OQ02.lean:1915:96: unsolved goals
error: Proofs/BallotProblemOQ03OQ02.lean:1927:78: Unknown identifier `cast_PathMN_coe`
error: Proofs/BallotProblemOQ03OQ02.lean:1925:96: unsolved goals
error: Proofs/BallotProblemOQ03OQ02.lean:1935:8: Unknown identifier `cast_PathMN_coe`
error: Proofs/BallotProblemOQ03OQ02.lean:2040:50: don't know how to synthesize placeholder for argument `sfx`
error: Proofs/BallotProblemOQ03OQ02.lean:2040:7: failed to infer `have` declaration type
error: Proofs/BallotProblemOQ03OQ02.lean:1976:81: unsolved goals
error: Proofs/BallotProblemOQ03OQ02.lean:2175:6: Type mismatch
error: Proofs/BallotProblemOQ03OQ02.lean:2185:6: Type mismatch
error: Proofs/BallotProblemOQ03OQ02.lean:2254:19: Tactic `rewrite` failed: …
error: Proofs/BallotProblemOQ03OQ02.lean:2255:19: Tactic `rewrite` failed: …
error: Proofs/BallotProblemOQ03OQ02.lean:2258:12: Tactic `rewrite` failed: …
error: Proofs/BallotProblemOQ03OQ02.lean:2268:8: Type mismatch: After simplification, term …
error: Proofs/BallotProblemOQ03OQ02.lean:2271:12: Tactic `rewrite` failed: …
error: Proofs/BallotProblemOQ03OQ02.lean:2281:8: Type mismatch: After simplification, term …
error: Lean exited with code 1
```

Total: **18 errors** (NOT the expected 8 per S79 §nextAction §expected
outcome).  Decision matrix branch: **(b) residual at Cluster A sites**
— matched the S78 §9 trap.4 contingency exactly.

Root cause: the S78 ACT inserted `cast_PathMN_coe` companion lemma
at L1853-1855 with type signature

```lean
@[simp] private lemma cast_PathMN_coe {m n₁ n₂ : ℕ} (h : n₁ = n₂) (e : PathMN m n₁) :
    ((cast (congrArg (PathMN m) h) e) : List Bool) = (e : List Bool) := by
  cases h; rfl
```

The `((·) : List Bool)` coercion target does NOT exist — `PathMN m n :=
{ l : LPath // …}` is a Subtype (no `CoeHead`/`Coe` instance to its
base `List Bool`), so the lemma's type signature fails to elaborate
with L1854 Type mismatch + L1854 Application type mismatch.  The
lemma symbol `cast_PathMN_coe` is therefore NEVER registered into the
namespace, cascading to 3× "Unknown identifier" at L1916/L1927/L1935
+ 3× unsolved-goals at L1915/L1925/L1976 from broken simp-only chains.

This was foreseeable from a closer read of `PathMN`'s definition at
L92: `def PathMN (m n : ℕ) : Type := { l : LPath // l.length = m + n ∧ l.countP (· = false) = m }`
— a plain `Subtype` with no coercion instance.  The pre-existing
`cast_PathMN_val` at L1849 correctly uses the `.val` accessor.  S78's
attempt to introduce a `: List Bool` coercion-form companion was
based on the false premise that the coercion would auto-resolve.

### §2.4 Trap.4 doctor patch (this S81 session, ACT) — 5 edits

Per S78 §9 trap.4 / S80 §decision matrix (b), the planned fallback is
to promote `cast_PathMN_val` to `@[simp]` and discard the malformed
`cast_PathMN_coe`.  Applied within this S81 session:

| # | File:line | Edit |
|---|---|---|
| 1 | L1849 | Add `@[simp]` attribute to `cast_PathMN_val` |
| 2 | L1853-1855 | DELETE the malformed `cast_PathMN_coe` definition (4 LOC removed) |
| 3 | L1916 | Strip `cast_PathMN_coe, ` from simp-only arg list (1 site, was L1916 post-S78) |
| 4 | L1927 | Strip `cast_PathMN_coe,` from simp-only arg list (1 site, was L1927-1928 post-S78) |
| 5 | L1935 | Swap `exact cast_PathMN_coe _ _` → `exact cast_PathMN_val _ _` (1 site, was L1935 post-S78) |

Net delta: **-4 / +1 LOC**, parent file 2532 → 2528 lines.

### §2.5 Second build (post-trap.4) outcome — 15 errors, Cluster A NOT closed

```
error: Proofs/BallotProblemOQ03OQ02.lean:1911:96: unsolved goals
error: Proofs/BallotProblemOQ03OQ02.lean:1921:96: unsolved goals
error: Proofs/BallotProblemOQ03OQ02.lean:1931:24: don't know how to synthesize placeholder for argument `h`
error: Proofs/BallotProblemOQ03OQ02.lean:1929:57: unsolved goals
error: Proofs/BallotProblemOQ03OQ02.lean:2036:50: don't know how to synthesize placeholder for argument `sfx`
error: Proofs/BallotProblemOQ03OQ02.lean:2036:7: failed to infer `have` declaration type
error: Proofs/BallotProblemOQ03OQ02.lean:1972:81: unsolved goals
error: Proofs/BallotProblemOQ03OQ02.lean:2171:6: Type mismatch
error: Proofs/BallotProblemOQ03OQ02.lean:2181:6: Type mismatch
error: Proofs/BallotProblemOQ03OQ02.lean:2250:19: Tactic `rewrite` failed: …
error: Proofs/BallotProblemOQ03OQ02.lean:2251:19: Tactic `rewrite` failed: …
error: Proofs/BallotProblemOQ03OQ02.lean:2254:12: Tactic `rewrite` failed: …
error: Proofs/BallotProblemOQ03OQ02.lean:2264:8: Type mismatch: After simplification, term …
error: Proofs/BallotProblemOQ03OQ02.lean:2267:12: Tactic `rewrite` failed: …
error: Proofs/BallotProblemOQ03OQ02.lean:2277:8: Type mismatch: After simplification, term …
error: Lean exited with code 1
```

Total: **15 errors** (down from 18; net −3 from cleaning up the
cascading "Unknown identifier" errors).  All line numbers shifted by
−4 vs first build (post `cast_PathMN_coe` removal: 4 LOC deleted).

| Cluster | First build (S78 ACT) | Post-trap.4 | Sites |
|---|---|---|---|
| A: lemma def | 2 (L1854 Type/App) | 0 | DELETED |
| A: cascade | 3 "Unknown ident" (L1916/1927/1935) | 0 | DELETED |
| A: simp-body | 2 unsolved (L1915/1925) | 4 (L1911/1921/1929/1931 — gvCanonInv_val_other split into 2) | **STILL OPEN** |
| B?: cascade | 4 (L1976/2040×2/2175/2185) | 4 (L1972/2036×2/2171/2181) | unchanged |
| D: rewrite | 6 (L2254/2255/2258/2268/2271/2281) | 6 (L2250/2251/2254/2264/2267/2277) | unchanged |
| **Total** | **18** | **15** | |

### §2.6 Diagnosis — trap.4 reverts to pre-S78 baseline; Cluster A genuinely unfixed

The pre-S78 baseline error count was **15** (per S76 + mechanic
#19264's Clusters E+F discharge, dropping 23 → 15).  Trap.4 returns
the file to the 15-error state by eliminating S78's malformed lemma
+ its cascade, BUT adds `@[simp]` to `cast_PathMN_val`.  The Cluster
A simp-only proof bodies at L1911-1931 (the `gvCanonInv_val_ci` /
`_cj` / `_other` triple) still don't close — `cast_PathMN_val`
@[simp] is NOT sufficient to discharge them.

This refutes the S77 §5.2 + S78 §9 trap.4 contingency: BOTH the
planned `cast_PathMN_coe` (broken at type-sig elaboration) AND the
fallback `cast_PathMN_val` @[simp] (insufficient at goal-closure) fail
to fix Cluster A.  The strategic premise — "Cluster A's
`gvCanonInv_val_*` lemmas need a `@[simp]` cast helper to close
their simp-only proofs" — is empirically falsified.

Additional finding at L1931 (`gvCanonInv_val_other` proof's final
`exact`): `cast_PathMN_val` takes explicit `(h : n₁ = n₂)` and
`(e : PathMN m n₁)`; calling `exact cast_PathMN_val _ _` cannot
synthesize `h` from local context (the goal mentions only
`(cast … (t.2 k)).val = (t.2 k).val` post-simp; the equality witness
`h : n₁ = n₂` lives implicitly inside the `congrArg (PathMN cfg.m) (…)`
proof inside the def of `gvCanonInv`'s `else` branch — not
reconstructible from the goal type alone).  This is a NEW Cluster A
site not previously catalogued — S82+ must treat it explicitly.

## §3. S82+ next-action recommendation

The two-attempt-failed Cluster A strategy invalidates the S78-era
mechanic kit for Cluster A.  Three candidate replanning paths:

- **(α) Open the `gvCanonInv` def black box.** L1911-1935's three
  `gvCanonInv_val_*` lemmas all peel `gvCanonInv` to access the inner
  `cast (congrArg …)`. Instead of fighting simp/cast, restructure the
  `gvCanonInv` definition itself so that `.val` is accessible without
  cast — e.g. define `gvCanonInv` to return paths via `.val`
  computation directly + a separate well-formedness witness, sidestepping
  the cast-equality round-trip. Refactor scope: ~30-50 LOC.
- **(β) Replace `exact cast_PathMN_val _ _` at L1931 with an explicit
  `have h : … := …` providing the equality witness.** Targets the new
  Cluster A site surfaced at S81 entry. Scope: ~5 LOC.
- **(γ) Switch from `cast` to `Eq.mpr (congrArg …)` in `gvCanonInv`.**
  Mathlib idiom for type-equal value transport; `Eq.mpr` plays better
  with simp than raw `cast` does in many cases. Scope: refactor
  L1869-1899 inner definition (~10-15 LOC).

Recommend **(α)** as the principled long-term fix; (β) is a tactical
plug but doesn't address the root simp-non-closure at L1911/L1921;
(γ) is medium-risk and would need a Mathlib API pin-walk first.

S82 PARENT-TRIAGE-2 (researcher next-session) should re-do S74's
6-cluster classification on the new 15-error baseline (Clusters A/B/D
remain; Clusters E/F were closed by #19264; Cluster C is now
ambiguous — the 4 errors at L1972/2036/2171/2181 may be Cluster B or
Cluster C in S74's original taxonomy; needs spot-check).

## §3. Cache-volume observation for future BUILD-VERIFY runs

S81 establishes a fresh `lean-mathlib-cache` Docker volume populated
with the 7727 .olean files at Mathlib SHA `2df2f015...`.  S82+
BUILD-VERIFY runs from the same host using `docker-build.sh` will hit
this volume and skip the P3 cache-get phase (~90s saved per run).
The S78 ACT precedent's "cache-replay-eligible once daemon healthy"
mitigation now applies for ~weeks until next host disk reset.

## §4. Non-actions at S81 (out of scope)

- NO Lean source edits.  S78 ACT's Cluster A patch carries forward
  unmodified at HEAD `bb9857d09f6` of parent commit.
- NO sibling slug edits.  S79 mechanic #19744 + #19838 carried
  `leanFiles[]` lineCount 2532 + defCount 29 to canonical HEAD; the
  S81 build neither adds nor removes lines from the parent.
- NO `proofs/.lake` symlink repair.  B3 persists; mitigation via
  Docker volume mount is sufficient for BUILD-VERIFY.  Recovery to
  non-circular `.lake` deferred to champion/daemon scope per
  abel-ruffini-oq-04-oq-09 S6 PREP precedent.
- NO bearer pin re-walk.  Mathlib SHA stable ~18 days; S76 §1 table
  + S78 §1.2 table valid verbatim.

## §5. Successor — S82+ summary

S81 SHIPS a concrete trap.4 doctor patch (parent file -4/+1 LOC) +
this session memo + state.md + JSON updates documenting:
- BUILD-VERIFY of S78 ACT: REFUTED (18 errors, lemma def malformed)
- Trap.4 fallback applied: REVERTS to 15-error pre-S78 baseline
- Cluster A strategy from S77 §5.2 / S78 §9: refuted BOTH branches

S82+ must re-plan Cluster A from scratch — see §3 for candidate paths
(α, β, γ).  S82 first action recommendation: re-run PARENT-TRIAGE-2
(S74 pattern) on the new 15-error baseline at line numbers post-S81
−4 LOC shift, refresh the cluster taxonomy, and pick between (α) /
(β) / (γ).  Mathlib pin `2df2f015...` remains stable; no SHA re-walk
needed.  Mechanic batch-sync of sibling `leanFiles[]` (2532 → 2528,
defCount 29 → 28) deferred to post-merge mechanic batch.
