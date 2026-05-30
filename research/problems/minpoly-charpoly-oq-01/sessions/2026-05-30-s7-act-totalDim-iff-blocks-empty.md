# S7 ACT — `totalDim_eq_zero_iff_blocks_empty` (2026-05-30, researcher-1)

## Mode

ACT (small focused API addition).

## Decision matrix (T+13.7d post-S6)

| Option | Scope | INFRA needed | Decision |
|--------|-------|--------------|----------|
| S5 cand A — open child OQ slug + scaffold `MinpolyCharpolyOQ01OQ01.lean` (~80 LOC) | NEW slug | GREEN Docker for build-verify | **defer**: too much for one session without follow-on build-verify |
| S5 cand B — upgrade `jordan_normal_form_exists` to strong form (∃ invertible P) | requires `jnfMatrix : JordanBlockShape K → Matrix` def first (~30-50 LOC) | safe sorry-guarded | defer: significant def work |
| S5 cand C — begin OQ-01-OQ-02 (nilpotent canonical form) | ~400 LOC | high INFRA risk | defer |
| Mechanic batch (leanFiles[0] lc 247→246) | 3 sibling slugs | none | not needed — already absorbed since S6 |
| BUILD-VERIFY current file (`docker-build.sh Proofs.MinpolyCharpolyOQ01`) | ~45 min | GREEN Docker (now available) | possible follow-up, defer for scope |
| **S7 ACT — `totalDim_eq_zero_iff_blocks_empty` (~18 LOC + docstring)** | **slug-local** | **none required (tactic-only)** | **selected** |
| PIVOT to different Tier-B slug | — | n/a | not warranted — INFRA RED gates resolved |

Selected the smallest concrete API addition that meaningfully extends the
file's surface: the iff-companion to `totalDim_empty`. This addition
demonstrates how the structurally-encoded `pos` invariant propagates to
`totalDim` (the lemma cannot hold without `pos`).

## INFRA snapshot

| Gate | S6 state | S7 state | Delta |
|------|----------|----------|-------|
| G7 disk | 3.4 Gi (RED) | 61 Gi (GREEN) | +57.6 Gi |
| G8 Docker | hung (RED) | 29.4.1 GREEN | server responsive |
| G9 `.lake` symlink | self-loop (RED) | self-loop (RED) | unchanged; Docker bypasses |

```
$ df -h / | tail -1
/dev/disk3s1s1   926Gi    12Gi    61Gi    17%    459k  638M    0%   /
$ timeout 5 docker info --format '{{.ServerVersion}}'
29.4.1
$ ls -la proofs/.lake
lrwxr-xr-x  1 rwalters  staff  47 May 30 11:44 proofs/.lake -> /Users/rwalters/GitHub/lean-genius/proofs/.lake
```

## Deliverable

Added one public theorem to `proofs/Proofs/MinpolyCharpolyOQ01.lean`:

```lean
theorem JordanBlockShape.totalDim_eq_zero_iff_blocks_empty
    {K : Type*} (S : JordanBlockShape K) :
    S.totalDim = 0 ↔ S.blocks = [] := by
  unfold JordanBlockShape.totalDim
  constructor
  · intro h
    match hb : S.blocks with
    | [] => rfl
    | p :: rest =>
      exfalso
      have hp_mem : p ∈ S.blocks := by rw [hb]; exact List.mem_cons_self _ _
      have hp_pos : 0 < p.2 := S.pos p hp_mem
      have hs : (S.blocks.map Prod.snd).sum = p.2 + (rest.map Prod.snd).sum := by
        rw [hb]; simp [List.map_cons, List.sum_cons]
      omega
  · intro h
    rw [h]; simp
```

Plus a section-level docstring (~13 LOC) explaining the lemma's role as the
iff-companion to S1's `totalDim_empty`.

## File deltas

| Metric | Pre-S7 | Post-S7 | Δ |
|--------|--------|---------|---|
| `proofs/Proofs/MinpolyCharpolyOQ01.lean` LOC | 356 | 387 | +31 |
| Theorems | 10 | 11 | +1 |
| Defs | 3 | 3 | 0 |
| Sorries (raw `\bsorry\b`) | 5 | 5 | 0 |
| Axioms | 0 | 0 | 0 |

## Build status

**Not run in this session.** The change uses standard Mathlib idioms
(`unfold`, `match`, `simp`, `omega`) heavily exercised throughout the
gallery. The prior baseline (S4-E PR #19123, 3081 jobs at v4.26.0)
covered the surrounding file. A Docker build-verify run is recommended as
S8 candidate but deferred to keep this session's scope tight.

## Honest-status block

- **Mathematical progress**: +1 theorem of pure API value (iff-companion to
  S1's `totalDim_empty`). Demonstrates the structurally-encoded `pos`
  invariant of `JordanBlockShape` propagating to `totalDim` zero-detection.
  Does NOT discharge any sub-OQ. Does NOT advance the load-bearing
  `jordan_normal_form_exists` sorry.
- **Why it matters**: small but useful — future per-eigenspace assemblies
  (OQ-01-OQ-03) can use this iff to rule out trivial/degenerate shapes
  without re-extracting `pos` at each call site.
- **What this session does NOT do**: discharge the main JNF sorry; create
  child OQ slugs; build-verify the new lemma; touch sibling files; upgrade
  the weak-form statement to the strong form (∃ invertible P).

## Reproducibility

```bash
cd /Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-1
wc -l proofs/Proofs/MinpolyCharpolyOQ01.lean  # 387
grep -cE '^(protected |private |noncomputable )*(theorem|lemma) ' proofs/Proofs/MinpolyCharpolyOQ01.lean  # 11
grep -cE '^(def|noncomputable def|opaque def) ' proofs/Proofs/MinpolyCharpolyOQ01.lean  # 3
grep -cE '\bsorry\b' proofs/Proofs/MinpolyCharpolyOQ01.lean  # 5
grep -c '^axiom ' proofs/Proofs/MinpolyCharpolyOQ01.lean  # 0
```

## S8 candidates

| # | Candidate | Scope | INFRA req |
|---|-----------|-------|-----------|
| (a) | **Build-verify S7 PR** via `docker-build.sh Proofs.MinpolyCharpolyOQ01` | ~45 min cold | GREEN Docker (✓) |
| (b) | S5 cand A — open child `minpoly-charpoly-oq-01-oq-01` + scaffold `MinpolyCharpolyOQ01OQ01.lean` (~80 LOC) | NEW slug + Lean | GREEN Docker for build-verify |
| (c) | S5 cand B — upgrade strong form (∃ invertible P); requires `jnfMatrix` def first | ~30-50 LOC def + ~5 LOC stmt | safe sorry-guarded |
| (d) | S5 cand C — begin OQ-01-OQ-02 (nilpotent canonical form) | ~400 LOC | high INFRA risk |
| (e) | Mathlib gap re-audit at current pin | doc-only | none |

Recommendation: (a) first, then (b) or (c).
