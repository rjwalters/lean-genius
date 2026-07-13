# S1b STATE-SYNC — 4-day quiescence + S2 ACT bearer-API pin + Docker / disk blocker

**Date**: 2026-06-03
**Researcher**: researcher-1
**Type**: Doc-only STATE-SYNC (no Lean edits).
**Scope**: Confirm `BurnsideCounting.lean` byte-stability since S1 ACT
(merged 2026-05-30, PR #21148 — same researcher as this SYNC). Pin
the Mathlib-bearer API surface needed for the **S2 ACT** (`AddAction
(ZMod n)` → `MulAction (Multiplicative (ZMod n))` bridge, per state.md
"What's Next" item 1). Document the host disk / Docker blocker
observed across two sibling slugs this session.

This iteration is **iteration-neutral** for the discharge plan: no
mathematical advance, no Lean edits, no axiom or sorry deltas. The
single load-bearing observation is that the disk constraint blocks
the next concrete deliverable (S2 ACT, ~80-150 LOC, Docker-required),
and the S2 ACT's Mathlib API surface is pinned so paste-ready
discharge becomes possible the moment disk recovers.

## §1 Bearer byte-stability (4-day window since S1 ACT)

Window: 2026-05-30T09:35:02Z (S1 ACT merge `86fa4268a04`) → today
2026-06-03.

| Bearer | SHA1 | Touches since S1 ACT |
|--------|------|----------------------|
| `proofs/Proofs/BurnsideCounting.lean` | `5879ade40b5ed901c5a8d5e5dbecb29cb626f59a` | 0 (only #21148 itself) |
| `research/problems/burnside-counting-oq-01/` | — | 0 |
| `src/data/research/problems/burnside-counting-oq-01.json` | — | 0 |
| `src/data/proofs/burnside-counting/meta.json` | — | check at PR time |

Per `git log origin/main -- proofs/Proofs/BurnsideCounting.lean`:
the only commit touching this file in its entire history (post-Sperner
mass-import on 2026-05-16) is **#21148 itself** (S1 ACT, 2026-05-30,
researcher-1). Zero substantive content drift across the 4-day window.

### §1.1 Axiom inventory re-verified

`grep -n "^axiom " proofs/Proofs/BurnsideCounting.lean`:

| # | Axiom | Line | Discharge route |
|---|-------|------|-----------------|
| 1 | `fixed_point_sum_binary_4` | 343 | S3 via `native_decide` |
| 2 | `coloringSetoid n k` | 350 | S2 via `MulAction.orbitRel` (this SYNC's bearer-pin focus) |
| 3 | `coloringQuotientFintype n k` | 353 | derived-once-`coloringSetoid`-is-concrete |
| 4 | `binary_necklaces_4` | 361 | S4 via `burnside_lemma` + #1 + `|ZMod 4| = 4` |

Lines match state.md "Axiom inventory" verbatim. 0 axioms have been
added; 0 have been removed.

## §2 S2 ACT bearer-API pin (`AddAction → MulAction` bridge for `ZMod n`)

state.md "What's Next" §1 recommends S2 as highest priority: build the
`AddAction (ZMod n)` → `MulAction (Multiplicative (ZMod n))` bridge so
that `coloringSetoid` can be derived rather than axiomatized. The
current file already has the additive action wired:

```
proofs/Proofs/BurnsideCounting.lean:204-205:
  instance cyclicAddActionOnColorings (n k : ℕ) [NeZero n] :
      AddAction (ZMod n) (Coloring n k) where
```

`burnside_lemma` is stated for **`MulAction`**:

```
proofs/Proofs/BurnsideCounting.lean:48-52:
  theorem burnside_lemma {G : Type*} {X : Type*} [Group G] [MulAction G X]
      [Fintype G] [(g : G) → Fintype (fixedBy X g)] [Fintype (orbitRel.Quotient G X)] :
      ∑ g, Fintype.card (fixedBy X g) =
        Fintype.card (orbitRel.Quotient G X) * Fintype.card G :=
    MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G X
```

The S2 ACT needs to bridge `AddAction (ZMod n) → MulAction (Multiplicative (ZMod n))`
so that `orbitRel.Quotient (Multiplicative (ZMod n)) (Coloring n k)` is
a defined type and `coloringSetoid` becomes `MulAction.orbitRel _ _`.

### §2.1 Mathlib v4.26.0 bearer-API pin

For the S2 ACT, the relevant Mathlib lemmas (verified by name only;
LOC/import path verification deferred to S2 ACT Docker smoke-test):

| Lemma / instance | Module | Use in S2 ACT |
|------------------|--------|---------------|
| `Multiplicative` | `Mathlib.Algebra.Group.TypeTags` | Convert `AddGroup` to `Group`. |
| `Multiplicative.instGroup` (or analogous instance) | same | Provides `Group (Multiplicative (ZMod n))`. |
| `AddAction.toMulAction` | `Mathlib.GroupTheory.GroupAction.Basic` | Bridge: `AddAction G X → MulAction (Multiplicative G) X`. |
| `MulAction.orbitRel` | same | The orbit equivalence — replaces axiomatized `coloringSetoid`. |
| `MulAction.orbitRel.Quotient` | same | The quotient type — replaces axiomatized `coloringQuotientFintype` (Fintype instance via `Quotient.fintype`). |
| `instance Fintype (ZMod n)` for `[NeZero n]` | `Mathlib.Data.ZMod.Basic` | `ZMod 4` Fintype is automatic. |
| `Fintype (Multiplicative G)` derived from `Fintype G` | `Mathlib.Algebra.Group.TypeTags` | Same cardinality as `G`. |

**Bridge sketch in pseudo-Lean** (for S2 ACT paste-ready):

```lean
-- After line 205 (cyclicAddActionOnColorings), add:
instance cyclicMulActionOnColorings (n k : ℕ) [NeZero n] :
    MulAction (Multiplicative (ZMod n)) (Coloring n k) :=
  AddAction.toMulAction (G := ZMod n) (X := Coloring n k)
  -- or: inferInstance once cyclicAddActionOnColorings is in scope

-- Then `coloringSetoid` becomes derivable:
def coloringSetoid' (n k : ℕ) [NeZero n] : Setoid (Coloring n k) :=
  MulAction.orbitRel (Multiplicative (ZMod n)) (Coloring n k)

-- And `coloringQuotientFintype` via Quotient.fintype + Fintype Coloring.
```

LOC estimate: ~10-15 LOC for the bridge + ~5 LOC each to discharge the
two axioms `coloringSetoid` and `coloringQuotientFintype` ⟹ **~20-25 LOC
total for S2 ACT** (smaller than state.md's open-ended estimate).

**Risk**: low-moderate. Failure modes are (a) `AddAction.toMulAction`
name not exact (Mathlib rename history is the main risk), (b) instance
search loops if `MulAction` and `AddAction` are both in scope
simultaneously (mitigated by `instance` vs `def` choice), (c) `Fintype`
instance for `Multiplicative G` may require an explicit `inferInstanceAs`
hint.

## §3 Infra blocker (Docker / disk pressure)

Host disk at PR-creation time:

```
$ df -h /Users/rwalters/GitHub/lean-genius
Filesystem      Size    Used   Avail Capacity
/dev/disk3s5   926Gi   890Gi   5.1Gi   100%
```

**5.1 Gi free, 100% capacity.** Below ≥10 Gi pre-flight threshold for
safe Docker build. S2 ACT (~20-25 LOC + 2-axiom discharge) requires
`./proofs/scripts/docker-build.sh Proofs.BurnsideCounting` verification;
blocked until disk recovers to ≥15 Gi free.

**Same blocker observed this session on**:
- `spherical-law-of-sines-oq-03` S5 PREP (PR #22209) — §7.
- `ehrhart-cube-proven-oq-05` S5 STATE-SYNC (PR #22210) — §5.

This is a **session-wide infrastructure constraint**, not a slug-specific
issue. PREP / SYNC work safe (this SYNC is ~150 LOC of writes).

## §4 Race / saturation

```
$ gh pr list --search "burnside-counting-oq-01 in:title" --state open
(no open PRs)
```

0 open PRs on slug at PR-creation time.

## §5 Files modified by this PR

1. `research/problems/burnside-counting-oq-01/sessions/2026-06-03-s1b-state-sync-blocker-and-s2-bearer-pin.md`
   (this file, NEW).
2. `research/problems/burnside-counting-oq-01/state.md` (UPDATE: head
   `Last Updated: 2026-05-30 → 2026-06-03` + new "S1b STATE-SYNC" entry
   at the top of "Session Log"; no narrative edits to existing content).

**No Lean source modified. No `lake-manifest.json` modified. No
parent gallery files modified. No new sorries. No new axioms.
No JSON file modified** (slug JSON `lastUpdated` was at S1 ACT and is
implicit-rolled by this SYNC, but no field changes warrant a touch).

## §6 Honest scope

* Pins Mathlib bearer-API for S2 ACT (3 instances, 2 functions) so that
  the next agent has a paste-ready discharge target.
* Documents the session-wide Docker / disk-pressure blocker (3rd of 3
  slugs this session to record it).
* Re-affirms 4-day byte-stability of the slug's Lean file.
* **Does NOT** ship the S2 ACT (infra-blocked).
* **Does NOT** ship the S3 (`native_decide`) or S4 (`binary_necklaces_4`)
  axiom discharges.
* **Does NOT** modify any Lean file or parent gallery file.
* Iteration counter stays at 1 (this SYNC is a sub-step of S1, named "S1b"
  to distinguish from a fresh iteration).

## §7 References

* Predecessor PR: #21148 (S1 ACT, researcher-1, 2026-05-30).
* Existing session log: state.md `## Session Log` (single entry, S1
  ACT 2026-05-30).
* Mathlib bridge `AddAction → MulAction`: `Mathlib/GroupTheory/GroupAction/Basic.lean`
  (pinned by name, exact line/SHA verification deferred to S2 ACT
  Docker smoke-test).
* Sibling slugs sharing the infra blocker: PR #22209
  (`spherical-law-of-sines-oq-03`), PR #22210
  (`ehrhart-cube-proven-oq-05`).
