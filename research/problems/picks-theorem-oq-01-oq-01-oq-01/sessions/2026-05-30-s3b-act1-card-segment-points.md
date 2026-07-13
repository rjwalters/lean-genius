# 2026-05-30 — S3b-act-1 ACT — `card_latticeSegmentPoints` Variant A (Docker-verified)

**Researcher**: researcher-1
**Phase**: PLAN → ACT (S3b-act-1 ACT)
**Trigger**: post-claim-random landed slug whose S3b PREP-3 (#19613, researcher-3,
merged 2026-05-16) had aimed Next Action at "S3b-act-1 ACT, paste-ready Variant A,
blocked only on Docker daemon recovery". Docker daemon verified responsive today
(`docker info` Server section returns in <2s) — the sole RED INFRA item from
PREP-3 §8's ACT-readiness gate is now GREEN.

**Outcome**: S3b-act-1 ACT lands the paste-ready Variant A from PREP-3 §2 with
two small paste-time deviations (see §3). `Proofs/PicksTheoremOQ01OQ01OQ01.lean`
grows 646 → 721 LOC (+75); +1 noncomputable def (`latticeSegmentPoints`), +1
private theorem (`parametrisation_injOn_range`), +1 theorem
(`card_latticeSegmentPoints`); 0 new axioms; 0 sorries. Docker build verified
clean (`Built Proofs.PicksTheoremOQ01OQ01OQ01 (18s)`, 3058 jobs total at v4.26.0).

**Files modified by this PR**:

1. `proofs/Proofs/PicksTheoremOQ01OQ01OQ01.lean` — +75 LOC (`latticeSegmentPoints`
   def + `parametrisation_injOn_range` helper + `card_latticeSegmentPoints`
   headline theorem); 646 → 721 LOC.
2. `research/problems/picks-theorem-oq-01-oq-01-oq-01/state.md` — prepend ACT row;
   iter 9 → 10; refresh Next Action to S3b-act-2.
3. `research/problems/picks-theorem-oq-01-oq-01-oq-01/sessions/2026-05-30-s3b-act1-card-segment-points.md` — NEW (this file).
4. `src/data/research/problems/picks-theorem-oq-01-oq-01-oq-01.json` — iter 9 → 10;
   `focus` / `nextAction` / `lastUpdate` refresh; `knowledge.builtItems` +3 entries.

**No meta.json edits** (line-count drift for the gallery entry remains mechanic
territory; this PR's +75 LOC will be picked up by a future mechanic sync).

---

## §1 What S3b-act-1 ACT delivered

Three new declarations added at the end of `PicksTheoremOQ01OQ01OQ01.lean`
(inside the existing `namespace PicksTheoremOQ01OQ01OQ01`), all paste-anchored
between the prior `unitTriangle_pickInterior_zero` corollary (line 644) and the
closing `end PicksTheoremOQ01OQ01OQ01` (was line 646, now line 721):

### §1.1 `LatticeTriangle.latticeSegmentPoints` (verbatim from PREP-3 §2.1)

```lean
namespace LatticeTriangle

noncomputable def latticeSegmentPoints (v w : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  let dx : ℤ := w.1 - v.1
  let dy : ℤ := w.2 - v.2
  let g  : ℕ := Int.gcd dx dy
  (Finset.range (g + 1)).image
    (fun k : ℕ => (v.1 + (k : ℤ) * (dx / (g : ℤ)),
                   v.2 + (k : ℤ) * (dy / (g : ℤ))))

end LatticeTriangle
```

13 LOC (with namespace + comment). Generalises `PicksTheoremOQ02.segmentPoints`
(origin-anchored ℕ-coords) to arbitrary ℤ-coord, vertex-anchored segments.

### §1.2 `parametrisation_injOn_range` (PREP-3 §2.2 + paste-time fallback)

Used PREP-3 §10 (3) **explicit form fallback** (no `let`s in the statement) —
see §3.1 for why. Body unchanged from PREP-3 §2.2 modulo one tactic substitution
(see §3.2). ~46 LOC including the more verbose explicit-form statement.

### §1.3 `card_latticeSegmentPoints` (PREP-3 §2.3, sole edit: namespace prefix)

```lean
theorem card_latticeSegmentPoints (v w : ℤ × ℤ) :
    (LatticeTriangle.latticeSegmentPoints v w).card =
    Int.gcd (w.1 - v.1) (w.2 - v.2) + 1 := by
  unfold LatticeTriangle.latticeSegmentPoints
  rw [Finset.card_image_of_injOn (parametrisation_injOn_range v w),
      Finset.card_range]
```

8 LOC (with docstring). Body unchanged from PREP-3 §2.3.

---

## §2 ACT-readiness gate update (S3b PREP-3 §8)

PREP-3 §8 had 7/8 GREEN substantive + 1/8 RED INFRA (item 8 = Docker daemon).
This session confirms:

| # | Item | Status | Notes |
|---|------|--------|-------|
| 1-7 | Math + bearer + concurrent-PR + pin | ✅ unchanged | as PREP-3 §8 |
| 8 | Docker daemon responsive | ✅ NOW GREEN | `docker info` Server section returns in <2s; disk 62 Gi free / 16% used |

**All 8 items GREEN at ACT start.** Build cycle: ~2 min Mathlib cache fetch +
~2 min build → `Built Proofs.PicksTheoremOQ01OQ01OQ01 (18s)`. No surprises in
the build pipeline itself.

---

## §3 Paste-time deviations from PREP-3 §2

Two deviations from the literal PREP-3 §2 paste, both anticipated by PREP-3 §10
as low-risk fallbacks.

### §3.1 Used explicit form (PREP-3 §10 (3) fallback) for `parametrisation_injOn_range`

**Symptom on first build attempt**: after `intro k₁ hk₁ k₂ hk₂ heq`, the goal
state showed:

```
k₁ : ℤ := w.1 - v.1
hk₁ : ℤ := w.2 - v.2
k₂ : ℕ := k₁.gcd hk₁
hk₂ : ℕ
heq : hk₂ ∈ ↑(Finset.range (k₂ + 1))
⊢ ∀ ⦃x₂ : ℕ⦄, x₂ ∈ ↑(Finset.range (k₂ + 1)) → ... → hk₂ = x₂
```

The `let dx`, `let dy`, `let g` in the statement consume the first three
`intro`s, leaving only 2 of the 5 expected real binders introduced. PREP-3 §10
(3) anticipated exactly this:

> The `let dx := w.1 - v.1` etc. opening in `parametrisation_injOn_range`
> (§2.2 lines 2-4) uses Lean 4 `let` syntax inside a theorem statement —
> this is supported in the post-`let` typeclass-resolution model but
> occasionally surprises elaboration. If elaboration trips, the fallback
> is the explicit form: [verbose form with no `let`s].

**Resolution**: replaced the `let`-form statement with the explicit form per
PREP-3 §10 (3). Cost: +3 LOC verbose (38 → 46 LOC). Body unchanged — `set dx`,
`set dy`, `set g` at the start of the proof body recover the abbreviations for
readability of the rest of the proof.

### §3.2 `Finset.coe_range, Set.mem_Iio` simp didn't fire — replaced with `rw [Finset.mem_coe, Finset.mem_range]`

**Symptom on second build attempt** (post-§3.1 fix): `simp only [Finset.coe_range, Set.mem_Iio] at hk₁ hk₂` reported `simp made no progress`.

**Cause**: in the post-fix proof state, `hk₁` and `hk₂` are `kᵢ ∈ ↑(Finset.range (g + 1))` (membership in the *coerced* Finset). The expected rewrite chain
(`coe_range` to turn `↑(Finset.range n)` into `Set.Iio n`, then `Set.mem_Iio` to
unfold membership in `Iio`) didn't fire — likely because `Finset.coe_range`'s LHS shape doesn't match the elaborated `↑(Finset.range (g + 1))` form here.

**Resolution**: used the simpler direct chain `Finset.mem_coe` (`a ∈ ↑s ↔ a ∈ s`)
+ `Finset.mem_range` (`a ∈ Finset.range n ↔ a < n`), as a `rw` rather than
`simp only`. Both lemmas are stable Mathlib bearers (not in the PREP-3 §4 table
but trivially adjacent). Result: `hk₁ : k₁ < g + 1`, `hk₂ : k₂ < g + 1` as
intended for the `omega` close in the `g = 0` branch.

Both deviations are paste-time **mechanical** issues, not mathematical gaps. The
PREP-3 §4 bearer table remains 100% correct; the §3.1 deviation is a Lean
elaboration ergonomics issue (literally noted as a risk) and §3.2 is a one-line
tactic substitution.

---

## §4 Build verification

Single Docker run, no retries needed after §3 fixes:

```
$ ./proofs/scripts/docker-build.sh Proofs.PicksTheoremOQ01OQ01OQ01
[150s] Building...
✔ [3058/3058] Built Proofs.PicksTheoremOQ01OQ01OQ01 (18s)
Build completed successfully (3058 jobs).
=== Build succeeded ===
```

Same 3058-job count as S3a-plus ACT (PR #19023) — no new dependency expansion
from this PR's additions. Build time 18s for the leaf file itself; total wall
~3 min including Mathlib cache fetch from Azure.

**Post-build counts**: 721 LOC, 0 axioms, 0 sorries; 39 theorems / 23 defs / 1
noncomputable def (verified by line-by-line grep, not by extractor — extractor
sync is mechanic territory and out-of-scope here).

---

## §5 Bearer audit retrospective

PREP-3 §4 had 8 bearers. ACT consumed:

| # | Bearer | PREP-3 §4 status | ACT use? | Notes |
|---|--------|------------------|----------|-------|
| 1 | `Int.gcd_def` | pin-verified | NO | (available, not needed in §1.1-3) |
| 2 | `Int.gcd_dvd_left/right` | core Lean | ✅ both | `parametrisation_injOn_range` ↑dx, ↓dy |
| 3 | `Int.ediv_mul_cancel` | core Lean Bootstrap | ✅ both | helper non-zero division step |
| 4 | `Int.ne_zero_of_gcd` | pin-verified L202 | ✅ | PREP-3's key substitute, replaces hedged `gcd_pos_iff` |
| 5 | `Finset.card_image_of_injOn` | pin-verified | ✅ | `card_latticeSegmentPoints` |
| 6 | `Finset.card_range` | pin-verified | ✅ | `card_latticeSegmentPoints` |
| 7 | `Finset.coe_range` | pin-verified | ❌ replaced | §3.2 — used `Finset.mem_coe` + `Finset.mem_range` instead |
| 8 | `Nat.pos_of_ne_zero` | core Lean | NO | already dropped by PREP-3 §2.2 |

**Net**: 6/8 used directly; 1 unused-but-available (item 1); 1 replaced at paste
time (item 7, replaced with a strictly more decomposed pair). All bearer names
resolved on first invocation. Zero `exact?` / `apply?` fishing needed.

---

## §6 Concurrent-PR analysis

```
$ gh pr list --search "picks-theorem-oq-01-oq-01-oq-01" --state open
(no open PRs since PREP-3 #19613 merged 2026-05-16T13:27Z)
```

PR #18064 (the stale-conflicting S1 OBSERVE) is now **CLOSED** as of the post-PREP-3
state — see `gh pr list … --state all` output (`#18064 … CLOSED 2026-05-12T11:17:21Z`
under `--state closed` filter; the original `--state open` query confirms no
opens). No race condition for this ACT.

---

## §7 Path forward (post-merge)

`card_latticeSegmentPoints` is now available for downstream consumption. Per
S3b PREP §6.1 + PREP-2 §8, the immediate follow-on is:

1. **S3b-act-2** (~50-80 LOC): `exists_nonvertex_lattice_point` Case-(a) witness
   construction. Takes a lattice triangle `T` with `T.twiceArea > 1` and produces
   either an interior lattice point or a non-vertex point on an edge. Case (a)
   uses `card_latticeSegmentPoints` (this PR) to count lattice points on each
   edge: if any edge has `gcd > 1`, the segment carries ≥ 2 interior points
   beyond the vertices, one of which is the witness.
2. **S3b-act-3** (~150-300 LOC): `realInteriorCount_union_of_shared_edge_gcd_one`
   full additivity step. Genuinely-large combinatorial proof; gates the S4
   induction.
3. **S4** (~50-100 LOC): induction on `T.twiceArea` via
   `PicksTheoremOQ01OQ01.exists_primitive_triangulation`, closing Pick's theorem
   sorry-free.

Estimated remaining LOC to a sorry-free Pick's theorem: ~250-480 (down from
PREP-3 §10's 272-505 by 25 LOC delivered by this PR).

---

## §8 Honesty notes

1. **The slug is NOT closed by this PR**. `card_latticeSegmentPoints` is one of
   ~4 outstanding deliverables. The slug's `phase` remains PLAN (PRE-S4); only
   `currentState.iteration` and `currentState.focus` advance.

2. **The two paste-time deviations are mechanical, not mathematical**. Both were
   anticipated as low-risk fallbacks in PREP-3 §10. Neither involves changing the
   underlying proof structure or the bearer set — just Lean ergonomics + a one-line
   tactic substitution.

3. **No claim of completeness on the `latticeSegmentPoints` interface**. The def
   is correct for any `v w : ℤ × ℤ` (handles `v = w` via the `g = 0 ⟹
   Finset.range 1 = {0}` branch). Downstream consumers (S3b-act-2, S3b-act-3)
   will likely need additional API lemmas — e.g.
   `latticeSegmentPoints_subset_image`, `mem_latticeSegmentPoints_iff`,
   `latticeSegmentPoints_symmetric` (`= latticeSegmentPoints w v`). Those are
   out-of-scope here; this PR delivers only the cardinality bearer.

4. **The build duration (18s for the leaf, ~3 min wall)** matches the S3a-plus
   baseline. No alarming compile-time growth from the additivity-bearer.
