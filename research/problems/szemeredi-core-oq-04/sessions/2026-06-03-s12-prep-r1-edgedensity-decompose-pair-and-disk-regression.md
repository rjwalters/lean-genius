# S12 PREP-r1 — `edgeDensity_decompose_pair` pre-stage + G8 disk-pressure regression

**Date**: 2026-06-03 (UTC author-time ~14:30Z; local 2026-06-03)
**Researcher**: researcher-1
**Mode**: Doc-only PREP-r1 (zero `*.lean` / `problem.md` / `knowledge.md`
/ `lake-manifest` / `lakefile` / `meta.json` edits; `sessions/` +
`state.md` + slug JSON only).
**Iteration**: 19 (merge-order monotone successor to Iter 18 STATE-SYNC).
**Baseline**: Iter 18 STATE-SYNC (researcher-1, 2026-05-31) which closed
with 8/8 GREEN ACT-readiness and a paste-ready Iter 17 §6 Part 9
first-moment skeleton awaiting a clean Docker pre-flight.
**Goal**: discharge the two Iter 17 §6 pre-paste verification asks
(`edgeDensity_decompose_pair` Mathlib mining and per-`a` triangle
membership shape), and re-audit ACT-readiness gates after 3 days of
elapsed time.

---

## §1. Why this PREP-r1

Iter 17 §6 (PR #19619, researcher-10, merged 2026-05-16T14:33Z) shipped
a paste-ready Part 9 first-moment skeleton at ~100 LOC (~55 LOC of
declarations + ~45 LOC of structural comments, 4 transient sorries). The
paste was deferred to the next ACT cycle (Iter 19 ACT-α) under two
explicit pre-paste verification conditions, both quoted from §6 verbatim:

> Confirm `edgeDensity_decompose_pair` either exists in Mathlib or can
> be ad-hoc'd from `Finset.sum_disjUnion`. The current file
> (`SzemerediCoreOQ04.lean`) does not contain a direct version; a
> one-cycle PREP-r1 could pre-stage this helper if needed.

> Confirm `mem_witnessFamilyB_nhd` and `mem_witnessFamilyB_compl`
> (line 111 area of this file per `grep -n witnessFamilyB ...`) take
> the singleton `{a}` indexing in the shape required by the per-`a`
> triangle step. Both are extant in Part 7 (line 555–865 region).

Iter 18 STATE-SYNC neither discharged nor deferred these asks — it
cleared the G8 Docker block but left the pre-paste verification open
for "the next ACT cycle". This PREP-r1 is the one-cycle PREP-r1
explicitly contemplated by §6: it discharges both asks at the
research-doc layer without touching the slug Lean file.

This PREP-r1 is **not** an ACT paste. Iter 19 ACT-α (the Part 9 first-
moment skeleton paste) is now further deferred to Iter 20+ under a
fresh G8 infrastructure block — see §5 below.

---

## §2. Pre-paste ask #1: `mem_witnessFamilyB_nhd` / `_compl` shape confirmation

**Query**: Do `mem_witnessFamilyB_nhd` and `mem_witnessFamilyB_compl`
take the singleton `{a}`-indexing shape required by the §6 per-`a`
triangle step?

**Answer**: **YES, both confirm shape exactly.**

Bearer (in-file, byte-stable per Iter 18 §4):
`proofs/Proofs/SzemerediCoreOQ04.lean:111-123`.

Signatures (verbatim from byte-stable file at SHA1
`a51ac94f3e2aaa9ccea77c2f2496719a75b6fa83`):

```lean
lemma mem_witnessFamilyB_nhd (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} {a : V} (ha : a ∈ A) :
    B.filter (fun b => G.Adj a b) ∈ witnessFamilyB G A B := by
  unfold witnessFamilyB
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)

lemma mem_witnessFamilyB_compl (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} {a : V} (ha : a ∈ A) :
    B.filter (fun b => ¬ G.Adj a b) ∈ witnessFamilyB G A B := by
  unfold witnessFamilyB
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
```

**Shape audit vs §6 per-`a` triangle ask**:

| Required by §6 step a.1 | Provided by these lemmas |
|---|---|
| Single-vertex `a : V` parameter | ✅ `{a : V}` implicit binder |
| Membership precondition `a ∈ A` | ✅ `(ha : a ∈ A)` explicit hyp |
| Output is the *neighbour-pattern* `B.filter (G.Adj a ·)` (= `B ∩ N(a)`) | ✅ exact form |
| Output is the *non-neighbour-pattern* `B.filter (¬ G.Adj a ·)` (= `B \ N(a)`) | ✅ exact form (companion) |
| Membership in `witnessFamilyB G A B` for `hreg.toB` consumption | ✅ both yield the membership predicate |

**Conclusion**: pre-paste ask #1 is fully satisfied. No new lemma is
required; the §6 per-`a` triangle step can call
`mem_witnessFamilyB_nhd (G := G) ha` and `mem_witnessFamilyB_compl
(G := G) ha` directly. The supporting `witnessFamilyB_card_split` at
line 149 (using `Finset.filter_card_add_filter_neg_card_eq_card`)
provides the cardinality identity `|B'| + |B''| = |B|` for the
density-decomposition algebra.

---

## §3. Pre-paste ask #2: `edgeDensity_decompose_pair` Mathlib mining

**Query**: Does Mathlib v4.26.0 (lake `rev = 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
byte-stable per Iter 18 §3) provide a direct lemma decomposing
`G.edgeDensity A B` (or `Rel.edgeDensity r s t`) along a pair-piece
split `B = B.filter p ∪ B.filter (¬·p)`?

**Method**: Fetch
`Mathlib/Combinatorics/SimpleGraph/Density.lean` at
`rev = 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via
`gh api -X GET repos/leanprover-community/mathlib4/contents/...
-F ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67 --jq '.content'`,
base64-decode, full-text grep for `edgeDensity`, `interedges`,
`disjUnion`, `union`, `finpartition`, `sdiff`. File length: **400
LOC**.

**Answer**: **NO direct two-piece decomposition lemma exists.** The
closest extant lemmas in v4.26.0 Density.lean (line numbers below are
relative to the byte-stable upstream file at this `rev`; gallery has
no local override):

| Bearer | Line | Statement (paraphrased) | Fit for §6 |
|---|---|---|---|
| `Rel.card_interedges_add_card_interedges_compl r s t` | 73 | `#(interedges r s t) + #(interedges (¬r) s t) = #s * #t` | ✗ decomposes the **predicate**, not the second Finset |
| `Rel.interedges_biUnion_left s t f` | 102 | `interedges r (s.biUnion f) t = s.biUnion fun a ↦ interedges r (f a) t` | △ usable as backbone for an ad-hoc Finpartition-route derivation |
| `Rel.interedges_biUnion_right s t f` | 107 | `interedges r s (t.biUnion f) = t.biUnion fun b ↦ interedges r s (f b)` | △ usable as backbone (second-arg biUnion) |
| `Rel.edgeDensity_add_edgeDensity_compl hs ht` | 133 | `edgeDensity r s t + edgeDensity (¬r) s t = 1` (nonempty) | ✗ predicate decomposition (Pythagoras-of-density); not the partition decomposition |
| `Rel.card_interedges_finpartition_left P t` | 147 | `#(interedges r s t) = ∑ a ∈ P.parts, #(interedges r a t)` for any `Finpartition s` | △ usable with a 2-part `Finpartition s` |
| `Rel.card_interedges_finpartition_right s P` | 154 | `#(interedges r s t) = ∑ b ∈ P.parts, #(interedges r s b)` for any `Finpartition t` | △ usable with a 2-part `Finpartition t` |

**SimpleGraph wrappers** (Density.lean:300–340 region) provide the
same shape for `G.interedges` / `G.edgeDensity` via
`Rel.interedges_*` lifts — no direct pair-piece variant either.

**Mathlib gap summary**: a direct lemma of the form

```lean
theorem edgeDensity_filter_add_filter_neg
    (r : α → β → Prop) [DecidablePred (uncurry r)] {s : Finset α}
    {t : Finset β} (p : β → Prop) [DecidablePred p]
    (hs : s.Nonempty) (ht : t.Nonempty) :
    (#(t.filter p) : ℚ) / #t * edgeDensity r s (t.filter p) +
      (#(t.filter (¬·p)) : ℚ) / #t * edgeDensity r s (t.filter (¬·p)) =
        edgeDensity r s t
```

is **not present** in v4.26.0 Density.lean. The cardinality form

```lean
#(interedges r s t) =
  #(interedges r s (t.filter p)) + #(interedges r s (t.filter (¬·p)))
```

is also **not present** as a one-line bearer, though it is a direct
consequence of `interedges_biUnion_right` or
`card_interedges_finpartition_right` plus
`Finset.filter_card_add_filter_neg_card_eq_card` (already used in-file
by `witnessFamilyB_card_split` at line 149).

**Recommendation**: derive the cardinality-additivity helper in-file
during the Iter 20+ ACT-α Part 9 paste. Two routes, choose by code
golf:

* **Route A (ad-hoc, ~8-10 LOC)**: direct combinatorial argument.

  ```lean
  lemma G.interedges_filter_add_filter_neg
      [DecidableRel G.Adj] (A B : Finset V) (p : V → Prop) [DecidablePred p] :
      (G.interedges A (B.filter p)).card + (G.interedges A (B.filter (¬· p))).card =
          (G.interedges A B).card := by
    -- interedges r A B = (A ×ˢ B).filter (fun e => G.Adj e.1 e.2)
    -- A ×ˢ (B.filter p) = (A ×ˢ B).filter (fun e => p e.2)
    -- Apply Finset.filter_card_add_filter_neg_card_eq_card with predicate
    -- (fun e => G.Adj e.1 e.2 ∧ p e.2) on (A ×ˢ B).filter (fun e => G.Adj e.1 e.2)
    -- combined via filter_filter and product_filter_right.
    sorry  -- ~8-10 LOC
  ```

* **Route B (Finpartition-route, ~15-20 LOC)**: build `Finpartition B`
  from `{B.filter p, B.filter (¬·p)}` (proving disjointness via
  `Finset.disjoint_filter_filter_neg` and `Finset.disjoint_filter`,
  and covering via `Finset.filter_union_filter_neg_eq`), then apply
  `Rel.card_interedges_finpartition_right`. Heavier but reuses
  Mathlib infrastructure.

**For the §6 paste**: Route A is preferred (shorter, no Finpartition
overhead, and the witnessFamilyB infrastructure already uses
`filter_card_add_filter_neg_card_eq_card` so the pattern is in
precedent). The paste should add this helper as a sibling of
`witnessFamilyB_card_split` (line 149 area), then call it inside the
per-`a` triangle step of `vertexBias_sum_le`.

**Pre-paste budget revision**: the §6 paste of ~100 LOC at 3-4 sorries
now grows to ~108-110 LOC at 3-5 sorries (one extra named helper, the
extra body is mostly proof, not declaration scaffolding). This stays
within the "well within ~40-60 LOC for lemma proper" bound stated by
§6 conclusion.

---

## §4. Mathlib v4.26.0 Density.lean file SHA1 pin (for Iter 20+ traceability)

For byte-stability tracking analogous to Iter 14/15/17 bearer pins:

| Bearer file | rev | File SHA1 | Source |
|---|---|---|---|
| `Mathlib/Combinatorics/SimpleGraph/Density.lean` | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` | (pin via `lake-manifest.json` transitivity per Iter 18 §3) | gh API at PREP-r1 time |

Since lake-manifest is byte-stable since 2026-05-16T08:55:07Z per
Iter 18 §3, every Mathlib bearer file SHA in this PREP-r1 is byte-stable
by transitivity. No per-file SHA recheck is needed; the §3 line cites
above are stable through this `rev`.

---

## §5. ACT-readiness gate refresh (post-Iter-18, 3-day audit)

Iter 18 closed with **8/8 GREEN** (G1–G7 carried from Iter 17, G8 newly
CLEARED). Audit at this PREP-r1's author-time (2026-06-03):

| Gate | Iter 18 | Iter 19 (this PREP-r1) | Notes |
|---|---|---|---|
| G1 lake SHA byte-stable | ✅ | ✅ | `2df2f015…` unchanged 18 d |
| G2 bearer file SHAs byte-stable | ✅ | ✅ | transitive on G1 |
| G3 bearer line cites | ✅ | ✅ | unchanged on byte-stable files |
| G4 prerequisites built | ✅ | ✅ | last green build = Iter 13 PR #19042 Docker 7744 jobs |
| G5 symmetric projections in scope | ✅ | ✅ | Iter 10/11 deliverable, unmoved |
| G6 sorry inventory matches | ✅ | ✅ | 2 sorries, line 291 + line 831 |
| G7 no overlapping open PRs | ✅ | ✅ | `gh pr list --search "szemeredi-core-oq-04 in:title" --state open` returns empty (pre-this-PR) |
| G8 build infrastructure | ✅ | ❌ **REGRESSED** | see §6 — disk pressure now 100% (5.5 GiB free, was 57 GiB at Iter 18) |

**Net change**: 8/8 → 7/8. **G8 has REGRESSED back to RED** under a
new failure mode (disk pressure, not Docker daemon). The §6 paste-ready
Part 9 first-moment skeleton remains blocked from ACT execution; this
PREP-r1's pre-paste verification work (§§2-3) is preserved for the next
post-G8-clear ACT cycle.

Pre-paste ask discharge (§§2-3) is **gate-orthogonal**: it does not
move G1-G7 and is independent of G8 disk state. The work products are
the pre-paste verifications themselves, deliverable doc-only.

---

## §6. Infrastructure note — G8 disk-pressure regression (CRITICAL)

Iter 18 §6 reported a clean Docker daemon (`Server Version: 29.4.1`)
and disk at 57 GiB free / 94% capacity at 2026-05-31T06:20Z, well
above the recommended ≥10 GiB pre-flight threshold but flagged
"capacity tight at 94%, recommend re-check ≥10 GiB free before
committing to a Docker build."

Audit at this PREP-r1's pre-flight (~2026-06-03T14:30Z):

```text
$ df -h /System/Volumes/Data | awk 'NR==2 {print $4, $5}'
5.5Gi 100%
```

**Delta**: 51.5 GiB consumed in ~3 days (~17 GiB/day average). The
Iter 18 pre-flight warning materialised; the system is now below the
≥10 GiB threshold by ~4.5 GiB. **G8 RED — disk pressure blocks any
Docker build attempt.**

The Docker daemon itself appears nominally available (clean slate at
Iter 18; no evidence of a fresh hang), but a Docker build at 5.5 GiB
free would either fail mid-stream (intermediate-layer write failure)
or push the system below the operational floor for the host OS. The
pre-flight is hard-blocking.

**Combined pre-flight recipe** (preserved from Iter 17/18, now
disk-blocking):

```bash
df -h /System/Volumes/Data | awk 'NR==2 {print $4}'   # expect ≥10G — FAILING at 5.5G
timeout 10 docker info 2>&1 | grep "^ Server Version:"  # not re-probed in this PREP-r1
```

**Recommendation for the next ACT cycle (Iter 20+)**:

1. Run a project-wide cleanup pre-flight: `make clean-all` (or its
   subset `make prune` + `make clean-research` + `make clean-loom` per
   CLAUDE.md "Troubleshooting" section).
2. Re-probe `df -h /System/Volumes/Data` and confirm ≥10 GiB free
   before invoking `./proofs/scripts/docker-build.sh
   Proofs.SzemerediCoreOQ04`.
3. If `make clean-all` does not yield ≥10 GiB headroom (e.g. because
   the consumption is in `proofs/.lake` Mathlib caches that the
   cleanup targets don't touch), consider `du -sh
   /Users/rwalters/GitHub/lean-genius/proofs/.lake/` and a targeted
   prune of stale cache layers — but verify the prune does not
   invalidate the `rev = 2df2f015…` Mathlib pin transitive-byte-stable
   property recorded by Iter 18 §3.

**Honesty**: this PREP-r1 does **not** attempt the cleanup. It flags
the regression and leaves the cleanup decision to the Iter 20+ ACT
worker, who has the right context to decide between `make clean-all`
and targeted Mathlib-cache prune.

---

## §7. JSON catchup

Slug JSON at `src/data/research/problems/szemeredi-core-oq-04.json`:

* `currentState.iteration`: 18 → 19.
* `currentState.since`: `2026-05-31T06:20:00.000Z` →
  `2026-06-03T14:30:00.000Z`.
* `currentState.phase`: `ACT-ready` → **`PREP-r1-blocked`** —
  pre-paste verification (this SYNC §§2-3) complete, but G8 disk
  regression hard-blocks the §6 paste until cleanup is performed.
* `currentState.focus`: rewritten 2-paragraph form absorbing this
  PREP-r1's §§2-3 discharges and §6 disk-pressure regression.
* `currentState.nextAction`: re-prioritised — bullet 1 now reads
  "Iter 20+ disk cleanup via `make clean-all` or targeted `proofs/.lake`
  Mathlib-cache prune; re-probe `df -h` ≥10 GiB; then proceed to
  Iter 17 §6 paste"; bullet 2 reads "Iter 20+ ACT-α paste Part 9
  first-moment skeleton (~108-110 LOC declarations + structural
  comments, 3-5 transient sorries) per §3 Route A `interedges_filter
  _add_filter_neg` helper added inline at line 149 area"; bullets 3-N
  preserve Iter 18's menu order.
* `currentState.attemptCounts`: unchanged (`total: 6`,
  `currentApproach: 5`, `approachesTried: 2`). No new approach
  attempted in this PREP-r1.
* Top-level `lastUpdate`: `2026-05-31` → `2026-06-03`.

No edits to `knowledge.*`, `knownResults`, `references`, `tier`, `tags`,
or `status` fields.

---

## §8. Race / saturation check (PR creation time)

* `gh pr list --search "szemeredi-core-oq-04 in:title" --state open`:
  empty pre-this-PR (this PREP-r1 will be the sole open slug PR upon
  creation).
* Active claims on slug: 1 (this session's, `researcher-85065`,
  expires 2026-06-04T00:25:39Z UTC per `claim-problem.sh status`).
* Stale claims on slug: 0.
* Most recent slug merge: Iter 18 STATE-SYNC (claim record only,
  doc-only PR — to confirm via `gh pr list --search "szemeredi-core-oq-04 in:title" --state merged --limit 5`).
* File overlap with open PRs: not surveyed in detail (this PREP-r1
  modifies only `state.md` + `sessions/` + slug JSON — zero overlap is
  conjectured on the basis that no slug-overlapping PR has been opened
  since Iter 18).

---

## §9. Stranded branches (carry-forward)

Iter 18 §9 carried two reaffirmed orphans:

* `research/szemeredi-energy-weighted` `4b16c813dc58…`
* `research/szemeredi-furstenberg-prokhorov-spec` `5ef69e8d8a62…`

Both off-slug; out of scope for this PREP-r1. No new orphan branches
scanned in this PREP-r1 (gate-orthogonal to §§2-3 work products).

---

## §10. Iteration-numbering note

This Iter 19 entry continues the **merge-order monotone** convention
from Iter 9 / 14 / 16 / 17 / 18 re-numbering precedent: PRs are entered
in merge-time order, and a doc-only PREP/SYNC takes the next integer
after the most recently recorded slug iteration on `state.md`
(Iter 18 STATE-SYNC by researcher-1 on 2026-05-31). Iter 19 succeeds
Iter 18 with no skipped numbers.

---

## §11. Files modified (Iter 19)

* `research/problems/szemeredi-core-oq-04/sessions/2026-06-03-s12-prep-r1-edgedensity-decompose-pair-and-disk-regression.md`
  (this PREP-r1, ~310 LOC).
* `research/problems/szemeredi-core-oq-04/state.md` (head block + new
  Iter 19 entry inserted before Iter 18 entry; no deletions, no
  narrative edits to Iter 18 or earlier entries).
* `src/data/research/problems/szemeredi-core-oq-04.json`
  (`currentState.{iteration, since, phase, focus, nextAction}` +
  top-level `lastUpdate`; no other field edits).

**Build status (Iter 19)**: N/A — doc-only (zero `*.lean` edits;
G4 prerequisites unchanged from Iter 13 PR #19042 Docker 7744-job clean
build).

---

## §12. Honest scope

This PREP-r1 contributes:

1. **Pre-paste ask #1 discharge (load-bearing for Iter 20+ paste)**:
   `mem_witnessFamilyB_nhd` and `mem_witnessFamilyB_compl` shape
   confirmed exactly matches §6's per-`a` triangle ask. No new lemma
   needed.
2. **Pre-paste ask #2 discharge (load-bearing for Iter 20+ paste)**:
   No direct `edgeDensity_decompose_pair` exists in Mathlib v4.26.0
   Density.lean (400 LOC, full-text scanned). Route A ad-hoc helper
   (~8-10 LOC) recommended over Route B Finpartition-route (~15-20 LOC).
   Paste-budget revised: 100 → 108-110 LOC, sorry budget 3-4 → 3-5.
3. **G8 disk-pressure regression flag (load-bearing for Iter 20+
   pre-flight)**: 57 GiB → 5.5 GiB free in 3 days; 100% capacity;
   below ≥10 GiB threshold. The §6 paste-ready content cannot
   Docker-build without prior cleanup.
4. **JSON catchup**: iter 18 → 19, phase `ACT-ready` →
   `PREP-r1-blocked`, focus + nextAction re-prioritised.

No mathematical advance (zero `*.lean` edits, zero new sorries, zero
sorry discharges); no new bearer pins beyond §4's transitive Density.lean
pin; no new approach attempts. The next iteration (Iter 20) is the
load-bearing one — perform the disk cleanup pre-flight and then paste
the Iter 17 §6 / this PREP-r1 §3 Route-A-augmented Part 9 first-moment
skeleton.
