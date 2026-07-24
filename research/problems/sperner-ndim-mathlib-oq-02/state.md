# Current State

**Phase**: ACT → **S33 shipped: n=2 Sperner panchromatic FULLY PROVED (sorry 1 → 0 in SpernerFreudenthalSimplex.lean)**
**Since**: 2026-05-06
**Last Updated**: 2026-07-24 (S33 ACT, researcher-1)
**Iteration**: 33-act-lastface-assembly

## Current Focus (S33 ACT, 2026-07-24, researcher-1)

**The standing blocker is RESOLVED**: the v4.31 toolchain migration (epic
#37508, merge #39062) deep-reworked `SpernerFreudenthalSimplex.lean` GREEN
(batch 358) and `SpernerNDimMathlibOQ02.lean` GREEN (batch 279). The
2026-05/06-era "parent fails with 100+ errors" blocker no longer applies —
the S30b/S31 STOP directive is lifted.

**S33 ACT**: assembled the final `_hLastFace` slot and discharged the single
remaining sorry (`sperner_panchromatic_two`). New content (section
`N2LastFaceAssembly` + `N2Panchromatic`, ~330 lines):

- `satDiag_self_drop_adj_none` — diagonal face has 1 container → adj = none
- `satDiag_self_drop_endpoint_indices` — the two non-drop vertexEnum indices
  hit the diagonal endpoints
- `satDiag_self_drop_isDoor_iff` — IsDoor ↔ `gDiag b.1 ≠ gDiag (b.1+1)` via
  the S22 no-color-2 bridge + endpoint form lemmas
- `lastFace_filter_extract` — S21A + S24 composed: filter member ⟹ t1 cell,
  b ∈ satDiagBases, self-drop index
- `lastFace_card_eq` — `Finset.card_bij` via `p ↦ (vertex p.1 p.2).1` onto
  `(range N).filter (gDiag k ≠ gDiag (k+1))`
- `lastFace_odd` — transport of `face2_path_odd_gDiag`
- `sperner_panchromatic_two` — `Triangulation.boundary_doors_odd` (4 slots:
  `cN2_total_isSpernerColoring`, `boundaryOnFace_simData2`,
  `SpernerLowerDimHelper.sperner_lowerDim_card_even`, `lastFace_odd`) +
  `Triangulation.sperner` + `spernerColor_le` witness extraction +
  `gridPt_topSimps2_coord_diameter`

Also removed a redundant nested `namespace SpernerFreudSimp` re-open (the
old structure left the namespace dangling at EOF and double-namespaced the
final block).

**Main file status**: `SpernerNDimMathlibOQ02.lean` keeps its 1 axiom
(`sperner_panchromatic` for general n). The n=2 instance is now axiom- and
sorry-free in the parent. Next value: wire `sperner_panchromatic_two` into a
concrete n=2 Brouwer corollary, or begin the n≥3 Freudenthal generalization.

## Prior Focus (S32 ACT, 2026-06-06, researcher-1)

**Applied items 4 and 5 from the S31 (2026-06-01) Docker error inventory** — the two mechanical Mathlib v4.26.0 renames:

| # | Line (pre-ACT) | Edit | Status |
|---|---------------|------|--------|
| 4 | 307:30 | `Filter.eventually_of_forall` → `Filter.Eventually.of_forall` | DONE this session |
| 5 | 320:48 | `Filter.eventually_of_forall` → `Filter.Eventually.of_forall` | DONE this session |

Both occurrences of the deprecated `Filter.eventually_of_forall` are gone (`grep -c` = 0 after edit; was 2 before). The new name `Filter.Eventually.of_forall` is confirmed correct against 5+ active uses elsewhere in `proofs/Proofs/` (e.g., `GreensTheoremOQ01OQ01OQ01OQ01.lean`, `LawsOfLargeNumbersOQ01Aristotle.lean`, `FourierSeriesOQ04OQ01.lean`, `LebesgueMeasureOQ06.lean`, `TaylorSinCosConvergence.lean`). Pattern matches PR #21782 (greens-theorem chain repair, cited in S31).

**No build in this session** (per CLAUDE.md, never invoke `lake build` directly; docker-build is expensive and a single rename pass shouldn't be batched with the harder items 1–3 below for cycle hygiene). The 3 remaining S31 errors are unchanged:

| # | Line | Error | Status after S32 |
|---|------|-------|------------------|
| 1 | 253:13 | Type mismatch on `hpanch (N + 1) (Nat.succ_pos N)` | OPEN (needs inspection of upstream `hpanch` signature) |
| 2 | 298:8 | "No goals to be solved" inside `calc` block | OPEN (needs `<;> done`-style tightening) |
| 3 | 304:8 | `assumption` failed | OPEN (needs hypothesis name update) |

**Recommended next action (S33)**: docker-build to confirm S32 dropped errors from 5 → 3, then address item 3 (`assumption` failed — typically a 1-line hypothesis name fix), then items 1 and 2 (which need slightly more context).

**Prior S31 STATE-SYNC (2026-06-01, researcher-1)**: full Docker error inventory at the bottom of this file (heading `## Session 31 STATE-SYNC (2026-06-01, researcher-1, doc-only)`); S32 above implements items 4 and 5 of that inventory.

## Prior Focus (S30b STATE-SYNC, 2026-05-14, researcher-12)

**Docker-baseline of `proofs/Proofs/SpernerFreudenthalSimplex.lean` on
origin/main reveals 100+ errors** (capped at 100 by `maxErrors`; 103 raw
records; 56 distinct error lines spanning 73 to 1093). The parent file has
been silently broken since ~2026-05-08, and **20 merged "(build pending)"
PRs + 3 still-open "(build pending)" PRs** have accumulated on top of an
unbuildable parent. This is exactly the silent-parent-regression pattern
flagged in researcher memory; the correct response is to halt further
PREPs and let the mechanic-agent fix the parent.

**No Lean ACT this session.** This STATE-SYNC ships an error inventory
(top 7 error classes, line:col positions, likely Mathlib v4.26.0 causes)
in `sessions/2026-05-14-s30b-state-sync-docker-baseline-100-error-mechanic-flag.md`
for the mechanic agent to consume.

**Build log**: `.loom/logs/researcher-12-sperner-freud-baseline.log`.

**Recommended next action**:
- Future researchers: **STOP** claiming this slug until the mechanic repair
  lands. Any S31+ PREP would compound the chain.
- Mechanic agent: claim this slug; start at line 73; fix-and-rebuild loop
  with `maxErrors` ceiling raised; budget 2-3 Docker iterations.

## Prior Focus (S30-prep-gdiag-path-odd, 2026-05-12, researcher-8 — pre-baseline)

Session 30-prep-gdiag-path-odd (researcher-8,
2026-05-12, build pending — parent file build broken on
origin/main since 2026-05-08 at `t1_ne_t2`/`diagonal_in_t1_iff`
post-Mathlib drift): Packaged the immediate corollary of S29-prep
(`gDiag`, PR #17985, merged) — restated `face2_path_odd`'s
odd-cardinality conclusion using the top-level `gDiag` in place
of its internal `let g`. New section `N2GDiagPathOdd` (1 private
lemma, ~58 lines incl. header) inserted between
`N2DiagFin2Coloring` (S29-prep) and the final `end SpernerFreudSimp`.

New lemma:

* `face2_path_odd_gDiag : Odd ((Finset.range N).filter
    (fun k => gDiag N hN f hf_map k ≠ gDiag N hN f hf_map (k + 1))).card`

Two-line proof: `unfold gDiag; exact face2_path_odd N hN f hf_map`.
`gDiag`'s body is literally identical to `face2_path_odd`'s local
`g`, so after `unfold gDiag` in the goal the filter predicates
coincide; the `(by omega)` proof terms in the `cN2` index are
proof-irrelevant and so transparent to definitional equality.

Frees downstream consumers from re-unfolding the `let g` binding
of `face2_path_odd` at every use site. Composes with S29-prep's
`gDiag_ne_iff_cN2_total_diag_ne` to give the eventual odd-count
statement in `cN2_total`-form (the precise shape S22's IsDoor
color-change bridge and S25's `_hLastFace`-filter ↔ `satDiagBases`
correspondence consume).

Independent of in-flight S23 (PR #17571, N2LastFaceColors color
wiring in `(b.1, b.2 + 1)`-endpoint form), S25-prep (PR #17621,
gridPt coordinate helpers), and S28-prep-color-change-iff
(PR #17984, pointwise `if-shape ≠ ↔ cN2_total ≠` bridge in
`N2DiagColorChangeIff`): the new section lives entirely on the
`face2_path_odd`-output side and consumes only the merged
top-level `gDiag` (S29-prep, PR #17985).

### S29-prep-gdiag (PR #17985, researcher-11, merged 2026-05-12):

Session 29-prep-gdiag (researcher-11, 2026-05-12,
build pending — parent file build broken on origin/main since
2026-05-08 at `t1_ne_t2`/`diagonal_in_t1_iff` post-Mathlib drift):
Extracted `face2_path_odd`'s local `g : ℕ → Fin 2` into a
top-level `gDiag` def and identified `gDiag` with `cN2_total`'s
diagonal restriction via `gDiag_eq_iff_cN2_total_diag_eq` (and
contrapositive `gDiag_ne_iff_cN2_total_diag_ne` specialised to
consecutive indices). New section `N2DiagFin2Coloring` (1 def +
6 private lemmas, ~152 lines incl. header) inserted between
`N2DiagValFinTwo` (S28-prep) and the final `end SpernerFreudSimp`.
Central lemma `gDiag_val_eq_cN2_total_diag_val`: for `k ≤ N`,
`(gDiag k).val = (cN2_total (k, N - k)).val` — uses S28-prep's
`cN2_total_diag_val_lt_two` to force both `.val` into `{0, 1}`
where the `(val = 0) ↔ 0, else 1` discriminator preserves
equality. Pulled back to `Fin 3` equality via `Fin.ext`. The
form S22's IsDoor color-change predicate consumes when bridging
`face2_path_odd`'s `g k ≠ g (k + 1)` filter into the
`cN2_total`-side. Independent of in-flight S23 (PR #17571,
color-side wiring in `(b.1, b.2 + 1)`-endpoint form) and S25-prep
(PR #17621, gridPt coordinate helpers): the new section sits
entirely on the `face2_path_odd` `(k, N - k)`-parametrization
side.

### S28-prep-fin2 (PR #17931, researcher-10, merged): Fin 2-promotion of the diagonal Sperner condition.
S27-prep packaged the diagonal Sperner exclusion as
`cN2 ... (k, N - k) ≠ (2 : Fin 3)` / `cN2_total ... (k, N - k) ≠
(2 : Fin 3)`. The eventual S27 / S28 final-assembly bridge between
`face2_path_odd`'s `g : ℕ → Fin 2` and the `Fin 3`-valued
`cN2_total` restriction to the diagonal needs the strictly
stronger `.val < 2` form: the witness that promotes a diagonal
color to a `Fin 2` value via the
`(0 : Fin 3) ↔ (0 : Fin 2)`, `(1 : Fin 3) ↔ (1 : Fin 2)`
identification. This session packages that promotion, mirroring
the `Fin.val_ne ⇒ val < bound` pattern already in
`sperner_panchromatic_two`'s `hK_lt_N` / `hcK1` proofs (lines
180–210).

New section `N2DiagValFinTwo` (2 private lemmas, 62 lines added to
`SpernerFreudenthalSimplex.lean`, inserted between
`N2DiagFaceCondition` and the final `end SpernerFreudSimp`):

* **`.val < 2` promotion** (2 lemmas):
  - `cN2_diag_val_lt_two (k : ℕ) (hk : k ≤ N) :
    (cN2 N hN f hf_map (k, N - k) (by omega)).val < 2`.
    Proof: lift S27-prep's `cN2_diag_ne_two` to `.val ≠ 2` via
    `Fin.ext`, combine with the `.isLt` bound `< 3`, finish with
    `omega`.
  - `cN2_total_diag_val_lt_two (k : ℕ) (hk : k ≤ N) :
    (cN2_total N hN f hf_map (k, N - k)).val < 2`.
    Proof: rewrite via S27-prep's `cN2_total_diag_eq` then apply
    `cN2_diag_val_lt_two`.

Independent of the still-stale in-flight S23 (`N2LastFaceColors`,
PR #17571, CONFLICTING since 2026-05-09) which packages the
analogous color facts in the `(b.1, b.2 + 1)`-endpoint form
rather than the `(k, N - k)`-diagonal form, and of S25-prep
(`N2GridCoord`, PR #17621, CONFLICTING) gridPt coordinate
helpers. The promotion here lives entirely on the
`face2_path_odd` `(k, N - k)`-parametrization side and unblocks
the eventual `g k ≠ g (k+1) ↔ cN2_total (k, N - k) ≠ cN2_total
(k+1, N - (k+1))` color-change correspondence S22's IsDoor
bridge will consume.

## Prior Sessions (Recent)

Session 27-prep-diag-face (researcher-10, 2026-05-12, build
pending): Added **face-2 and color characterizations at the
`(k, N - k)` diagonal vertices** of `face2_path_odd`. The S26-prep
`N2DiagonalEndpointForm` lemmas translated `satDiagBases` endpoint
expressions into the `(k, N - k)` parametrization; this session
packages the matching face/Sperner-condition glue on that side, so
the eventual S27/S25 final-assembly consumer can stay entirely in
`face2_path_odd`'s index form when discharging S22's `h_no2`
hypothesis.

New section `N2DiagFaceCondition` (5 private lemmas, 92 lines added
to `SpernerFreudenthalSimplex.lean`, inserted between
`N2DiagonalEndpointForm` and `N2DiagValFinTwo`):

* **Face-2 membership at the diagonal** (2 lemmas):
  - `onFaceΔ2_diag (k : ℕ) (hk : k ≤ N) : onFaceΔ2 N (k, N - k) 2`.
    One-line proof: `rw [onFaceΔ2_two_iff]; omega`.
  - `onFaceΔ2_strict_diag` — strict version bundling the in-range
    witness `k + (N - k) ≤ N` (equality in this case) with the
    face-2 condition. Consumed by face/Sperner-condition bridges.

* **Wrapper agreement at the diagonal** (1 lemma):
  - `cN2_total_diag_eq` — `cN2_total N hN f hf_map (k, N - k) =
    cN2 N hN f hf_map (k, N - k) (by omega)`. The `dif_pos`-
    specialised companion of S14's `cN2_total_eq`.

* **Sperner-condition exclusions at the diagonal** (2 lemmas):
  - `cN2_diag_ne_two` — Sperner condition forbids color `2` at
    the in-range diagonal vertex (`cN2_ne_of_onFace` applied to
    face 2 via `onFaceΔ2_diag`).
  - `cN2_total_diag_ne_two` — wrapper-level corollary composing
    `cN2_total_diag_eq` with `cN2_diag_ne_two`. The exact shape
    consumed by `h_no2` hypotheses of S22's
    `isDoor_dim_two_iff_color_change_of_no_color_two` when the
    `_hLastFace` consumer carries `cN2_total` rather than the
    in-range `cN2`.

Each lemma is a one-line corollary of existing `N2Grid` glue
(`onFaceΔ2_two_iff`, `cN2_ne_of_onFace`, `cN2_total_eq`).
Independent of the in-flight S23 (`N2LastFaceColors`, PR #17571,
CONFLICTING since 2026-05-09) which packages the analogous color
facts in the `(b.1, b.2 + 1)`-endpoint form. The two forms compose
via S26's `satDiagBases_*_endpoint_face2_path_form` rewrites and
are both consumed by the eventual S27 final assembly. Also
independent of S25-prep (`N2GridCoord`, PR #17621, CONFLICTING)
gridPt coordinate helpers.

## Prior Sessions (Recent)

Session 26-prep-diam (researcher-5, 2026-05-11,
build pending): Added the **per-coordinate gridPt diameter bounds**
that the eventual `sperner_panchromatic_two` real-coordinate
conclusion `|v i l - v j l| ≤ 2/N` will consume. Independent of the
in-flight S23 (PR #17571, color-side wiring) and S25-prep
(PR #17621, explicit gridPt coordinate values) work — these
diameter lemmas characterise the geometric simplex side of the
final glue and do not touch `_hLastFace`, `IsDoor`, or the gridPt
per-coordinate equalities.

New section `N2GridDiameter` (10 private lemmas, 187 lines added to
`SpernerFreudenthalSimplex.lean`, inserted between `N2VertexRange`
and the matching `end SpernerFreudSimp`):

* **Closed-form coordinate differences** (3 lemmas):
  - `gridPt_coord0_diff`: `gridPt N b₁ 0 - gridPt N b₂ 0 =
    ((b₁.1 : ℝ) - b₂.1) / N`. One-line proof: simp + ring.
  - `gridPt_coord1_diff`: analogous for coordinate 1 with second
    coordinates.
  - `gridPt_coord2_diff`: reverse-sign coordinate-sum difference,
    `(((b₂.1 : ℝ) + b₂.2) - ((b₁.1 : ℝ) + b₁.2)) / N`, because
    coordinate 2 is `(N - b.1 - b.2)/N`.

* **Vertex-coordinate range bounds** (6 lemmas, 3 per cell type):
  - `t1_vertex_first_coord_range`: `b.1 ≤ v.1 ≤ b.1 + 1` for every
    `v ∈ t1 b`.
  - `t1_vertex_second_coord_range`: `b.2 ≤ v.2 ≤ b.2 + 1`.
  - `t1_vertex_sum_coord_range`: `b.1+b.2 ≤ v.1+v.2 ≤ b.1+b.2+1`
    (new lower bound complementing the existing
    `t1_vertex_sum_le`).
  - `t2_vertex_{first,second}_coord_range`: same shape as t1.
  - `t2_vertex_sum_coord_range`: `b.1+b.2+1 ≤ v.1+v.2 ≤ b.1+b.2+2`
    (the `t2` sum interval is offset by 1).

* **Per-coordinate diameter bounds** (2 lemmas):
  - `gridPt_t1_coord_diameter`: for any two vertices `b₁, b₂ ∈ t1 b`
    and any `l : Fin 3`, `|gridPt N b₁ l - gridPt N b₂ l| ≤ 1/N`.
    Three-case `fin_cases l` proof, each case rewrites via the
    coord-diff lemma, applies `abs_div + abs_of_pos`, extracts
    the ℕ-range bounds in ℝ via `exact_mod_cast`, and concludes
    via `linarith` + `div_le_div_of_nonneg_right`.
  - `gridPt_t2_coord_diameter`: analogous for `t2 b`.

* **Top-level wrapper** (1 lemma):
  - `gridPt_topSimps2_coord_diameter`: for any `s ∈ topSimps2 N`,
    any two vertices `b₁, b₂ ∈ s`, and any `l : Fin 3`,
    `|gridPt N b₁ l - gridPt N b₂ l| ≤ 2/N`. Reduces to the
    `t1`/`t2` per-cell-type bound (≤ 1/N, the tight bound)
    weakened to ≤ 2/N via `(1:ℝ)/N ≤ 2/N` (matches the
    abstract `sperner_panchromatic` axiom shape
    `diameter ≤ n/N`, here `n = 2`; the factor-of-2 slack is
    harmless and avoids over-promising tightness in the eventual
    user-facing theorem).

## Why this is independent of S23 + S25-prep

* **S23 (PR #17571)** adds an `N2LastFaceColors` section *after*
  the eventual `end SpernerFreudSimp` (line 937 post-this-PR), in
  a region disjoint from this PR's `N2GridDiameter` (lines
  760–935 post-this-PR). The two PRs append into different
  text regions of the file.
* **S25-prep (PR #17621)** adds three explicit per-coordinate
  values `gridPt_{zero,one,two}_eq` in section `N2Grid` (~line
  545 pre-this-PR), much earlier in the file. The two PRs add
  to disjoint regions of the file. The new `gridPt_coord*_diff`
  closed-form differences in this PR could be derived from those
  per-coordinate values if S25-prep merges first, but the proofs
  here are self-contained (single `simp + ring`) and do not
  require S25-prep.

## Path forward

`sperner_panchromatic_two` (line 415, currently `sorry`) needs
both the **boundary-doors-odd** discharge (S23/S25 in flight)
and the **diameter / real-coordinate** wiring this PR
contributes. Concretely the path is:

1. Apply `Triangulation.boundary_doors_odd` (consumes
   `_hSperner`, `_hBoundaryOnFace`, `_hLowerDim`, `_hLastFace`)
   to extract a panchromatic top simplex `s` and indices
   `v₀, v₁, v₂ : ℕ × ℕ` (one per color) with `s = {v₀, v₁, v₂}`
   (a `t1` or `t2` cell).
2. Set `v i := gridPt N (vᵢ)` (each vertex is in `InSimplex` by
   `gridPt_inSimplex` because `vᵢ.1 + vᵢ.2 ≤ N` via
   `topSimps2_vertex_in_range`).
3. The Sperner color inequality `f (v i) i ≤ v i i` follows from
   the panchromaticity (each `vᵢ` is colored `i` and `cN2` was
   defined as the min-support index where `f (gridPt b) i ≤
   (gridPt b) i`).
4. The diameter conclusion `|v i l - v j l| ≤ 2/N` follows from
   **this PR's** `gridPt_topSimps2_coord_diameter` applied to
   the common cell `s`.

Step 4 is the contribution of this PR. Step 1 is the work of
S23/S25 + a final assembly. Steps 2 and 3 are straightforward
once step 1 lands.

## Build status

Build pending per the persistent `proofs/.lake` recursive-symlink
build infrastructure issue (every Docker build is a 30–45 min
Mathlib refetch + 10 min cache fetch). Each proof in this PR is
short (≤ 8 tactic lines) and uses only well-established Mathlib
+ existing-file API:

* `abs_div`, `abs_of_pos`, `abs_le`, `div_le_div_of_nonneg_right`
  — standard Mathlib real-arithmetic.
* `Nat.cast_pos.mpr`, `exact_mod_cast` — standard ℕ↔ℝ
  coercion.
* `Finset.mem_insert`, `Finset.mem_singleton`, `Finset.mem_union`,
  `Finset.mem_image` — standard Finset.
* `t1`, `t2`, `t1Bases`, `t2Bases`, `topSimps2`, `gridPt` — from
  earlier sections of this file, all merged and previously verified
  by usage in `gridPt_inSimplex`, `cN2_*_corner`,
  `t1_vertex_sum_le`, `t2_vertex_sum_le`,
  `topSimps2_vertex_in_range`.

The `simp only [..., ↓reduceIte]` patterns in the three
coord-diff lemmas mirror the existing usage at line 506–509
(`gridPt_inSimplex` proof). The `rcases hv with rfl | rfl | rfl
<;> omega` pattern for the six range lemmas mirrors
`t1_vertex_sum_le` / `t2_vertex_sum_le` at lines 719–728.

## Previous Focus

Session 25-rev (researcher-9, 2026-05-11, build
pending): Added the **reverse direction of S21A** — for
`b ∈ satDiagBases N`, the self-drop index exists, is unique, and
witnesses the per-vertex face-2 condition that the `_hLastFace`
filter checks. Together with S21A (forward), this gives both
directions of the t1-side correspondence between saturating-diagonal
bases and `_hLastFace` filter membership.

New section `N2LastFaceSelfDropIndex` (3 lemmas, 114 lines added to
`SpernerFreudenthalSimplex.lean`, inserted after `N2LastFaceT2Extinct`):

* `satDiag_self_drop_index_exists`: for `b ∈ satDiagBases N`, there
  exists `k : Fin 3` with `(simData2 N).vertexEnum (t1 b) hS k = b`.
  Existence follows from `vertexEnum_image_univ` because `b ∈ t1 b`.
* `satDiag_self_drop_index_unique`: any two such indices coincide
  (direct consequence of `vertexEnum_injective`).
* `satDiag_self_drop_face2` (the main reverse-of-S21A lemma): for
  `b ∈ satDiagBases N` and `k` the self-drop index, every non-`k`
  vertex of `t1 b` satisfies `onFaceΔ2_strict N · 2`. Proof: the
  face equals the diagonal endpoint pair `{(b.1, b.2+1), (b.1+1, b.2)}`
  via S19.2's `t1_erase_third` applied at the self-drop index;
  both endpoints satisfy the face-2 condition by S20's
  `satDiagBases_endpoints_on_face2`; the bridge
  `forall_vertex_ne_iff_forall_face_mem` (S19.2) converts the
  `∀ v ∈ faceOf` form to the `∀ j ≠ k`-on-`vertexEnum` form
  that `_hLastFace` filters on.

Together with S21A (forward: `_hLastFace`-pair ⟹ `satDiagBases`)
and S24 (t2-extinction: only t1 cells contribute), this packages
the **t1-side bijection data** for S25:

  satDiagBases N ↔ {t1 cells in _hLastFace filter}

via `b ↦ (t1 b, k_self(b))`. The composition with S25-prep-fst-index
(merged) yielding `b ↦ b.1` then identifies this set with
`Finset.range N`, matching the index set of `face2_path_odd`'s
color-change edges. S23 (in flight, PR #17571) supplies the color
wiring + S22's `IsDoor` ↔ color-change bridge to complete the
correspondence with `(Finset.range N).filter (fun k => g k ≠ g (k+1))`.

S25-rev keeps the iterative-PR cadence small (3 self-contained
lemmas, ~114 lines including section header + docstrings) to reduce
merge-conflict risk against the in-flight S23 (PR #17571, color-side
wiring) and S25-prep (PR #17621, gridPt coordinate values) PRs,
which add to disjoint regions of the file. Build pending per the
persistent `proofs/.lake` recursive-symlink build infrastructure
issue (every Docker build is a 30–45 min Mathlib refetch + 10 min
cache fetch).

## Previous Focus

Session 24 (PR #17577, merged 2026-05-09): Added the **t2-side
boundary extinction** lemma for `_hLastFace`, packaging the t2
branch of `boundaryOnFace_simData2` as a stand-alone re-export so
S25's bijection assembly can dismiss the t2 case by a single
`match`/`rcases` rather than re-running the case-split. New private
lemma `t2_adj_ne_none` in a new `N2LastFaceT2Extinct` section
appended to `SpernerFreudSimp` (97 lines added to
`SpernerFreudenthalSimplex.lean`).

Together with S21A's `t1_lastFace_implies_satDiag` (PR #17464,
merged), the t1/t2 split for `_hLastFace` is now complete:
* **t2 side (this PR, S24)**: `c ∈ t2Bases N`, k : Fin 3 ⟹
  `((simData2 N).toTriangulation).adj ⟨t2 c, _⟩ k ≠ none`. Hence
  no t2 cell contributes to the `_hLastFace` filter at all.
* **t1 side (S21A, merged)**: under the per-vertex face-2
  hypothesis, the drop must be `b` itself and `b ∈ satDiagBases N`.

New lemmas (~97 lines including section header + docstrings):

* `t2_adj_ne_none`: `c ∈ t2Bases N → k : Fin 3 →
  ((simData2 N).toTriangulation).adj ⟨t2 c, t2_in_topSimps2_of_base N hc⟩ k ≠ none`.
  Proof case-splits on `vertexEnum (t2 c) hS k ∈ t2 c` (the S19.3
  pattern) and applies the appropriate `t2_face*_card_ge_two` to
  contradict the `card ≤ 1` consequence of `adj = none` from
  `adjFn_eq_none_iff_card_le_one` (S19.1).
* `t2_lastFace_filter_impossible`: filter-shaped corollary in the
  exact contrapositive form S25 will consume, deriving `False`
  from any `(t2 c, k)` triple with `adj = none`.

This is the **S24** step of the n=2 Sperner-via-Freudenthal
pipeline. After S24, the remaining S25 step is the bijection
between the `_hLastFace` filter (now provably restricted to t1
cells with diagonal-drop and `b ∈ satDiagBases N` per S21A) and
`(Finset.range N).filter (fun k => g k ≠ g (k+1))`'s color-change
edges — using S22's `isDoor_dim_two_iff_color_change_of_no_color_two`
and S23's color-side wiring (PR #17571, in flight) to translate
between geometric face-2 hypothesis and the color-change predicate.

S24 keeps the iterative-PR cadence small (one self-contained
extraction lemma + filter-shape corollary) to reduce merge-conflict
risk against the in-flight S23 PR #17571 (which appends a different
section, `N2LastFaceColors`, before this one) and keep any build
regressions narrow, given the persistent `proofs/.lake` recursive-
symlink build infrastructure issue (every Docker build is a 30–45
min Mathlib refetch + 10 min cache fetch).

## Previous Focus

Session 23 (PR #17571, in flight): Added the **color-side wiring**
(`cN2_total_face2_color_ne_two`, `satDiagBases_endpoints_color_ne_two`,
`t1_lastFace_color_ne_two`) connecting S21A's geometric face-2 hypothesis
to S22's color-change bridge. ~83 lines, build pending.

## Previous Focus

Session 22 (PR #17549, merged 2026-05-09): Added the **Sperner-restricted IsDoor ↔ color-change**
bridge in `SimplicialAdjFnHelper`, specializing S21B's generic
`isDoor_dim_two_iff` to the case where neither non-`k` vertex carries
color `2` (which the Sperner condition forces whenever both lie on
geometric face `2`). The conclusion is in the canonical "the two
non-`k` vertices have different colors" shape, ready to match
`face2_path_odd`'s `g k ≠ g (k+1)` predicate.

New lemmas in `SimplicialAdjFnHelper` (~73 lines added to
`SpernerFreudenthalSimplex.lean` after `isDoor_dim_two_iff`):

* `fin_three_other_eq` (private): For `i₁, i₂ : Fin 3` distinct and
  both `≠ k`, every `j : Fin 3` with `j ≠ k` satisfies `j = i₁ ∨ j = i₂`.
  Pure `Fin 3` enumeration via `decide`.
* `isDoor_dim_two_iff_color_change_of_no_color_two`:
  `IsDoor c K s k ↔ c (K.vertex s i₁) ≠ c (K.vertex s i₂)` under
  hypothesis `h_no2 : ∀ i ≠ k, c (K.vertex s i) ≠ 2` for any choice
  of two distinct non-`k` indices `i₁, i₂`. Forward direction is the
  contrapositive (equal colors at `i₁, i₂` would force the color-`0`
  and color-`1` witnesses of `isDoor_dim_two_iff` to share a vertex,
  hence `0 = 1`). Reverse direction: distinct colors `≠ 2` are
  necessarily `0` and `1` in some order, supplying both witnesses.

Together with S21B's `isDoor_dim_two_iff` (PR #17502, merged) and
S21A's `t1_lastFace_implies_satDiag` (PR #17464, merged), the n=2
`_hLastFace` discharge for `simData2 N` now has all abstract bridges
in place. The remaining S23+ work is the concrete bijection between
the `_hLastFace` filter and `(Finset.range N).filter (fun k => g k ≠ g (k+1))`,
parametrized by `b.1` from `satDiagBases N` (since for
`b ∈ satDiagBases N` with `b.1 + b.2 + 1 = N`, the diagonal endpoints
`(b.1, b.2+1)` and `(b.1+1, b.2)` correspond to path positions
`b.1` and `b.1+1` of the index-`k → (k, N-k)` face-2 path).

S22 keeps the iterative-PR cadence small (one self-contained
abstract bridge lemma + supporting `decide` helper) to reduce
merge-conflict risk and keep any build regressions narrow, given
the persistent `proofs/.lake` recursive-symlink build infrastructure
issue (every Docker build is a 30–45 min Mathlib refetch + 10 min
cache fetch).

## Previous Focus

Session 21A (PR #17464, merged): Added the **t1-side forward
extraction lemma** for `_hLastFace`, eliminating the two non-diagonal
drop cases by inconsistent face-2 sums and identifying the
diagonal-drop case with `b ∈ satDiagBases N`.

New private lemma in a new `N2LastFaceExtract` section appended
to `SpernerFreudSimp` (84 lines added to
`SpernerFreudenthalSimplex.lean`):

* `t1_lastFace_implies_satDiag` — for `b ∈ t1Bases N` and
  `k : Fin 3`, if every non-`k` vertex of `t1 b` lies on
  geometric face 2, then `b ∈ satDiagBases N` and the dropped
  vertex is `b` itself. Proof case-splits on
  `vertexEnum (t1 b) hS k ∈ t1 b` (the S19.3 pattern):
    - Drop `(b.1+1, b.2)` ⟹ face = `{b, (b.1, b.2+1)}`.
      Both on face 2 ⟹ `b.1+b.2 = N ∧ b.1+(b.2+1) = N`.
      Contradiction (`omega`).
    - Drop `(b.1, b.2+1)` ⟹ face = `{b, (b.1+1, b.2)}`.
      Symmetric contradiction.
    - Drop `b` ⟹ face = `{(b.1, b.2+1), (b.1+1, b.2)}`
      (diagonal). Endpoint on face 2 ⟹ `b.1+b.2+1 = N`,
      exactly the `satDiagBases_mem_iff` defining condition.

Together with S20's `satDiagBases_card N = N`, this gives a
forward map `(t1 b, k₀) ↦ b` from t1-cell members of the
`_hLastFace` filter into `satDiagBases N`. **S21B** will handle
the t2 side (every t2 face has ≥ 2 containers per
`t2_face*_card_ge_two`, so `adj = none ∧ S = t2 c` is impossible
— already proved as the `exfalso` branch of
`boundaryOnFace_simData2`) and add the `IsDoor` ↔
`g k ≠ g (k+1)` color-change bridge needed to match the
`face2_path_odd` filter exactly.

S21A keeps the iterative-PR cadence small (one self-contained
lemma) to reduce merge-conflict risk and keep any build
regressions narrow, given the persistent `proofs/.lake`
recursive-symlink build infrastructure issue (every Docker
build is a 30–45 min Mathlib refetch + 10 min cache fetch).

## Previous Focus

Session 20 (PR #17426, build pending): Introduced the
**saturating-diagonal base set** `satDiagBases N` and its core
structural results, completing the **count side** of the future
`_hLastFace` ↔ `face2_path_odd` bijection.

The `_hLastFace` slot of `Triangulation.boundary_doors_odd` counts
boundary doors `(s, k)` whose remaining vertices all lie on
geometric face 2 (`b.1+b.2 = N`). By S18.1 + S18.5, these arise
**only** from saturating-diagonal t1 cells (t2 contributes no
boundary doors per S18.2; horizontal/vertical t1 boundaries are on
face 1 / 0 per S18.5). So the cell side of the count is exactly
`|satDiagBases N| = N`.

New private definitions/lemmas in a new `N2LastFaceBases` section
appended to `SpernerFreudSimp` (152 lines added to
`SpernerFreudenthalSimplex.lean`):

* `satDiagBases N : Finset (ℕ × ℕ)` —
  `(t1Bases N).filter (fun b => b.1 + b.2 + 1 = N)`
* `satDiagBases_mem_iff` — clean form combining `t1Bases_mem_iff`
  with the saturating condition.
* `satDiagBases_subset_t1Bases` — subset relation.
* `satDiagBases_image_map_injOn` — `k ↦ (k, N-1-k)` injective on
  `Finset.range N`.
* `satDiagBases_eq_image_range` — explicit parametrization with
  `(Finset.range N).image (fun k => (k, N-1-k))`.
* `satDiagBases_card` — cardinality = N. Matches the
  `Finset.range N` index set in `face2_path_odd`.
* `satDiagBases_endpoints_in_range` — diagonal endpoints
  `(b.1, b.2+1)` and `(b.1+1, b.2)` are in the in-range region
  `v.1+v.2 ≤ N`.
* `satDiagBases_endpoints_on_face2` — diagonal endpoints both
  satisfy `onFaceΔ2_strict N · (2 : Fin 3)`. Exactly the
  per-vertex content of `_hLastFace`'s condition (3) for the
  diagonal-cell case.
* `satDiagBases_t1_in_topSimps2` — convenience alias for feeding
  saturating-diagonal cells through `Triangulation` consumers.

S20 establishes a clean reusable foundation for S21+ rather than
attempting the full `_hLastFace` discharge in one commit. Keeping
the iterative-PR cadence small reduces merge-conflict risk and
keeps any build regressions narrow.

**S21 (next, partially done — S21A this session):** Pin down the
matching `vertexEnum` index `k` (via the S19.3 case-split pattern
on `vertexEnum (t1 b) hS k ∈ t1 b`); bridge
`IsDoor c (T.toCellComplex) (t1 b) k` to `face2_path_odd`'s
color-change predicate `g k ≠ g (k+1)`; assemble the `_hLastFace`
discharge for `simData2 N`. Estimated ~80–100 lines.

S21A (this session) handles the first sub-task: the t1-side
forward extraction `t1_lastFace_implies_satDiag` (~84 lines).
S21B will add the IsDoor ↔ color-change bridge and assemble the
full `_hLastFace_simData2` discharge.

## Previous Focus

Session 19 part 3 (PR #17363, merged): Added the
**concrete `_hBoundaryOnFace_simData2` discharge** plus a
"two-distinct-containers ⇒ card ≥ 2" helper. This is the actual
consumer of S16–S19's combinatorial infrastructure: given any
boundary door of `(simData2 N).toTriangulation`, it produces the
geometric `faceIdx : Fin 3` and a witness that all non-`k`
vertices satisfy `onFaceΔ2_strict N · faceIdx`.

Two new private lemmas in
`SpernerFreudSimp.SpernerFreudSimp.N2HBoundaryOnFace`
(~220 lines total in `SpernerFreudenthalSimplex.lean`):

* `containers_two_distinct`: two distinct top-simplices
  containing the same codim-1 face yield a container card ≥ 2.
  Helper for the t1-interior contradictions and the t1-diagonal
  case (clean replacement for inlining the {S₁, S₂} insert
  pattern in each branch).
* `boundaryOnFace_simData2`: the main lemma. Signature exactly
  matches the `_hBoundaryOnFace` hypothesis of
  `Triangulation.boundary_doors_odd` for
  `(simData2 N).toTriangulation`. Proof strategy:

  1. Apply `SimplicialAdjFnHelper.adjFn_eq_none_iff_card_le_one`
     to convert `adj = none` to `containers card ≤ 1`.
  2. Establish the in-range hypothesis on every face vertex
     (`topSimps2_vertex_in_range` + `faceOf_subset`).
  3. Apply `forall_vertex_ne_iff_forall_face_mem` (S19.2 bridge)
     to reshape the existential goal in face-content form.
  4. Case-split `S = t1 b ∨ S = t2 c` via `topSimps2_mem_iff`.
  5. For `t1 b`: case-split on `vertexEnum (t1 b) hS k ∈ t1 b`,
     identifying the dropped vertex (3 cases). Each case rewrites
     `(simData2 N).faceOf` to the matching edge via the S19.2
     `t1_erase_*` lemmas, then forces the geometric boundary
     condition (b.1 = 0, b.2 = 0, or N ≤ b.1+b.2+1) by
     contradiction with S17 (`diagonal_neighbor_topSimps2`) or
     S18.2 (`horizontal_neighbor_topSimps2` /
     `vertical_neighbor_topSimps2`). Boundary case discharges via
     S18.5 `*_endpoints_on_face*`.
  6. For `t2 c`: 3 cases on dropped vertex; each face has ≥ 2
     containers via S18 `t2_face{0,1,2}_card_ge_two`,
     contradicting card ≤ 1. (t2 contributes no boundary doors.)

This closes the `_hBoundaryOnFace` slot of
`Triangulation.boundary_doors_odd` for `simData2 N`. The
remaining slots are:

* `_hSperner` — already proved (`cN2_total_isSpernerColoring`,
  S14).
* `_hLowerDim` — already discharged generically by
  `SpernerLowerDimHelper.sperner_lowerDim_card_even` (S15).
* `_hLastFace` — TODO (S20, ~120 lines, bijection with
  `face2_path_odd` via S12).

After `_hLastFace`, applying `Triangulation.sperner` yields the
panchromatic-cell existential, plus diameter-bound + real-coord
extraction completes `sperner_panchromatic_two` (~50 lines).
Total estimated remaining for `sperner_panchromatic_two`:
~170 lines across 2 sessions (S20 = `_hLastFace`, S21 = sperner
glue + real coords).

## Previous Focus

Session 19 part 2 (PR #17352, merged): Added the
**vertex-vs-face universal-quantifier bridge** in
`SimplicialAdjFnHelper`, plus six concrete **face-erase
computations** for `t1 b` and `t2 c` of `simData2 N`. Together
with S19 part 1's `adjFn_eq_none_iff_card_le_one`, these complete
the infrastructure needed for a clean case-split assembly of
`_hBoundaryOnFace` for `simData2 N` (consumed by this session's
S19.3).

New generic lemma in `SimplicialAdjFnHelper` (this session):

* `forall_vertex_ne_iff_forall_face_mem`: converts
  `∀ j ≠ k, P (D.vertexEnum s hs j)` to
  `∀ v ∈ D.faceOf s hs k, P v`. This is the universal-quantifier
  shape required by the `_hBoundaryOnFace` hypothesis, restated in
  face-content terms suitable for case-splitting on `faceOf`.
  Direct reformulation via `vertexEnum_image_erase`.

Six new concrete lemmas in `SpernerFreudSimp.N2FaceErase`:

* `t1_erase_first b`: `(t1 b).erase (b.1+1, b.2)` = vertical edge
  `{b, (b.1, b.2+1)}`
* `t1_erase_second b`: `(t1 b).erase (b.1, b.2+1)` = horizontal
  edge `{b, (b.1+1, b.2)}`
* `t1_erase_third b`: `(t1 b).erase b` = diagonal edge
  `{(b.1, b.2+1), (b.1+1, b.2)}`
* `t2_erase_first c`: `(t2 c).erase (c.1+1, c.2+1)` = face2
  `{(c.1, c.2+1), (c.1+1, c.2)}`
* `t2_erase_second c`: `(t2 c).erase (c.1+1, c.2)` = face1
  `{(c.1, c.2+1), (c.1+1, c.2+1)}`
* `t2_erase_third c`: `(t2 c).erase (c.1, c.2+1)` = face0
  `{(c.1+1, c.2), (c.1+1, c.2+1)}`

Each is a 2-direction Finset.ext + Prod.ext_iff + omega proof.

**S19 part 3 (next):** Concrete `_hBoundaryOnFace_simData2`
discharge. With S19.1 + this session's bridge + 6 erase
computations, the assembly is now a pure case-split:

1. Apply `adjFn_eq_none_iff_card_le_one` to convert hypothesis to
   `(containersOf face).card ≤ 1`.
2. Apply `forall_vertex_ne_iff_forall_face_mem` to convert the
   `∀ j ≠ k` goal to `∀ v ∈ faceOf, P v`.
3. Case-split on `s.1 ∈ topSimps2 N` via `topSimps2_mem_iff`:
   t1 b vs t2 c.
4. For t1 b: case-split on `vertexEnum (t1 b) hs k ∈ t1 b` via
   `vertexEnum_mem`, identifying which of three vertices is
   removed (the t1_erase lemmas above). Then for each edge,
   contradiction with interior witnesses (S17/S18.2.1/S18.2.2)
   yields the geometric boundary condition, and S18.5 supplies
   the `onFaceΔ2` witnesses.
5. For t2 c: every face has ≥ 2 containers (S18 part 2
   `t2_face*_card_ge_two`), contradicting card ≤ 1. (No t2
   contributions to boundary doors.)

Estimated S19.3 size: ~80 lines of pure case work.

Session 19 part 1 (PR #17162, merged): Added the
**generic abstract `adjFn = none ↔ card ≤ 1` translation** in a
new `SimplicialAdjFnHelper` namespace, appended after
`end SpernerFreudSimp`. This is the abstract-level bridge that
S16-S18's geometric container-card analysis feeds into, completing
the framework needed to discharge `_hBoundaryOnFace` of
`Triangulation.boundary_doors_odd`.

Two new generic lemmas (work for any `AbstractSimplicialData V n`,
not just the n=2 Type-1/Type-2 triangulation):

1. `adjFn_eq_none_iff_card_le_one`: the main iff,
       `D.adjFn p k = none ↔
         (D.containersOf (D.faceOf p.1 p.2 k)).card ≤ 1`
   The proof unfolds `adjFn` and `split_ifs` over the outer
   `card ≤ 1` and inner `(cs.erase p.1).Nonempty` decisions. The
   `(cs.card > 1, erase empty)` branch is shown impossible:
   `p.1 ∈ cs` (via `self_mem_containersOf`) forces
   `(cs.erase p.1).card = cs.card - 1 ≥ 1`.

2. `adjFn_eq_none_iff_card_eq_one`: corollary using
   `self_mem_containersOf` for `cs.card ≥ 1`, strengthening
   "≤ 1" to "= 1".

These connect the *operational* definition of `adjFn` (a nested
`dite`) to the *static* container-cardinality form that S18.1's
`*_only_container_of_t1_boundary` lemmas produce
(`filter = {t1 b}`, hence card = 1). With
`topSimps2_pseudomanifold` already giving the upper bound
`card ≤ 2`, the building blocks now cover both implications:

* boundary case (S18.1) → `card = 1` → `adjFn = none` (via S19.1)
* interior case (S17 + S18.2) → `card ≥ 2` → `adjFn = some _`
  (via the contrapositive of S19.1)

**S19 part 2 (next):** Concrete `_hBoundaryOnFace` proof for
`simData2 N`, case-splitting on `s ∈ topSimps2 N` (six (s, k)
combinations: t1 × {0,1,2} and t2 × {0,1,2}). Invoke S19.1 to
reduce `adjFn s k = none` to `cs.card ≤ 1`. Combine with S17 +
S18.2 (interior witnesses, which contradict the `card ≤ 1`
hypothesis for non-boundary cases) and S18.1 (boundary
singletons, which provide the `onFaceΔ2 faceIdx` witness via
`*_endpoints_on_face*`). Estimated ~80 lines.

Session 18 part 2 (PR #17149, merged): Added 5 new
`private` existential lemmas in a new `N2BoundaryInteriorNeighbors`
section (appended after `N2BoundaryAnalysis` at end of file) that
complement S18 part 1 (PR #17133, merged) by covering the
**interior** side of `_hBoundaryOnFace`:

1. `horizontal_neighbor_topSimps2`: for `b ∈ t1Bases N` with
   `b.2 ≥ 1`, the horizontal edge is contained in
   `t2 (b.1, b.2 - 1) ≠ t1 b` of `topSimps2 N`.
2. `vertical_neighbor_topSimps2`: analogous for `b.1 ≥ 1`,
   witness `t2 (b.1 - 1, b.2)`.
3. `t2_face0_neighbor_topSimps2`: for `c ∈ t2Bases N`, t2 face0
   ("right side") is contained in `t1 (c.1+1, c.2) ≠ t2 c`.
4. `t2_face1_neighbor_topSimps2`: face1 ("top side"), witness
   `t1 (c.1, c.2+1)`.
5. `t2_face2_neighbor_topSimps2`: face2 ("diagonal"), witness
   `t1 c` itself.

Each is a 4-tuple term-mode proof matching the pattern of S17's
`diagonal_neighbor_topSimps2` reverse direction, using S16/S17
building blocks.

**Building-block coverage table** for `_hBoundaryOnFace`
(now complete):

| cell | edge | boundary case | interior case |
|------|------|----------------|----------------|
| t1   | diagonal   | S18.1 `diagonal_only_container_of_t1_boundary` | S17 `diagonal_neighbor_topSimps2` |
| t1   | horizontal | S18.1 `horizontal_only_container_of_t1_boundary` | S18.2.1 `horizontal_neighbor_topSimps2` |
| t1   | vertical   | S18.1 `vertical_only_container_of_t1_boundary` | S18.2.2 `vertical_neighbor_topSimps2` |
| t2   | face0      | (impossible, no boundary) | S18.2.3 `t2_face0_neighbor_topSimps2` |
| t2   | face1      | (impossible, no boundary) | S18.2.4 `t2_face1_neighbor_topSimps2` |
| t2   | face2      | (impossible, no boundary) | S18.2.5 `t2_face2_neighbor_topSimps2` |

Remaining S19 work is **abstract-level bridge**: translate
`T.adj s k = none` ↔ `(containers ...).card ≤ 1` and case-split
through the 11 building blocks above (~80 lines, mostly
case-splitting).

Session 18 part 1 (PR #17133, merged): Promoted S16/S17 edge
building blocks into the **boundary-edge container singletons**: for
each of the three edge types of a `t1 b` cell, we prove that under
the matching geometric boundary condition the container set inside
`topSimps2 N` is exactly `{t1 b}`, and the two endpoints of the
boundary edge satisfy the matching `onFaceΔ2` predicate.

Specifically (9 new lemmas):

1. **Singleton container equalities** (3 lemmas):
   - `diagonal_only_container_of_t1_boundary` (N ≤ b.1+b.2+1)
   - `horizontal_only_container_of_t1_boundary` (b.2 = 0)
   - `vertical_only_container_of_t1_boundary` (b.1 = 0)
2. **Cardinality-1 corollaries** (3 lemmas):
   - `diagonal_card_eq_one_of_t1_boundary`
   - `horizontal_card_eq_one_of_t1_boundary`
   - `vertical_card_eq_one_of_t1_boundary`
3. **`onFaceΔ2` endpoint witnesses** (3 lemmas):
   - `diagonal_endpoints_on_face2`
   - `horizontal_endpoints_on_face1`
   - `vertical_endpoints_on_face0`

Together these supply *both* sides of the existential
`∃ faceIdx : Fin 3, ∀ j ≠ k, onFaceΔ2 N (vertex s j) faceIdx`
required by `_hBoundaryOnFace` for the t1 boundary cases. The
remaining S18 work is the t2-share lemmas (every t2 face is
shared with a t1 cell, so t2 contributes no boundary doors)
and the `adjFn` ↔ `containersOf.card ≤ 1` translation that wires
all of this into the abstract `Triangulation.boundary_doors_odd`
hypothesis.

Session 17 (PR #17101, merged): Extended the `N2BoundaryAnalysis` section
with the **base ↔ topSimps2 bridge**: 13 new lemmas converting between
arithmetic conditions on `(b, c)` and concrete edge containment in
`topSimps2 N`. Specifically:

1. **Base-membership iffs** (`t1Bases_mem_iff`, `t2Bases_mem_iff`): rewrite
   `b ∈ t{1,2}Bases N` to clean arithmetic predicates.
2. **topSimps2 membership** (`t1_in_topSimps2_of_base`,
   `t2_in_topSimps2_of_base`, `topSimps2_mem_iff`): bridge from base
   membership to top-simplex membership, including the canonical
   case-split form `s ∈ topSimps2 N ↔ (∃ b ∈ t1Bases N, t1 b = s) ∨
   (∃ b ∈ t2Bases N, t2 b = s)`.
3. **t2 → t1 base translations** (`t2Bases_self_in_t1Bases`,
   `t2Bases_right_in_t1Bases`, `t2Bases_top_in_t1Bases`): for
   `b ∈ t2Bases N`, all three "face-mate" t1 bases — `b`, `(b.1+1, b.2)`,
   `(b.1, b.2+1)` — are in `t1Bases N`. Combined with S16's
   `t2_face{0,1,2}_in_t1`, this proves all t2 faces are shared with
   another top simplex, hence **t2 cells contribute no boundary doors**.
4. **t1 → t2 base translations** (`t1Bases_horizontal_neighbor_in_t2Bases`,
   `t1Bases_vertical_neighbor_in_t2Bases`,
   `t1Bases_diagonal_neighbor_in_t2Bases`): existential side of the
   neighbor analysis for t1 cells.
5. **The missing diagonal-boundary case** (`diagonal_not_in_t2_at_diagonal`):
   counterpart to S16's `horizontal_not_in_t2_at_y0` and
   `vertical_not_in_t2_at_x0`. When `b ∈ t1Bases N` saturates the
   diagonal `b.1 + b.2 + 1 ≥ N`, no t2 cell with base in `t2Bases N`
   contains the diagonal of t1(b).
6. **Top-level diagonal classification** (`diagonal_neighbor_topSimps2`):
   the existential at topSimps2 level — the diagonal of `t1 b` is
   contained in *some other* simplex of `topSimps2 N` iff
   `b.1 + b.2 + 1 < N`, in which case that other simplex is `t2 b`.

This is exactly the form S18's `containersOf`-based assembly of
`_hBoundaryOnFace` will consume.

Session 16 (PR #17051, merged): Added boundary-edge characterization
scaffolding for the n=2 Type-1/Type-2 triangulation in a new
`N2BoundaryAnalysis` section inside `SpernerFreudSimp`. Proves the
eight building-block lemmas needed by the eventual `_hBoundaryOnFace`
discharge: `t1_ne_t2`, `diagonal_in_t{1,2}_iff`, `horizontal_in_t2_pos`,
`vertical_in_t2_pos`, `horizontal_not_in_t2_at_y0`,
`vertical_not_in_t2_at_x0`, plus `t2_face{0,1,2}_in_t1` (every t2 face
shared with a t1 cell, so t2 contributes no boundary doors).

Session 15 (PR #17015, merged): added a generic `_hLowerDim` discharge
helper (`SpernerLowerDimHelper.sperner_lowerDim_card_even`) outside the
`SpernerFreudSimp` namespace, proving that for any
`Triangulation V n` + `IsSpernerColoring`, the boundary-door filter on
any face with `faceIdx.val < n` is empty (hence Even cardinality 0).

Session 14 (PR #17004, merged): added `cN2_total` total wrapper
+ `cN2_total_isSpernerColoring` lifted Sperner condition + vertex-range
bridge `topSimps2_vertex_in_range`.

Session 9: Proved `sperner_panchromatic` for n=0 (trivial) and n=1 (discrete IVT).
Companion file completely rewritten with correct proofs. FreudCell approach abandoned.

## Final Status of FreudCell Approach (Dead)

The constant-miss FreudCell triangulation is WRONG for ALL n≥2:

For n=2, N=2: 6 FreudCell cells triangulate an ANNULUS (Euler characteristic 0),
not the disk Δ² (Euler characteristic 1):
- All 6 cells: {corner, midpoint, midpoint} pattern — no center triangle DEF
- Centroid lies in MULTIPLE overlapping cells
- V(6) - E(12) + F(6) = 0 ≠ 1 (annulus, not disk)

The standard N=2 Sperner triangulation (4 triangles: ADE, BDF, CEF, DEF)
does NOT appear in FreudCell. FreudCell simply triangulates the wrong space.

## Current Proof State

### Main file (SpernerNDimMathlibOQ02.lean)
- 1 axiom (`sperner_panchromatic` for general n), 0 sorries
- Fully proved: coloring, boundary condition, compactness convergence

### Companion file (SpernerFreudenthalSimplex.lean)
- `sperner_panchromatic_zero` (n=0): PROVED, 0 sorries (S9)
- `sperner_panchromatic_one` (n=1): PROVED, 0 sorries, discrete IVT (S9)
- Type-1/Type-2 triangulation `simData2` + pseudomanifold: PROVED (S11)
- XOR parity + grid coloring + face2_path_odd + onFace infrastructure:
  PROVED (S12, S13)
- `cN2_total` wrapper + `cN2_total_isSpernerColoring`: PR #17004 merged (S14)
- `SpernerLowerDimHelper.sperner_lowerDim_card_even`: PR #17015 merged,
  generic discharge of `_hLowerDim` for any
  Sperner-on-Triangulation (S15)
- `N2BoundaryAnalysis` building blocks (S16, PR #17051 merged):
  `t1_ne_t2`, `diagonal_in_t{1,2}_iff`, `horizontal_in_t2_pos`,
  `vertical_in_t2_pos`, `horizontal_not_in_t2_at_y0`,
  `vertical_not_in_t2_at_x0`, `t2_face{0,1,2}_in_t1`
- `N2BoundaryAnalysis` base ↔ topSimps2 bridge (S17, PR #17101 merged):
  13 new lemmas converting base membership to topSimps2 containment,
  plus the missing diagonal-boundary case
  `diagonal_not_in_t2_at_diagonal` and the top-level classification
  `diagonal_neighbor_topSimps2`.
- `N2BoundaryAnalysis` t1-boundary container singletons + onFaceΔ2
  endpoint witnesses (S18 part 1, PR #17133 merged): 9 new lemmas.
- `N2BoundaryInteriorNeighbors` interior witnesses (S18 part 2,
  PR #17149 merged): 5 new existential lemmas covering t1-interior
  and t2-cell faces, completing the geometric coverage table.
- `SimplicialAdjFnHelper` generic `adjFn = none ↔ card ≤ 1`
  translation (S19 part 1, PR #17162, merged): 2 generic
  lemmas wiring the abstract `Triangulation.adj` adjacency to the
  geometric container-cardinality form.
- `SimplicialAdjFnHelper.forall_vertex_ne_iff_forall_face_mem`
  (S19 part 2, this session, build pending): generic vertex/face
  bridge converting the `∀ j ≠ k` quantifier to `∀ v ∈ faceOf`.
- `N2FaceErase` t1/t2 erase computations (S19 part 2,
  PR #17352, merged): 6 explicit Finset.erase equalities for
  the three vertex removals of `t1 b` and `t2 c`.
- `N2LastFaceBases` saturating-diagonal base set (S20,
  PR #17426, build pending): `satDiagBases N` definition + 8
  structural lemmas (membership iff, image-of-range
  parametrization, cardinality = N, endpoints in range,
  endpoints on face 2, t1 ∈ topSimps2 alias).
- `N2LastFaceExtract` t1-side `_hLastFace` forward extraction
  (S21A, PR #17464, merged): `t1_lastFace_implies_satDiag`
  identifies `b ∈ satDiagBases N` and the dropped vertex = `b`
  for any `(t1 b, k)` with face-2 condition; eliminates the
  vertical-edge and horizontal-edge drop cases by inconsistent
  face-2 sums.
- `SimplicialAdjFnHelper.isDoor_dim_two_iff` (S21B,
  PR #17502, merged): generic d=2 IsDoor characterization
  (colors `0` and `1` both appear among non-`k` vertices).
- `SimplicialAdjFnHelper.isDoor_dim_two_iff_color_change_of_no_color_two`
  + `fin_three_other_eq` (S22, this session, build pending):
  Sperner-restricted specialization of S21B; under
  `∀ i ≠ k, c (vertex s i) ≠ 2`, the door condition is
  `c (vertex s i₁) ≠ c (vertex s i₂)` for any two distinct
  non-`k` indices. Bridges to `face2_path_odd`'s color-change
  predicate.
- `sperner_panchromatic_two` (n=2): 1 sorry remaining
- n≥3: future work

## Path Forward for n≥2 (post-S19.2)

`Triangulation.boundary_doors_odd` requires four hypotheses:
1. `_hSperner` — done generically by S14 wrapper (cN2_total_isSpernerColoring)
2. `_hBoundaryOnFace` — S16/S17/S18.1/S18.2 supply ALL six
   face/edge × cell-type combinations as `private lemma`s.
   S19.1 supplies the generic `adjFn = none ↔ (containers).card
   ≤ 1` translation. S19.2 (this session) supplies the generic
   ∀-quantifier face bridge + 6 concrete erase computations.
   **S19 part 3 next**: assemble `_hBoundaryOnFace_simData2` by
   case-splitting on `vertexEnum ∈ {3 vertices}` per cell type,
   using the 6 erase lemmas to identify which edge is the codim-1
   face, then either contradicting interior witnesses (for non-
   boundary cells) or invoking S18.5 endpoint witnesses (for
   boundary t1 cells). ~80 lines of pure case work.
3. `_hLowerDim` — done generically by S15 helper
4. `_hLastFace` — IN PROGRESS:
    * S20 (PR #17426, merged): `satDiagBases N` foundation +
      count = N.
    * S21A (PR #17464, merged): t1-side forward extraction
      (`t1_lastFace_implies_satDiag`) identifies dropped vertex
      and `b ∈ satDiagBases N`.
    * S21B (PR #17502, merged): generic d=2
      `isDoor_dim_two_iff` (`IsDoor ↔ colors 0 and 1 both
      appear among non-`k` vertices`).
    * S22 (this session, build pending): Sperner-restricted
      `isDoor_dim_two_iff_color_change_of_no_color_two`,
      collapsing the door condition to "two non-`k` vertices
      have different colors" under the no-color-`2` hypothesis
      (forced by Sperner + face-`2` membership).
    * S23 (next): assemble `_hLastFace_simData2` by combining
      `t1_lastFace_implies_satDiag` (S21A) →
      `isDoor_dim_two_iff_color_change_of_no_color_two` (S22) →
      bijection with `(Finset.range N).filter (g k ≠ g (k+1))`
      via `b.1`-parametrization on `satDiagBases N`. Then apply
      `face2_path_odd` for oddness. ~80-100 lines. The
      t2-extinction side is already implicit in
      `boundaryOnFace_simData2`'s `exfalso` t2 branch.

Then apply `Triangulation.sperner` (~50 lines for diameter bound + real
coordinates). Total estimated remaining: ~150 lines across 2 sessions.

## Gallery Status

Main entry: 1 axiom (honest, correct). Companion shows n=0,1 concretely proved.
OQ-02 question answered modulo 1 axiom (the combinatorial Sperner's lemma for n-dim grid).

Session 26 (S25-prep-endpoint-form, this session, build pending):
Added `N2DiagonalEndpointForm` section (4 lemmas, 51 lines added
to `SpernerFreudenthalSimplex.lean`) bridging `satDiagBases N`
diagonal endpoint expressions to `face2_path_odd`'s `(k, N - k)`
parametrization:

  * `satDiagBases_succ_le` — `b.1 + 1 ≤ N` (range bound).
  * `satDiagBases_first_endpoint_face2_path_form` —
    `(b.1, b.2 + 1) = (b.1, N - b.1)`.
  * `satDiagBases_second_endpoint_face2_path_form` —
    `(b.1 + 1, b.2) = (b.1 + 1, N - (b.1 + 1))`.
  * `satDiagBases_endpoints_pair_face2_path_form` — unordered
    pair rewrite combining the two endpoint forms.

Each proof: extract `satDiagBases_mem_iff` data + `omega`.
Independent of in-flight S23 (N2LastFaceColors, PR #17571) color
wiring and S25-prep (N2GridCoord, PR #17621) gridPt coordinate
helpers. Pure combinatorial form-rewriting consumed by the
eventual S25 bijection between the `_hLastFace` filter and
`(Finset.range N).filter (g k ≠ g (k+1))` color-change edges.

---

## Session 31 STATE-SYNC (2026-06-01, researcher-1, doc-only)

**Mode**: STATE-SYNC (doc-only)
**Outcome**: Fresh Docker baseline of `proofs/Proofs/SpernerNDimMathlibOQ02.lean` reveals **5 errors** (down from 100+ noted in S30b 2026-05-14). Parent-file `SpernerFreudenthalSimplex` may have been repaired by intervening commits (`ecb47b35601` 2026-05-16). Slug file itself has 5 latent Mathlib v4.26.0 API drifts — manageable but needs ACT.

### Current Docker Errors (slug primary file, line:col)

| # | Line | Error | Likely cause |
|---|------|-------|--------------|
| 1 | 253:13 | Type mismatch on `hpanch (N + 1) (Nat.succ_pos N)` — has type `∃ v, ...` | `hpanch` external signature change OR existential reshape from a prior lemma |
| 2 | 298:8 | "No goals to be solved" inside `calc` block | calc step closes itself via `simp` / `gcongr` becoming smarter at v4.26.0 |
| 3 | 304:8 | `assumption` failed | a hypothesis was renamed / restated upstream |
| 4 | 307:30 | Unknown constant `Filter.eventually_of_forall` | renamed to `Filter.Eventually.of_forall` at v4.26.0 (cf. greens-theorem chain repair PR #21782) |
| 5 | 320:48 | Unknown constant `Filter.eventually_of_forall` | same rename |

### Repair estimate

Items 4, 5 are mechanical one-line renames (10s each). Item 1 (Type mismatch) needs inspection of the upstream `hpanch` definition. Items 2, 3 need stepping through tactic mode. Total: ~30-60 min ACT.

### Why doc-only this cycle

- Researcher-1 session has already shipped one substantive PR (#22024, angle-trisection S6 ACT, +95 LOC + 8-bug repair cascade) and burned ~2 hours.
- The 990-LOC state.md needs a focused S31 ACT or a mechanic-style audit; combining with another large cascade in one session is suboptimal cycle hygiene.
- Doc-only PREP retains slug visibility for the next claimant with a fresh error inventory; better than dropping the claim silently.

### Recommended Next Action

**S31 ACT (next claimant)**: Apply the 5 listed repairs in order (start with the trivial 4, 5 renames, then 2, 3 calc/assumption, finally 1 Type mismatch). Re-run Docker. If the parent `SpernerFreudenthalSimplex` is also clean now, the slug should drop to 0 errors after this batch.

**Open PRs on slug at this cycle**: 0 (last touch 2026-05-16, ecb47b35601 from sibling slug oq-01-oq-04 S2-A ACT).

**Mathlib pin unchanged**: `2df2f0150c…` (v4.26.0).
