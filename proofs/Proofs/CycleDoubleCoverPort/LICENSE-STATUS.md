# Cycle Double Cover port — upstream license status and vendored-file inventory

Tracking issue: [#43638](https://github.com/rjwalters/lean-genius/issues/43638).
Porting epic: [#37507](https://github.com/rjwalters/lean-genius/issues/37507).
Upstream: <https://github.com/openai/cdc-lean> (`CDCLean/`, Lean `v4.31.0`,
Mathlib `9a9483a92959bc92bd6a60176dd1fe597298c1f8` — the same pin this
repository uses).

This file is the standing record for the one legal question the port leaves
open: `openai/cdc-lean` has no license, and part of the port vendors upstream
text under an operator **risk acceptance**. It exists so that the inventory
below — which files would have to go, and what would replace them — does not
have to be reconstructed from twenty-two module docstrings under time pressure
if upstream ever objects.

## 1. Upstream license state

**No license, as of 2026-09-22.** Evidence checked on that date:

| Check | Result |
|-------|--------|
| `gh api repos/openai/cdc-lean --jq .license` | `null` |
| `gh api repos/openai/cdc-lean/license` | `404 Not Found` |
| `gh api repos/openai/cdc-lean/contents --jq '.[].name'` | `.gitignore`, `CDCLean.lean`, `CDCLean/`, `README.md`, `VERIFICATION.md`, `lake-manifest.json`, `lakefile.toml`, `lean-toolchain` — **no `LICENSE`/`COPYING`** |
| `gh api repos/openai/cdc-lean --jq .pushed_at` | `2026-07-09T20:20:10Z` (unchanged since the port was made) |
| `gh issue view 4 -R openai/cdc-lean` | `the 'openai/cdc-lean' repository has disabled issues` — the license request thread is unreachable |
| `gh api repos/openai/cdc-lean --jq .has_issues` | `false` |

History of the check:

| Date | Finding |
|------|---------|
| 2026-07-12 | Permissive license requested upstream as `openai/cdc-lean#4`. No response. |
| 2026-08-03 | Operator records an explicit risk acceptance on #37507 (comment of ~23:55 UTC) permitting verbatim vendoring **with attribution**. |
| 2026-08-04 | Re-checked: `license: null`, contents unchanged, issues disabled (comment on #43638). |
| 2026-09-22 | Re-checked as above: still `license: null`, issues still disabled, upstream tree unchanged since `2026-07-09`. |

**What the absence of a license means.** Default copyright — all rights
reserved. It is *not* public domain, and silence is not a grant: publishing a
repository does not waive copyright, and GitHub's Terms of Service grant only
viewing and forking, not reproduction or adaptation. **No document in this
repository may describe upstream as "unlicensed, therefore free to use."** The
only correct framing is the one below.

## 2. The operator decision (what actually authorizes the vendored files)

The vendored files in §3 are here under the operator's explicit **risk
acceptance** recorded on
[#37507 (comment of 2026-08-03)](https://github.com/rjwalters/lean-genius/issues/37507),
which permits vendoring upstream text **with attribution**.

That is a risk acceptance, **not a license grant** and not a determination that
reuse is permitted. It is a decision by this repository's operator to carry a
known copyright risk, taken with the bounded-removal plan in §4 as its
mitigation. Every vendored file says so in its own header; the fullest wording
is in `NashWilliams3.lean` / `NashWilliams4.lean` ("Provenance, attribution and
licensing — READ BEFORE RESTATING") and is the template for any new vendored
file.

## 3. Per-file inventory

Classification is taken **from each file's own header**, verified by reading all
22 files in `proofs/Proofs/CycleDoubleCoverPort/` on 2026-09-22 (commit
`9992736d1e`), not from the summary in #43638 — which predates the final waves
and omits `CubicTheorem.lean` and `Audit.lean`.

* **Vendored** = the file's header states that upstream proof text is vendored
  with adaptation under the 2026-08-03 operator decision. These are the files
  at risk.
* **Re-derived** = the file's header states it is an *independent
  re-derivation*: upstream consulted for definitions/statements only, every
  proof script written from scratch. Safe regardless of the license outcome.

**Counts: 9 vendored (4,324 of 9,046 lines, 48%), 13 independent
re-derivations, 0 files with no provenance statement.**

### Vendored (adapted upstream text — the removal set)

| File | Lines | Upstream origin | Landed | Header completeness |
|------|------:|-----------------|--------|---------------------|
| `NashWilliams3.lean` | 1273 | `CDCLean/NashWilliams.lean` ~1348-2528 | #43633 | Full (canonical wording, cites `cdc-lean#4`) |
| `NashWilliams4.lean` | 1127 | `CDCLean/NashWilliams.lean` ~2570-3653 | #43633 | Full (canonical wording, cites `cdc-lean#4`) |
| `JaegerKilpatrickEvenCover.lean` | 204 | `CDCLean/JaegerKilpatrick.lean` 12-178 | #43634 | Top-comment only → **provenance section added 2026-09-22** (#43638) |
| `JaegerKilpatrickContraction.lean` | 554 | `CDCLean/JaegerKilpatrick.lean` 399-793, plus `sum_conservation_eq_cut` + `sum_endpoint_indicator` from `CDCLean/FlowCount.lean` 359-381 | #43636 | Full |
| `JaegerKilpatrickPacking.lean` | 293 | `CDCLean/JaegerKilpatrick.lean` 180-397 | #43637 | Top-comment only → **provenance section added 2026-09-22** (#43638) |
| `JaegerKilpatrick.lean` | 518 | `CDCLean/JaegerKilpatrick.lean` 795-1219 | #43640 | Full |
| `CubicTheorem.lean` | 142 | `CDCLean/CubicTheorem.lean` (all three declarations) | #43635 | Full (one stale sentence corrected 2026-09-22) |
| `Main.lean` | 179 | `CDCLean/Main.lean` | #43641 | Full |
| `Audit.lean` | 34 | `CDCLean/Audit.lean` (a list of `#print axioms` lines, extended here) | #43641 | Top-comment only → **provenance section added 2026-09-22** (#43638) |

Ambiguity notes:

* `Audit.lean` is vendored *by its own header*, but its entire content is
  `#print axioms <name>` commands plus commentary written for this repository.
  There is effectively no upstream expression left in it; treated as vendored
  anyway, conservatively, and listed as the cheapest possible removal.
* `JaegerKilpatrickContraction.lean` is the only file that vendors from a
  *second* upstream file (`FlowCount.lean`). Our own `FlowCount.lean` is a
  clean-room re-derivation, so that lemma has a ready replacement (§4).
* `CubicTheorem.lean`'s header claimed "nothing else in the port vendors
  upstream text". True when it was written (it was the first file to use the
  risk acceptance); false once the Jaeger–Kilpatrick, `NashWilliams3/4` and
  `Main` slices landed the same day. Corrected to point here.

### Independent re-derivations (no upstream text — not at risk)

| File | Lines | Upstream counterpart | Landed |
|------|------:|----------------------|--------|
| `GeneralGraph.lean` | — | `CDCLean/GeneralGraph.lean` | #43625 |
| `CycleDecomposition.lean` | — | `CDCLean/CycleDecomposition.lean` | #43625 |
| `Basic.lean` | — | `CDCLean/Basic.lean` | #43626 |
| `EvenCover.lean` | — | `CDCLean/EvenCover.lean` (part) | #43626 |
| `SixFlow.lean` | — | `CDCLean/SixFlow.lean` | #43627 |
| `CubicLabeling.lean` | — | `CDCLean/CubicLabeling.lean` | #43628 |
| `CubicBridge.lean` | — | `CDCLean/CubicBridge.lean` | #43630 |
| `Expansion.lean` | — | `CDCLean/Expansion.lean` | #43630 |
| `CubicEvenCover.lean` | — | `CDCLean/EvenCover.lean` (`cubic_even_double_cover`) | #43631 |
| `FlowCount.lean` | — | `CDCLean/FlowCount.lean` | #43632 |
| `PathCut.lean` | — | `CDCLean/PathCut.lean` | #43632 |
| `NashWilliams.lean` | — | `CDCLean/NashWilliams.lean` part 1 | #43629 |
| `NashWilliams2.lean` | — | `CDCLean/NashWilliams.lean` ~801-1348 | #43633 |

These thirteen headers say "no license file, so default copyright applies and
no proof text may be vendored". That wording predates the 2026-08-03 risk
acceptance and is *more* conservative than current policy, not less; it is
left as written (it accurately describes how those files were produced) and is
not a claim that upstream is freely usable.

## 4. Bounded removal / relicense plan

The port was deliberately sliced so that vendoring is confined to whole files:
**removal is a file-level operation, and nothing outside
`proofs/Proofs/CycleDoubleCoverPort/` imports the port** (`CycleDoubleCover.lean`
and `CycleDoubleCoverDecomposition.lean` only mention it in prose). The internal
import graph fixes the blast radius:

```
GeneralGraph → Basic → EvenCover → {CubicLabeling → CubicEvenCover, CubicBridge → Expansion}
GeneralGraph → SixFlow → FlowCount → PathCut
GeneralGraph → NashWilliams → NashWilliams2 → [NashWilliams3] → [NashWilliams4]
NashWilliams{,4} + FlowCount → [JKEvenCover] → [JKPacking] ┐
NashWilliams → [JKContraction]                             ├→ [JaegerKilpatrick]
{[CubicTheorem], CubicEvenCover, CycleDecomposition, Expansion, PathCut, [JaegerKilpatrick]} → [Main] → [Audit]
```

(Bracketed = vendored.) Removing any vendored file therefore also takes out its
vendored dependents, and — because `Main.lean` is vendored — **removing any of
them forces `Main.lean` to be re-derived too**, i.e. the headline theorem
`cycleDoubleCover_of_bridgeless` would revert to `axiomatized` in the gallery
until the replacement lands.

Replacement route per file, cheapest first:

| File | Replacement plan | Effort |
|------|------------------|--------|
| `Audit.lean` | Delete or rewrite from scratch: it is a list of `#print axioms` commands over *our* declaration names. No upstream expression needs replacing. | Trivial |
| `CubicTheorem.lean` | Re-derive: three declarations whose proofs are three-line assemblies of already-clean-room machinery (`CubicBridge`, `CubicEvenCover`, `FlowCount`). Follow the style of `CubicEvenCover.lean`. | Hours |
| `Main.lean` | Re-derive: an assembly file. The statement it proves is fixed by `Proofs/CycleDoubleCover.lean` (our own statement layer), and the adaptation notes in its header (universe handling, inlined `let`s) already describe a non-upstream shape. | Hours |
| `JaegerKilpatrickEvenCover.lean` | Re-derive: two lemmas (flow-from-three-even-sets, even superset of a spanning-tree complement). Both are built from our clean-room `FlowCount.lean` primitives (`hasCycleCorrection_of_integerPath`, `isFlow_sum_int`, `isFlow_intCast_f2`), so only the two assembly arguments need writing. | Days |
| `JaegerKilpatrickPacking.lean` | Re-derive: classical doubling + double-counting + an application of our clean-room `nashWilliamsTutte`. The upstream-specific `simp` idioms are already replaced here by `mem_crossingEdges`/`mem_cut` characterisations, so the file is half ours already. | Days |
| `JaegerKilpatrickContraction.lean` | Two parts. (a) The vendored `sum_conservation_eq_cut` + `sum_endpoint_indicator` are **already superseded**: our clean-room `FlowCount.lean` proves the same computation through its own `divergence`/`cut` API — drop the vendored copies and route through it. (b) The contraction/two-cut lifting argument must be re-derived; model it on the clean-room `Expansion.lean`, which does comparable graph-surgery transport. | Days |
| `JaegerKilpatrick.lean` | Re-derive: component decomposition plus the final 8-flow assembly, once segments 1–3 exist. Declaration names must be preserved so `Main` keeps compiling. | Days |
| `NashWilliams4.lean` | Re-derive Kaiser's counting equality and the tree-packing endgame, following the clean-room method of `NashWilliams.lean`/`NashWilliams2.lean` (parts 1–2 of the same upstream file), which already deviate from upstream in statement-preserving ways. | Weeks |
| `NashWilliams3.lean` | Re-derive the local-exchange layer (~1,180 upstream lines: walk transport, the `*_exchange_of_path_edge` family, colour-swap component counting). The hardest slice; same method as above. | Weeks |

Sequencing if a removal is ordered: work **bottom-up** (`Audit`, `Main`,
`CubicTheorem` first — they are cheap and unblock a green build with the rest
temporarily `sorry`-free-but-conditional), then Jaeger–Kilpatrick segments 1→4,
then `NashWilliams3`→`4`. While any vendored file is deleted and not yet
replaced, the gallery entry must be flipped back to `axiomatized` with the gap
disclosed — never left claiming `verified`.

## 5. What to do when the license question resolves

1. **A permissive license lands upstream** (`gh api repos/openai/cdc-lean/license`
   stops returning 404): update §1 with the license and the date, replace the
   "risk acceptance" paragraph in each of the 9 vendored headers with a citation
   of the actual license (keeping attribution), note the license in
   `src/data/proofs/cycle-double-cover/meta.json` and
   `src/data/proofs/cycle-double-cover-port/meta.json`, and close #43638.
2. **A restrictive license lands, or upstream objects**: execute §4 in the order
   given, one PR per file, flipping the gallery to `axiomatized` for the
   duration.
3. **Still nothing**: re-run the §1 checks, append a row to the history table,
   and leave #43638 open. This is the expected outcome of most cycles.

## 6. Gallery framing (must not drift)

`src/data/proofs/cycle-double-cover/` and
`src/data/proofs/cycle-double-cover-port/` describe the provenance in
`meta.json` → `assumptions` and in their header annotations. The required
framing: *upstream carries no license file, so default copyright applies; the
vendored files are here under the operator risk acceptance recorded on #37507,
not under a license.* Audited 2026-09-22 (#43638): no "unlicensed therefore
free" wording present.
