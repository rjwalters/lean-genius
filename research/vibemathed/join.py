#!/usr/bin/env python3
"""Join the VibeMathed dataset against this repo's Erdos-problem gallery.

Source: research/vibemathed/dataset-snapshot.json, a snapshot of
GET https://vibemathed.com/api/dataset (CC BY 4.0, see README.md in this
directory for attribution). VibeMathed: https://vibemathed.com/ ·
source code: https://github.com/mrconter1/vibemathed

Join key: the dataset's `problemNumber` field for entries whose `slug`
starts with "erdos-" (VibeMathed's own Erdos-problem numbering matches
erdosproblems.com, the same numbering this repo's `erdos-N` gallery slugs
and `meta.erdosNumber` field use) against this repo's
`src/data/proofs/erdos-<N>/meta.json` base entries (the canonical article
for problem N; `erdos-<N>-oq-*`/`-wip-*`/`-incomplete-*` variant slugs are
sub-pages of the same problem and are not used as separate join targets).

Note per issue #43622: VibeMathed's own slugs are NOT directly compatible
with ours (e.g. their `erdos-131-non-dividing-sets` vs our bare
`erdos-131`), so this is a numeric join on `problemNumber`, not a string
join on `slug`.

Writes research/vibemathed/join-results.json (machine-readable) and prints
a summary to stdout. Does NOT modify any src/data/proofs/*/meta.json file
(out of scope per the issue -- discovery/triage only).
"""

import glob
import json
import re
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
DATASET_PATH = REPO_ROOT / "research/vibemathed/dataset-snapshot.json"
GALLERY_GLOB = str(REPO_ROOT / "src/data/proofs/erdos-*/meta.json")
OUT_PATH = REPO_ROOT / "research/vibemathed/join-results.json"

BASE_SLUG_RE = re.compile(r".*/erdos-(\d+)/meta\.json$")

# Gallery erdosProblemStatus values that mean "we still consider this open"
# (per repo status vocabulary observed across src/data/proofs/erdos-*/meta.json).
GALLERY_OPEN_VALUES = {"open", None}


def load_dataset() -> dict:
    with open(DATASET_PATH) as f:
        return json.load(f)


def read_gallery_fields(meta_json: dict) -> dict:
    """Fields can live at the top level or nested under `meta` -- both
    patterns occur in this repo (see CLAUDE.md Axiom Integrity Policy /
    prior mechanic-agent scans), so check nested first, fall back to
    top-level."""
    top = meta_json
    nested = meta_json.get("meta", {}) or {}
    return {
        "status": nested.get("status") or top.get("status"),
        "badge": nested.get("badge") or top.get("badge"),
        "axiomCount": nested.get("axiomCount", top.get("axiomCount")),
        "sorries": nested.get("sorries", top.get("sorries")),
        "erdosProblemStatus": nested.get("erdosProblemStatus")
        or top.get("erdosProblemStatus"),
        "title": top.get("title"),
    }


def load_gallery_base_entries() -> dict[int, dict]:
    """erdosNumber -> info about the canonical `erdos-<N>` gallery entry."""
    out = {}
    for path in glob.glob(GALLERY_GLOB):
        m = BASE_SLUG_RE.match(path)
        if not m:
            continue  # skip -oq-*, -wip-*, -incomplete-* variant slugs
        n = int(m.group(1))
        with open(path) as f:
            meta_json = json.load(f)
        info = read_gallery_fields(meta_json)
        info["slug"] = f"erdos-{n}"
        info["path"] = str(Path(path).relative_to(REPO_ROOT))
        out[n] = info
    return out


def is_vm_erdos_entry(problem: dict) -> bool:
    return problem.get("slug", "").startswith("erdos-") and problem.get(
        "problemNumber"
    ) is not None


def main() -> None:
    dataset = load_dataset()
    problems = dataset["problems"]
    vm_erdos = [p for p in problems if is_vm_erdos_entry(p)]

    # A small number of VibeMathed entries credit Erdos in `posedBy` but have
    # no numeric `problemNumber` and a non-"erdos-" slug -- they cannot be
    # numerically joined against our gallery, so they're reported separately
    # rather than silently dropped.
    vm_erdos_unnumbered = [
        p
        for p in problems
        if not is_vm_erdos_entry(p)
        and "erdos" in (p.get("posedBy") or "").lower().replace("ő", "o")
    ]

    gallery = load_gallery_base_entries()

    vm_by_number: dict[int, list] = {}
    for p in vm_erdos:
        vm_by_number.setdefault(p["problemNumber"], []).append(p)

    matched_numbers = sorted(set(vm_by_number) & set(gallery))
    vm_only_numbers = sorted(set(vm_by_number) - set(gallery))
    gallery_only_numbers = sorted(set(gallery) - set(vm_by_number))

    # Two tiers, kept separate so the report doesn't overclaim a discrepancy:
    #
    # Tier 1 (high confidence): our own `erdosProblemStatus` field -- the
    # signal this repo uses specifically to track whether *the underlying
    # Erdos problem* is open -- still says "open" (or is unset) while
    # VibeMathed calls it resolved. This is the direct match for the issue's
    # "our gallery still says open" checklist item.
    #
    # Tier 2 (context only, NOT a discrepancy by itself): our
    # `erdosProblemStatus` already agrees the problem is solved/proved, but
    # our formalization `status` is still "axiomatized". Per this repo's
    # Axiom Integrity Policy, "axiomatized" is the *expected* status for
    # many legitimately-resolved entries (assumption-carrying proofs,
    # native_decide-based results, or problems we haven't independently
    # re-verified) -- so this tier is reported for awareness only, not as a
    # status-drift claim.
    resolved_but_gallery_open = []
    resolved_gallery_agrees_but_axiomatized = []
    for n in matched_numbers:
        g = gallery[n]
        for vp in vm_by_number[n]:
            if vp.get("resolution") != "resolved":
                continue
            row = {
                "erdosNumber": n,
                "vmSlug": vp["slug"],
                "vmName": vp.get("name"),
                "vmResolution": vp.get("resolution"),
                "vmSolveType": vp.get("solveType"),
                "vmVerification": vp.get("verification"),
                "vmSolveDate": vp.get("solveDate"),
                "vmSourceUrl": vp.get("sourceUrl"),
                "vmResultNote": vp.get("resultNote"),
                "gallerySlug": g["slug"],
                "galleryTitle": g["title"],
                "galleryStatus": g["status"],
                "galleryBadge": g["badge"],
                "galleryErdosProblemStatus": g["erdosProblemStatus"],
            }
            if g["erdosProblemStatus"] in GALLERY_OPEN_VALUES:
                resolved_but_gallery_open.append(row)
            elif g["status"] == "axiomatized":
                resolved_gallery_agrees_but_axiomatized.append(row)

    partial_candidate_no_gallery = []
    for n in vm_only_numbers:
        for vp in vm_by_number[n]:
            if vp.get("resolution") in ("partial", "candidate"):
                partial_candidate_no_gallery.append(
                    {
                        "erdosNumber": n,
                        "vmSlug": vp["slug"],
                        "vmName": vp.get("name"),
                        "vmResolution": vp.get("resolution"),
                        "vmVerification": vp.get("verification"),
                        "vmSolveDate": vp.get("solveDate"),
                        "vmSourceUrl": vp.get("sourceUrl"),
                    }
                )

    resolution_counts: dict[str, int] = {}
    for p in vm_erdos:
        r = p.get("resolution")
        resolution_counts[r] = resolution_counts.get(r, 0) + 1

    report = {
        "vmDatasetGenerated": dataset.get("generated"),
        "vmDatasetTotalCount": dataset.get("count"),
        "vmErdosTaggedEntries": len(vm_erdos),
        "vmErdosUniqueNumbers": len(vm_by_number),
        "vmErdosPosedButUnnumbered": [
            {"slug": p.get("slug"), "name": p.get("name"), "posedBy": p.get("posedBy")}
            for p in vm_erdos_unnumbered
        ],
        "vmErdosResolutionCounts": resolution_counts,
        "galleryErdosBaseEntries": len(gallery),
        "matchedNumberCount": len(matched_numbers),
        "vmOnlyNumberCount": len(vm_only_numbers),
        "galleryOnlyNumberCount": len(gallery_only_numbers),
        "mappingRatePctOfVmErdosNumbers": round(
            100 * len(matched_numbers) / len(vm_by_number), 1
        )
        if vm_by_number
        else 0.0,
        "mappingRatePctOfGalleryErdosNumbers": round(
            100 * len(matched_numbers) / len(gallery), 1
        )
        if gallery
        else 0.0,
        "resolvedButGalleryOpenCount": len(resolved_but_gallery_open),
        "resolvedButGalleryOpen": resolved_but_gallery_open,
        "resolvedGalleryAgreesButAxiomatizedCount": len(
            resolved_gallery_agrees_but_axiomatized
        ),
        "resolvedGalleryAgreesButAxiomatized": resolved_gallery_agrees_but_axiomatized,
        "partialCandidateNoGalleryCount": len(partial_candidate_no_gallery),
        "partialCandidateNoGallery": partial_candidate_no_gallery,
    }

    with open(OUT_PATH, "w") as f:
        json.dump(report, f, indent=2)

    summary = {k: v for k, v in report.items() if not isinstance(v, list)}
    print(json.dumps(summary, indent=2))
    print(f"\nWrote full results to {OUT_PATH.relative_to(REPO_ROOT)}")


if __name__ == "__main__":
    main()
