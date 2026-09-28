"""Cluster boundaries + bucket dispatch for `anvil:project-scout` (issue #407).

The cluster-boundary algorithm, locked at curation: **evidence nominates
project roots; BRIEF anchors merging; each cluster classifies
independently at its root.**

- *Nomination*: each family site nominates a candidate project root —
  slug-nested families (``<project>/<slug>/<slug>.N``, i.e.
  ``parent.name == stem``) nominate the grandparent; flat families
  nominate the parent. BRIEF sites and ``.anvil.json`` sites nominate
  themselves (an ``.anvil.json`` carried by a thread-root sibling of a
  flat family — the #382 deck shape — is suppressed; ``inventory_project``
  already accounts for it at the project root).
- *Merge*: a candidate root that is a strict descendant of another
  candidate root **carrying a project BRIEF** merges into the nearest
  such BRIEF-bearing ancestor (bounded by the scan root). Descendants of
  BRIEF-less candidates do NOT merge — ``project-migrate`` is handed one
  project dir at a time and ``inventory_project`` only sees root-level
  classic groups + one level of nesting.
- *Dispatch* (precedence order):

  1. **FOREIGN_GRAMMAR** if the guard fires — BEFORE any ``detect_shape``
     delegation (see ``foreign.py`` for the verified misclassification
     hazard). Mixed roots (foreign + clean families) also bucket foreign.
  2. Delegate ``inventory_project`` + ``_classify`` from the promoted
     ``anvil/lib/project_detect.py``: ``FULLY_MIGRATED`` →
     ALREADY_MIGRATED; ``PRE_283_CLASSIC`` with ``is_bare`` (the #408
     sub-state — NOT reimplemented here) → BARE_THREADS;
     ``PRE_283_CLASSIC`` (non-bare) / ``POST_283_ANVIL_JSON`` →
     LEGACY_MIGRATABLE; ``UNKNOWN`` → diagnostic note, cluster dropped
     (its files flow through the loose-file path — counted, never lost).
  3. Document-ish loose files → LOOSE_DOCUMENTS.
  4. Everything else → NOT_DOCUMENT (counted; listed under ``--verbose``).

Recommended-action strings name real commands that exist at merge time:
BARE_THREADS gets plain ``/anvil:project-migrate <dir>`` (BRIEF synthesis
is automatic when ``is_bare``, post-#411 — there is no
``--synthesize-brief`` flag); LOOSE_DOCUMENTS gets
``/anvil:project-migrate --enroll <file>`` (#406/#414).

Strictly read-only.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

from anvil.lib.project_detect import (
    Shape,
    _INFRASTRUCTURE_DIRS,
    _VERSION_DIR_RE,
    _classify,
    inventory_project,
)

from .docish import (
    CONFIDENCE_LOW,
    VERDICT_DOCUMENT,
    build_doc_context,
    classify_document,
)
from .foreign import ForeignFamily, find_foreign_families
from .walk import FamilySite, WalkResult


BUCKET_ALREADY_MIGRATED = "ALREADY_MIGRATED"
BUCKET_LEGACY_MIGRATABLE = "LEGACY_MIGRATABLE"
BUCKET_BARE_THREADS = "BARE_THREADS"
BUCKET_LOOSE_DOCUMENTS = "LOOSE_DOCUMENTS"
BUCKET_FOREIGN_GRAMMAR = "FOREIGN_GRAMMAR"

# Directory parts that mark a file as CLAIMED by its enclosing cluster:
# version dirs (`<stem>.<N>`) and critic sidecars (`<stem>.<N>.<tag>`,
# foreign `-vN` variants included) — anything carrying a `.<digits>`
# segment.
_CLAIMED_PART_RE = re.compile(r"^.+\.\d+(\..+)?$")

_BARE_NOTE = (
    "bare shape — BRIEF will be synthesized; dry-run shows the proposed "
    "BRIEF"
)
_LOW_CONFIDENCE_NOTE = "verify before enrolling"
_OUTSIDE_CLUSTER_NOTE = (
    "enroll will propose a new project root at the file's parent"
)


@dataclass
class LooseDocument:
    path: Path
    rel: str
    enclosing_cluster: Optional[str]  # rel path of cluster root, or None
    confidence: str
    signals: List[str] = field(default_factory=list)
    recommended_command: Optional[str] = None
    notes: List[str] = field(default_factory=list)


@dataclass
class NotDocumentFile:
    path: Path
    rel: str
    signals: List[str] = field(default_factory=list)


@dataclass
class Cluster:
    root: Path
    rel: str
    bucket: str
    detected_shape: Optional[str] = None
    is_bare: bool = False
    threads: List[dict] = field(default_factory=list)
    recommended_command: Optional[str] = None
    confidence: str = "high"
    evidence: List[str] = field(default_factory=list)
    notes: List[str] = field(default_factory=list)
    foreign_families: List[ForeignFamily] = field(default_factory=list)
    loose_documents: List[LooseDocument] = field(default_factory=list)
    # Internal: dir names treated as thread roots for the claim check.
    _thread_root_names: frozenset = frozenset()


@dataclass
class Coverage:
    dirs_scanned: int = 0
    candidate_files: int = 0
    in_clusters: int = 0
    loose_classified: int = 0
    not_document: int = 0
    pruned_subtrees: int = 0

    @property
    def identity_holds(self) -> bool:
        return self.candidate_files == (
            self.in_clusters + self.loose_classified + self.not_document
        )


@dataclass
class Classification:
    root: Path
    clusters: List[Cluster] = field(default_factory=list)
    loose_documents: List[LooseDocument] = field(default_factory=list)
    not_document_files: List[NotDocumentFile] = field(default_factory=list)
    diagnostics: List[str] = field(default_factory=list)
    coverage: Coverage = field(default_factory=Coverage)


def _rel(path: Path, root: Path) -> str:
    if path == root:
        return "."
    return path.relative_to(root).as_posix()


def _under(path: Path, ancestor: Path) -> bool:
    try:
        path.relative_to(ancestor)
        return True
    except ValueError:
        return False


# ---------------------------------------------------------------------------
# Nomination + merge
# ---------------------------------------------------------------------------


def _nominate(
    wr: WalkResult,
) -> Tuple[Dict[Path, List[str]], Dict[Path, List[FamilySite]]]:
    """Pass 2: evidence nominates candidate project roots."""
    nominations: Dict[Path, List[str]] = {}
    fams: Dict[Path, List[FamilySite]] = {}

    # Family stems per directory (for the .anvil.json thread-root
    # suppression below).
    stems_at: Dict[Path, set] = {}
    for fam in wr.family_sites:
        stems_at.setdefault(fam.parent_dir, set()).add(fam.stem)

    for fam in wr.family_sites:
        if fam.parent_dir != wr.root and fam.parent_dir.name == fam.stem:
            # Slug-nested thread (<project>/<slug>/<slug>.N) — the
            # project root is the grandparent.
            cand = fam.parent_dir.parent
            if not _under(cand, wr.root):
                cand = wr.root
            kind = "slug-nested"
        else:
            cand = fam.parent_dir
            kind = "flat"
        nominations.setdefault(cand, []).append(
            f"{kind} version-dir family `{fam.stem}` "
            f"(versions {fam.version_numbers}) at "
            f"`{_rel(fam.parent_dir, wr.root)}`"
        )
        fams.setdefault(cand, []).append(fam)

    for b in wr.brief_sites:
        nominations.setdefault(b, []).append("project `BRIEF.md`")

    for a in wr.anvil_json_sites:
        # Suppress the #382 thread-root carrier: `<project>/<slug>/`
        # holding `.anvil.json` as a sibling of flat `<slug>.N/` dirs —
        # inventory_project(<project>) already records it.
        if a != wr.root and a.name in stems_at.get(a.parent, set()):
            continue
        nominations.setdefault(a, []).append("`.anvil.json`")

    return nominations, fams


def _merge(
    wr: WalkResult,
    nominations: Dict[Path, List[str]],
    fams: Dict[Path, List[FamilySite]],
) -> Tuple[Dict[Path, List[str]], Dict[Path, List[FamilySite]]]:
    """Pass 3: merge candidates upward into BRIEF-bearing ancestors."""
    brief_set = set(wr.brief_sites)
    merged_noms: Dict[Path, List[str]] = {}
    merged_fams: Dict[Path, List[FamilySite]] = {}

    for cand in sorted(nominations, key=lambda p: (len(p.parts), str(p))):
        target = cand
        for anc in cand.parents:
            if anc in brief_set and anc in nominations:
                target = anc
                break
            if anc == wr.root:
                break
        if target != cand:
            merged_noms.setdefault(target, []).append(
                f"merged descendant candidate `{_rel(cand, wr.root)}` "
                f"(BRIEF-bearing ancestor)"
            )
        merged_noms.setdefault(target, []).extend(nominations[cand])
        merged_fams.setdefault(target, []).extend(fams.get(cand, []))

    return merged_noms, merged_fams


# ---------------------------------------------------------------------------
# Per-cluster bucket dispatch
# ---------------------------------------------------------------------------


def _thread_versions(version_dirs: Sequence[Path]) -> List[int]:
    out: List[int] = []
    for vd in version_dirs:
        m = _VERSION_DIR_RE.match(vd.name)
        if m is not None:
            out.append(int(m.group("num")))
    return sorted(out)


def _classify_cluster(
    root: Path,
    scan_root: Path,
    evidence: List[str],
    families: List[FamilySite],
    diagnostics: List[str],
) -> Optional[Cluster]:
    """Bucket one cluster root. Returns None for UNKNOWN (diagnostic)."""
    rel = _rel(root, scan_root)
    thread_root_names = frozenset(
        {f.stem for f in families}
        | {
            f.parent_dir.name
            for f in families
            if f.parent_dir != root and f.parent_dir.name == f.stem
        }
    )

    # 1. Foreign-grammar guard — BEFORE trusting detect's verdict.
    foreign = find_foreign_families(
        [
            (f.stem, f.version_numbers, f.sidecar_dir_names)
            for f in families
        ]
    )
    if foreign:
        clean = sorted(
            {f.stem for f in families} - {ff.stem for ff in foreign}
        )
        notes = [
            "report-only: foreign version grammar — migration would "
            "mangle this cluster; not recommending any command"
        ]
        if clean:
            notes.append(
                "mixed root: clean families "
                + ", ".join(f"`{s}`" for s in clean)
                + " coexist with foreign ones; a migrate here would "
                "partially mangle the root, so the whole cluster is "
                "report-only"
            )
        return Cluster(
            root=root,
            rel=rel,
            bucket=BUCKET_FOREIGN_GRAMMAR,
            recommended_command=None,
            confidence="high",
            evidence=sorted(evidence),
            notes=notes,
            foreign_families=foreign,
            _thread_root_names=thread_root_names,
        )

    # 2. Delegate to the promoted detector.
    inv = inventory_project(root)
    shape = _classify(inv)
    threads = [
        {"slug": t.slug, "versions": _thread_versions(t.version_dirs)}
        for t in inv.threads
    ]
    threads.sort(key=lambda t: t["slug"])

    if shape is Shape.FULLY_MIGRATED:
        return Cluster(
            root=root,
            rel=rel,
            bucket=BUCKET_ALREADY_MIGRATED,
            detected_shape=shape.value,
            threads=threads,
            recommended_command=None,
            confidence="high",
            evidence=sorted(evidence),
            notes=["nothing to do"],
            _thread_root_names=thread_root_names
            | frozenset(t["slug"] for t in threads),
        )
    if shape is Shape.PRE_283_CLASSIC and inv.is_bare:
        return Cluster(
            root=root,
            rel=rel,
            bucket=BUCKET_BARE_THREADS,
            detected_shape=shape.value,
            is_bare=True,
            threads=threads,
            recommended_command=f"/anvil:project-migrate {rel}",
            confidence="high",
            evidence=sorted(evidence),
            notes=[_BARE_NOTE],
            _thread_root_names=thread_root_names,
        )
    if shape in (Shape.PRE_283_CLASSIC, Shape.POST_283_ANVIL_JSON):
        return Cluster(
            root=root,
            rel=rel,
            bucket=BUCKET_LEGACY_MIGRATABLE,
            detected_shape=shape.value,
            threads=threads,
            recommended_command=f"/anvil:project-migrate {rel}",
            confidence="high",
            evidence=sorted(evidence),
            _thread_root_names=thread_root_names,
        )

    # UNKNOWN — shouldn't occur for a nominated root; never dropped
    # silently. The candidate files under it flow through the
    # loose-file path so coverage accounting stays whole.
    diagnostics.append(
        f"nominated root `{rel}` classified UNKNOWN by detect — "
        f"evidence was: {'; '.join(sorted(evidence))}. Its files are "
        f"classified individually below."
    )
    return None


# ---------------------------------------------------------------------------
# File assignment
# ---------------------------------------------------------------------------


def _is_claimed(file: Path, cluster: Cluster) -> bool:
    """True iff ``file`` is claimed by cluster machinery (not loose).

    Claimed: anything under a version dir or critic sidecar (any
    ``.<digits>``-bearing path part), under an infrastructure dir
    (``research`` / ``refs`` / ``build`` / ``_archive``) or ``SHARE``,
    under a thread-root dir, or the ``BRIEF.md`` config marker itself.
    """
    if file.name == "BRIEF.md":
        return True
    parts = file.relative_to(cluster.root).parts[:-1]
    for part in parts:
        if _CLAIMED_PART_RE.match(part):
            return True
        if part in _INFRASTRUCTURE_DIRS or part == "SHARE":
            return True
        if part in cluster._thread_root_names:
            return True
    return False


def _enclosing_cluster(
    file: Path, clusters: List[Cluster]
) -> Optional[Cluster]:
    """Deepest cluster whose root is an ancestor of (or equals) the file's dir."""
    best: Optional[Cluster] = None
    for c in clusters:
        if _under(file, c.root):
            if best is None or len(c.root.parts) > len(best.root.parts):
                best = c
    return best


# ---------------------------------------------------------------------------
# Top-level entry
# ---------------------------------------------------------------------------


def classify_tree(wr: WalkResult) -> Classification:
    """Pass 2-4: nominate, merge, dispatch, and account for every file."""
    out = Classification(root=wr.root)
    out.coverage.dirs_scanned = wr.dirs_scanned
    out.coverage.pruned_subtrees = len(wr.pruned_subtrees)
    out.coverage.candidate_files = len(wr.candidate_files)

    nominations, fams = _nominate(wr)
    nominations, fams = _merge(wr, nominations, fams)

    clusters: List[Cluster] = []
    for root in sorted(nominations, key=lambda p: str(p)):
        c = _classify_cluster(
            root=root,
            scan_root=wr.root,
            evidence=nominations[root],
            families=fams.get(root, []),
            diagnostics=out.diagnostics,
        )
        if c is not None:
            clusters.append(c)

    # ---- candidate-file accounting --------------------------------------
    outside_loose_by_dir: Dict[Path, List[LooseDocument]] = {}
    for f in wr.candidate_files:
        enclosing = _enclosing_cluster(f, clusters)
        if enclosing is not None and _is_claimed(f, enclosing):
            out.coverage.in_clusters += 1
            continue
        # Loose candidate — classify (read the text here; the classifier
        # itself is pure).
        try:
            text = f.read_text(encoding="utf-8", errors="replace")
        except OSError:
            text = ""
        ctx = build_doc_context(f, wr.root)
        verdict = classify_document(f.name, text, ctx)
        rel = _rel(f, wr.root)
        if verdict.verdict != VERDICT_DOCUMENT:
            out.coverage.not_document += 1
            out.not_document_files.append(
                NotDocumentFile(path=f, rel=rel, signals=verdict.signals)
            )
            continue
        out.coverage.loose_classified += 1
        notes: List[str] = []
        if verdict.confidence == CONFIDENCE_LOW:
            command = None
            notes.append(_LOW_CONFIDENCE_NOTE)
        else:
            command = f"/anvil:project-migrate --enroll {rel}"
        if enclosing is None:
            notes.append(_OUTSIDE_CLUSTER_NOTE)
        doc = LooseDocument(
            path=f,
            rel=rel,
            enclosing_cluster=(
                enclosing.rel if enclosing is not None else None
            ),
            confidence=verdict.confidence,
            signals=verdict.signals,
            recommended_command=command,
            notes=notes,
        )
        out.loose_documents.append(doc)
        if enclosing is not None:
            enclosing.loose_documents.append(doc)
        else:
            outside_loose_by_dir.setdefault(f.parent, []).append(doc)

    # ---- standalone LOOSE_DOCUMENTS clusters (outside-any-cluster files,
    # grouped by directory) -------------------------------------------------
    for d in sorted(outside_loose_by_dir, key=lambda p: str(p)):
        docs = outside_loose_by_dir[d]
        notes = []
        enrollable = [
            doc for doc in docs if doc.recommended_command is not None
        ]
        if len(enrollable) > 1:
            suffixes = sorted({doc.path.suffix for doc in enrollable})
            for suffix in suffixes:
                notes.append(
                    "batch form: /anvil:project-migrate --enroll "
                    f"{_rel(d, wr.root)}/*{suffix}"
                )
        clusters.append(
            Cluster(
                root=d,
                rel=_rel(d, wr.root),
                bucket=BUCKET_LOOSE_DOCUMENTS,
                recommended_command=None,
                confidence="high",
                evidence=[
                    f"{len(docs)} loose document candidate(s) grouped "
                    f"by directory"
                ],
                notes=notes,
                loose_documents=docs,
            )
        )

    clusters.sort(key=lambda c: (c.rel, c.bucket))
    out.clusters = clusters
    out.loose_documents.sort(key=lambda d: d.rel)
    out.not_document_files.sort(key=lambda d: d.rel)
    return out


__all__ = [
    "BUCKET_ALREADY_MIGRATED",
    "BUCKET_BARE_THREADS",
    "BUCKET_FOREIGN_GRAMMAR",
    "BUCKET_LEGACY_MIGRATABLE",
    "BUCKET_LOOSE_DOCUMENTS",
    "Classification",
    "Cluster",
    "Coverage",
    "LooseDocument",
    "NotDocumentFile",
    "classify_tree",
]
