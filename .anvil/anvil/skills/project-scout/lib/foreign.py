"""Foreign-grammar guard for `anvil:project-scout` (issue #407).

**Why this module exists — the empirically verified hazard.** The greedy
version-dir grammar (``project_detect._VERSION_DIR_RE``,
``^(?P<stem>.+)\\.(?P<num>\\d+)$``) happily matches the observed
in-the-wild foreign shape: ``Whitepaper.A.3`` matches with stem
``Whitepaper.A``, so ``detect_shape`` on such a tree returns
``PRE_283_CLASSIC`` — **not** ``UNKNOWN``. A scout that naively delegated
to ``detect_shape`` would bucket the cluster LEGACY_MIGRATABLE and
recommend a migrate that mangles it (the stems ``Whitepaper.A`` /
``Whitepaper.B`` violate the canonical slug grammar
``^[a-z0-9][a-z0-9-]*$``, and ``plan._iter_critic_siblings`` would rename
the ``.review-v2`` sidecars by prefix-match with no tag-grammar check).

Therefore: **this guard runs BEFORE any delegation to detect's verdict.**
A cluster with any foreign family buckets ``FOREIGN_GRAMMAR``
(report-only) — including mixed roots where clean families coexist with
foreign ones, because recommending migrate on a root the migration would
partially mangle is worse than recommending nothing.

Predicates (small, pure, unit-testable on names — no I/O):

(i)   a family stem containing ``.`` — canonical slugs never do. This
      also catches the numeric-tag corner (``memo.3.1`` groups as stem
      ``memo.3``, already a documented skip in
      ``anvil/lib/critics.py::discover_critics``).
(ii)  >= 2 stems differing only in a final dot-segment
      (``Whitepaper.A`` vs ``Whitepaper.B``) — reinforcing detail for
      the ``why`` string.
(iii) sidecar dirs whose tag matches ``^(review|audit|critic[^.]*)-v\\d+$``
      (the observed ``.review-v2`` / ``.audit-v2`` variants). The
      canonical critic-tag grammar is a single dot-free tag with no
      version suffix.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import List, Optional, Sequence, Tuple


# Versioned sidecar tags observed in the wild (`.review-v2`, `.audit-v2`).
# Canonical anvil tags are a bare word (`review`, `audit`, `<critic>`).
_FOREIGN_SIDECAR_TAG_RE = re.compile(r"^(review|audit|critic[^.]*)-v\d+$")

# Extract `<N>.<tag>` off the end of a sidecar dir name for a given stem.
def _sidecar_tag(stem: str, sidecar_name: str) -> Optional[str]:
    m = re.match(
        r"^" + re.escape(stem) + r"\.\d+\.(?P<tag>.+)$", sidecar_name
    )
    return m.group("tag") if m is not None else None


@dataclass
class ForeignFamily:
    """One family that fired the guard, with the operator-facing why."""

    stem: str
    versions: List[int] = field(default_factory=list)
    sidecars: List[str] = field(default_factory=list)
    why: List[str] = field(default_factory=list)


def find_foreign_families(
    families: Sequence[Tuple[str, Sequence[int], Sequence[str]]],
) -> List[ForeignFamily]:
    """Run the guard over a cluster's families.

    ``families`` is a sequence of ``(stem, version_numbers,
    sidecar_dir_names)`` tuples — names only, no paths, no I/O. Returns
    the (possibly empty) list of families that fired, each carrying a
    per-predicate ``why`` entry. An empty return means the cluster is
    safe to hand to ``detect_shape``.
    """
    stems = [stem for stem, _, _ in families]

    # Predicate (ii) precomputation: group dotted stems by their prefix
    # before the final dot-segment.
    prefix_groups: dict = {}
    for stem in stems:
        if "." in stem:
            prefix = stem.rsplit(".", 1)[0]
            prefix_groups.setdefault(prefix, []).append(stem)

    out: List[ForeignFamily] = []
    for stem, versions, sidecar_names in families:
        why: List[str] = []

        # (i) dotted stem.
        if "." in stem:
            why.append(
                f"stem `{stem}` contains `.` — canonical slugs are "
                f"dot-free (`^[a-z0-9][a-z0-9-]*$`)"
            )
            # (ii) sibling stems differing only in the final dot-segment.
            prefix = stem.rsplit(".", 1)[0]
            siblings = sorted(
                s for s in prefix_groups.get(prefix, []) if s != stem
            )
            if siblings:
                why.append(
                    f"stem `{stem}` differs only in its final "
                    f"dot-segment from {', '.join(f'`{s}`' for s in siblings)}"
                    f" — a `<name>.<letter>` series, not a slug family"
                )

        # (iii) versioned sidecar tags.
        foreign_sidecars: List[str] = []
        for name in sidecar_names:
            tag = _sidecar_tag(stem, name)
            if tag is not None and _FOREIGN_SIDECAR_TAG_RE.match(tag):
                foreign_sidecars.append(name)
        if foreign_sidecars:
            why.append(
                "versioned critic-sidecar tag(s) "
                + ", ".join(f"`{n}`" for n in sorted(foreign_sidecars))
                + " — canonical tags are a single dot-free word with no "
                "`-vN` suffix"
            )

        if why:
            out.append(
                ForeignFamily(
                    stem=stem,
                    versions=sorted(versions),
                    sidecars=sorted(sidecar_names),
                    why=why,
                )
            )
    out.sort(key=lambda f: f.stem)
    return out


__all__ = ["ForeignFamily", "find_foreign_families"]
