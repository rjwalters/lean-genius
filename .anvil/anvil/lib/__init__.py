"""Framework primitives shared across Anvil skills.

Public modules:

- ``review_schema``: the canonical typed schema for ``_review.json`` critic
  outputs. See ``anvil/lib/README.md`` for the field-by-field reference.
- ``critics``: discovery, loading, aggregation, and verdict computation for
  the "N parallel critics, one reviser" primitive.
- ``cite``: identifier parsing (DOI/arXiv), Crossref / arXiv resolution,
  deterministic BibTeX key generation, and idempotent ``refs.bib``
  writing. See ``anvil/lib/snippets/cite.md`` for the on-disk convention.
- ``convergence``: ``check_stable`` and ``decide_termination`` — pure
  functions for the multi-iteration termination decision (threshold met /
  critical flag / max-iterations / stalled). Produces ``Verdict.STALLED``
  when successive revisions have plateaued.
- ``revise_consistency``: stale-token sweep for the ``*-revise``
  lifecycle. Compares old- vs new-source priced-number tokens and flags
  companion files (figure scripts, speaker-notes, CSVs) that still
  reference a token the new source has fully dropped. Wired into
  ``deck-revise`` step 9.5; available to every other ``*-revise``
  command on adoption. See ``anvil/lib/snippets/critics.md``'s
  "Deterministic-checks family" section.
- ``scorecard_check``: deterministic scorecard arithmetic validation
  (issue #392). ``check_scorecard`` is a pure function of
  ``(Review, rubric stamps)`` — weights sum to the effective pool,
  per-dim scores within bounds, declared total equals Σ per-dim,
  advance consistent with threshold + critical flags;
  ``check_review_dir`` is the filesystem convenience that loads a
  critic sibling via ``critics.load_review`` and reads the issue-#346
  stamps from ``_meta.json``. Write-time consumers hard-fail on
  findings (memo-review step 7b, the pilot); read-time consumers
  treat a finding-bearing sidecar's verdict as advisory.
- ``sidecar``: directory-level atomic writes for critic sibling dirs.
  ``staged_sidecar`` is a context manager that writes files into a
  leading-dot staging dir and renames atomically on clean completion;
  ``cleanup_one_staging`` is the per-critic entry-step sweep that
  removes only the staging dir corresponding to a single ``final_dir``
  (parallel-safe; the load-bearing surface for fan-out workflows —
  issue #376); ``cleanup_stale_staging`` is the operator-facing
  portfolio-wide sweep that removes ALL ``.*.tmp/`` leftovers under a
  parent (maintenance use only — see issue #376 for why it is unsafe
  from per-critic entry steps). See issue #350 and
  ``anvil/lib/snippets/progress.md`` §"Crash recovery contract".
"""

from anvil.lib.cite import (
    BibRecord,
    CiteResolutionError,
    Identifier,
    IdentifierKind,
    UnsupportedIdentifierError,
    bib_key,
    cite,
    parse_identifier,
    resolve,
)
from anvil.lib.convergence import (
    TERMINATION_CRITICAL_FLAG,
    TERMINATION_MAX_ITERATIONS,
    TERMINATION_STALLED,
    TERMINATION_THRESHOLD_MET,
    check_stable,
    decide_termination,
)
from anvil.lib.revise_consistency import (
    DEFAULT_COMPANION_GLOBS,
    DEFAULT_IGNORE_TOKENS,
    DEFAULT_TOKEN_SET,
    ConsistencyResult,
    StaleFinding,
    TokenSet,
    sweep,
)
from anvil.lib.rubric import (
    CriticalFlagDefinition,
    Rubric,
    RubricDimension,
    discover_venue_rubric,
    load_rubric,
)
# NOTE: the ``sidecar`` primitives are re-exported *lazily* via the PEP 562
# module-level ``__getattr__`` below rather than with an eager
# ``from anvil.lib.sidecar import (...)`` here. The eager form registers
# ``anvil.lib.sidecar`` in ``sys.modules`` as an ordinary submodule during
# package init, which makes ``python -m anvil.lib.sidecar`` emit a
# ``runpy`` ``RuntimeWarning`` ("found in sys.modules after import of package
# 'anvil.lib', but prior to execution") on every invocation — noise in every
# critic log across every skill (issue #673). The lazy re-export preserves the
# public contract (``from anvil.lib import staged_sidecar`` etc., documented in
# CHANGELOG #350 and guarded by
# ``test_sidecar_reexported_from_anvil_lib_package``) while keeping
# ``anvil.lib.sidecar`` out of ``sys.modules`` until first attribute access.
_SIDECAR_LAZY_ATTRS = frozenset(
    {
        "STAGING_SUFFIX",
        "SidecarIncompleteError",
        "cleanup_one_staging",
        "cleanup_stale_staging",
        "staged_sidecar",
        "staging_path_for",
    }
)


def __getattr__(name: str) -> object:
    """Lazily resolve the sidecar re-exports (PEP 562).

    Importing ``anvil.lib.sidecar`` eagerly at package-init time triggers a
    ``runpy`` ``RuntimeWarning`` on ``python -m anvil.lib.sidecar`` (issue
    #673). Deferring the import to first attribute access keeps the module out
    of ``sys.modules`` until something actually needs it, so the ``-m``
    invocation stays warning-free while the public re-export contract is
    preserved.
    """
    if name in _SIDECAR_LAZY_ATTRS:
        from anvil.lib import sidecar as _sidecar

        return getattr(_sidecar, name)
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")


def __dir__() -> list[str]:
    """Include the lazily re-exported sidecar names in ``dir(anvil.lib)``."""
    return sorted(set(globals()) | _SIDECAR_LAZY_ATTRS)


__all__ = [
    "BibRecord",
    "CiteResolutionError",
    "ConsistencyResult",
    "CriticalFlagDefinition",
    "DEFAULT_COMPANION_GLOBS",
    "DEFAULT_IGNORE_TOKENS",
    "DEFAULT_TOKEN_SET",
    "Identifier",
    "IdentifierKind",
    "Rubric",
    "RubricDimension",
    "STAGING_SUFFIX",
    "SidecarIncompleteError",
    "StaleFinding",
    "TERMINATION_CRITICAL_FLAG",
    "TERMINATION_MAX_ITERATIONS",
    "TERMINATION_STALLED",
    "TERMINATION_THRESHOLD_MET",
    "TokenSet",
    "UnsupportedIdentifierError",
    "bib_key",
    "check_stable",
    "cite",
    "cleanup_one_staging",
    "cleanup_stale_staging",
    "decide_termination",
    "discover_venue_rubric",
    "load_rubric",
    "parse_identifier",
    "resolve",
    "staged_sidecar",
    "staging_path_for",
    "sweep",
]
