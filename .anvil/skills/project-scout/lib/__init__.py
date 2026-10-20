"""Skill-local lib for `anvil:project-scout` (issue #407).

Modules (composition order):

- ``walk``: pruned repo walk + glob filters + evidence collection
  (family sites, BRIEF sites, ``.anvil.json`` sites, candidate files,
  pruned subtrees for honest coverage).
- ``foreign``: the foreign-grammar guard — pure predicates over family
  stems / version names / sidecar names. MUST run before any
  ``detect_shape`` delegation (the greedy ``_VERSION_DIR_RE`` matches
  ``Whitepaper.A.3`` with stem ``Whitepaper.A``, so a naive delegation
  silently misclassifies foreign grammars as ``PRE_283_CLASSIC``).
- ``docish``: the conservative document-ish heuristic —
  ``classify_document`` is a pure function of (filename, text, context).
- ``cluster``: root nomination + BRIEF-anchored merging + per-cluster
  bucket dispatch (delegating shape detection to the promoted
  ``anvil/lib/project_detect.py``) + candidate-file accounting.
- ``report``: deterministic markdown + versioned JSON sidecar.
- ``orchestrate``: single ``run()`` entry composing the above.

The entire skill is **strictly read-only**: no module writes under the
scanned root; the only writes anywhere are the operator-requested
``--report`` / ``--json`` output paths, handled in ``orchestrate``.
"""
