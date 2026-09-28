"""Skill-local lib for `anvil:deslop` (issue #898).

Modules (composition order):

- ``ingest``: extract prose to iterate on from a file path (markdown,
  HTML) or pasted plain text, keeping a map back to the origin so the
  operator can apply results. Strictly read-only over the source —
  nothing under this module ever writes to an ingested file.
- ``orchestrate``: scratchpad-thread management (versioned dirs matching
  the ``anvil/lib/critics.py`` ``discover_critics`` sibling-dir shape),
  the deterministic lint wrapper (``anvil.lib.rhetoric_lint``), the
  voice-grounding / rhetoric-rules resolution wrappers
  (``anvil.lib.project_brief``), critic-review IO against the canonical
  ``_review.json`` schema, convergence wiring
  (``anvil.lib.convergence`` / ``anvil.lib.critics``), and the final
  diff + rationale emission. The actual rhetorical-economy / voice
  judgment is an LLM critique step driven by ``commands/deslop.md`` —
  this module supplies every deterministic primitive around it.

``anvil:deslop`` NEVER writes to an ingested source file. All output
(the scratchpad thread, the cleaned text, the rationale, the diff)
lands under an operator-chosen scratch directory; the operator applies
the diff to the source themselves.
"""
