"""Skill-local lib for `anvil:help` (issue #725).

A single pure-introspection module, `introspect`, that reads a consumer
repo's Anvil install state and renders the operator-facing help text.

The skill is **strictly read-only**: no module writes anywhere. Every
value is derived from reads of `.anvil/install-metadata.json`, the
`.claude/skills/anvil-*/` shims, and the per-skill `.anvil/skills/<name>/`
directories (with the source-repo `anvil/skills/<name>/` layout also
recognized so the command works from an Anvil checkout itself).
"""
