# research/problems/&lt;slug&gt;/ — substrate for the OODA loop

This document defines the file layout for an actively-attempted research target
under `research/problems/<slug>/`. The Erdős-problem convention (one
`problem.md` per `erdos-N-oq-K`) is the prior art; this document generalizes
that convention for non-Erdős targets and adds the `claims/`, `notes/`, and
`links/` subdirectories that turn a problem entry into a working OODA-loop
substrate.

See issue #22628 for context and rationale.

## Layout

```
research/problems/<slug>/
  problem.md            # statement, current state, attack-vector menu
  claims/               # one file per researcher (or Aristotle) attempt
    YYYY-MM-DD-<vector>-<short-tag>.md
    ...
  notes/                # curated cross-claim insights (less frequently updated)
    leads.md
    dead-ends.md
    open-sub-conjectures.md
  links/                # pointers into the rest of the repo
    lean-files.md       # which proofs/Proofs/*.lean files instantiate / depend on this
    gallery.md          # which src/data/proofs/<slug>/ entries reference this
```

The `<slug>` matches the gallery slug exactly (e.g., `fermat-defect-one`
matches `src/data/proofs/fermat-defect-one/`). For Erdős problems the legacy
convention `erdos-<N>-oq-<K>` is retained; new non-Erdős targets use the
gallery slug.

## problem.md

The top-level file is a working brief. It must contain at minimum:

1. **Statement** — formal Lean statement and a plain-language version.
2. **Current state** — what is known, what is open, citations.
3. **Attack vectors** — a numbered menu the next iteration can choose from.
   Each vector should be named (one of: `witness-search`, `modular-obstruction`,
   `parameterization`, `reduction`, `structural-lemma`, `literature-reading`,
   `other`) so claim files can reference it.
4. **Connections** — neighboring problems, both in the gallery and in the
   literature.

Style is functional; this is a working file, not a publication artifact.

## claims/

A `claims/` file records **one attempt**, success or failure. Negative results
are first-class — the whole point of writing them down is so the next
iteration does not redo the same dead end.

File naming: `YYYY-MM-DD-<vector>-<short-tag>.md`, e.g.

```
2026-06-10-mod3-obstruction-n4.md
2026-06-12-witness-search-n5-bound500.md
2026-06-14-thue-reduction-n3.md
```

Required sections inside a claim file:

```markdown
# Claim — <short title>

- **Vector attempted**: one of (witness-search | modular-obstruction |
  parameterization | reduction | structural-lemma | literature-reading | other)
- **Date**: YYYY-MM-DD
- **Author**: (agent id or human)
- **Status**: succeeded | failed | inconclusive | partial

## What was tried

(concrete: search bound, prime modulus, parameterization family,
Lean file path, literature reference)

## What happened

(witness found / no witness in bound / obstruction found / no obstruction /
lemma proved / lemma failed / paper located)

## What this suggests for next iteration

(actionable: try larger bound, try different prime, write Lean lemma X,
read paper Y, abandon this vector)
```

Aristotle's wrapper auto-generates a stub claim file (vector `aristotle-mcts`)
via `scripts/aristotle/write-run-artifact.sh` whenever it completes a run on
the target. Researchers can promote these stubs into curated claims; they do
not need to be hand-written from scratch.

## notes/

Three optional curated files. These survive after individual claim files age
out. Updated less frequently (weekly at most) and only when an insight is
durable enough that future iterations will want to know it.

- `leads.md` — promising directions not yet attempted.
- `dead-ends.md` — vectors known not to work, with brief justifications.
- `open-sub-conjectures.md` — smaller open conjectures discovered along the way.

## links/

Two pointer files that keep the problem entry in sync with the rest of the
repository:

- `lean-files.md` — `proofs/Proofs/*.lean` files that instantiate or depend on
  the problem.
- `gallery.md` — `src/data/proofs/<slug>/` entries that reference it.

These are short lists; they exist so that an agent picking up the slug for the
first time can find the surrounding code without grepping.

## Lifecycle

A `research/problems/<slug>/` entry exists exactly when:

1. The corresponding `src/data/proofs/<slug>/meta.json` has
   `researchStatus: "actively-attempting"`, OR
2. The slug is listed in `research/open-conjectures.json` (Tier-3 registry).

When either condition is dropped (e.g., the conjecture is proven, abandoned, or
demoted to `input`), the problem directory remains for historical reference but
is no longer updated.

## Relationship to existing Erdős convention

The `research/problems/erdos-<N>-oq-<K>/` directories pre-date this document.
Existing Erdős entries continue to follow their established convention; the
new `claims/`, `notes/`, `links/` subdirectories are optional additions, not
retroactive requirements.
