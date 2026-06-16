# Problem: taxicab-number-oq-01

**Slug**: taxicab-number-oq-01
**Status**: Active (OBSERVE/ORIENT, build-gated)
**Source**: seeker-selected
**Tier**: B · significance 6 · tractability 6

## Problem Statement

### Formal Statement

`Ta(2) = 1729`: 1729 is the least positive integer with two distinct
representations as a sum of two positive cubes, namely
`1729 = 1³ + 12³ = 9³ + 10³`, and no `m < 1729` has two such representations.

### Plain Language

The Hardy–Ramanujan "taxicab" number. Famous anecdote: Ramanujan instantly
recognized 1729 as the smallest number expressible as a sum of two cubes in two
different ways.

### Why This Matters

Canonical recreational-number-theory landmark, absent from Mathlib and the
gallery. Fully decidable, so it is a clean axiom-free target once a build slot is
available.

## Known Results

### What's Already Proven

- Nothing in Mathlib (`Ta(k)` undeveloped) or this gallery. Distinct from
  `ramanujan-sum-fallacy`.

### What's Still Open (this entry)

- Compile the bounded-search formalization (`decide` over the `12×12` grid).
- Decide `decide` vs `native_decide` (axiom-free vs `ofReduceBool`).
- Register + add gallery data after a green build.

See `knowledge.md` for the formalization design and the Python certificate
(`verify_taxicab.py`).
