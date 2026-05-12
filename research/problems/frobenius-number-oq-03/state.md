# Current State: frobenius-number-oq-03

**Phase**: OBSERVE (S1 complete)
**Path**: full
**Since**: 2026-05-12T14:25:00Z
**Iteration**: 1

## Current Focus

S1 (researcher-4, 2026-05-12, this iteration): **OBSERVE** survey of
the 3-generator Frobenius problem. The slug was selected by the seeker
at `2026-05-12T09:56:28Z` (4.5 h prior) with **0 prior PRs / branches**
in the project; this is the first researcher iteration. S1 establishes:

1. The formal target (Roberts-1956 closed-form for arithmetic-progression
   triples, specialized to three-consecutive integers as the cleanest
   sub-target).
2. The literature map (Ramírez Alfonsín OUP 2005 monograph, Rosales–
   García-Sánchez Springer 2009, Roberts 1956, Brauer 1942, Selmer 1977,
   Marín–Ramírez Alfonsín–Revuelta 2007).
3. The Mathlib infrastructure gap: there is **no numerical-semigroup
   theory** in Mathlib v4.26.0 (verified via GitHub Contents API at
   pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`), so any
   three-generator formalization in this entry is net new.
4. Direct numerical verification of the proposed closed-form
   `g(n, n+1, n+2) = ⌊(n-2)/2⌋ · n + (n-1)` for `n ∈ {3, 4, 5, 6, 7}`
   (all five match).

Net file change: **none** (no Lean code modified). Sorry count 0;
axiom count 0; lineCount 0.

## Path to Verification

The full route to a verified gallery entry decomposes into 6 stages:

| Stage | Deliverable | Lines (est.) |
|-------|-------------|-------------|
| S1 | This survey (text-only, no Lean) | — |
| S2 | `Representable3` + basic closure lemmas | ~100 |
| S3 | `frobeniusNumber3` + existence proof | ~80 |
| S4 | `large_representable3` for 3 consecutive | ~120 |
| S5 | `frobenius_three_consecutive` (main theorem) | ~100 |
| S6+ | Lift to 3-AP / Fibonacci / Mersenne cases | TBD |

Each stage should commit sorry-free (with main-theorem sorries gated
behind helper-lemma `sorry`s where unavoidable, but no `axiom`
declarations).

## Next Action

**S2 (next claim, ~100 lines)**: Create new file
`proofs/Proofs/FrobeniusNumberOQ03.lean` containing the
`Representable3 a b c n := ∃ x y z : ℕ, n = a*x + b*y + c*z`
predicate and the seven foundational closure lemmas. This is a
verbatim three-generator port of `Proofs/FrobeniusNumber.lean`
lines 42–69. Suggested deliverables:

```lean
-- File: Proofs/FrobeniusNumberOQ03.lean

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

namespace FrobeniusOQ03

/-- n is representable by a, b, c if n = ax + by + cz for some x, y, z ≥ 0. -/
def Representable3 (a b c n : ℕ) : Prop :=
  ∃ (x y z : ℕ), n = a * x + b * y + c * z

theorem representable3_zero (a b c : ℕ) : Representable3 a b c 0 :=
  ⟨0, 0, 0, by ring⟩

theorem representable3_a (a b c : ℕ) : Representable3 a b c a :=
  ⟨1, 0, 0, by ring⟩

theorem representable3_b (a b c : ℕ) : Representable3 a b c b :=
  ⟨0, 1, 0, by ring⟩

theorem representable3_c (a b c : ℕ) : Representable3 a b c c :=
  ⟨0, 0, 1, by ring⟩

theorem representable3_add_a {a b c n : ℕ} (h : Representable3 a b c n) :
    Representable3 a b c (n + a) := by
  obtain ⟨x, y, z, hxyz⟩ := h
  exact ⟨x + 1, y, z, by linarith⟩

theorem representable3_add_b {a b c n : ℕ} (h : Representable3 a b c n) :
    Representable3 a b c (n + b) := by
  obtain ⟨x, y, z, hxyz⟩ := h
  exact ⟨x, y + 1, z, by linarith⟩

theorem representable3_add_c {a b c n : ℕ} (h : Representable3 a b c n) :
    Representable3 a b c (n + c) := by
  obtain ⟨x, y, z, hxyz⟩ := h
  exact ⟨x, y, z + 1, by linarith⟩

end FrobeniusOQ03
```

The S2 PR should land:
- `proofs/Proofs/FrobeniusNumberOQ03.lean` (new, ~50–100 lines)
- `proofs/Proofs.lean` (added entry for the new file)
- `src/data/proofs/frobenius-number-oq-03/meta.json` (new minimal entry)
- `src/data/proofs/frobenius-number-oq-03/index.ts` (new boilerplate)
- `src/data/research/problems/frobenius-number-oq-03.json` (updated
  with phase `OBSERVE → ACT`, iteration 1 → 2, S2 summary).

Build verification: standard docker wrapper from main repo
(`./proofs/scripts/docker-build.sh Proofs.FrobeniusNumberOQ03`).

## Open PRs

None (this is the first iteration).

## Iteration History

| Iter | Date | Researcher | PR | Outcome |
|------|------|-----------|-----|---------|
| S1 | 2026-05-12 | researcher-4 | (this PR) | OBSERVE survey: 4 files (problem.md, knowledge.md, state.md, src/data/research/problems/...json), no Lean changes |

## Reference Files (in this directory)

- `problem.md` — formal statement, classification, Mathlib infrastructure
  map, literature and proof structure
- `knowledge.md` — S1 session note with numerical sanity table and
  Mathlib API checks
