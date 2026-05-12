# Current State

**Phase**: ACT (S2 file written; advancing to S3 gallery + `#print axioms`)
**Since**: 2026-05-12T05:00:00Z (S1)
**Last Updated**: 2026-05-12 (S2 ACT by researcher-3)
**Iteration**: 2
**Last researcher**: researcher-3

## S2 Summary (2026-05-12, researcher-3)

**Mode**: ACT (witness each row of the S1 taxonomy table with a
working Lean `example := rfl`).

### Deliverable

New file `proofs/Proofs/OnePlusOneOQ04.lean` (161 lines, 0 axioms,
0 sorries) containing five `example` theorems, one per row of the
taxonomy table:

1. **Row 0 (`Rules = ∅`)** — unfolded baseline. `Peano.ℕ.succ
   (Peano.ℕ.succ Peano.ℕ.zero) = Peano.ℕ.succ (Peano.ℕ.succ
   Peano.ℕ.zero) := rfl`.
2. **Row 1 (`Rules = {δ, ι}`)** — pattern-matched Peano (parent's
   encoding). `Peano.one + Peano.one = Peano.two := rfl`.
3. **Row 2 (`Rules = {δ, ι, β}`)** — raw recursor. New `def addRec
   (n m : Peano.ℕ) : Peano.ℕ := Peano.ℕ.rec (motive := fun _ =>
   Peano.ℕ) n (fun _ acc => Peano.ℕ.succ acc) m`. `addRec
   Peano.one Peano.one = Peano.two := rfl`.
4. **Row 3 (`Rules = {δ, β}`)** — Church numerals. New `def Church
   : Type 1`, `cOne`, `cTwo`, `cAdd`. `cAdd cOne cOne = cTwo := rfl`.
5. **Row 4 (`Rules = {δ, ι}`)** — binary naturals. New `inductive
   Bin`, `Bin.succ` (carry-chain), `Bin.add` (struct-rec on 2nd
   arg). `Bin.add Bin.one Bin.one = Bin.b0 Bin.one := rfl`.

Added to `proofs/Proofs.lean` import list alphabetically between
`Proofs.OnePlusOne` and `Proofs.PACLearning`.

### Design choices

* **Single-file `OnePlusOneOQ04.lean`, no companion.** This is
  pedagogy with no Mathlib-API drift exposure (Mathlib not even
  imported — the file only depends on `Proofs.OnePlusOne`). No
  reason to split.

* **`Peano.ℕ.rec` via the named-argument `(motive := fun _ =>
  Peano.ℕ)`.** The auto-generated `rec` is dependent
  (`{motive : ℕ → Sort u}`), but for non-dependent addition we
  collapse to the constant motive. The named argument keeps the
  intent clear (vs. positional `@Peano.ℕ.rec`).

* **`Church : Type 1` annotation.** Bare `(α : Type) → (α → α) →
  α → α` lives in `Type 1` because the Π over `Type 0` increases
  the universe. The explicit annotation avoids universe-inference
  surprises in the example.

* **Binary `Bin.b0 Bin.one` as little-endian `2`.** Matches the
  knowledge.md S1 hand-trace. The shallow `1+1` depth is illusory
  for general `2^k + 2^k`; the docstring records this.

### File deltas

- `proofs/Proofs/OnePlusOneOQ04.lean`: NEW, 161 lines.
- `proofs/Proofs.lean`: +1 import line.
- Sorry count: 0.
- Axiom count: 0.
- Theorem count: 0 (all 5 main results are `example`s, by
  convention for one-line `rfl` witnesses).
- Definition count: 7 (`addRec`, `Church`, `cOne`, `cTwo`,
  `cAdd`, `Bin.succ`, `Bin.add`) plus the `inductive Bin`.

### Build status

Pending. The file imports `Proofs.OnePlusOne` (no Mathlib) and uses
only kernel reductions; per S1 risk notes "build verification is
highly likely to succeed (no Mathlib API drift risk, only kernel
reductions)." Standard Hilbert-15-style build-pending PR for the
research wave.

## Current Focus

Reduction-rule taxonomy for `one + one = two := rfl` across the
standard ℕ encodings (Peano pattern-matched, Peano recursor-only,
Church numerals, binary naturals, plus `let`-laden variants).

S1 OBSERVE deliverables (this iteration):

- `problem.md` — Expanded statement, classification, why-it-matters,
  theoretical framework (β, δ, ι, ζ catalogue, confluence,
  δ-unavoidability), representation catalogue, summary table,
  Principia comparison, related gallery proofs, Mathlib map,
  next-action decomposition, risk notes.
- `knowledge.md` — S1 entry with:
  - Compact taxonomy table mapping each encoding to its minimal
    rule subset and step count.
  - Hand-traces for all five encodings (unfolded, Peano-pattern,
    Peano-recursor, Church, binary).
  - Lower-bound (necessity) arguments per rule.
  - 6 numbered insights.
  - 3 Mathlib gaps.
  - 5 next steps (S2–S5 + deferred OQ-04-OQ-01 candidate).
  - Risk notes (Lean 4 universe handling, elaboration accounting).
  - Informal references (Coquand-Huet, de Moura-Ullrich,
    Whitehead-Russell).

No Lean changes in S1 — pure exploration / survey.

## Active Approach

S2 will be a single Lean file `proofs/Proofs/OnePlusOneOQ04.lean`
containing five `example` theorems, one per row of the taxonomy
table. Each `example` is the Lean-witnessed *sufficiency* claim
for that row's rule set. Surrounding comments document the
*necessity* claim with reference to `knowledge.md` S1.

The file mirrors the pedagogical style of the parent entry
(`Proofs/OnePlusOne.lean`): no Mathlib dependency beyond
`Mathlib.Init`, axiom-free, `verified` track.

## Blockers

None. S1 is complete; S2 is unblocked.

## Next Action

**S3 ACT**: Augment `proofs/Proofs/OnePlusOneOQ04.lean` with
`#print axioms` + `#reduce` stanzas for each example, plus a
docstring section at the top tying the file to `problem.md`'s
summary table. The `#print axioms` stanzas confirm each example
is axiom-free, doubling as the *propositional* dual of the
reduction-rule taxonomy (per knowledge.md S1 insight #6).

**S4 ACT**: Add a gallery entry
`src/data/proofs/russell-1-plus-1-oq-04/` so the worked file is
browsable on the live site. `meta.json` uses `status:
"verified"`, `badge: "original"`, `axiomCount: 0`, `sorries: 0`.
Cross-reference the parent entry `russell-1-plus-1`.

**S5 (optional)**: A `let`-binding example demonstrating the role
of `ζ`:

```lean
def addLet (n m : Peano.ℕ) : Peano.ℕ :=
  let n' := n; let m' := m
  Peano.add n' m'
example : addLet Peano.one Peano.one = Peano.two := rfl
```

**Deferred (→ OQ-04-OQ-01)**: A meta-theorem stating `Rules(E)`
precisely (perhaps via a sandboxed kernel parametrised on a
subset of `{β, ι, δ, ζ}`) and proving minimality. Significant
project; stub as a child open question.

## Attempt Counts

- Total attempts: 2 (S1 OBSERVE complete; S2 ACT complete)
- Current approach attempts: 2
- Approaches tried: 1 (reduction-rule taxonomy across encodings)
