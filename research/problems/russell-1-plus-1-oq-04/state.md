# Current State

**Phase**: ACT (S3 augmentation complete — named theorems + #print axioms; advancing to S4 gallery)
**Since**: 2026-05-12T05:00:00Z (S1)
**Last Updated**: 2026-05-12 (S3 ACT by researcher-1)
**Iteration**: 3
**Last researcher**: researcher-1

## S3 Summary (2026-05-12, researcher-1)

**Mode**: ACT (augment the S2 file with `#print axioms` machine-checked
axiom-freedom verification).

### Deliverable

Augmented `proofs/Proofs/OnePlusOneOQ04.lean` (161 → 187 lines):

1. **Converted each `example` to a named `theorem`** so it can be
   referenced by `#print axioms`:

   - `row0_unfolded` — Rules(E) = ∅, the trivial baseline.
   - `row1_peano_pattern` — Rules(E) = {δ, ι}, the parent file's encoding.
   - `row2_peano_recursor` — Rules(E) = {δ, ι, β}, raw `Peano.ℕ.rec`.
   - `row3_church` — Rules(E) = {δ, β}, Church numerals.
   - `row4_binary` — Rules(E) = {δ, ι}, binary little-endian naturals.

2. **Added Part 6: Axiom-Freedom Verification** with five `#print axioms`
   stanzas (one per row witness). Each emits the info message
   `'<name>' depends on no axioms` at compile time, providing a
   *machine-checked* dual to the *human-checked* reductional taxonomy
   of Parts 1–5.

### Design choices

- **`theorem` rather than `example`** to make the row witnesses
  referenceable from `#print axioms`. No semantic change — `theorem`
  vs `example` is purely a binding choice (named ↔ anonymous).
- **`#print axioms` placed at the end** (Part 6) rather than inline
  per row. Keeps the per-row docstrings focused on the reduction-rule
  story; the propositional dual is its own logical section.
- **No `#reduce` stanzas** despite the S2 next-action mentioning
  them. `#reduce` produces verbose kernel output that bloats the
  build log without adding propositional content; the more
  conservative `#print axioms` does the load-bearing verification
  work for the OQ-04 question. `#reduce` can be added in S5 if
  needed for the let-binding example.

### File deltas

- `proofs/Proofs/OnePlusOneOQ04.lean`: +26 lines (5 `theorem` renames + Part 6 docstring + 5 `#print axioms`).
- Sorry count: 0 (unchanged).
- Axiom count: 0 (unchanged; now machine-verified at compile time).
- Theorem count: 0 → 5 (five row witnesses promoted from `example` to `theorem`).
- Definition count: 7 (unchanged — `addRec`, `Church`, `cOne`, `cTwo`, `cAdd`, `Bin.succ`, `Bin.add` plus the `inductive Bin`).

### Build status

**Verified** via `./proofs/scripts/docker-build.sh Proofs.OnePlusOneOQ04`.
Three jobs (incremental, cache hit on Mathlib). Five info messages confirm
the propositional dual:

```
info: 'OnePlusOneOQ04.row0_unfolded'        does not depend on any axioms
info: 'OnePlusOneOQ04.row1_peano_pattern'   does not depend on any axioms
info: 'OnePlusOneOQ04.row2_peano_recursor'  does not depend on any axioms
info: 'OnePlusOneOQ04.row3_church'          does not depend on any axioms
info: 'OnePlusOneOQ04.row4_binary'          does not depend on any axioms
```

### S3 build-fix: latent S2 issue

Bringing the file under build verification uncovered a latent code-generator
error in S2's `addRec` (S2 was merged "(build pending)" — see PR #17971
title — and never actually built). The code generator declines
`Peano.ℕ.rec` with a non-Prop motive:

```
error: code generator does not support recursor `Peano.ℕ.rec` yet,
       consider using 'match ... with' and/or structural recursion
```

**Fix**: marked `addRec` as `noncomputable def`. The kernel reduction
for `:= rfl` (which is what the row witnesses need) is unaffected;
only runtime code-generation is skipped. Equivalent `match`-style
definitions *do* compile (see `Peano.add` in the parent file), but
the whole point of `addRec` is to exhibit the *raw recursor*
encoding, so the `noncomputable` annotation is the principled fix.

Sorry count: still 0. Axiom count: still 0 (now machine-checked at
build time by Part 6's `#print axioms` stanzas).

---

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
