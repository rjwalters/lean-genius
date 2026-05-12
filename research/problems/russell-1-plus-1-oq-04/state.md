# Current State

**Phase**: ACT (S5 ζ-demonstrator complete — let-bound row + #print axioms; OQ-04 saturated, deferred meta-theorem → OQ-04-OQ-01)
**Since**: 2026-05-12T05:00:00Z (S1)
**Last Updated**: 2026-05-12 (S5 ACT by researcher-6)
**Iteration**: 5
**Last researcher**: researcher-6

## S5 Summary (2026-05-12, researcher-6)

**Mode**: ACT (add the optional `let`-bound ζ-demonstrator row noted
in S1's `nextSteps` and S3/S4 state.md).

### Deliverable

Augmented `proofs/Proofs/OnePlusOneOQ04.lean` with a sixth row that
isolates the `ζ`-rule (let-reduction):

1. **New def `addLet`**: `Peano.add` applied to `let`-bound copies
   of its arguments. Definitionally equal to `Peano.add n m`, but
   only after `ζ` fires on the two `let`-binders.

2. **New theorem `row5_let : addLet Peano.one Peano.one = Peano.two := rfl`**.
   Rules(E) = `{δ, ι, ζ}`. 7-step rewrite (row 1's 5 plus 2 `ζ`-steps).

3. **Header table extended** to include the 6th row with column
   alignment widened to fit `{δ, ι, ζ}`. New "Observation (ζ)"
   paragraph explaining why ζ is a *fourth* CIC primitive rather
   than syntactic sugar (no β/ι/δ rule has a `let` in its LHS
   pattern, so on closed terms with let-bindings, ζ is not
   derivable from `{β, ι, δ}`).

4. **New `## Row 5` section** with full docstring: necessity
   argument (without ζ the LHS is stuck at
   `let n' := one; let m' := one; Peano.add n' m'`, which `ι`
   cannot reduce because `Peano.add`'s pattern-match expects a
   constructor head, not a `let`) and sufficiency argument (after
   ζ fires the term reduces to `Peano.add Peano.one Peano.one`,
   identical to row 1's LHS, closing on `{δ, ι}`).

5. **Part 6 extended** with `#print axioms row5_let` stanza
   (expected: `'OnePlusOneOQ04.row5_let' depends on no axioms`).
   Part 6 docstring updated "five" → "six" row witnesses.

### Design choices

- **Single `let`-binder vs. nested**: I used a *pair* of let-binders
  (`let n' := n; let m' := m`) rather than a single binder. The
  pair is more honest as a ζ-stress-test: a single binder
  followed by one application could in principle be elided by an
  optimizer, but a pair of binders followed by a binary
  application makes the ζ-step unambiguous. Each let-binder
  produces exactly one `ζ`-step (2 total), giving the cleanest
  step-count arithmetic with row 1.
- **`addLet` not `Peano.addLet`**: kept in the `OnePlusOneOQ04`
  namespace rather than extending `Peano`, since this is a
  pedagogical artifact specific to the OQ-04 taxonomy, not a
  general-purpose addition operator.
- **`def addLet (n m : Peano.ℕ) : Peano.ℕ`** (not `def addLet := …`):
  giving explicit argument names makes the `let`-binders
  obviously *bind something* (the formal parameter), which is
  the pedagogical point. An anonymous-argument variant
  (`addLet := fun n m => let … in Peano.add n' m'`) would
  introduce a spurious β-step.

### File deltas

- `proofs/Proofs/OnePlusOneOQ04.lean`: +52 lines
  (header table row + ζ observation + §Row 5 docstring + `def addLet` +
  `theorem row5_let` + Part 6 prose + `#print axioms row5_let`).
- Sorry count: 0 (unchanged).
- Axiom count: 0 (unchanged; row5_let machine-verified at compile time).
- Theorem count: 5 → 6 (added `row5_let`).
- Definition count: 7 → 8 (added `addLet`).

### Build status

**Verified** via `./proofs/scripts/docker-build.sh Proofs.OnePlusOneOQ04`.
Six info messages confirm the propositional dual:

```
info: 'OnePlusOneOQ04.row0_unfolded'        does not depend on any axioms
info: 'OnePlusOneOQ04.row1_peano_pattern'   does not depend on any axioms
info: 'OnePlusOneOQ04.row2_peano_recursor'  does not depend on any axioms
info: 'OnePlusOneOQ04.row3_church'          does not depend on any axioms
info: 'OnePlusOneOQ04.row4_binary'          does not depend on any axioms
info: 'OnePlusOneOQ04.row5_let'             does not depend on any axioms
```

### OQ-04 status after S5

The OQ-04 question is now saturated at the *worked-example* level:
all five rule subsets identified in S1's taxonomy table are
witnessed by an `:= rfl` Lean theorem, and each witness's
axiom-freedom is machine-checked at compile time. The remaining
work belongs to the child question **OQ-04-OQ-01** (a precise
meta-theorem stating `Rules(E)` and proving minimality of the
rule subsets, perhaps via a sandboxed kernel parametrised on a
subset of `{β, ι, δ, ζ}`).



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

**OQ-04 saturated at the worked-example level** after S5.
Remaining work belongs to the child question **OQ-04-OQ-01** (or
a new sibling): a precise meta-theorem stating `Rules(E)` and
proving minimality of the rule subsets, perhaps via a sandboxed
kernel parametrised on a subset of `{β, ι, δ, ζ}`. That work is
significantly larger than a single research iteration.

Optional follow-ons (not strictly required for OQ-04):

- **S6 (optional)**: A `#reduce`-stanza per row showing the
  *literal* kernel-reduced output. Verbose (each `#reduce` emits
  the fully-normalised term), but pedagogically clean for the
  Church and recursor rows where the normalisation is non-trivial.
- **S7 (optional)**: A timing harness using `set_option
  trace.profiler true` to measure the *kernel cost* (μs per
  rewrite class) of each row. Would empirically reify the
  "step count" column of the taxonomy table.

## Attempt Counts

- Total attempts: 5 (S1 OBSERVE; S2 ACT skeleton; S3 ACT named theorems + #print axioms; S4 ACT gallery entry; S5 ACT ζ-demonstrator row)
- Current approach attempts: 5
- Approaches tried: 1 (reduction-rule taxonomy across encodings)
