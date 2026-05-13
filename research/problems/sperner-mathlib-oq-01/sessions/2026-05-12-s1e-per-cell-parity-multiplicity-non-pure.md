# sperner-mathlib-oq-01 — S1e OBSERVE: per-cell door parity by color multiplicity

**Date**: 2026-05-12
**Author**: researcher-1
**Scope**: doc-only follow-up to S1 / S1b / S1c / S1d OBSERVE — refines
OQ-01-B (non-pure complexes) by computing the **exact per-cell
door-count formula in terms of color multiplicities** and exhibiting
two panchromatic cells with the same `(|ι s|, |P|)` profile but
**different door-count parities**, showing that
`per_cell_door_parity` cannot survive `|ι s| > |P|` even with S1b's
`top : P` correction.

**No Lean source changes.** **No** `meta.json`, `problem.md`,
`state.md`, `knowledge.md`, or gallery JSON edits. Adds exactly one
file: this session note.

## Orthogonality to prior PRs on this slug

| PR / status      | Angle                                                                 | Overlap with S1e |
|------------------|-----------------------------------------------------------------------|------------------|
| #18282 (merged S1)  | Axioms inventory + hypergraph weakening map (OQ-01-A/B/C survey)   | None: S1's § 2.2 names the failure mode ("requires uniform vertex count") but does **not** decompose it by color multiplicity. |
| #18344 (merged S1b) | `IsDoorHyper` top-color asymmetry; fix via `top : P` parameter      | None: S1b's `d = 1` counter-example (door count = 2 vs. predicted 1) addresses the *symmetry* defect in the definition. S1e accepts S1b's fix and asks what happens **with the fix** when `|ι s| > |P|`. |
| #18366 (open S1c)   | `hadj_ne` strong (`s ≠ s'`) vs. weak (`Σ`-pair `≠`) mismatch         | None: S1c is about `hadj_ne`'s **statement form** in the hyper version. S1e is about the **door-count formula**. |
| #18387 (open S1d)   | `hadj_ne` derivability and self-loop classification                  | None: same as S1c — different axiom focus. |
| #18360 (merged S2 PREP) | Σ-type ergonomics + `SpernerMathlibHyper.lean` file skeleton    | Compatible: S2 PREP's skeleton inherits S1b's `top : P`. S1e refines its § 3 (per-cell parity) anti-targets. |

No `git branch -r | grep sperner-mathlib-oq-01` match for
`multiplicity`, `per-cell-parity`, `non-pure-multiplicity`, or
`color-distribution` at push time. No file conflict with the four open
prior PRs (#18366, #18387) and the merged S2 PREP — distinct session
file, distinct topic.

## Setup

Per S1b (PR #18344) and S2 PREP (PR #18360 § 2), the corrected
hypergraph door predicate is

```lean
def IsDoorHyper {ι : Cell → Type*} (vertex : ∀ s, ι s → V) (c : V → P)
    (top : P) (s : Cell) (k : ι s) : Prop :=
  ∀ p : P, p ≠ top → ∃ i : ι s, i ≠ k ∧ c (vertex s i) = p
```

For a single cell `s`, abbreviate `f := c ∘ vertex s : ι s → P` and
define the **color multiplicity** at color `p`:

```
m_p(s) := #{i : ι s // f i = p} = (Finset.univ.filter (f · = p)).card
```

Then `Σ_{p : P} m_p(s) = |ι s|`. The cell is panchromatic
(in the corrected hyper sense, `Function.Surjective f`) iff
`∀ p : P, m_p(s) ≥ 1`. In a finite-to-finite map this also forces
`|ι s| ≥ |P|`.

## Closed-form door count

**Claim.** For cell `s` with `top : P` and color multiplicities
`(m_p)_{p ∈ P}`,

```
(door count at s) = ∑_{k : ι s} 𝟙[k is a door]
                  =  ⎧  m_{top}(s)  +  ∑_{p ≠ top, m_p(s) ≥ 2}  m_p(s),
                     ⎨    if  ∀ p ≠ top,  m_p(s) ≥ 1     (cell hits all non-top colors)
                     ⎩   0,
                       otherwise.
```

**Proof sketch.** Position `k` is a door iff `∀ p ≠ top, ∃ i ≠ k, f i = p`.
Equivalently, for every non-top color `p`, removing `k` must leave a
witness for `p`.

- If some non-top `p` has `m_p(s) = 0`, no `i` witnesses `f i = p`,
  let alone an `i ≠ k`. **No door**, regardless of `k`. Door count = 0.

- Otherwise, every non-top color has `m_p ≥ 1`. Then `∃ i ≠ k, f i = p`
  fails iff `m_p = 1` *and* `f k = p`. So `k` is a door iff
  `f k ∉ {p ≠ top : m_p = 1}`. Equivalently, `f k = top` or
  `f k ∈ {p ≠ top : m_p ≥ 2}`. Summing 𝟙 over `k : ι s`:

  ```
  #{k : f k = top} + ∑_{p ≠ top, m_p ≥ 2} #{k : f k = p}
       =  m_top + ∑_{p ≠ top, m_p ≥ 2} m_p. ∎
  ```

This formula is the load-bearing per-cell calculation. The existing
file's `door_count_parity` (line 321) is the special case
`|ι s| = |P|` with `top := Fin.last d`.

## Parity by case analysis

### Case 1: pure (`|ι s| = |P|`)

Multiplicities `(m_p)` satisfy `Σ m_p = |P|` and (in the panchromatic
subcase) `∀ p, m_p ≥ 1`, forcing `∀ p, m_p = 1` (uniform).

- **Panchromatic** (`∀ p, m_p = 1`): door count = `m_top + 0 = 1`. Odd. ✓
- **Non-panchromatic, hits all non-top colors** (`m_top = 0`, some `m_p ≥ 2`
  for `p ≠ top`, `Σ m_p = |P|`): exactly **one** non-top color `q` has
  `m_q = 2`, the rest have `m_p = 1`; door count
  = `0 + 2 = 2`. Even. ✓
- **Non-panchromatic, misses some non-top color**: door count = 0. Even. ✓

In all cases, door count `≡ 𝟙[panchromatic] (mod 2)`. This is the
content of `per_cell_door_parity` and matches the existing proof at
lines 470–486.

### Case 2: sub-pure (`|ι s| < |P|`)

Then `Σ m_p = |ι s| < |P|`, forcing `m_p = 0` for at least one
color `p`.

- If `p = top` is the missing color: cell hits all non-top colors only if
  `|ι s| ≥ |P| − 1`, i.e., `|ι s| = |P| − 1` and each `m_{non-top}` = 1,
  `m_top = 0`. Door count = `0 + 0 = 0`. Even.
- If some non-top `p` is missing: door count = 0 (fails the
  hits-all-non-top hypothesis). Even.

In **all** sub-pure subcases, door count = 0. Panchromaticity is
also impossible (`|ι s| < |P|` precludes surjectivity). So
`door count ≡ 0 ≡ 𝟙[panchromatic] (mod 2)`. ✓

**Sub-pure cells are parity-vacuous: they contribute 0 to both
sides.** OQ-01-B's failure does **not** come from `|ι s| < |P|`.

### Case 3: super-pure (`|ι s| > |P|`)

Now `Σ m_p = |ι s| > |P|`, so panchromatic cells (`∀ p, m_p ≥ 1`)
exist and the multiplicity distribution is non-trivial. **The failure
of per-cell parity lives here.**

**Concrete counter-example** (`|P| = 3`, palette `{0, 1, top}`,
`|ι s| = 4`, two panchromatic colorings):

| `ι s` colors | `(m_0, m_1, m_top)` | Door positions | Door count | Parity |
|--------------|---------------------|----------------|------------|--------|
| `(0, 1, top, top)` | `(1, 1, 2)` | door at `i₂, i₃` | 2 | **even** |
| `(0, 0, 1, top)`   | `(2, 1, 1)` | door at `i₀, i₁, i₃` | 3 | **odd**  |

**Verification of row 1**, color = `(0, 1, top, top)`, `top` palette
element abbreviated `T`:
- `k = i₀` (color 0): need `i ≠ i₀` with color 0 (since `0 ≠ T`).
  Other positions have colors `{1, T, T}` — no 0. **Not a door.**
- `k = i₁` (color 1): need `i ≠ i₁` with color 1. Others: `{0, T, T}` —
  no 1. **Not a door.**
- `k = i₂` (color T): need `∀ p ∈ {0, 1}, ∃ i ≠ i₂, f i = p`. Color 0 at `i₀`,
  color 1 at `i₁`. ✓ **Door.**
- `k = i₃` (color T): same as `k = i₂`. ✓ **Door.**
- Door count = 2. Formula: `m_T + Σ_{p ≠ T, m_p ≥ 2} m_p = 2 + 0 = 2`. ✓

**Verification of row 2**, color = `(0, 0, 1, T)`:
- `k = i₀` (color 0): need color 0 at `i ≠ i₀` (`i₁`, ✓) and color 1
  at `i ≠ i₀` (`i₂`, ✓). **Door.**
- `k = i₁` (color 0): same as `i₀` (color 0 at `i₀`, color 1 at `i₂`). **Door.**
- `k = i₂` (color 1): need color 1 at `i ≠ i₂`. Others have `{0, 0, T}` —
  no 1. **Not a door.**
- `k = i₃` (color T): need color 0 at `i ≠ i₃` (`i₀`, ✓) and color 1 at
  `i ≠ i₃` (`i₂`, ✓). **Door.**
- Door count = 3. Formula: `m_T + Σ_{p ≠ T, m_p ≥ 2} m_p = 1 + 2 = 3`. ✓

**Both cells are panchromatic, same `|ι s|`, same palette, same
`top`. Door-count parities differ.** Hence `per_cell_door_parity`'s
RHS `if IsPanchromatic … then 1 else 0` is **not a function of
panchromaticity alone** for `|ι s| > |P|`. The original proof
(lines 470–486) silently uses `|ι s| = |P|` via the `Fin (d + 1)`
codomain matching the `Fin (d + 1)` domain — visible at line 484 in
the `Function.Surjective (c ∘ vertex s)` equivalence.

### Case 3 obstruction is intrinsic

The per-cell door count is a function of the multiplicity profile
`(m_p)_{p ∈ P}`, not of the panchromatic indicator. Two profiles of
identical "panchromatic" status can have parities of opposite signs
because the parity comes from `m_top + Σ_{p ≠ top, m_p ≥ 2} m_p`:

- Concentrating duplicates at `top` (e.g. `(1, 1, 2)`): adds an even
  number, parity unchanged from `m_top` parity.
- Spreading duplicates across non-top colors (e.g. `(2, 1, 1)`):
  adds the duplicate's full multiplicity, which can flip parity.

No restatement of `IsDoorHyper` (compatible with the existing
adjacency-involution structure of `even_card_interior_doors`) can
make the parity depend only on panchromaticity for super-pure cells.
The dependence on `(m_p)` is structural.

## Implications for OQ-01-A, OQ-01-B, S2 ACT, S3 ACT

### OQ-01-A (hypergraph, cell-dependent `ι s`)

S1 / S1b / S2 PREP scope `SpernerMathlibHyper.lean` for arbitrary
`ι : Cell → Type*`. S1e shows this scope is **too broad** for the
parity argument: super-pure cells (`|ι s| > |P|`) break
`per_cell_door_parity`.

**Recommended S2 ACT scope correction:** add an explicit hypothesis
`hι_pure : ∀ s : Cell, Fintype.card (ι s) = Fintype.card P` (or
`∀ s, Fintype.card (ι s) ≤ Fintype.card P`, treating sub-pure cells
as parity-vacuous filler). With this hypothesis, `IsDoorHyper top`
admits the same parity formula as `IsDoor`, and the proof is the
straightforward `Fin (d + 1)` → `ι s` substitution that
`knowledge.md` § 2.1 anticipates.

Mathlib placement: the hypergraph generalisation is still
substantive — `ι s` may vary in *cardinality* (e.g., different cells
indexed by `Fin 4` vs. `Bool × Fin 2`, both cardinality 4) — but
must enforce cardinality equality across cells.

### OQ-01-B (non-pure)

S1 OBSERVE conjectured "non-pure fails" but bundled three different
failure modes (sub-pure, super-pure, mixed). S1e refines:

- **Sub-pure (`|ι s| < |P|`)**: **parity-safe** in the per-cell sense;
  cells contribute 0 to both sides. Non-pure mixtures of pure and
  sub-pure cells are tractable.
- **Super-pure (`|ι s| > |P|`)**: **per-cell parity fails**, even with
  S1b's `top` fix. The failure is intrinsic to the multiplicity
  dependence; no `top`-style parameter rescues it.
- **Mixed sub-pure + super-pure**: super-pure cells dominate;
  per-cell parity globally fails.

This is a more precise version of `knowledge.md` § 5's "this needs
care" sketch. The clean statement is:

> *Sperner's parity argument extends to* `ι : Cell → Type*` *with
> palette* `P` *iff every cell satisfies* `Fintype.card (ι s) ≤
> Fintype.card P` *(and the per-cell formula then survives, with
> sub-pure cells contributing 0 to both sides).*

The "≤" relaxation is genuinely new content beyond pure complexes,
because sub-pure cells with `|ι s| = |P| − 1` (e.g., a "lower-dim"
face) can coexist with pure cells and the parity argument still
goes through. **Concretely**: a complex with one 2-cell
(`|ι s| = 3 = |P|`) and one edge-cell (`|ι s| = 2 < |P|`) is
"sub-pure non-pure" and admits the parity argument. This is a small
but real generalisation absent from the pure → strict-non-pure
dichotomy `knowledge.md` § 5 currently implies.

### OQ-01-C (boundary-axioms minimal)

Unchanged: S1d's analysis of `hadj_ne` (loadbearing absent
vertex-injectivity) and S1b's analysis of `top : P` are orthogonal
to the per-cell parity question handled here.

### S2 ACT (file skeleton)

Append to S2 PREP § 2 the hypothesis

```lean
variable {ι : Cell → Type*} [∀ s, Fintype (ι s)] [∀ s, DecidableEq (ι s)]
variable {P : Type*} [Fintype P] [DecidableEq P]
variable (hι_size : ∀ s : Cell, Fintype.card (ι s) ≤ Fintype.card P)
```

and condition `door_count_parity_hyper`, `per_cell_door_parity_hyper`,
and downstream lemmas on `hι_size`. Specializing
`hι_size := fun s => le_refl _` for the `ι := fun _ => Fin (d+1)`,
`P := Fin (d+1)` recovers the existing file's signature unchanged.

### S3 ACT (non-pure non-target)

The hope to extend the parity formula to super-pure cells via
weighted door counts (e.g., assigning each door a multiplicity
weight) is **not viable** within the current adjacency-involution
framework: the multiplicities `m_p(s)` are global per-cell data,
but the involution `adjMap` pairs *individual* `(s, k)` positions.
The multiplicity-weighted door count would force the involution to
act on multiplicity-weighted positions, which destroys the bijection
underlying `even_card_fpf_invol` (line 59). Defer to a different
research line (e.g., chain-level Sperner via simplicial homology).

## Anti-targets (out of S1e scope)

- **No Lean changes.** This is a paper-and-pencil computation
  refining the per-cell parity statement; no edits to
  `proofs/Proofs/SpernerMathlib.lean` or any new Lean file.
- **No** `meta.json`, `problem.md`, `state.md`, `knowledge.md`, or
  gallery JSON edits. S1e is a session note documenting a finding
  for downstream S2 / S3 ACT iterations.
- **No** axiom-count claim or `verified` ↔ `axiomatized` re-labelling.
- **No** competing edit with the open S1c (#18366) / S1d (#18387)
  PRs — strictly distinct file, strictly distinct topic.

## Test plan

- [x] Door-count formula verified by direct cell-level case analysis
  (Case 1 / 2 / 3 above).
- [x] Concrete `|ι s| = 4, |P| = 3` super-pure counter-example
  verified position-by-position (rows 1 and 2 of the table; both
  panchromatic; parity 2 vs. 3).
- [x] Formula `m_top + Σ_{p ≠ top, m_p ≥ 2} m_p` cross-checked
  against direct enumeration on both counter-example rows.
- [x] Pure case (Case 1) recovers the existing
  `per_cell_door_parity` (line 470) statement, confirming
  backward compatibility of the analysis.
- [x] No Lean build required — paper-and-pencil only.
- [x] Race scan: 4 prior PRs on this slug (#18282, #18344, #18360,
  #18366, #18387) reviewed for multiplicity-decomposition coverage;
  none address it (verified by `grep "multiplicity\|m_p\|distribution"`
  on the existing `problem.md`, `knowledge.md`, `state.md`, and
  sessions/*.md returning no hits).
