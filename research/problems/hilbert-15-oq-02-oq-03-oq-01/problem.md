# Formalize `lrCoeffN` (Hilbert 15 / OQ-02 / OQ-03 / OQ-01)

**Parent**: `hilbert-15-oq-02-oq-03` — *LR positivity via Klyachko's
Horn inequalities*.  
**File**: `proofs/Proofs/Hilbert15OQ02OQ03.lean`  
**Status**: AVAILABLE (tier B, score 0, EMPTY).  
**Iteration**: S1 (researcher-1, 2026-05-11).

## The Question

Replace the axiom

```lean
axiom lrCoeffN {n : ℕ} : Partition n → Partition n → Partition n → ℕ
```

in `Hilbert15OQ02OQ03.lean` with a **concrete computable definition**
matching the standard Littlewood–Richardson rule

> `c^ν_{λ,μ} = #{ SSYT T of skew shape ν/μ, content λ, with reverse
>   row reading word a *lattice word* }`

and prove that the new definition satisfies the structural lemmas
that `Hilbert15OQ02OQ03.lean` currently states as axioms over
`lrCoeffN` (the most important being Klyachko's theorem, which is a
separate target; for *this* slug only the **definition** is in
scope — the deep equivalence with Horn inequalities is OQ-02 / OQ-03
proper).

## Why It Matters

`Hilbert15OQ02OQ03.lean` carries **3 axioms**

1. `lrCoeffN`            — the LR coefficient itself
2. `admissible`          — admissibility predicate for index triples
3. `klyachko_theorem`    — LR positivity ↔ Horn inequalities

Axiom 1 is structurally different from the other two: it is a
*combinatorial counting function* with a fully explicit definition in
the literature (Littlewood 1934 / Fulton 1997 Ch. 5 §2). Replacing
it requires only Mathlib's developing SSYT theory plus a small
amount of new infrastructure (lattice-word predicate). It is a
self-contained Mathlib-style formalization task with no open
mathematics in it. Eliminating axiom 1 reduces the assumption count
on **every** downstream Hilbert 15 OQ-02-OQ-03 result.

It is also a candidate *Mathlib contribution*: Mathlib has
`YoungDiagram`, `StandardYoungTableau`, and an in-progress
`SemistandardYoungTableau` (`SSYTFin` is the ad-hoc analog already
used in the gallery's `BallotProblemOQ03OQ01OQ01OQ01.lean`). The
LR rule and lattice-word predicate are *not yet present* in Mathlib
at the pinned revision (v4.26.0), so a clean formalization here can
be submitted upstream.

## Mathematical Specification

### Inputs

Three weakly decreasing partitions with exactly `n` parts (the
`Partition n` structure already exists in
`Hilbert15OQ02OQ03.lean`):

- `ν` — outer shape  
- `μ` — inner shape (required `μ ⊆ ν`, i.e. `μ.parts i ≤ ν.parts i`
  for every `i`)  
- `λ` — content (any partition; size constraint `|ν| = |λ| + |μ|`
  is enforced via the count returning 0 otherwise)

### Skew shape `ν/μ`

The set of cells `{(i,j) : μ.parts i < j+1 ≤ ν.parts i}` (i.e. cells
of `ν` not in `μ`). Encoded in Lean as a sigma-type
`(i : Fin n) × Fin (ν.parts i - μ.parts i)` together with a "column
offset" function `j ↦ μ.parts i + j`.

### Semistandard skew tableau of content `λ`

A filling `T : skewCells → Fin n` (entries are *row labels*, not
arbitrary naturals) such that:

1. **Row-weak**: in each row of `ν/μ`, entries are weakly increasing
   left-to-right.
2. **Column-strict**: in each column of `ν/μ`, entries are strictly
   increasing top-to-bottom.
3. **Content `λ`**: for every `k : Fin n`,
   `(T ⁻¹' {k}).card = λ.parts k`.

### Reverse row reading word

Read each row right-to-left, from **top to bottom**:

  `w(T) = T(0, last)·…·T(0, first) · T(1, last)·…·T(1, first) · …`

This is the *Fulton convention* (different from the Stanley reading
order, which goes bottom-up; for the LR rule both produce the same
count via a bijection but the Fulton order matches our `lrCoeff2`
in `Hilbert15OQ02.lean`).

### Lattice (= ballot) word

A word `w ∈ Fin n ^*` is a **lattice word** if at every prefix `p`
and for every pair `k < k'`, the count of `k`s in `p` is `≥` the
count of `k'`s in `p`. (Equivalently: at every prefix, the multiset
of entries is the content of a valid partition.)

### Definition

```lean
def lrCoeffN_def {n : ℕ} (ν λ μ : Partition n) : ℕ :=
  if h : μ ⊆ ν ∧ ν.weight = λ.weight + μ.weight then
    Fintype.card {T : SkewSSYT n ν μ //
                  T.content = λ ∧ isLatticeWord (reverseRowWord T)}
  else 0
```

(All three predicates are decidable on a finite type, so the
subtype is `Fintype` and `lrCoeffN_def` is *computable*.)

### Compatibility theorem (deferred)

```lean
theorem lrCoeffN_def_eq_axiom {n : ℕ} (ν λ μ : Partition n) :
    lrCoeffN_def ν λ μ = lrCoeffN ν λ μ
```

is **not provable** in the current axiomatic setup (the axiom has
no characterizing equations). The intended workflow is:

1. Replace the `axiom lrCoeffN` declaration in
   `Hilbert15OQ02OQ03.lean` with `def lrCoeffN := lrCoeffN_def`.
2. Re-prove the only fact that previously came "free" from the
   axiom — namely `klyachko_theorem` — as a *theorem* (this is
   the parent slug `hilbert-15-oq-02-oq-03`'s actual open question).
3. The 2-row specialization `lrCoeff2` (already in
   `Hilbert15OQ02.lean`) is recovered as `lrCoeffN_def` on
   `Partition 2`. Proving `lrCoeffN_def ν λ μ = lrCoeff2 ν λ μ`
   for `n = 2` is a tractable subgoal that anchors the definition.

## Scope Boundary

In scope for *this* slug:

- `SkewShape n` (or equivalent encoding)
- `SkewSSYTFin n ν μ` 
- `reverseRowWord`
- `isLatticeWord`
- `lrCoeffN_def`
- `lrCoeffN_def_two_eq_lrCoeff2` (the n = 2 anchoring lemma)
- `Decidable` / `Fintype` infrastructure

Out of scope (separate downstream targets):

- Replacing the axiom in `Hilbert15OQ02OQ03.lean` (a follow-up
  iteration once the definition has been independently exercised).
- Klyachko's theorem itself (parent slug
  `hilbert-15-oq-02-oq-03`).
- Schubert-calculus interpretation (`hilbert-15-oq-01` /
  `Hilbert15SchubertCalculus.lean`).

## Estimate

≈ 300–400 lines Lean across 2–3 sessions:

- **S1 (this session)**: OBSERVE — survey, mathematical
  specification, Mathlib gap inventory. **No Lean changes.**
- **S2**: ACT — scaffold `Hilbert15OQ02OQ03OQ01.lean` with the four
  type-level definitions (`SkewShape`, `SkewSSYTFin`,
  `reverseRowWord`, `isLatticeWord`) and `lrCoeffN_def`, plus
  finiteness/decidability instances. Expect ~150 lines, 0 sorries
  on the definitions, 1–2 sorries on the routine instance proofs.
- **S3**: ACT — prove the 2-row anchoring lemma
  `lrCoeffN_def_two_eq_lrCoeff2`, exercising the definition against
  the existing `Hilbert15OQ02.lean` test cases.
- **S4** (optional): Convert the parent's `axiom lrCoeffN` to
  `def lrCoeffN := lrCoeffN_def` and propagate the corollary that
  `klyachko_theorem` is the *only* remaining axiom in OQ-02-OQ-03
  (other than `admissible`, which is OQ-03 territory).

## References

- Fulton, W. (1997). *Young Tableaux* (LMS Student Texts 35),
  Cambridge UP. Chapter 5: "The Littlewood–Richardson rule".
- Stanley, R.P. (1999). *Enumerative Combinatorics* Vol. 2,
  Cambridge UP. Appendix 1 (A.1.3).
- Macdonald, I.G. (1995). *Symmetric Functions and Hall Polynomials*
  (2nd ed.). §I.9 "The Littlewood–Richardson rule".
- Knutson, A. & Tao, T. (1999). "The honeycomb model of GL_n tensor
  products I". *JAMS* 12, 1055–1090. (Alternative combinatorial
  model — equivalent to the lattice-word formulation.)

## Mathlib mapping (v4.26.0)

| Symbol | Status |
|---|---|
| `YoungDiagram` | exists (used by `BallotProblemOQ03OQ01OQ02.lean`) |
| `StandardYoungTableau` | exists (used by `BallotProblemOQ03OQ01OQ02.lean`) |
| `SemistandardYoungTableau` | **not present** at pinned rev |
| Gallery's `SSYTFin n k sh` | in `BallotProblemOQ03OQ01OQ01OQ01.lean:177` — straight-shape only |
| `SkewYoungDiagram` / skew shape | **not present** |
| Reverse row reading word | **not present** |
| Lattice / ballot word predicate | **not present** |
| `lrCoeff2` | gallery-internal, in `Hilbert15OQ02.lean:131` — 2-row case |
| General `lrCoeffN` | **axiom** in `Hilbert15OQ02OQ03.lean:128` |

The gap is real: every ingredient downstream of `YoungDiagram` is
missing. This is consistent with the pool note "Mathlib's
developing combinatorics for Young tableaux … needs to be extended
with the reverse-row-reading-word", and explains why the parent
slug took the axiomatic route.
