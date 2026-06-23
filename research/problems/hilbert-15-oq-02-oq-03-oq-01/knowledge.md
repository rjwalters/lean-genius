# Knowledge — `hilbert-15-oq-02-oq-03-oq-01` (Formalize `lrCoeffN`)

## Session log

### S1 (researcher-1, 2026-05-11) — OBSERVE

Survey-only iteration. **No Lean changes.** Established mathematical
specification, Mathlib gap inventory, and 4-iteration roadmap.

#### Key insights

1. **Axiom 1 (`lrCoeffN`) is structurally easier than axioms 2–3 in
   the parent file.** The parent slug `hilbert-15-oq-02-oq-03`
   carries 3 axioms (`lrCoeffN`, `admissible`, `klyachko_theorem`).
   Of these, `lrCoeffN` is the only one with a fully explicit
   combinatorial definition in the literature; the other two are
   either recursive on `lrCoeffN` or are the deep Klyachko/Belkale
   theorem itself. So OQ-01 is a *Mathlib-style scaffold*, not a
   research result.

2. **The right level of abstraction is `Fin n` entries, not `ℕ`
   entries.** Mathlib's `StandardYoungTableau` uses `ℕ` for entries
   but the LR rule requires entries in `{1, …, n}` (the row labels
   of `λ`). Use `SSYTFin n k sh` (already in
   `BallotProblemOQ03OQ01OQ01OQ01.lean:177`) as the template — it
   enforces the bounded-entry constraint via the codomain `Fin n`,
   which makes finiteness automatic.

3. **Reverse row reading word — convention matters.** Fulton (1997,
   Ch. 5) reads each row *right to left*, *top to bottom*. Stanley
   (EC Vol. 2, A.1.3) reads *right to left*, *bottom to top*. The
   gallery's `lrCoeff2` in `Hilbert15OQ02.lean:131` follows the
   Fulton convention (verified by inspection of the comment block
   at lines 99–122 and the explicit ballot-condition analysis).
   For consistency with the existing 2-row anchor, **use the Fulton
   order**.

4. **Lattice word ≡ ballot word ≡ Yamanouchi word.** Three names
   for the same predicate. Define once as `isLatticeWord` and add
   docstring listing the synonyms — saves search time for the next
   researcher.

5. **The 2-row anchoring lemma is the right *first* theorem after
   the definitions.** It serves three purposes simultaneously:
   - sanity-checks that the abstract definition reduces to the
     known computable case;
   - exercises the `reverseRowWord` / `isLatticeWord` predicates on
     concrete data (Gr(2,4) Chow ring constants from
     `Hilbert15OQ01.lean`);
   - leaves a *concrete subgoal* (rather than an `axiom_replace`
     refactor) for S3, which is friendlier to Aristotle / manual
     proof search.

6. **`Decidable` is non-negotiable.** Klyachko's theorem (axiom 3)
   characterizes `0 < lrCoeffN` via *decidable* Horn inequalities,
   so `lrCoeffN > 0` must itself be decidable. The proposed
   `lrCoeffN_def` is decidable by construction (a `Fintype.card`
   guarded by a decidable `if`), so this requirement is met without
   extra work — but it must be *explicitly* stated as an `instance`
   so that downstream `decide` / `Decidable.decide` invocations in
   `Hilbert15OQ02OQ03.lean` continue to typecheck after the axiom
   is replaced.

#### Mathlib API map (v4.26.0)

| Need | Mathlib symbol | Status |
|---|---|---|
| Young diagram | `YoungDiagram` | available |
| `cell ∈ diagram` | `YoungDiagram.mem_cells` | available |
| Row length | `YoungDiagram.rowLen` | available |
| Standard YT | `StandardYoungTableau` | available |
| Semistandard YT | `SemistandardYoungTableau` | **missing** |
| Skew YT | `SkewYoungTableau` | **missing** |
| Reverse reading word | — | **missing** |
| Lattice word | — | **missing** |
| LR rule | — | **missing** |

(Verified via `Grep` over `proofs/Proofs/` — gallery's
`BallotProblemOQ03OQ01OQ02.lean` is the only file using Mathlib's
`YoungDiagram`/`StandardYoungTableau`. No project file references a
Mathlib `SkewYoungDiagram` or `lattice_word`.)

#### Mathematical specification

(Full spec in `problem.md`.)

The combinatorial count
> `c^ν_{λ,μ} = #{ T : ν/μ → Fin n | T row-weak, col-strict,
>                  content(T) = λ, reverseRowWord(T) is a lattice word }`

is a **rank-1 monoid count** — there is no recursion, no fixed
point, no choice principle involved. It is exactly the kind of
finite-combinatorial counting that Lean's `Fintype.card` was
designed for.

## Built items

(None this iteration.)

## Mathlib gaps surfaced

1. **`SemistandardYoungTableau`** — no public definition at pinned
   Mathlib v4.26.0. (`SSYTFin n k sh` in
   `BallotProblemOQ03OQ01OQ01OQ01.lean:177` is the gallery's
   private analog, restricted to straight shapes with
   `Fin n`-valued entries.) Upstream blocker for any Schur-positive
   formalization.

2. **Skew shape encoding** — neither
   `Mathlib.Combinatorics.Young.YoungDiagram` nor the gallery
   carries a public `SkewYoungDiagram` (a pair `(ν, μ)` with
   `μ ⊆ ν`). Defining one cleanly is a small Mathlib PR in its own
   right.

3. **Reverse row reading word + lattice word predicate** — neither
   appears anywhere in the Mathlib `Combinatorics` library. These
   are the *load-bearing* pieces of any LR-rule formalization.

4. **LR rule (general n)** — every Schur-positive theorem in the
   gallery's Hilbert-15 cluster currently bottoms out in the axiom
   `lrCoeffN` (parent file). This slug is the single point of
   leverage to remove that.

## Next steps

- **S2** (next session): scaffold `Hilbert15OQ02OQ03OQ01.lean` with
  four definitions (`SkewShape`, `SkewSSYTFin`, `reverseRowWord`,
  `isLatticeWord`) + `lrCoeffN_def`. Target ~150 lines, 0 sorries
  on the type-level definitions, decidability/finiteness instances.

- **S3**: prove `lrCoeffN_def_two_eq_lrCoeff2` (2-row anchoring
  lemma) — bridges the new abstract definition to the existing
  computable `lrCoeff2`. Exercises the definition on Gr(2,4) test
  data from `Hilbert15OQ01.lean`.

- **S4** (optional): refactor `Hilbert15OQ02OQ03.lean` to replace
  `axiom lrCoeffN` with `def lrCoeffN := lrCoeffN_def`. Verifies
  that nothing downstream breaks (the axiom was only used in
  `klyachko_theorem`'s statement and in `lr_polytime_positivity`'s
  decidable wrap).

## Honesty notes

- This slug is **scaffolding**, not research. The result
  (computable `lrCoeffN`) is well-known since Littlewood 1934. The
  contribution is *making it Lean-native* and removing an axiom
  declaration. Per the researcher honesty rules: do not describe
  this as a breakthrough.

- The 2-row anchoring lemma is the *minimum convincing test* for
  the definition. Without it the new `lrCoeffN_def` is unverified
  scaffolding. With it the definition is exercised against 7
  concrete Gr(2,4) Chow ring constants already verified in
  `Hilbert15OQ02.lean`.
