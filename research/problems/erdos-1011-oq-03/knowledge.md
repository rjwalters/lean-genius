# Knowledge: Compute f_5(n) (Erdős #1011, OQ-03)

## Problem

f_r(n) = minimal m such that every n-vertex graph with ≥ m edges and chromatic
number ≥ r contains a triangle. OQ-03 asks for **f_5(n)**, the first case beyond
the 2024 determination of f_4(n).

## Known data (from Erdos1011Problem.lean)

| r | f_r(n)              | shift s | constant c |
|---|---------------------|---------|------------|
| 2 | ⌊n²/4⌋ + 1          | 0       | 1          | Turán 1941
| 3 | ⌊(n-1)²/4⌋ + 2      | 1       | 2          | Erdős–Gallai 1962
| 4 | ⌊(n-3)²/4⌋ + 6 (n≥150) | 3    | 6          | Ren–Wang–Wang–Yang 2024
| 5 | **open**            | 6 (conj.) | ?        | this entry

Asymptotic (Simonovits): f_r(n) = n²/4 − g(r)·n/2 + O(1), with
(1/2−o(1))r²log r ≤ g(r) ≤ (2+o(1))r²log r (Davies–Illingworth 2022;
Hefetz–Horn–King–Pfender 2025).

## What was proved this session (Erdos1011OQ03.lean, 0 new axioms)

- `f_antitone_in_chromatic : r ≤ r' → f r' n ≤ f r n`. The threshold is antitone
  in the chromatic parameter: a stronger χ-hypothesis lowers the forcing
  threshold. Derived purely from the `sInf` definition of `f` (subset of
  defining sets + `Nat.sInf_le`/`Nat.sInf_mem`), with nonemptiness from
  `card_edgeFinset_le_card_choose_two`.
- `f_five_le_f_four : f 5 n ≤ f 4 n` and the chain `f 5 ≤ f 4 ≤ f 3 ≤ f 2`.
  Together with the known f_4 value this gives the unconditional upper bound
  f_5(n) ≤ ⌊(n-3)²/4⌋ + 6 (n ≥ 150).
- `chromaticShift r := (r-1).choose 2`; `chromaticShift_known` certifies the
  shift sequence 0,1,3 and predicts 6 for r=5; `chromaticShift_eq`,
  `chromaticShift_mono`.
- `shiftConjecture`, `f5Conjecture` recorded as Props (not proved);
  `shiftConjecture_imp_f5`.

## Key insight

The shift `n − s` in the leading ⌊·²/4⌋ term follows s = C(r-1,2) exactly across
all three solved cases. This is the structural fingerprint of the extremal
construction: a balanced complete bipartite (Turán) graph with a small
triangle-free χ=r gadget grafted onto one side, the gadget occupying ~C(r-1,2)
"shifted" vertices. The additive constants 1, 2, 6 are not yet identified with a
closed form and are the genuinely open part for r = 5.

## Session 2 (researcher-1): build repair + boundary value + characterization

**Critical finding: the entry never actually compiled.** The parent
`Erdos1011Problem.lean` (an `additionalFile`) had three independent build breaks
on `main`, and `Erdos1011OQ03.lean` had two latent bugs that only surface once
the parent builds:

1. Parent `g` used instance binders inside `∃` (`∃ (V : Type*) [Fintype V]`),
   invalid Lean 4 — `∃` does not take `[…]` binders (only `∀` does). Rewrote with
   anonymous hypotheses `(_ : Fintype V)`, dropped the spurious `[DecidableRel] →`.
2. Parent `simonovits_asymptotic` mixed ℤ/ℕ without coercions. Added `(n : ℤ)`,
   `(C : ℤ)`.
3. `f`/`g` were universe-polymorphic (`∀ (V : Type*)`), leaking a free universe
   parameter into the `def … : Prop` conjectures → "universe level metavariables".
   Quantified over `Type`; value unchanged (predicate fixes `card V = n`).
4. OQ03 `forces_nonempty` / `f_antitone_in_chromatic` had redundant
   `haveI := instF; …` after `intro`. The `intro`'d instance-implicit binders are
   already local instances; the `haveI` duplicates shadowed them, so `rw [hcard]`
   and the `f_forces` application saw a *different* `Fintype V` instance →
   "pattern not found" / "instance not definitionally equal". Removing the `haveI`
   lines fixed both. (Errored proofs were briefly replaced by `sorry`, which is
   why `#print axioms` momentarily showed `sorryAx`.)

**New mathematical content (0 axiom, verified):**
- `forces_mono` + `forces_iff_f_le : Forces r n m ↔ f r n ≤ m` — the forcing
  predicate is an up-set in the edge bound; `f r n` is exactly its least element.
- `chromaticNumber_le_card : χ(G) ≤ card V` (identity colouring `V ≃ Fin (card V)`).
- `f_eq_zero_of_lt : n < r → f r n = 0` — left boundary of the table: once `r`
  exceeds the vertex count, no graph attains `χ ≥ r`, so forcing is vacuous. The
  antitone-in-r value has bottomed out at 0.

After repair: parent + OQ01 + OQ03 all build clean; every OQ03 theorem
`#print axioms` reports only propext / Classical.choice / Quot.sound.
14 theorems, 4 defs, 0 axiom, 0 sorry, 234 lines.

## Honest status

The headline open problem (the value of f_5(n)) is **not solved**. The new
mathematical content is the antitonicity theorem and its corollary upper bound,
plus the up-set characterization (`forces_iff_f_le`) and the boundary value
(`f_eq_zero_of_lt`); the rest organizes known data and the conjecture. Verified,
axiom-free. Arguably the most consequential part of session 2 is the build
repair: the entry was marked `verified` but did not actually compile until now.

## Next steps

1. Lower bound via explicit construction (needs χ ≥ 5 lower bound in Lean —
   hard; Grötzsch / Mycielskian).
2. Identify the constant pattern 1, 2, 6 with an edge-count of the χ=r gadget.
3. If a sorry isolates cleanly (e.g. a numeric inequality from the construction),
   route to Aristotle.
