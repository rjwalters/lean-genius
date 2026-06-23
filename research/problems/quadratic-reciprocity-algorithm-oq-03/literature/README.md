# Literature for quadratic-reciprocity-algorithm-oq-03

This directory contains:
- Related papers and their summaries
- Links to relevant Mathlib documentation
- References to similar problems and their solutions

## Related Gallery Proofs

- `quadratic-reciprocity-algorithm` — direct parent; algorithmic (flip-and-reduce) presentation.
  Lean file `Proofs/QuadraticReciprocityOQ03.lean`.
- `QuadraticReciprocityAlgorithmOQ01.lean` — sibling answering the recursive-function form
  (`jacobiAlgo`, `jacobiAlgo_eq_jacobiSym`); the permutation-sign route here is disjoint from it.
- `quadratic-reciprocity` (gallery) — Gauss-sum / Eisenstein proof; cross-check for the statement.
- `primitive-roots` — cyclic structure of `(ZMod p)ˣ` used in the Zolotarev sign computation.

## External References

- Zolotarev, E. I. (1872). "Nouvelle démonstration de la loi de réciprocité de Legendre."
  *Nouvelles Annales de Mathématiques.* — original permutation-sign proof.
- Rousseau, G. (1994). "On the quadratic reciprocity law." *J. Austral. Math. Soc.* — modern
  permutation-sign exposition.
- Frobenius / Lerch — the row-vs-column shuffle reduction used for the reciprocity step (M2).

## Mathlib Documentation

- `Mathlib.NumberTheory.LegendreSymbol.Basic` — `legendreSym`, `legendreSym.eq_pow` (Euler's
  criterion link).
- `Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity` — existing `ZMod.quadratic_reciprocity`
  (statement reference / cross-check only).
- `Mathlib.GroupTheory.Perm.Sign` — `Equiv.Perm.sign`, `Equiv.Perm.sign_mul`, cycle-sign machinery.
- `Mathlib.GroupTheory.SpecificGroups.Cyclic` — `IsCyclic (ZMod p)ˣ`, generators.

Note: a string search for "Zolotarev" across the pinned Mathlib returns nothing — the bridging
lemma `legendreSym p a = sign πₐ` is not yet in Mathlib and is the core deliverable (M1).
