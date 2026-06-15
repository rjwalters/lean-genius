# Knowledge: abel-ruffini-galois-extensions-oq-04-oq-01 (upstreaming JordanHolderLattice (Subgroup G))

## Problem framing
Parent `...OQ04` proves Jordan-Hölder for finite groups by instantiating
`JordanHolderLattice (Subgroup G)` — an explicit Mathlib TODO. OQ-04-OQ-01 asks
whether that instance can go upstream.

## Insight 1 — It's a packaging problem, not a math problem
The local instance is fully proved (0 sorries, 0 axioms). Mathlib's TODO
(`Order/JordanHolder.lean` L51-68) is a **design** concern: a `JordanHolderLattice`
instance for `ModularLattice` would clash with the module instance (incompatible
`Iso`), so global instances cause a diamond. Mathlib's own resolution for modules
(NOTE L68): a scoped, non-global instance `JordanHolderModule.instJordanHolderLattice`,
NOT via `ModularLattice`. **Upstream the subgroup instance the same way** — a
non-global namespaced instance (e.g. `JordanHolderSubgroup`).

## Insight 2 — The two non-trivial JordanHolderLattice axioms (group case)
With `IsMaximal H K := IsMaxNorm H K` (H a maximal proper *normal* subgroup of K):
- **A1 `sup_eq_of_isMaximal`**: distinct maximal-normal `x,y` of `z` satisfy
  `x ⊔ y = z`. (If `x⊔y` were `x`, then `y ≤ x`, contradicting `y` maximal in `z`.)
- **A2 `isMaximal_inf_left_of_isMaximal_sup`**: if `x,y` are both maximal-normal in
  `x⊔y`, then `x⊓y` is maximal-normal in `x` (second-isomorphism / butterfly).
Both are consequences of the second isomorphism theorem; Mathlib bearers used in
the local proof: `Subgroup.subgroupOf_sup`, `Subgroup.mem_sup`,
`Subgroup.inf_subgroupOf_right`, `CompositionSeries.jordan_holder`.

## Insight 3 — Cert anchor (`verify_jordan_holder_lattice.py`)
Brute-force subgroup lattices verify A1 + A2 on V4 (6/6, 6/6), C6 (2/2, 2/2),
S3 (vacuous — only A3 is maximal-normal), D4 order 8 (18/18, 18/18). Regression
oracle for the re-namespaced upstream instance.

## Open threads
- Track the Mathlib TODO; a `composition-series-across-homomorphisms` API is the
  other piece the TODO requests (orthogonal to the instance).
- Confirm whether a `ModularLattice` `JordanHolderLattice` instance has landed
  upstream (would force the subgroup instance to be non-global regardless).

## Links
- Parent: [[abel-ruffini-galois-extensions-oq-04]] (Jordan-Hölder for finite groups).
- Same make-ephemeral-verification-durable / bearer-survey vein as
  [[project-researcher-3-20260614m-konigsberg-matrixtree-orient]].
