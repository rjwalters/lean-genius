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
oracle for the re-namespaced upstream instance. **S2 (2026-06-15) added a
map-obstruction witness** (see Insight 4) — script still exits 0 / ALL PASS.

## Insight 4 — The "map composition series across homomorphisms" piece (S2, 2026-06-15)
The TODO asks for two things: (i) the subgroup *instance* (Insights 1–2), and
(ii) **"an API for mapping composition series across homomorphisms."** S2 pins
down what (ii) actually needs, against the repo pin and master:

- **The generic carrier already exists** at BOTH v4.26.0 and master:
  `RelSeries.map (p : RelSeries r) (f : r.Hom s) : RelSeries s`
  (`Mathlib/Order/RelSeries.lean:372`, with `@[simp] head_map`/`last_map`),
  where `r.Hom s` is a function preserving the relation (`f.1 : α → β`,
  `f.2 : r a b → s (f a) (f b)`). So pushing a series along a relation-preserving
  map is **not** the missing infrastructure.
- **The missing piece is the group-specific `RelSeries.Hom` builder.** The naive
  candidate — push a `CompositionSeries (Subgroup G)` along `Subgroup.map φ` —
  does **not** instantiate `r.Hom s` for the JordanHolder `IsMaximal = IsMaxNorm`
  relation, because **maximal-normality is not stable under images with
  nontrivial kernel**. Concrete obstruction (now in the cert):
  `G = C4 = ⟨g⟩`, `N = ⟨g²⟩ = ker φ`, quotient `φ : C4 ↠ C4/N ≅ C2`. The covering
  `{e} ◁ ⟨g²⟩` maps to `φ{e} = φ⟨g²⟩ = {e}`, i.e. `{e} ◁ {e}` — not strict, not a
  covering, so `Subgroup.map φ` fails the `r.Hom s` *step law*.
- **Consequence**: the map API the TODO wants is not `RelSeries.map (Subgroup.map φ)`.
  It must restrict φ (injective ⇒ images preserve the covering) or handle quotient
  steps through the second isomorphism theorem (collapse the kernel-side prefix
  and re-index). This is a sharper statement of the remaining upstream work than
  S1's "an API for mapping composition series across homomorphisms (orthogonal)".

## Open threads
- **OQ still OPEN at master (re-confirmed S2, 2026-06-15)**: the TODO block in
  `Mathlib/Order/JordanHolder.lean` is present at v4.26.0 and master (master file
  grew 420→454 LOC, now under `@[expose] public section`, but the TODO/NOTE at
  L51-68 is unchanged). No `JordanHolderLattice (Subgroup G)` instance has landed
  (`search/code JordanHolderLattice Subgroup` → only the TODO mention +
  `nolints.json`). So this OQ does not auto-close.
- The map-API builder (Insight 4) — restrict to injective φ first; the quotient
  case needs the second-iso-theorem re-indexing.
- Confirm whether a `ModularLattice` `JordanHolderLattice` instance has landed
  upstream (would force the subgroup instance to be non-global regardless).
  **S2: still not present at master.**

## Links
- Parent: [[abel-ruffini-galois-extensions-oq-04]] (Jordan-Hölder for finite groups).
- Same make-ephemeral-verification-durable / bearer-survey vein as
  [[project-researcher-3-20260614m-konigsberg-matrixtree-orient]].
