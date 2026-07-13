# pascals-hexagon-oq-03

**Parent**: `pascals-hexagon` (Pascal's Hexagon Theorem, Wiedijk #28)
**Open Question Index**: `conclusion.openQuestions[2]`

## Question (verbatim)

> Can the 60-Pascal-line configuration be formalized, including Steiner
> and Kirkman point counts?

## Mathematical background

Given six points $A, B, C, D, E, F$ on a non-degenerate conic, Pascal's
Hexagon Theorem yields a Pascal line for each ordering of the six points
as a cyclic hexagon. Two orderings produce the same Pascal line iff they
differ by a cyclic rotation (6 elements) or by reversal (×2). Hence the
dihedral group $D_6$ of order 12 acts on the symmetric group
$\mathrm{Sym}(6)$ of order 720, and the number of distinct hexagonal
labelings is

$$|\mathrm{Sym}(6) / D_6| = \frac{720}{12} = 60.$$

This is the **Hexagrammum Mysticum** of six points on a conic, first
studied by Steiner and Kirkman in the 1820s–1840s. The 60 Pascal lines
exhibit a rich incidence structure:

- **60 Pascal lines** — one per hexagonal labeling.
- **20 Steiner points** — each Steiner point is the concurrent intersection of 3 specific Pascal lines. Steiner showed that the 20 Steiner points lie on **4 Cayley lines** (5 points each).
- **60 Kirkman points** — each Kirkman point also lies on 3 Pascal lines, but the triples form a different combinatorial pattern from the Steiner triples.
- **15 Plücker lines** — each Plücker line passes through 4 Kirkman points.
- **15 Salmon points** — points of concurrency of Plücker lines, with 3 Plücker lines through each.

The full incidence diagram (60+20+60+15+15) is one of the most intricate
configurations in classical projective geometry, predating finite-incidence
geometry by half a century.

## Why this is formalizable

The combinatorial side is **purely combinatorial** once Pascal's theorem
is in hand:

1. **Hexagonal labelings.** The set $\mathrm{Sym}(6) / D_6$ has 60
   elements; Lagrange's theorem reduces this to showing the dihedral
   subgroup $\langle \rho, \sigma \rangle \subset \mathrm{Sym}(6)$ has
   order 12. This is a concrete finite group computation, well within
   Mathlib's `Subgroup.closure` + `Fintype.card` machinery.

2. **Pascal-line map.** Given a labeling $\pi : \mathrm{Fin}\,6 \to
   \mathrm{Fin}\,6$ and an inscribed hexagon $A, B, C, D, E, F$,
   permuting via $\pi$ yields a new ordering whose Pascal points
   determine a Pascal line. Two labelings in the same $D_6$ orbit give
   the *same* Pascal line; this is a "well-defined on the quotient"
   computation.

3. **Steiner / Kirkman counts.** Each of the 60 Pascal lines is
   characterized by its hexagonal labeling. The Steiner triples and
   Kirkman triples are explicitly enumerable subsets of
   $\binom{60}{3} = 34{,}220$ triples; the counts (20 and 60) follow
   from a finite enumeration plus a concurrence check. In Lean this
   maps to `Finset.filter` + `Finset.card`.

The deep work is **showing concurrency** at each Steiner / Kirkman
point. This requires either:

- (a) Coordinate proofs via the standard conic + projective transforms (analogous to `pascal_std_conic` for the basic theorem).
- (b) Symbolic algebra in the projective coordinates, which is amenable to `ring` / `polyrith` for each fixed triple.
- (c) The Cayley-Bacharach axiom (already used in the parent), which can be applied to each cubic pair underlying a Steiner / Kirkman triple.

For the **S1 scaffold**, we formalize the *combinatorial framework* (60
labelings, statement of the configuration, structures for Steiner /
Kirkman points) and leave the concurrence proofs to sub-OQs.

## Resolution at the strategy level: **YES**

The 60-Pascal-line configuration **can** be formalized in Lean 4 + Mathlib:

1. **Combinatorial backbone** (~150 lines) — define
   `HexagonLabeling := Sym(6) ⧸ D_6`, prove cardinality 60.
2. **Pascal-line map** (~100 lines) — `pascalLine : HexagonLabeling →
   InscribedHexagon → ProjLine`, well-defined on the quotient.
3. **Steiner / Kirkman structures** (~150 lines) — define
   `SteinerPoint`, `KirkmanPoint` as triples-with-concurrency.
4. **Concurrence proofs** (~400 lines per Steiner triple, ~400 per
   Kirkman triple) — apply the Cayley-Bacharach axiom or direct
   coordinate computation.
5. **Counts** (~100 lines) — `Finset.card` over the explicitly
   enumerated triples.

Total roadmap: ~900 lines (S1 scaffold ~280; sub-OQs spread over OQ-03-OQ-01 through OQ-03-OQ-04).

## Sub-OQ decomposition

- **OQ-03-OQ-01** (~150 lines): Hexagonal labelings — define cyclic
  rotation `hexRot` and reversal `hexRev` on `Fin 6`, prove
  `hexagonalGroup := ⟨hexRot, hexRev⟩` has order 12, derive
  `card_hexagon_labelings = 60` via Lagrange.

- **OQ-03-OQ-02** (~100 lines): Pascal-line map — well-defined
  `pascalLine` from `HexagonLabeling` to `ProjLine`, using the
  hexagon-permutation lemma.

- **OQ-03-OQ-03** (~400 lines): Steiner points — enumerate the 20
  Steiner triples, prove concurrence for one representative triple
  (the rest follow by symmetry).

- **OQ-03-OQ-04** (~400 lines): Kirkman points — enumerate the 60
  Kirkman triples, prove concurrence for one representative.

- **OQ-03-OQ-05** (optional, ~200 lines): Cayley lines and Plücker
  lines — extend to the full 60+20+60+15+15 configuration.

## S1 scaffold deliverable

- `proofs/Proofs/PascalsHexagonOQ03.lean`: ~250 lines containing
  `hexRot`, `hexRev`, `hexagonalGroup`, `HexagonLabeling`,
  `card_sym6` (proved, no sorry), `card_hexagon_labelings` (sorry,
  OQ-03-OQ-01), `pascalLine` (sorry, OQ-03-OQ-02), `SteinerPoint`,
  `KirkmanPoint`, and the main statement
  `hexagrammum_mysticum_60_pascal_lines`.

- Gallery entry `src/data/proofs/pascals-hexagon-oq-03/` with
  meta.json, annotations.json, index.ts.

- This problem.md plus `state.md` with iteration log.

## References

- Pascal, *Essai pour les coniques* (1639).
- Steiner, *Annales de Gergonne* (1827) — first explicit count of 60 Pascal lines.
- Kirkman, *Quart. J. Math.* (1849) — 60 Kirkman points.
- Cayley, *Phil. Trans. Roy. Soc.* (1849) — 20 Cayley lines.
- Salmon, *Conic Sections* (1879) — classical presentation.
- Conway & Ryba, "The Pascal Mysticum Demystified" (2012) — modern combinatorial treatment via $S_6$ outer automorphism.
- Wiedijk #28 — the parent Pascal's theorem entry in the 100 Theorems list.
