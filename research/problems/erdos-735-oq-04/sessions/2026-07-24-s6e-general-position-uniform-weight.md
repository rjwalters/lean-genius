# S6e (2026-07-24, researcher-3): the general-position uniform-weight theorem

## Goal

Discharge the S6 roadmap's S6e milestone: abstract the S6a tetrahedron argument
("a rank-2 flat cannot hold four affinely independent points, so every 2-flat
sum is exactly 3") into the general theorem behind it.

## Outcome (0 axioms, 0 sorries)

New leaf `proofs/Proofs/Erdos735OQ04GeneralPosition.lean` (~180 LOC, namespace
`Erdos735OQ04GenPos`, auto-discovered by the lakefile glob — no `Proofs.lean`
registration needed):

| Declaration | Content |
|---|---|
| `IsKFlatGeneralPositionD k P` | no rank-`k` flat contains more than `k+1` points of `P` |
| `isKFlatMagic_of_kFlatGeneralPosition` | **general-position ⟹ magic**: uniform weight `1`, magic constant `k+1` |
| `kFlatGeneralPositionD_of_affineIndependent` | affinely independent configs are in k-flat general position for every `k` |
| `isKFlatMagic_of_affineIndependent` | simplex-type configs are k-flat magic for **every** `k` simultaneously |
| `kFlatGeneralPositionD_one_of_generalPosition` | parent's class-2 (`IsGeneralPositionD`) ⟹ bound form at `k = 1` |
| `isKFlatMagic_one_of_generalPosition` | **class-2 forward implication of the S5 classification axiom, proved outright, all `d`** |

Verification: `lake env lean` exit 0 (zero diagnostics) on the worktree's
pinned v4.31.0 toolchain (mathlib `9a9483a929` — byte-identical to
origin/main's pin); parent oleans compiled by hand
(`lake env lean -o .lake/build/lib/lean/Proofs/….olean`). `#print axioms` on
all three headline theorems: `[propext, Classical.choice, Quot.sound]` — no
dependence on the S5 classification axiom.

## Why this matters for the slug

* The S6a tetrahedron (`d = 3, k = 2, c = 3`) is now one instance of a uniform
  family: **the conjectured higher-flat magic classes are inhabited at every
  dimension and every flat rank** (`isKFlatMagic_of_affineIndependent`).
* The S5 axiom `oneflat_classification_higher_dim` asserts a four-class *iff*
  for `d ≥ 3`. One of its eight implication-pieces — "general position ⟹
  1-flat magic" — is now a theorem, unconditionally and in every dimension.
  The axiom's genuinely open content shrinks correspondingly.

## Proof notes

* Magic sum: `ConfigKFlat` supplies `card ≥ k+1`; general position supplies
  `≤ k+1`; `le_antisymm` then the S6a sum idiom
  (`Finset.sum_congr rfl (fun p hp => dif_pos …)`, `Finset.sum_const`,
  `Nat.smul_one_eq_cast`).
* Rank bound: extract `s ⊆ filter` with `card = k+2`
  (`Finset.exists_subset_card_eq`), restrict the affinely independent family
  along the Finset-subtype inclusion (`AffineIndependent.comp_embedding`),
  `AffineIndependent.finrank_vectorSpan` (with `Fintype.card_coe`), then
  `affineSpan_le` → `direction_affineSpan` → `AffineSubspace.direction_le` →
  `Module.finrank_eq_of_rank_eq` + `Submodule.finrank_mono` → `omega`.
* Class-2 bridge: `Finset.card_eq_three` on a card-3 subset of the filter,
  feed the three membership pairs to `IsGeneralPositionD`.

## v4.31 gotchas (new this session)

* `congrArg Subtype.val hxy`, where `hxy` is a (beta-redex) equality of
  `Subtype.mk`s in `↥P` but the expected type is a val-equality for `↥s`,
  elaborates `congrArg` **at the wrong subtype** ("expected `x = y`") — use
  `Subtype.ext (Subtype.mk_eq_mk.mp hxy)` instead.
* `Finset.exists_subset_card_eq : n ≤ s.card → ∃ t ⊆ s, t.card = n` is the
  current name (`exists_smaller_set` era ended).

## Next

* S6d: dodecahedron/icosahedron — decide witness vs refutation (likely
  refutations à la octa/cube: both have 3-point-coplanar face structures with
  more than k+1 points per flat — check face lattices first).
* S7: gallery JSON (`src/data/proofs/` entry for the slug — still missing).
* `IsIncenterConfigD` tightening (structural skeleton → genuine incenter
  condition).
