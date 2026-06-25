# S1 ORIENT — Pascal-line map well-definedness (OQ-03-OQ-02)

**Agent:** researcher-4 · **Date:** 2026-06-25 · **Phase:** OBSERVE → ORIENT

## Summary

Worked out the complete mathematical content of **OQ-03-OQ-02** (the
`pascalLine` definition-`sorry`): the precise action of the dihedral generators
`hexRot`, `hexRev` on the three Pascal points, with the exact signs coming from
cross-product antisymmetry. This is the well-definedness backbone that lets
`pascalLine` descend to `HexagonLabeling = Sym(6) ⧸ D₆`.

**Verification status: NOT machine-checked this session.** The local Lean build
is unusable (Docker wrapper down; host disk at 99%, 15 GiB free; an attempted
`lake exe cache unpack`/`get` corrupted the dependency oleans —
`aesop/.../Tactic.olean` and several Mathlib oleans report `invalid header`,
and `leantar` fails decompressing on the full disk). The proposed Lean below is
hand-derived and should be compiled before integration. I deliberately did
**not** edit the gallery file `PascalsHexagonOQ03.lean`, to avoid committing an
unverified change that could break the build.

## The action, derived by hand

Notation: `×` is `crossProduct`; it is bilinear and antisymmetric
(`cross_anticomm : -(v ×₃ w) = w ×₃ v`, i.e. `v × w = -(w × v)`).
`lineThrough = lineIntersection = crossProduct`.

```
pascalP = (A×B) × (D×E)        -- AB ∩ DE
pascalQ = (B×C) × (E×F)        -- BC ∩ EF
pascalR = (C×D) × (F×A)        -- CD ∩ FA
```

`permuteHexagon hex π` relabels vertices by `i ↦ hexVertex hex (π i)`.

### hexRot (cyclic +1): new labeling (A',…,F') = (B,C,D,E,F,A)

```
P' = (A'×B')×(D'×E') = (B×C)×(E×F) = pascalQ                      [exact]
Q' = (B'×C')×(E'×F') = (C×D)×(F×A) = pascalR                      [exact]
R' = (C'×D')×(F'×A') = (D×E)×(A×B) = -[(A×B)×(D×E)] = -pascalP     [sign]
```

So **hexRot: (P, Q, R) ↦ (Q, R, −P)**.

### hexRev (reversal i↦5−i): new labeling (A',…,F') = (F,E,D,C,B,A)

Using `F×E = -(E×F)`, `C×B = -(B×C)`, etc. (each inner factor flips sign; the
two flips cancel under bilinearity, then one outer `cross_anticomm` remains):

```
P' = (F×E)×(C×B) = (E×F)×(B×C) = -[(B×C)×(E×F)] = -pascalQ        [sign]
Q' = (E×D)×(B×A) = (D×E)×(A×B) = -[(A×B)×(D×E)] = -pascalP        [sign]
R' = (D×C)×(A×F) = (C×D)×(F×A) =  pascalR                         [exact]
```

So **hexRev: (P, Q, R) ↦ (−Q, −P, R)**.

### Consequence (well-definedness)

Both generators send `{[P],[Q],[R]}` to itself as a set of **projective**
points (sign is invisible projectively). The three points are collinear
(`pascal_hexagon_theorem`), so they span a single projective line, and that
line is fixed by `hexRot` and `hexRev`, hence by all of
`hexagonalGroup = ⟨hexRot, hexRev⟩ = D₆`. Therefore the assignment
`π ↦ Pascal-line(permuteHexagon hex π)` is constant on each `D₆`-coset and
descends to a well-defined map `HexagonLabeling → ProjLine`.

## Proposed Lean (UNVERIFIED — compile before use)

Replace the `pascalLine` definition-`sorry` (currently `PascalsHexagonOQ03.lean`
~line 631) with a representative-based total definition, and add the
generator-action lemmas as a new PART 4c. The lemmas turn `Fin 6` index
arithmetic (`hexRot k`, `hexRev k`) into vertex literals via `decide`, then
reduce to `crossProduct` identities closed by `cross_anticomm` or by coordinate
expansion (`cross_apply` + `ring`).

```lean
-- PART 4c: action of the dihedral generators on the Pascal points

theorem pascalP_permuteHexagon_hexRot {C : Conic} (hex : InscribedHexagon C) :
    pascalP (permuteHexagon hex hexRot) = pascalQ hex := by
  show lineIntersection (lineThrough (hexVertex hex (hexRot 0)) (hexVertex hex (hexRot 1)))
        (lineThrough (hexVertex hex (hexRot 3)) (hexVertex hex (hexRot 4)))
      = lineIntersection (lineThrough hex.B hex.C') (lineThrough hex.E hex.F)
  rw [show hexRot 0 = 1 from by decide, show hexRot 1 = 2 from by decide,
      show hexRot 3 = 4 from by decide, show hexRot 4 = 5 from by decide]
  rfl

theorem pascalQ_permuteHexagon_hexRot {C : Conic} (hex : InscribedHexagon C) :
    pascalQ (permuteHexagon hex hexRot) = pascalR hex := by
  show lineIntersection (lineThrough (hexVertex hex (hexRot 1)) (hexVertex hex (hexRot 2)))
        (lineThrough (hexVertex hex (hexRot 4)) (hexVertex hex (hexRot 5)))
      = lineIntersection (lineThrough hex.C' hex.D) (lineThrough hex.F hex.A)
  rw [show hexRot 1 = 2 from by decide, show hexRot 2 = 3 from by decide,
      show hexRot 4 = 5 from by decide, show hexRot 5 = 0 from by decide]
  rfl

theorem pascalR_permuteHexagon_hexRot {C : Conic} (hex : InscribedHexagon C) :
    pascalR (permuteHexagon hex hexRot) = -(pascalP hex) := by
  show lineIntersection (lineThrough (hexVertex hex (hexRot 2)) (hexVertex hex (hexRot 3)))
        (lineThrough (hexVertex hex (hexRot 5)) (hexVertex hex (hexRot 0)))
      = -(lineIntersection (lineThrough hex.A hex.B) (lineThrough hex.D hex.E))
  rw [show hexRot 2 = 3 from by decide, show hexRot 3 = 4 from by decide,
      show hexRot 5 = 0 from by decide, show hexRot 0 = 1 from by decide]
  -- goal: (D×E)×(A×B) = -((A×B)×(D×E))
  show lineIntersection (lineThrough hex.D hex.E) (lineThrough hex.A hex.B)
      = -(lineIntersection (lineThrough hex.A hex.B) (lineThrough hex.D hex.E))
  exact (cross_anticomm (lineThrough hex.A hex.B) (lineThrough hex.D hex.E)).symm

-- hexRev lemmas: same skeleton, but each Pascal point picks up sign flips on
-- BOTH inner lineThrough factors. Cleanest uniform tactic is coordinate
-- expansion (robust to all sign cases):
--   funext k; fin_cases k <;>
--     simp only [pascalP, pascalQ, pascalR, permuteHexagon, hexVertex,
--                lineIntersection, lineThrough, cross_apply, Pi.neg_apply,
--                Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
--     ring
-- with the hexRev k ↦ literal rewrites (decide) applied first.
theorem pascalP_permuteHexagon_hexRev {C : Conic} (hex : InscribedHexagon C) :
    pascalP (permuteHexagon hex hexRev) = -(pascalQ hex) := by
  sorry  -- coordinate ring; see tactic sketch above
theorem pascalQ_permuteHexagon_hexRev {C : Conic} (hex : InscribedHexagon C) :
    pascalQ (permuteHexagon hex hexRev) = -(pascalP hex) := by
  sorry
theorem pascalR_permuteHexagon_hexRev {C : Conic} (hex : InscribedHexagon C) :
    pascalR (permuteHexagon hex hexRev) = pascalR hex := by
  sorry

-- PART 5: the total definition (discharges the definition-sorry)
noncomputable def pascalLine
    (C : Conic) (hex : InscribedHexagon C) (lbl : HexagonLabeling) : ProjLine :=
  lineThrough (pascalP (permuteHexagon hex lbl.out'))
              (pascalQ (permuteHexagon hex lbl.out'))
```

### Open follow-on for a later session (with a working build)

Full quotient-level well-definedness as a **projective** line equality needs a
notion of `ProjLine` equality up to nonzero scalar plus a nondegeneracy
hypothesis (so the line is actually determined by two of the three collinear
points). The generator-action lemmas above are the hard geometric input; the
remaining work is the projective-equivalence bookkeeping
(`P×Q ∝ Q×R` when `P,Q,R` collinear and pairwise independent). The two
downstream count theorems `steiner_count_eq_20` / `kirkman_count_eq_60` remain
genuinely open and out of scope here.

## Risk notes / gotchas

- `lbl.out'` = `Quotient.out'` is the standard representative for `G ⧸ H` in
  Mathlib (`Quotient.out_eq'`). Confirm it elaborates against
  `HexagonLabeling`'s `Setoid` instance when compiling.
- `hexRot k = ℓ` and `hexRev k = ℓ` are `by decide` (the file already discharges
  `hexRot`/`hexRev` facts by `decide`).
- `hexVertex hex ℓ = hex.<field>` should hold by `rfl` once the index is a
  `Fin 6` literal (`hexVertex` pattern-matches on `⟨ℓ, _⟩`).
- Defining `pascalLine` via `out'` makes downstream `SteinerPoint`/`KirkmanPoint`
  typecheck; `hexagrammum_mysticum_pascal_lines` stays `rfl`.
- **Environment:** do NOT `lake exe cache unpack` onto this host while the disk
  is ~99% full — it produced truncated/`invalid header` oleans. Use Docker
  (`./proofs/scripts/docker-build.sh Proofs.PascalsHexagonOQ03`) once it is back,
  or free disk first.
