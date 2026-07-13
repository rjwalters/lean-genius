# sperner-simplicial-instance-oq-05 — Knowledge / Mathlib + Gallery API survey

S1 audit of what is already in the gallery and Mathlib v4.26.0, against
the three candidate targets in `problem.md`. All gallery line numbers
verified against `proofs/Proofs/SpernerSimplicialInstance.lean` and
`proofs/Proofs/SpernerMathlib4.lean` at the merge of
`6457155f73e` (origin/main, 2026-05-12).

## A. Gallery infrastructure already verified and usable

### `Proofs/SpernerMathlib4.lean` — the abstract `CellComplex` framework

- `structure CellComplex (V : Type*) [DecidableEq V] (d : ℕ)` (line 404)
  with fields:
  - `Cell : Type`, `cellDecEq : DecidableEq Cell`, `cellFintype : Fintype Cell`
    — *all three are essential for computability*; the `attribute [instance]`
    declarations on lines 431–432 make them auto-resolvable.
  - `adj : Cell → Fin (d+1) → Option (Cell × Fin (d+1))` — adjacency oracle
    in `Option` form. Computable iff the concrete instance supplies a
    computable `adj`.
- `def IsPanchromatic` (line 440): `Function.Surjective (c ∘ K.vertex s)`.
- `def IsDoor` (line 446): `∀ j : Fin d, ∃ i : Fin (d+1), i ≠ k ∧ c (vertex s i) = castSucc j`.
- `instance decidableIsPanchromatic` (line 452), `instance decidableIsDoor`
  (line 459). **Both are `Decidable` for free** since `Fin (d+1)`, function
  application, and equality on `Fin (d+1)` are all decidable.
  Consequence: `Finset.filter` and `Finset.toList` on the panchromatic /
  door predicates *already compute*.
- `theorem door_count_parity` (line 386): a finite-set involution argument
  showing the number of door positions of a fixed cell is `0` or `2`
  except when the cell is panchromatic (in which case it's `1`).
  *This is the algorithmic heart of Scarf's pivoting.* The function
  `private def adjMap` (line 467) is the pivoting step.
- `theorem sperner_parity` (line 652): panchromatic count ≡ boundary
  door count `(mod 2)`.
- `theorem sperner` (line 714): existence — odd boundary doors ⇒
  `∃ s : K.Cell, IsPanchromatic c K s`. **Non-constructive** in form: the
  proof traces back through `sperner_parity` and `exists_of_sum_eq_one`
  (line 108), which uses `Finset.exists_ne_zero_of_sum_ne_zero` and
  `Classical.choose`-flavoured `Finset.exists` API.

### `Proofs/SpernerSimplicialInstance.lean` — the bridge

- `structure Triangulation V n` (line 81) with the same fields as
  `CellComplex` plus `vertex_injective`.
- `def toCellComplex` (line 123) — trivial field-projection bridge.
- `theorem Triangulation.sperner` (line 147) — one-line application
  of `CellComplex.sperner`.
- `theorem boundary_doors_odd` (line 173) — recipe for showing odd
  boundary doors given (a) a Sperner coloring and (b) per-face
  decomposition data.

#### The 1-d worked example (lines ~789–992)

- `def ivtx (m : ℕ) (hm : 0 < m) (i : Fin m) (k : Fin 2) : ℕ`:
  `if k = 0 then i.val else i.val + 1`. **Fully computable.**
- `def iadj (m : ℕ) : Fin m → Fin 2 → Option (Fin m × Fin 2)`:
  computable by case analysis on `k` and on `i.val + 1 < m` /
  `0 < i.val`. **Fully computable.**
- `def intervalTriangulation (m : ℕ) (hm : 0 < m) : Triangulation ℕ 1`
  (line 958): assembled from `ivtx` and `iadj`. **Fully computable**
  (no `Classical.choose`, no `Nonempty.some`, no `noncomputable`).
- `theorem interval_sperner` (line 982): the 1-d existence theorem
  via `Triangulation.sperner`.

#### The `AbstractSimplicialData` machinery (lines ~265–765)

- `structure AbstractSimplicialData V n` (line 265): bundles
  `topSimplices : Finset (Finset V)` with `card_eq` and the
  pseudomanifold containment lemmas.
- `def vertexEnum` (lines ~280–295): `(t.sort (· ≤ ·)).get` — **fully
  computable** (`Finset.sort` is computable on `[LinearOrder V]`).
- `noncomputable def findOppositeIdx` (line 367): **the bottleneck.**
  Uses `hex.choose` on the existential "∃ k : Fin (n+1), vertexEnum t ht k ∉ f".
  This existential is decidable in `k` (each `k`-membership in `f` is
  decidable on a `[DecidableEq V]`-typed `f : Finset V`), so the choice
  is *unnecessary* — a `Finset.filter (fun k => …) |>.min'` formulation
  would compute. See `problem.md` (C3) for the refactor sketch.
- `noncomputable def adjFn` (line 529): downstream of `findOppositeIdx`,
  also `noncomputable`. Once `findOppositeIdx` is fixed, this is a
  one-line cleanup.
- All lemmas `AbstractSimplicialData.*` (lines 295–765) are *propositions*,
  so they remain unchanged regardless of computability — they prove
  facts about `findOppositeIdx` and `adjFn` that hold for *any* choice
  satisfying the existential, computable or not.
- `def AbstractSimplicialData.toTriangulation` (cited in meta):
  builds a `Triangulation` instance from the unordered data. Currently
  `noncomputable` by transitive closure.

## B. Mathlib v4.26.0 infrastructure (verified by file presence)

### Computability / decidability foundations

- `Mathlib.Logic.Basic`, `Mathlib.Data.Fin.Basic`: `Decidable` instances
  for `Fin n`, `∀ i : Fin n, …`, `∃ i : Fin n, …`.
- `Mathlib.Data.Finset.Basic`, `Mathlib.Data.Finset.Sort`:
  - `Finset.toList : Finset α → List α` (computable, on `[DecidableEq α]`);
  - `Finset.sort : Finset α → List α` (computable, on `[LinearOrder α]`);
  - `Finset.filter` (computable on a decidable predicate);
  - `Finset.min'`, `Finset.min` (returns `Option`);
  - `List.head?`, `List.find?` (computable);
  - `Finset.image` (computable on `[DecidableEq β]`).
- `Mathlib.Data.Fintype.Basic`: `Fintype.exists` (non-computable in
  general) vs `Fintype.toFinset`, `(Finset.univ).toList`, `(Finset.univ).filter`
  (computable on a `[Fintype α] [DecidableEq α]`).
- `Mathlib.Tactic.Decide`: provides `decide` tactic for closing
  decidable goals via `Decidable.decide = true`.

### Sperner / fixed-point support not yet in Mathlib

- No `Mathlib.Combinatorics.Simplicial.Sperner` module — gallery is
  the only Lean 4 Sperner formalization.
- `Mathlib.Geometry.SimplicialComplex` exists but has *unordered*
  simplices (no `Fin (n+1)`-indexing); the `AbstractSimplicialData`
  structure in the gallery is the missing ordered-vertex layer.
- No `Mathlib.Analysis.FixedPoint.Brouwer` (it's only an open problem
  there; the gallery's `BrouwerFixedPointOQ04OQ04.lean` has `axiom
  scarf_approx_fixed_point` as a placeholder).

## C. Algorithmic content of Scarf's pivoting

For completeness, the door-following walk that OQ-05 is asking us to
implement:

```text
input  : Triangulation T, Sperner coloring c, boundary door (s₀, k₀)
output : panchromatic cell  or  another boundary door

state  : (s, k) — current cell and the door we just entered through
loop:
    if IsPanchromatic c s then return s
    let k' = unique j ≠ k with IsDoor c s j      -- door_count_parity gives 0 or 2;
                                                 -- we just came from k, so 2; pick the other
    match T.adj s k' with
    | none       => return boundary door (s, k')  -- chain terminates on boundary
    | some (s', k'') => (s, k) := (s', k'')      -- pivot to neighbor; recurse
```

Mathematical content all proved in the gallery:

- **"unique j ≠ k with IsDoor c s j"** — this is `door_count_parity`
  (`SpernerMathlib4.lean:386`) plus the case analysis "if `s` is not
  panchromatic, the count is `0` or `2`; if `2` and one of the doors is
  `k`, the other is unique". The pivot step is computable iff the
  `IsDoor` decision is computable (✓, by `decidableIsDoor`).
- **termination** — the walk never visits the same cell twice. Proof:
  if it did, the chain would be cyclic, but pseudomanifold doors are
  involutive (`adj_symm`) and the door predicate transfers along
  `adj` (`isDoor_iff_of_adj`, line 500), so a cycle would force the
  cell to be panchromatic (handled by the `if` branch). Concretely the
  termination measure is `|T.Cell| - (set of cells visited)`.
- **correctness** — boundary doors come in pairs except for the
  panchromatic-ending chain. `sperner_parity` gives the parity equation
  `panchromatic = boundary doors (mod 2)`. Combined with `Odd
  boundary doors`, at least one chain ends at a panchromatic cell.

## D. Gaps surfaced for follow-on sessions

1. **`findOppositeIdx` computability** (the explicit OQ ask). Replace
   `Classical.choose` with `Finset.filter … |>.min'` and add a
   `Nonempty` proof from the same cardinality argument. ~50 LOC.
2. **`adjFn` computability** — follows from (1) mechanically. ~20 LOC.
3. **`AbstractSimplicialData.toTriangulation` computability** —
   follows from (1)+(2). ~10 LOC of removing `noncomputable`.
4. **`door_count_parity`-driven pivot function** — currently
   `door_count_parity` is a counting *theorem*, not a function. We
   need `def pivotDoor : (s : K.Cell) (k : Fin (d+1)) → (¬ IsPanchromatic c K s) → IsDoor c K s k → {k' : Fin (d+1) // k' ≠ k ∧ IsDoor c K s k'}`,
   which is computable from `Finset.filter` on `Fin (d+1)`. ~30 LOC.
5. **Termination via `|T.Cell|`-bounded walk** — `Nat.rec` or
   `WellFoundedRecursion` on the *complement* of the visited set.
   The cleanest Lean 4 idiom is a `Fin (|T.Cell|+1)`-bounded loop.
   ~80 LOC.
6. **End-to-end correctness theorem**: `scarfFind T c hbdry` returns
   a *specific* `s` with `IsPanchromatic c T.toCellComplex s`. Proof
   reuses `sperner_parity` + invariant of the walk. ~60 LOC.

Total estimated cost for a *full* Scarf implementation on
`AbstractSimplicialData`: ~250–350 LOC, multi-session. For the
1-d-only specialisation on `intervalTriangulation`: ~120 LOC,
single-session feasible.

## E. Tractability assessment

| Target | Mathlib readiness | Gallery readiness | S2 effort | Notes |
| --- | --- | --- | --- | --- |
| (C1) brute-force + correctness | HIGH | HIGH | ~50 LOC | safe; ships a `#eval`-able demo on `intervalTriangulation` |
| (C2-1d) Scarf walk on `intervalTriangulation` | HIGH | HIGH | ~120 LOC | clean, doesn't touch `findOppositeIdx` |
| (C2-gen) Scarf walk on general `Triangulation` | HIGH | MED (decid. instances OK) | ~250 LOC | depends on (C3) for `AbstractSimplicialData` users |
| (C3) make `findOppositeIdx` computable | HIGH | n/a (refactor) | ~80 LOC | clean refactor; risk is just `noncomputable` taint propagation |
| Replace `scarf_approx_fixed_point` axiom in `BrouwerFixedPointOQ04OQ04.lean` | NONE (analysis bridge) | requires (C2-gen) | ≥ research-grade | out of scope for this slug |

## F. Open Mathlib PR opportunities (long-tail)

- `Mathlib.Combinatorics.Sperner` — if (C2-gen) lands cleanly, the
  abstract `CellComplex.sperner` + decidable witness extractor is a
  natural Mathlib PR (cf. Yael Dillies' mathlib4#25231, #34310 cited
  in the parent's `## References`).
- `Mathlib.Logic.Decidable.Finset` — a small helper
  `Finset.filter_nonempty_of_card_lt` (or similar) that powers the
  `findOppositeIdx` computable refactor.

## G. References

- Scarf, H. (1967). "The approximation of fixed points of a continuous
  mapping". *SIAM J. Appl. Math.* **15**, 1328–1343.
- Border, K. C. (1985). *Fixed Point Theorems with Applications to
  Economics and Game Theory.* Cambridge, ch. 7.
- Sperner, E. (1928). "Neuer Beweis für die Invarianz der
  Dimensionszahl und des Gebietes". *Abh. Math. Sem. Univ. Hamburg*
  **6**, 265–272.
- Yael Dillies, mathlib4#25231 (Sperner-related Mathlib draft).
- Gallery: `Proofs/SpernerMathlib4.lean`, `Proofs/SpernerSimplicialInstance.lean`,
  `Proofs/BrouwerFixedPointOQ04OQ04.lean` (axiom site).
