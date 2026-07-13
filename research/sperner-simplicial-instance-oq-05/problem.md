# sperner-simplicial-instance-oq-05 — Problem Statement

**Parent**: `sperner-simplicial-instance` — gallery entry
`Proofs/SpernerSimplicialInstance.lean`, 994 lines, 28 theorems, 0 sorries,
0 axioms (status: `verified`, badge: `original`). It builds the
`Triangulation V n` structure, a `toCellComplex` bridge into the abstract
`CellComplex` framework of `Proofs/SpernerMathlib4.lean`, the general
`Triangulation.sperner` existence theorem, and a fully verified 1-d
`intervalTriangulation` example.

**Source notes** (from `src/data/proofs/sperner-simplicial-instance/meta.json`,
`overview.openQuestions[OQ-05]`):

> Implement Scarf's algorithm as a *computable* function in Lean 4: input a
> Sperner-colored triangulation, output a panchromatic cell. The parity proof
> is non-constructive in form but the door-following procedure is finite —
> bridging the two would yield a verified fixed-point algorithm. The
> `iadj`/`iadj_cases` machinery already provides a computable adjacency oracle
> for the 1-d case; generalising to `AbstractSimplicialData` requires a
> decidable witness for `findOppositeIdx`.

## S1 observation: the parent proof is constructively-shaped but non-computably-witnessed

The Sperner parity machinery in `SpernerMathlib4.lean` is *combinatorially* a
finite door-following walk, but the Lean 4 formalization carries two
non-computable signatures that block extraction of a `Scarf`-style function:

1. **`CellComplex.sperner` reaches the panchromatic witness via**
   `Sperner.exists_panchromatic` ⇝ `sperner_parity` (mod-2 counting) ⇝
   classical `∃ s, P s` from `Odd N`. The proof never names a *specific*
   panchromatic cell; it only shows the count is non-zero.

2. **`AbstractSimplicialData.findOppositeIdx`** is explicitly declared
   `noncomputable def` (line 367 of `SpernerSimplicialInstance.lean`); the
   witness is produced by `Classical.choose` on a `by by_contra; push_neg`
   existential. Consequently `AbstractSimplicialData.adjFn` (line 529) is also
   `noncomputable`. The *concrete* 1-d `intervalTriangulation` sidesteps this
   by defining `iadj : Fin m → Fin 2 → Option (Fin m × Fin 2)` by direct
   case analysis (lines ~800–880), giving a computable adjacency oracle for
   the 1-d case only. The OQ task explicitly identifies the
   `findOppositeIdx` non-computability as the gating bottleneck for
   generalisation.

## Three candidate formal targets

S1 deliberately surfaces three reasonable interpretations of "implement
Scarf's algorithm as a *computable* function". We expect S2 to commit to
**(C2)** — the door-chain walk — since it is the literal Scarf algorithm
and provides the *algorithmic* content the OQ asks for. (C1) is a
brute-force cheat already available in 5–10 LOC, and (C3) is a deep
extraction-oriented refactor that requires upstream `noncomputable`
removal.

### (C1) Brute-force enumeration (trivial, already buildable today)

`IsPanchromatic` is `Decidable` (`SpernerMathlib4.decidableIsPanchromatic`)
and `T.Cell` is `Fintype` (via `Triangulation.cellFintype`). So:

```lean
def findPanchromaticBrute
    (T : Triangulation V n) (c : V → Fin (n + 1)) :
    Option T.Cell :=
  haveI := T.cellDecEq
  haveI := T.cellFintype
  (Finset.univ.filter
    (fun s => CellComplex.IsPanchromatic c T.toCellComplex s)).toList.head?
```

This is **computable today**, requires no new infrastructure, and has a
correctness specification of the form

```lean
theorem findPanchromaticBrute_eq_some_iff … :
    findPanchromaticBrute T c = some s ↔
    (CellComplex.IsPanchromatic c T.toCellComplex s ∧ … minimality clause … )
```

The minimality clause must be the `Finset.toList` enumeration order on
`T.Cell`'s `Fintype` instance — not a particularly natural notion. The
honest framing is *not* "Scarf's algorithm" — it is "brute-force search,
correctness-proved against the parity existence theorem". The companion
totality lemma would be:

```lean
theorem findPanchromaticBrute_isSome_of_hbdry
    (T : Triangulation V n) (c : V → Fin (n + 1))
    (hbdry : Odd (boundary doors count for T c).card) :
    (findPanchromaticBrute T c).isSome :=
  -- follows from Triangulation.sperner + Finset.toList_filter_nonempty + Option.isSome_iff
```

Estimated cost: ~50 LOC, 0 sorries, no new mathematical content.
**Limitation**: this is `O(|T.Cell|)` enumeration, not Scarf's
door-chain `O(door-path-length)`. It does *not* exhibit the pivoting
structure that gives the algorithm its computational-economics interest.

### (C2) Scarf door-chain pivoting (the literal target)

The algorithm Scarf actually wrote down (Scarf 1967; reformulated cleanly
in Border 1985 ch. 7): start at a boundary door, follow the unique
door-cell-door chain, terminate at either (a) a panchromatic cell or
(b) another boundary door. Boundary-door parity (odd) ⇒ at least one
chain ends at a panchromatic cell.

Formally we want a function

```lean
def scarfWalk
    (T : Triangulation V n) (c : V → Fin (n + 1))
    (start : T.Cell × Fin (n + 1))
    (hstart : T.adj start.1 start.2 = none ∧
              CellComplex.IsDoor c T.toCellComplex start.1 start.2) :
    T.Cell ⊕ (T.Cell × Fin (n + 1))
```

returning either a panchromatic cell (`.inl`) or another boundary door
(`.inr`). The *fixed-point search* function is then

```lean
def scarfFindPanchromatic
    (T : Triangulation V n) (c : V → Fin (n + 1))
    (hbdry : Odd …) : T.Cell
```

obtained by enumerating boundary doors, running `scarfWalk` on each
that has not yet been paired, and returning the first `.inl` panchromatic
result. The parity hypothesis guarantees at least one chain returns `.inl`.

Required ingredients (all enumerated in `knowledge.md`):

- a *computable* adjacency oracle for `Triangulation` (currently
  axiomatic via `T.adj : T.Cell → Fin (n+1) → Option (T.Cell × Fin (n+1))`;
  any *concrete* triangulation supplies a computable instance — the 1-d
  `iadj` is the worked example);
- a *computable* "given a non-panchromatic cell `s` and a door position `k`
  in `s`, find the unique other door position `k' ≠ k` of `s`" — this is
  the *pivot* lemma `door_count_parity` of `SpernerMathlib4.lean:386` made
  computational;
- a termination measure: no cell is visited twice (the walk is acyclic),
  so the walk length is bounded by `|T.Cell|`.

Estimated cost: ~300–500 LOC plus the `findOppositeIdx` refactor (see C3)
if generalisation beyond the 1-d case is required. Single-dimension
specialisation (1-d `intervalTriangulation`) is much cheaper, ~150 LOC.

### (C3) Make `AbstractSimplicialData.findOppositeIdx` computable

The deepest of the three. Currently `findOppositeIdx t ht f hf hfc :
Fin (n+1)` uses `Classical.choose` on the existential "some vertex of `t`
is not in `f`". To make it computable:

```lean
def AbstractSimplicialData.findOppositeIdxComp
    (t : Finset V) (ht : t ∈ D.topSimplices)
    (f : Finset V) (hf : f ⊆ t) (hfc : f.card = n) :
    Fin (n + 1) :=
  -- enumerate Fin (n+1); find first k with D.vertexEnum t ht k ∉ f
  (Finset.univ : Finset (Fin (n+1))).filter
    (fun k => D.vertexEnum t ht k ∉ f)
    |>.min' (by … card argument …)
```

(uses `Finset.min'` plus a `Nonempty` proof from the same counting
argument as the existing `findOppositeIdx`). Then every lemma
`AbstractSimplicialData.findOppositeIdx_*` must be re-proved (or, better,
both definitions are shown propositionally equal via
`Classical.choose_spec` + the explicit witness, and the existing lemmas
go through unchanged after a one-line bridge).

Estimated cost: ~100–200 LOC; touches lines 367–510 of
`SpernerSimplicialInstance.lean`. Caveat: this is a *refactor* of a
verified 0-sorry parent and would require re-running the full build.
It only pays off if (C2) is then implemented on top.

## Recommended S2 commitment

S2 should commit to **(C1) first**, as a 50-LOC "brute-force + correctness
proof" companion file `SpernerSimplicialInstanceOQ05.lean`, with three
named purposes:

1. produce a *now-verified* concrete computable witness extractor for the
   1-d `intervalTriangulation` example, demonstrating the bridge from the
   parity theorem to a `def : … → T.Cell` and `#eval`-able algorithm;
2. surface the `noncomputable` blockers in `AbstractSimplicialData` so that
   (C3) becomes a well-scoped subsequent session;
3. avoid duplicating work — three open Sperner-related PRs on
   `sperner-ndim` and `sperner-freudenthal-simplex` are simultaneously
   trying to build the n-d existence theorem, and any direct attack on
   Scarf-pivoting in those files would race them.

(C2) is the right *long-term* target for this slug (it is the literal
mathematical content of OQ-05) but it is multi-session work and should
be scaffolded only after (C1) lands and (C3) is unblocked.

## Cross-references

- Parent: `Proofs/SpernerSimplicialInstance.lean` (verified, 0-sorry)
- Abstract framework: `Proofs/SpernerMathlib4.lean` (verified, 0-sorry)
- Existing Scarf reference (as **axiom**): `Proofs/BrouwerFixedPointOQ04OQ04.lean:244`
  declares `axiom scarf_approx_fixed_point`. The OQ-05 deliverable would
  give Lean a path to replacing that axiom with a verified algorithm
  (modulo the analytic ε-fixed-point bridge).
- Related open slugs: `sperner-ndim-oq-*`, `sperner-freudenthal-*` —
  these are building the *existence* theorems in higher dimensions; OQ-05
  is orthogonal (it asks for *computability*, not for higher-dim
  existence).
