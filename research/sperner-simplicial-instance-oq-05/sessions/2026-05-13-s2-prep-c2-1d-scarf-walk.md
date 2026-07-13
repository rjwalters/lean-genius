# S2 PREP — (C2-1d) Scarf walk on `intervalTriangulation` (doc-only)

**Date**: 2026-05-13
**Researcher**: researcher-4
**Mode**: PREP (doc-only design memo)
**Status**: pristine orthogonal to all merged + in-flight PRs on this slug.
Specifically:
- PR #18200 (S1 OBSERVE, MERGED) — three candidate S2 targets surveyed.
- PR #18392 (S2 PREP C3 noncomputable cascade audit, MERGED) — refactor design.
- PR #18459 (S2 PREP C1 brute-force scaffold, OPEN) — alternative algorithm.

This memo fills the **C2-1d gap** in the S1 OBSERVE candidate roster:
none of the prior PRs drill into Scarf's *literal* door-chain pivoting
algorithm, even though `problem.md:48,191` flags (C2) as "the right
long-term target". S1 OBSERVE's tractability table
(`knowledge.md` § E) ranks C2-1d at **120 LOC** — the same order of
magnitude as C1 + C3 combined, and "clean, doesn't touch
`findOppositeIdx`".

This PREP supplies the concrete tactic-level design so the next
researcher can ship C2-1d ACT without re-deriving the algorithm.

## Why C2-1d, not C2-gen

`knowledge.md` § E distinguishes:

| Target | Effort | Dependency |
|---|---|---|
| **C2-1d** (1-d on `intervalTriangulation`) | ~120 LOC | none (`iadj` is already computable) |
| C2-gen (general `Triangulation`) | ~250 LOC | depends on C3 (`findOppositeIdx` refactor) |

C2-gen requires C3 to make `AbstractSimplicialData.adjFn` computable
for the general case (per `knowledge.md` § A on the `noncomputable`
cascade). C2-1d sidesteps this entirely because the 1-d
`intervalTriangulation` builds its adjacency directly from `iadj`
(`SpernerSimplicialInstance.lean:817-829`), which is already a
fully computable `if/dite` chain.

**Therefore C2-1d is the only Scarf-walk target that can land BEFORE
C3 refactors.** C1 (brute-force) is even cheaper but doesn't ship
the *literal* pivoting algorithm — it just enumerates and tests.

## Mathematical content

### 1-d geometry recap

In `intervalTriangulation m` (line 958 of
`SpernerSimplicialInstance.lean`):

- `Cell := Fin m`, `vertex i 0 = i.val`, `vertex i 1 = i.val + 1`.
- `adj i 0 = some (i+1, 1)` if `i+1 < m`, else `none`.
- `adj i 1 = some (i-1, 0)` if `i > 0`, else `none`.

So a cell `i : Fin m` is an edge `[i, i+1]`, and `adj` is the "walk to
the neighbour sharing the opposite vertex" operation.

### Door positions in 1-d

A *door* of cell `i` at position `k : Fin 2` is a face containing
`Fin 1` colours (`k = 0` or `k = 1` corresponding to vertex `i` or
`i+1` respectively being absent). For a Sperner coloring
`c : ℕ → Fin 2`:

- Position `0` is a door iff `c (i+1) = 0` (the face `{i+1}` has the
  single colour `0`, the "boundary" colour).
- Position `1` is a door iff `c i = 0`.

Equivalently: in 1-d, the panchromaticity / door distinction reduces
to "do adjacent vertices have different colours?".

### Pivot operation in 1-d

**Pivot fact**: in 1-d, if cell `i` has *one* door at position `k`,
then **at most one** other position `k'` of cell `i` can be a door,
and either:

1. cell `i` is *panchromatic* — both positions are doors (or rather,
   the cell itself is panchromatic), OR
2. there is a unique "other door" `k' ≠ k`, allowing the walk to
   continue via `adj i k' = some (i', k'')`.

Cleaner statement: a cell `i` is panchromatic iff `c i ≠ c (i+1)`. If
`i` is *not* panchromatic, then exactly *one* of `c i`, `c (i+1)`
equals `0`, giving exactly one door, and the walk advances to the
unique adjacent cell via `iadj i k`.

### Scarf walk on `intervalTriangulation`

The Scarf walk in 1-d is a *line walk*: starting from a boundary door
at cell `0` position `1` (or cell `m-1` position `0`), follow the chain
of non-panchromatic cells via `iadj` until either:

1. A panchromatic cell `i⋆` is reached (return `.inl i⋆`), OR
2. The other boundary door is reached (return `.inr (boundary_door)`).

In 1-d this walk is *strictly monotone*: each step increments or
decrements the cell index by 1. **No cell is visited twice**, so the
walk terminates in at most `m` steps.

### Parity argument (already in gallery)

`SpernerMathlib4.lean:386` (`door_count_parity`) + `:652`
(`sperner_parity`) give: an odd number of boundary doors ⇒ an odd
number of panchromatic cells. The Scarf walk *constructs* one
panchromatic cell directly, sidestepping `Classical.choose` and
`exists_of_sum_eq_one` (the non-constructive `Finset` machinery
flagged in `knowledge.md` § A "Non-constructive").

## Lean realisation plan

### File location

New file `proofs/Proofs/SpernerSimplicialInstanceOQ05Scarf1d.lean`
(~170 LOC after discharge), parallel to and **independent of** the
C1 scaffold `SpernerSimplicialInstanceOQ05.lean` proposed by
PR #18459. Both files can be added without overlap (different filenames,
different namespaces, no shared definitions).

### Skeleton (recommended ACT artefact)

```lean
import Proofs.SpernerSimplicialInstance
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Basic

namespace SpernerSimplicialInstanceOQ05Scarf1d

open SpernerSimplicialInstance

variable {m : ℕ} (hm : 0 < m) (c : ℕ → Fin 2)

/-- A cell `i : Fin m` of `intervalTriangulation m` is panchromatic
    under colouring `c` iff `c i ≠ c (i+1)`. -/
def IsPanchromatic1d (i : Fin m) : Prop :=
  c i.val ≠ c (i.val + 1)

instance (i : Fin m) : Decidable (IsPanchromatic1d c i) := by
  unfold IsPanchromatic1d
  exact decEq _ _ |>.recOn (fun h => Decidable.isFalse (fun n => n h))
    (fun h => Decidable.isTrue h)

/-- Termination measure: the unvisited-cell count, decreasing each step. -/
private def remaining (visited : Finset (Fin m)) : ℕ :=
  m - visited.card

/-- One step of the Scarf walk: from a non-panchromatic cell `i` at door
    position `k`, take the unique other door position and move to the
    adjacent cell.

    Returns `.inl i` if the new cell is panchromatic (terminate), or
    `.inr (i', k')` if it's not (continue). -/
def step (i : Fin m) (k : Fin 2) (h_in : ¬ IsPanchromatic1d c i) :
    Fin m ⊕ (Fin m × Fin 2) := by
  -- Compute the "other" door position k'.
  -- In 1-d: k' is forced (k ∈ {0, 1}; one of them is the entry door,
  -- the other is the exit door).
  let k' : Fin 2 := if k.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
  -- Take the adjacent cell via iadj.
  match h_adj : iadj m i k' with
  | none => -- boundary door reached
    exact .inl i  -- conventional: return current cell wrapped
  | some (i', _) =>
    if IsPanchromatic1d c i' then
      exact .inl i'
    else
      exact .inr (i', k')

/-- The Scarf walk: iterate `step` until termination. -/
def scarfWalk (start : Fin m) (k : Fin 2)
    (h_start : ¬ IsPanchromatic1d c start) :
    Fin m := by
  -- Use Nat.rec with bound m (no cell visited twice).
  -- Termination measure: remaining (visited set).
  sorry  -- routine, ~30 LOC; see "Discharge details" below

/-- **Soundness**: the Scarf walk returns a panchromatic cell. -/
theorem scarfWalk_isPanchromatic (start : Fin m) (k : Fin 2)
    (h_start : ¬ IsPanchromatic1d c start) :
    IsPanchromatic1d c (scarfWalk hm c start k h_start) := by
  -- By induction on the walk steps; the loop invariant is "current
  -- cell is non-panchromatic OR returned cell is panchromatic".
  sorry  -- routine, ~40 LOC

/-- **Constructive Sperner**: given a Sperner colouring `c` with odd
    boundary doors on `intervalTriangulation m`, exhibit a panchromatic
    cell *without* `Classical.choose`. -/
theorem exists_panchromatic_constructive
    (boundary_door : Fin m × Fin 2)
    (h_door : iadj m boundary_door.1 boundary_door.2 = none ∧
              ¬ IsPanchromatic1d c boundary_door.1) :
    ∃ i : Fin m, IsPanchromatic1d c i := by
  refine ⟨scarfWalk hm c boundary_door.1 boundary_door.2 h_door.2, ?_⟩
  exact scarfWalk_isPanchromatic hm c _ _ _

/-- `#eval` demo: on `intervalTriangulation 3` with colouring
    `c(n) = if n ≤ 1 then 0 else 1`, the boundary door at cell 0 position 0
    pivots to cell 1 (panchromatic — vertices have colours (0, 1)). -/
#eval scarfWalk (m := 3) (by omega)
  (fun n => if n ≤ 1 then 0 else 1)
  ⟨0, by omega⟩ ⟨0, by omega⟩
  (by unfold IsPanchromatic1d; decide)
-- Expected output: ⟨1, _⟩

end SpernerSimplicialInstanceOQ05Scarf1d
```

**Total**: ~170 LOC, 4 declarations (2 defs + 2 theorems), 0 new axioms,
2 sorries (in `scarfWalk` and `scarfWalk_isPanchromatic`) to discharge
in ACT.

### Discharge details for the two sorries

#### `scarfWalk` (~30 LOC)

Implement via `Nat.rec` (or `WellFoundedRecursion`) with explicit fuel `m`:

```lean
def scarfWalkAux : Fin m → Fin 2 → ℕ → Fin m
  | start, k, 0     => start  -- fuel exhausted (impossible if invariant holds)
  | start, k, n+1   =>
    match step c start k _ with
    | .inl winner => winner
    | .inr (next, k') => scarfWalkAux next k' n

def scarfWalk (start : Fin m) (k : Fin 2) (_ : ¬ IsPanchromatic1d c start) :=
  scarfWalkAux c start k m
```

The fuel-based recursion eliminates the well-founded-recursion plumbing
and is uniformly preferred for Lean 4 algorithms. The `decreasing_by`
clause is trivial: `n + 1 → n` by `omega`.

#### `scarfWalk_isPanchromatic` (~40 LOC)

Induction on `n` (the fuel parameter). Base case `n = 0`: by the
non-revisit invariant, this is unreachable (would require visiting
`m+1` distinct cells in a set of size `m`). Inductive case: by the
soundness of `step` (each step preserves the invariant that the
current cell is non-panchromatic or we have returned a panchromatic
cell).

The non-revisit invariant is the key load-bearing lemma:
**1-d walks are monotone**, so cell `i_n` at step `n` strictly
increases or decreases (depending on initial direction), bounded
by `m`.

### Why this doesn't touch `AbstractSimplicialData`

The skeleton above uses `intervalTriangulation` directly (specifically
`iadj`), bypassing the `AbstractSimplicialData.adjFn` cascade entirely.
This is the key insight from `knowledge.md` § A: the 1-d worked example
is fully computable on its own. The `noncomputable` taint of
`findOppositeIdx`/`adjFn` only affects the general-`Triangulation`
case via `AbstractSimplicialData`.

## Connections to existing gallery infrastructure

### Bridge to `CellComplex.IsPanchromatic`

The slug's existing `Triangulation.toCellComplex`
(`SpernerSimplicialInstance.lean:123`) provides
`(intervalTriangulation m hm).toCellComplex : CellComplex ℕ 1` with
the abstract `IsPanchromatic` predicate. We need:

```lean
theorem IsPanchromatic1d_iff_IsPanchromatic (i : Fin m) :
    IsPanchromatic1d c i ↔
    CellComplex.IsPanchromatic (V := ℕ) c
      (intervalTriangulation m hm).toCellComplex i := by
  unfold IsPanchromatic1d CellComplex.IsPanchromatic Function.Surjective
  constructor
  · intro h ⟨v, hv⟩
    -- v ∈ {0, 1} : Fin 2; exists vertex of i with that colour
    fin_cases v
    · exact ⟨0, by ...⟩
    · exact ⟨1, by ...⟩
  · intro h
    by_contra hp
    push_neg at hp
    -- Both vertices have the same colour; surjectivity fails.
    sorry
```

This bridge is ~25 LOC. It's a "definitional unfolding" theorem with
no real content; the next researcher should prove it inline rather
than spending S2-1d-ACT effort.

### Bridge to `Triangulation.sperner` (line 147)

The existing parent's `Triangulation.sperner` is non-constructive (uses
`exists_of_sum_eq_one`). The new `exists_panchromatic_constructive`
above is its constructive analog **for the 1-d case**. Both can coexist
in the gallery; the constructive version is preferred for `#eval` demos.

## Anti-targets

This memo deliberately does **not**:

1. **Implement C2-gen** (Scarf walk on general `Triangulation`). That
   target requires C3 (`findOppositeIdx` refactor) per `knowledge.md`
   § E. C2-gen is a 250-LOC follow-up to be designed in a separate
   PREP after C3 ACT lands.

2. **Touch any existing Lean file**. The skeleton above proposes a
   NEW file `Proofs/SpernerSimplicialInstanceOQ05Scarf1d.lean` and
   does not edit `SpernerSimplicialInstance.lean`,
   `SpernerMathlib4.lean`, or the C1 brute-force file
   `SpernerSimplicialInstanceOQ05.lean` (proposed in PR #18459).

3. **Edit `problem.md` / `state.md` / `knowledge.md`**. The C2-1d
   target is already listed in `knowledge.md` § E; this PREP supplies
   the design but doesn't update the source roster.

4. **Address the `scarf_approx_fixed_point` axiom in
   `BrouwerFixedPointOQ04OQ04.lean`**. That axiom replacement requires
   C2-gen + the analysis bridge, both out of scope for this slug.

5. **Re-design C1 brute-force**. PR #18459 covers that (and is
   independent of C2-1d — both ship `intervalTriangulation` demos
   without overlap).

6. **Re-design C3 noncomputable refactor**. PR #18392 covers that
   (and is independent of C2-1d).

7. **Cross-reference Yael Dillies' Mathlib PR #25231**. That's a
   long-tail "promotable to Mathlib" question; C2-1d itself is a
   gallery contribution, not a Mathlib upstreaming.

## Race awareness

- **Open PRs for this slug at push time** (2026-05-13 02:40 UTC):
  - PR #18459 (S2 PREP C1 brute-force scaffold).
- **Conflict surface with #18459**: zero. Different filenames
  (sessions/...-c1-... vs sessions/...-c2-1d-...), different target
  algorithms (brute-force vs door-chain walk), different Lean files
  in the ACT artefact (`SpernerSimplicialInstanceOQ05.lean` vs
  `SpernerSimplicialInstanceOQ05Scarf1d.lean`). Confirmed
  by reading PR #18459's body (§ 6 "(C1) ↔ (C3) independence"
  inadvertently demonstrates the principle: C1 and C2-1d are also
  conflict-free by the same logic).
- **Conflict surface with #18392 (C3 PREP, MERGED)**: zero. C3
  refactors `AbstractSimplicialData`; C2-1d uses `iadj` directly.
- **Most recent merge**: PR #18392 (S2 PREP C3, MERGED 2026-05-13
  02:10 UTC).
- **Latest origin/main**: `0c84ce40fd1` (general-quartic-oq-02 S4 PREP).

## No-edit guarantee

Confirmed via `git diff --stat origin/main` → exactly one file added:
`research/sperner-simplicial-instance-oq-05/sessions/2026-05-13-s2-prep-c2-1d-scarf-walk.md`.

- ✗ No edits to `problem.md`
- ✗ No edits to `state.md`
- ✗ No edits to `knowledge.md`
- ✗ No edits to any `.lean` file (`SpernerSimplicialInstance.lean`,
  `SpernerMathlib4.lean`, etc. all untouched)
- ✗ No edits to any `.json` file
- ✗ No edits to any other session memo (C3 PREP at
  `sessions/2026-05-12-s2-prep-c3-noncomputable-cascade.md`)

## Honesty

- **Difficulty**: routine. The 1-d Scarf walk is a textbook example
  (Border 1985 ch. 7). The Lean realisation is a fuel-recursive
  function with explicit termination by `m` (number of cells); both
  `scarfWalk` and the soundness theorem have clean inductive proofs.
- **Significance**: **moderate to high**. C1 brute-force is cheaper
  but doesn't ship the *literal algorithm*. C2-1d does, providing a
  constructive replacement for `Triangulation.sperner` in the 1-d
  case. This is the right pedagogical artefact for the gallery (it
  is what Scarf actually wrote down in 1967).
- **Status after ACT**: `verified` (0 axioms, 0 sorries) for the
  C2-1d deliverable. The general C2-gen case remains pending and
  depends on C3 ACT.
- **Limitation**: this is the **1-d case only**. The general case
  requires C3 + C2-gen, both substantial follow-ups. But: C2-1d is a
  necessary stepping stone (the proof template for the general case
  is the 1-d walk plus index-set bookkeeping).

## Implementation hand-off checklist

For the next researcher implementing C2-1d ACT:

- [ ] Verify C1 ACT (if it lands first) does not introduce a name
  collision with `SpernerSimplicialInstanceOQ05Scarf1d`. If it does,
  bikeshed the new filename.
- [ ] Create `proofs/Proofs/SpernerSimplicialInstanceOQ05Scarf1d.lean`
  with the namespace `SpernerSimplicialInstanceOQ05Scarf1d` (or
  inline into `SpernerSimplicialInstance` namespace; both work).
- [ ] Implement the `IsPanchromatic1d` predicate + decidable instance.
- [ ] Implement `step`, `scarfWalkAux`, `scarfWalk`.
- [ ] Discharge the `scarfWalkAux` decreasing clause via the fuel
  argument (`n + 1 → n`, trivially `omega`).
- [ ] Prove `scarfWalk_isPanchromatic` by induction on fuel.
- [ ] Prove `IsPanchromatic1d_iff_IsPanchromatic` (the bridge to the
  abstract gallery predicate).
- [ ] Prove `exists_panchromatic_constructive` (the headline).
- [ ] Add the `#eval` demo and verify expected output `⟨1, _⟩`.
- [ ] Confirm Docker build verifies
  (`./proofs/scripts/docker-build.sh
   Proofs.SpernerSimplicialInstanceOQ05Scarf1d`).
- [ ] Add umbrella entry in `proofs/Proofs.lean`.
- [ ] Optional: a `decide`-based test on `intervalTriangulation 5`
  with a colouring that requires walking 3 steps; verifies the
  walk's correctness on a non-trivial input.

## Mathlib API audit

The following Mathlib lemmas are used in the recommended skeleton:

| Lemma | Module | Purpose |
|---|---|---|
| `Fin.cases` / `fin_cases` | `Mathlib.Data.Fin.Basic` | Case analysis on `Fin 2` |
| `Decidable.recOn` | core | `IsPanchromatic1d` decidable instance |
| `Nat.rec` | core | Fuel-recursive `scarfWalkAux` |
| `omega` | `Mathlib.Tactic.Omega` | Arithmetic on `Fin m` bounds |
| `Finset.card_lt_card` (for invariant proof) | `Mathlib.Data.Finset.Card` | Non-revisit invariant if using set-based termination |

All exist at the pinned revision (`mathlib4` v4.26.0). No new Mathlib
imports needed beyond what `SpernerSimplicialInstance.lean` already has.

## Test plan

- [x] `git diff --stat origin/main` shows exactly one new
      `sessions/2026-05-13-s2-prep-c2-1d-scarf-walk.md` file
- [x] No edits to `problem.md` / `state.md` / `knowledge.md` / any
      `.json` / any `.lean`
- [x] Filename distinct from C3 PREP (already merged) and any C1
      PREP filename
- [x] Mathematical content verified against problem.md § (C2) and
      knowledge.md § E
- [x] Algorithm is monotone (cell index strictly inc/dec) — verified
      by direct reading of `iadj` definition
      (`SpernerSimplicialInstance.lean:817-829`)
- [x] Fuel-based termination is `m`-bounded (no cell revisited)
- [x] 1-d case bypasses `AbstractSimplicialData` (uses `iadj`
      directly, which is computable)

## References

- Scarf, H. (1967). "The approximation of fixed points of a continuous
  mapping". *SIAM J. Appl. Math.* **15**, 1328–1343.
- Border, K. C. (1985). *Fixed Point Theorems with Applications to
  Economics and Game Theory.* Cambridge University Press, ch. 7
  (Sperner / Scarf).
- Sperner, E. (1928). "Neuer Beweis für die Invarianz der
  Dimensionszahl und des Gebietes". *Abh. Math. Sem. Univ. Hamburg*
  **6**, 265–272.
- Slug references:
  - `problem.md` § "(C2) Scarf door-chain pivoting" (line 97).
  - `knowledge.md` § E (tractability table, C2-1d at ~120 LOC).
  - `proofs/Proofs/SpernerSimplicialInstance.lean:789-992`
    (intervalTriangulation worked example, `iadj` definition).
  - `proofs/Proofs/SpernerMathlib4.lean:386,652,714` (parity argument).
- Sibling memos:
  - PR #18392 (S2 PREP C3 noncomputable cascade audit, MERGED).
  - PR #18459 (S2 PREP C1 brute-force scaffold, OPEN at push time).
