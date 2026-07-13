# S13 PREP — OQ-01-B WitnessTree encoding design (researcher-2, 2026-06-12)

**Mode**: PREP (doc-only — no Lean, problem.md, knowledge.md, or meta.json
edits; resolves the central encoding obstacle ahead of the S14 ACT).
**Slug**: prob-method-lovasz-local-oq-01
**Parent file**: `proofs/Proofs/MoserTardos.lean` (517 LOC after S12 ACT,
0 sorries, 0 axioms; Docker 7743 jobs at pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`).

## 0. Purpose

`knowledge.md` flags OQ-01-B (witness trees) as "the hardest part — both
definitionally (rooted labelled trees with `Finset`-valued children) and
proof-theoretically" and budgets "2–3 PRs" before substantive ACT. The S12
state.md S13 entry asks for a design memo for `inductive WitnessTree P` +
`isProper`. This memo resolves the single biggest definitional risk — the
**strict-positivity wall** for `Finset`-valued children — and produces a
paste-ready, positivity-safe skeleton for S14 ACT.

## 1. The positivity obstacle (why `Finset` children fail)

The mathematically natural type is:

```lean
-- DOES NOT COMPILE
inductive WitnessTree (P : MTProblem) : Type
  | node (label : Fin P.numEvents) (children : Finset (WitnessTree P))
```

Lean 4's strict-positivity checker rejects this. `Finset α` is
`{ s : Multiset α // s.Nodup }`, and `Multiset α := Quotient (List.Perm.setoid α)`
is a quotient of `List α`. Nested occurrence of the inductive type **under a
quotient** is not accepted: the checker cannot certify positivity through
`Quotient`/`Multiset` (the recursor would have to commute with the quotient,
which is not derivable structurally). This is the same wall that blocks
`inductive T | mk : Finset T → T` generally — it is not specific to this file.

`List`, by contrast, **is** strictly positive: `inductive T | mk : List T → T`
compiles. So the fix is to carry children as a `List`, and recover the
"set of children with distinct labels" semantics through a `Nodup`-on-labels
side-condition inside `isProper` (which is exactly the Moser–Tardos
requirement — siblings carry distinct event labels).

### Decision D1 — children are `List`, distinctness is a `Prop` side-condition

```lean
inductive WitnessTree (P : MTProblem) : Type
  | node (label : Fin P.numEvents) (children : List (WitnessTree P))
```

Rationale: positivity-safe; `List` order is irrelevant to the MT analysis and
is quotiented away at the `isProper` level (siblings’ labels are `Nodup`, so
the multiset of child-labels — the only thing the probability bound sees — is
recovered). Mathlib has `List.Nodup`, `List.map`, `List.Forall`, and
`List.Mem` with good simp support, all of which the S14 proofs will lean on.

## 2. `labelOf` and `isProper`

```lean
namespace WitnessTree

/-- Root label of a witness tree. -/
def labelOf {P : MTProblem} : WitnessTree P → Fin P.numEvents
  | node l _ => l

end WitnessTree
```

The Moser–Tardos **proper** condition at a node with label `i`:
1. each child’s label `k` lies in the *inclusive* neighbourhood
   `Γ⁺(i) = {i} ∪ collisionAdj i` (a child either re-fires the same event or
   fires a colliding event);
2. distinct children carry distinct labels (`Nodup` on child labels);
3. every child subtree is itself proper (structural recursion).

### Decision D2 — recurse with `List.Forall`, not `∀ t ∈ children`

A literal `∀ t ∈ children, isProper t` inside the match body makes the equation
compiler reach for well-founded recursion (it cannot see `t` as a structural
subterm through `List.Mem`). The clean, structural alternative is Mathlib’s
`List.Forall : (α → Prop) → List α → Prop`, which Lean unfolds along the list
spine so the nested `isProper` call on each element **is** structurally
decreasing. Proposed body:

```lean
/-- Inclusive neighbourhood `Γ⁺(i) = {i} ∪ collisionAdj i`. -/
def inclNbhd {P : MTProblem} (i : Fin P.numEvents) : Finset (Fin P.numEvents) :=
  insert i (P.collisionAdj i)

def isProper {P : MTProblem} : WitnessTree P → Prop
  | node i ch =>
      (ch.map labelOf).Nodup
      ∧ (∀ t ∈ ch, labelOf t ∈ inclNbhd i)
      ∧ List.Forall isProper ch
```

If the equation compiler still balks at `List.Forall isProper ch` (the
recursive argument appears under `List.Forall`), the fallback is an explicit
`termination_by`/`decreasing_by sizeOf` proof, or splitting `isProper` into a
mutual block with a `List`-level helper `isProperList`. **S14 ACT must Docker-
verify which of these three forms the v4.26.0 elaborator accepts** — this is
the one residual risk this PREP cannot retire on paper. Confidence ranking:
`List.Forall` (high) > explicit `sizeOf` termination (high, more boilerplate)
> mutual helper (certain, most boilerplate).

### Decision D3 — parametrise by `MTProblem P`, not an abstract `SimpleGraph`

The S1 open question ("parametrise the tree by the dependency graph or by the
parent `MTProblem`?") is now settled in favour of `MTProblem`: the S12 ACT
shipped the canonical dependency graph `collisionAdj : Fin numEvents → Finset
(Fin numEvents)` *as a def on `P`*, plus `uniformDrawProb`. The tree-
probability bound (S15) multiplies `uniformDrawProb (labelOf v)` over nodes,
so the tree must see `P`. Threading an abstract `SimpleGraph` would force a
re-derivation of `collisionAdj` compatibility at every consumer. Reusability
across the symbolic `LLLAdmissible` path is unaffected — `collisionAdj` is the
intended adjacency for the variable-collision model (`knowledge.md` finding 2).

## 3. Paste-ready S14 ACT skeleton (~40 LOC of the budgeted ~200)

```lean
-- New `§ Part VI: Witness Trees` in MoserTardos.lean, after Part V.
namespace MTProblem
variable (P : MTProblem)

inductive WitnessTree : Type
  | node (label : Fin P.numEvents) (children : List WitnessTree)

namespace WitnessTree
variable {P}

def labelOf : P.WitnessTree → Fin P.numEvents
  | node l _ => l

def inclNbhd (i : Fin P.numEvents) : Finset (Fin P.numEvents) :=
  insert i (P.collisionAdj i)

def isProper : P.WitnessTree → Prop
  | node i ch =>
      (ch.map labelOf).Nodup
      ∧ (∀ t ∈ ch, labelOf t ∈ P.inclNbhd i)
      ∧ List.Forall isProper ch

end WitnessTree
end MTProblem
```

Remaining S14 budget (~160 LOC) goes to: `DecidablePred isProper` (needed for
later filtering/counting), a `size`/`nodeMultiset` accessor for the
probability product, and 3–4 sanity lemmas (`isProper` of a leaf;
`labelOf (node i ch) = i`; membership monotonicity). None require new Mathlib
bearers beyond `List.Nodup`/`List.Forall`/`Finset.insert`, all present at pin.

## 4. Bearer check (no new absences)

| Bearer | Module | Use |
|---|---|---|
| `List.Forall` | `Mathlib/Data/List/Forall2` (core `List.Forall` in `Init`) | structural recursion in `isProper` |
| `List.Nodup` / `List.map` | core | sibling-distinctness |
| `Finset.insert` / `Finset.mem_insert` | core | `inclNbhd` = `{i} ∪ collisionAdj i` |
| `MTProblem.collisionAdj` | this file (S12 ACT, line 408) | adjacency |

All in-pin at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. The only thing the
ACT cannot pre-confirm on paper is **which recursion form (D2) the elaborator
accepts**; that is a first-Docker-iteration check, not a bearer absence.

## 5. Scope / honesty

This is a **doc-only PREP**: no Lean change, no Docker build (a PREP that
asserted a build result would be dishonest). It retires the single largest
definitional risk (positivity) with a certain resolution (`List` children) and
narrows the residual `isProper`-recursion risk to three ranked candidate forms
for the S14 ACT to test. It does not touch `MoserTardos.lean`, `problem.md`,
`knowledge.md`, or the gallery `meta.json`.

## 6. Next action

**S14 ACT**: paste §3’s skeleton into a new `§ Part VI` of `MoserTardos.lean`;
Docker-verify the `isProper` recursion form (try `List.Forall`, fall back to
`termination_by sizeOf`, then to a mutual `isProperList` helper); add the
`DecidablePred` instance + leaf/label sanity lemmas. Target ~200 LOC, 0 new
sorries, 0 new axioms. Then S15 PREP/ACT: the tree-probability bound consuming
`LLLAdmissibleUniform.lll_uniform` (S12 ACT).
