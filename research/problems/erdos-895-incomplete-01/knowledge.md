# Erdős 895 — Formalization correctness finding

**Problem:** `erdos-895-incomplete-01` ("Sorry Completion") — file `proofs/Proofs/Erdos895Problem.lean`.
**Researcher:** researcher-1, 2026-06-25.
**Outcome:** the file's three `sorry`s do **not** all encode true statements. Two
independent bugs make `counterexample_17` / `threshold_sharp` unprovable as written,
and make the stated threshold `n = 18` mismatch Barber's theorem. Documented here with
a reproducible Z3 + pure-Python verification and an explicit corrected counterexample.

## The problem (Barber 2015 / Erdős–Hajnal)

For a triangle-free graph `G` on `{1,…,n}`, must there exist three **distinct**
vertices `a, b, a+b` that are pairwise non-adjacent (an independent additive/Schur
triple)? Barber proved YES for all `n ≥ 18`, and `n = 18` is sharp (a counterexample
exists on `{1,…,17}`).

## What the Lean file does

- `GraphOnInterval n := SimpleGraph (Fin n)` — vertices `{0,…,n-1}`.
- `IsAdditiveTriple a b c := a.val + b.val = c.val ∧ a.val > 0 ∧ b.val > 0`  (no `a ≠ b`).
- `IsIndependentTriple G a b c := ¬G.Adj a b ∧ ¬G.Adj b c ∧ ¬G.Adj a c`.
- `barber_theorem  : ∀ n ≥ 18, …`  (`sorry`)
- `counterexample_17 : ∃ G : GraphOnInterval 17, …`  (`sorry`)
- `erdos895_sat_verified`, `threshold_sharp` depend on the above.

## Bug 1 — `IsAdditiveTriple` omits `a ≠ b`

The definition admits the degenerate triple `(a, a, 2a)`. Because
`IsIndependentTriple` evaluates `¬G.Adj a a` (vacuously true), a single non-edge
`a — 2a` already yields an "independent additive triple". Barber's theorem is about
**three distinct** vertices. Allowing `a = b` strictly weakens the counterexample
requirement and strengthens the positive statement, changing the answer.

## Bug 2 — off-by-one in `Fin n` ↔ `{1,…,m}`

`SimpleGraph (Fin n)` has value-set `{0,…,n-1}`; vertex `0` is **inert** (it is never
part of any additive triple, since `a+b ≥ 2`). So `Fin n` faithfully models `{1,…,n-1}`.
Barber's `{1,…,m}` therefore corresponds to `Fin (m+1)`, and the threshold "m = 18"
lands at **`Fin 19`**, not `Fin 18`. The counterexample for `{1,…,17}` lives on **`Fin 18`**.

## Verified results (Z3 exhaustive search + pure-Python witness checks)

`sat-threshold-scan.py` encodes "∃ triangle-free `G` on `Fin N` with no independent
additive triple" as SAT. Z3 `unsat` is a sound proof that **every** triangle-free
graph on `Fin N` has such a triple. Witness graphs (the `sat` cases) are independently
re-checked by `verify-counterexample.py` (no solver) against the exact Lean predicates.

| definition | counterexample exists on `Fin N` for … | property holds for … | matches Barber? |
|---|---|---|---|
| LOOSE (`a ≤ b`, = file's def) | `N ≤ 11` | `N ≥ 12` | no |
| STRICT (`a < b`, distinct) | `N ≤ 18` | `N ≥ 19` | **yes** (Fin 19 ↔ {1,…,18}) |

### Consequences for the file's `sorry`s (under the file's own LOOSE definition)
- `barber_theorem` (`∀ n ≥ 18`): **TRUE**, but not sharp — it already holds from `n ≥ 12`.
  The `sorry` is the genuinely hard SAT-verified combinatorics; **OPEN to formalize**.
- `counterexample_17` (`∃ G : Fin 17 …`): **FALSE** — Z3 proves UNSAT for `Fin 17`.
  This `sorry` can never be filled.
- `threshold_sharp`, `erdos895_sat_verified`: unfixable as stated (depend on the above).

**Key incompatibility:** there is **no** single definition under which both
`barber_theorem` (`n ≥ 18`) and `counterexample_17` (`Fin 17`) are true.

## Explicit counterexample (corrected statement, distinct vertices)

A triangle-free graph on `Fin 18` (= `{1,…,17}`, vertex `0` isolated), 42 edges, with
**no** independent additive triple in distinct vertices. Stored in
`counterexample-fin18.json`. Edges on `{1,…,17}`:

```
(1,3) (1,5) (1,10) (1,12) (1,14) (1,16) (2,5) (2,6) (2,9) (2,12) (2,13) (2,16)
(3,7) (3,9) (3,11) (3,13) (3,15) (4,5) (4,11) (4,12) (4,13) (4,14) (5,8) (5,15)
(6,7) (6,10) (6,11) (6,14) (6,15) (7,8) (7,12) (7,16) (8,9) (8,10) (8,13) (9,14)
(10,17) (11,16) (12,17) (14,17) (15,17) (16,17)
```

It is a counterexample for the distinct-vertex reading; under the file's loose
definition the triple `(1, 1, 2)` is an independent additive triple (1—2 is a non-edge),
so the graph is **not** a counterexample there — illustrating Bug 1 concretely.

## Recommended fix (for a build-capable session)

1. Add `a ≠ b` to `IsAdditiveTriple` (or quantify over distinct vertices in
   `HasIndependentAdditiveTriple`).
2. Restate `barber_theorem` as `∀ n ≥ 19` (or reindex to `{1,…,m}`, `m ≥ 18`).
3. Replace `counterexample_17` with `counterexample` on `Fin 18`, proving
   `IsTriangleFree G ∧ ¬HasIndependentAdditiveTriple G` by `decide` (the graph is
   `decide`-checkable: ~816 triangle checks + ~64 triple checks) using the explicit
   edge set above. `native_decide` works too but would add `Lean.ofReduceBool`.
4. Leave `barber_theorem` as the genuinely open formalization target (Barber's proof
   is a large SAT/case computation; document it as an `axiom`/`sorry` with provenance).

This session could not build locally (Docker down + olean header mismatch vs the
prebuilt cache), so the corrected Lean proof is left for a build-capable session; the
mathematics above is fully settled and reproducible via the two scripts in this folder.
