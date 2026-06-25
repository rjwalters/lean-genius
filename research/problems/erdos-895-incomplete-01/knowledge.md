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

---

## S2 (researcher-9, 2026-06-25) — corrected Fin-18 counterexample MACHINE-VERIFIED + build-broken finding

**Shipped:** new self-contained file `proofs/Proofs/Erdos895CounterexampleFin18.lean`
(111 lines, 0 sorry, 0 literal axiom; native_decide ⟹ depends on `Lean.ofReduceBool`,
status `axiomatized`/badge `axiom`). Builds the 42-edge witness as a genuine
`SimpleGraph (Fin 18)` and proves by `native_decide`:
- `ce895_triangleFree` — triangle-free;
- `ce895_no_distinct_independent_additive_triple` — no independent additive triple in
  DISTINCT vertices;
- `counterexample_fin18` — the two combined (the sharp-threshold witness).
Verified locally via host `lake env lean` (exit 0); independently cross-checked against
the Z3 UNSAT result and the pure-Python verifier in this directory. Gallery entry
`src/data/proofs/erdos-895-counterexample-fin18/`.

This is the corrected, build-verified replacement for the false `counterexample_17`
(researcher-1's analysis confirmed and now realized in Lean), using the explicit
`IsDistinctAdditiveTriple` (a ≠ b) on `Fin 18`.

**NEW build-integrity finding:** `proofs/Proofs/Erdos895Problem.lean` itself is
**build-broken on Mathlib v4.26.0** — it has ~9 PRE-EXISTING compilation errors
(independent of the sorries), all Mathlib API drift in unrelated lemmas:
`Finset.exists_max_image` / `degree G` signature change (dense_triangleFree_independence),
`overloaded` errors and a failed `rw` (mantel_theorem / schur_2 region), and `omega`
failures (erdos895_implies_schur_variant, triangleFree_independence_bound). These are
NOT touched by this PR; the new counterexample is delivered as a clean standalone file
so it compiles regardless. Repairing Erdos895Problem.lean (and reconciling its
statements: add `a ≠ b`, reindex barber_theorem to n ≥ 19) remains open, as does the
genuinely-hard positive direction `barber_theorem` (large SAT/case computation).

---

## S3 (researcher-9, 2026-06-25) — REPAIRED the build-broken Erdos895Problem.lean

The build-broken finding above is now **fixed**. `proofs/Proofs/Erdos895Problem.lean`
compiles cleanly (`lake env lean`, exit 0; 0 errors) with only the 3 expected `sorry`
warnings (`barber_theorem`, `counterexample_17`, `erdos895_sat_verified`). 16 → 0
compile errors. Concrete Mathlib v4.26.0 API fixes applied (auxiliary lemmas only — no
change to any theorem statement):

| was | now |
|---|---|
| `Finset.ssubset_of_subset_of_ne` | `ssubset_of_subset_of_ne` (no longer Finset-namespaced) |
| `Finset.mem_of_mem_sdiff h` | `(Finset.mem_sdiff.mp h).1` |
| `SimpleGraph.mem_neighborFinset.mpr x` | `by rw [SimpleGraph.mem_neighborFinset]; exact x` (lemma now takes explicit `w`) |
| `Finset.mem_union_left {v} h` | `Finset.mem_union_left _ h` (singleton parse / inferred arg) |
| `Nat.sqrt_lt'.mpr` hack for `√n·√n ≤ n` | `Nat.sqrt_le n` (direct lemma) |
| `exists_max_image univ G.degree` | `exists_max_image univ (fun v => G.degree v)` (`degree` carries a `[Fintype (neighborSet…)]` arg, needs η-expansion) |
| greedy helper `omega` (removed.card ≤ k) | added `have hdv : G.degree v < k := hdeg_S v hv` |
| `rw [dif_pos …] at h1` (schur_2 lift) | `simp only [dif_pos …] at h1` (β-reduce the `dite` redex first) |
| `rw [mul_comm (n/3) n, …]` | `rw [mul_comm n (n/3), …]` (goal had `n * (n/3)`, not `(n/3) * n`) |
| `⟨…, by omega, by omega⟩` for `(⟨1,_⟩:Fin n).val > 0` | `Nat.one_pos` (omega/decide choke on the free-var `Fin.mk`; defeq term works) |

**Net effect:** the file's genuinely-proved auxiliary results are now machine-checked,
not silently broken — Mantel's theorem (`mantel_theorem`), R(3,3)=6 (`ramsey_3_3` via
`native_decide`), Schur S(2)=4 (`schur_2`), and the √n / dense triangle-free
independence bounds (`triangleFree_independence_bound`, `dense_triangleFree_independence`).
The 3 remaining `sorry`s are the irreducible ones: `barber_theorem` (open, hard SAT/case
computation), `counterexample_17` (FALSE as stated — corrected witness lives in the
machine-verified companion `Erdos895CounterexampleFin18.lean`), and `erdos895_sat_verified`
(depends on barber). Statement-level reconciliation (add `a ≠ b`, reindex to n ≥ 19)
remains future work but is no longer needed for buildability.

---

## S4 (researcher-6, 2026-06-25) — Erdos895Problem.lean fully reconciled: 3 sorries → 0, build-verified

Picks up exactly where S3 left "statement-level reconciliation" as future work. The main
gallery file `proofs/Proofs/Erdos895Problem.lean` is now **0-sorry, build-verified**
(`lake env lean`, exit 0; 0 errors, 0 warnings of substance) and mathematically
consistent. Note: origin/main still carried the *broken, 3-sorry* version (S3's repair
was never merged and no open PR existed), so this PR re-applies the v4.26 API fixes too.

Statement-level changes (the reconciliation):
- `IsAdditiveTriple` now requires `a ≠ b` (Bug 1 fixed — Barber's three DISTINCT vertices).
- `barber_theorem`: `sorry` → **`axiom`** with provenance, threshold reindexed `n ≥ 18` →
  `n ≥ 19` (Fin model; Bug 2 fixed). Barber's positive direction is a large SAT/case
  computation, recorded as a stated assumption, not reformalized.
- `counterexample_17` (FALSE on `Fin 17`) → **`counterexample`** on `Fin 18` (= {1,…,17}),
  the explicit 42-edge witness proved IN-FILE by `native_decide`. `threshold_sharp` now
  bundles the axiom + the machine-checked counterexample, so n = 19 is sharp.
- `erdos895_sat_verified`: `sorry` → derived corollary of the `barber_theorem` axiom.
- `erdos895_implies_schur_variant`: **removed** (its only proof exploited the degenerate
  (1,1,2) triple that the corrected `a ≠ b` definition now rejects).

Axiom profile (`#print axioms`): `counterexample`/`threshold_sharp` depend on
`Lean.ofReduceBool` (native_decide); the whole file has exactly ONE literal axiom
(`barber_theorem`). Verified infrastructure (`mantel_theorem`, `ramsey_3_3`, `schur_2`,
`triangleFree_independence_bound`, `dense_triangleFree_independence`) is genuinely
assumption-free (propext/Classical.choice/Quot.sound only). Gallery meta updated:
status `axiomatized`, badge `axiom`, axiomCount 2 (barber_theorem + Lean.ofReduceBool),
sorries 0. This integrates into the main file the result S2 shipped standalone as
`Erdos895CounterexampleFin18.lean` (which remains as an independent companion).
