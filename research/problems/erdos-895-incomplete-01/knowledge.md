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

## S4 (researcher-2, 2026-06-25) — BLOCKED: why the reconciliation is NOT a clean local fix

**Mode**: REVISIT. Local build path confirmed working again (host
`env LAKE_UNSAFE=1 lake env lean Proofs/Erdos895CounterexampleFin18.lean` → exit 0;
~7382 Mathlib oleans now present in `.lake`, Docker still down). No code shipped:
the only tractable change cascades. Recording the precise coupling so future
sessions don't re-derive it.

**The trap in the "add `a ≠ b`" reconciliation.** It looks like a 1-line def edit,
but `IsAdditiveTriple`'s *loose* form (allowing `a = b`) is **load-bearing** for a
PROVEN (non-sorry) lemma:

```
theorem erdos895_implies_schur_variant {n : ℕ} (hn : n ≥ 18) : … :=
  …; left; exact ⟨⟨1,_⟩, ⟨1,_⟩, ⟨2,_⟩, ⟨by norm_num, Nat.one_pos, Nat.one_pos⟩, rfl⟩
```

This proof discharges the goal *trivially* with the degenerate triple `(1,1,2)`
(`a = b = 1`), so `c a = c b` is `rfl`. Adding `a ≠ b` makes the term
`IsAdditiveTriple 1 1 2` ill-typed (needs `(1:Fin n) ≠ (1:Fin n)`), so this lemma
**breaks** and would require a genuine Schur-pair argument (every 2-colouring of
`[1,n]`, `n ≥ 18`, has a same-coloured *distinct* additive pair) — nontrivial work,
not a rename. **This is the concrete reason researcher-9 deferred the reconciliation.**

**State of the three sorries (final classification):**
- `barber_theorem` (`∀ n ≥ 18`, positive direction) — **BLOCKED / OPEN**. Barber's
  full combinatorial proof is large (>1000 ln of case/SAT analysis); not a session-
  sized target. Under the file's loose def it is even true from `n ≥ 12`, but proving
  it still needs the real argument (the graph space `2^(n choose 2)` is not
  `decide`-able for unbounded `n`).
- `counterexample_17` (`∃ G : Fin 17 …`) — **FALSE under the loose def** (Z3 UNSAT).
  Making it true requires the cascading `a ≠ b` edit above. The *correct, sharp*
  witness is already machine-verified in the companion `Erdos895CounterexampleFin18.lean`
  (`counterexample_fin18`, Fin 18, distinct-vertex def, `native_decide`). So the
  mathematical content is delivered; only the in-file statement stays cosmetically false
  (and is prominently documented in the file's own header warning).
- `erdos895_sat_verified` (`∀ n : Fin 100, n ≥ 18 → …`) — **BLOCKED**. It is a finite
  family over `n ∈ [18,99]`, but each `n` ranges over `2^(n choose 2)` graphs, far
  beyond `decide`/`native_decide`. No shortcut without Barber's proof.

**Conclusion / next steps.** This OQ is essentially mined out at the session level:
every tractable result (the analysis, the corrected machine-verified counterexample,
the v4.26 build repair) is already shipped. The remaining work is the genuinely-hard
`barber_theorem` formalization. The reconciliation should only be attempted by a
session willing to *also* re-prove `erdos895_implies_schur_variant` with distinct
vertices (or split the loose/strict predicates into two named defs and keep both
lemmas). Recommend leaving the loose def + header warning as-is until then.

---

## Session 2026-06-28 (researcher-1) — ACT: counterexample upgraded to 0-axiom (native_decide → decide)

**Mode**: REVISIT (axiom elimination) · **Outcome**: progress — the corrected Fin-18 counterexample
is now **0-axiom verified**, not `axiomatized`.

### Context
The prior session (2026-06-25) documented that `Erdos895Problem.lean`'s `counterexample_17` is FALSE
(Z3 UNSAT on Fin 17; two bugs: missing `a ≠ b`, and Fin n ↔ {1,…,n−1} off-by-one) and shipped the
corrected witness `Erdos895CounterexampleFin18.lean` (`counterexample_fin18`) — but discharged the two
exhaustive checks with `native_decide`, so it carried `Lean.ofReduceBool` (status `axiomatized`).

### What I did
Replaced both `native_decide` with plain kernel `decide` (`set_option maxRecDepth 10000 in`). The search
is tiny — `18³ = 5832` triples over a 42-edge adjacency list — so the trusted kernel evaluates it directly
(~few seconds). `#print axioms counterexample_fin18` now = `[propext, Quot.sound]` — **no
`Lean.ofReduceBool`, no `sorryAx`**. Host-verified `lake env lean` exit 0 (Docker host down).
- Updated the gallery meta `src/data/proofs/erdos-895-counterexample-fin18/meta.json`: it previously
  OVERCLAIMED the now-absent axiom (`status: axiomatized`, `badge: axiom`, `axiomCount: 1`, ofReduceBool
  in `assumptions`). Corrected to `status: verified`, `badge: verified`, `axiomCount: 0`, rewrote
  `assumptions` and the native_decide prose. (`listings.json` regenerates from meta on `pnpm build`.)

### Honest status
This upgrades only the **counterexample** companion (one of the two directions). The positive direction
`barber_theorem` (n ≥ 18 ⟹ a distinct-vertex independent additive triple always exists) is still a hard
SAT-verified `sorry` in `Erdos895Problem.lean`, and that file is build-broken on Mathlib 4.26 (~9
pre-existing API-drift errors in unrelated Turán/Mantel lemmas) — both remain open.

### Files modified
- proofs/Proofs/Erdos895CounterexampleFin18.lean (native_decide → decide; docstring + axiom audit)
- src/data/proofs/erdos-895-counterexample-fin18/meta.json (verified, 0-axiom)
- research/problems/erdos-895-incomplete-01/knowledge.md (this entry)

### Next steps
- Repair `Erdos895Problem.lean`'s 4.26 build breaks, then restate `barber_theorem` at n ≥ 19 (Fin) /
  reconcile with the corrected distinct-vertex predicate + this proven witness.
- `barber_theorem` positive direction: genuinely hard (Barber's SAT computation), not short-tactic.

---

## S6 (researcher-2, 2026-06-28) — CORRECTION: file builds clean + deprecation future-proofing

**Mode:** REVISIT · **Outcome:** small maintenance progress; stale "build-broken" finding corrected.

### Correction to the "build-broken" claim above
The "Next steps → Repair `Erdos895Problem.lean`'s 4.26 build breaks" and the S2 finding of
"~9 pre-existing compile errors" are **STALE**. `Erdos895Problem.lean` **builds cleanly today**
on Mathlib v4.26.0. Host-verified:
`LAKE_UNSAFE=1 lake env lean Proofs/Erdos895Problem.lean` → **exit 0, 0 errors**, only the 3
expected `sorry` warnings (`barber_theorem` L129, `counterexample_17` L141,
`erdos895_sat_verified` L495). The S3 (researcher-9) repair landed and holds — the build is
**not** broken. Future sessions should NOT chase a build repair here; that work is done.

### What I shipped
Future-proofed two Mathlib-v4.26 **deprecations** the linter flags, which become hard errors
when the old names are removed (pure renames, no statement/proof-structure change):
- L264 `Finset.card_insert_of_not_mem` → `Finset.card_insert_of_notMem`
- L448 `Finset.not_mem_empty` → `Finset.notMem_empty`

Re-verified after the edit: `lake env lean` **exit 0, 0 deprecation warnings, 0 errors,
3 sorries** (unchanged). No mathematical content touched; the 3 sorries and all proven
auxiliary lemmas (Mantel, R(3,3), Schur S(2)=4, √n independence bounds) are intact.

(Left the remaining *linter* warnings — one unused binder `hk` L208, four unused simp args —
untouched: cosmetic only, no build-stability value, not worth the diff churn / re-verify cost.)

### Honest status of the OQ (unchanged, still essentially mined out)
- `barber_theorem` — BLOCKED/OPEN (hard Barber SAT computation; Aristotle still **down**: MCP
  `prove` returns `Resource not found`, host smoke test 404s — re-confirmed this session).
- `counterexample_17` — FALSE as stated under the loose def; sharp corrected witness already
  shipped 0-axiom in companion `Erdos895CounterexampleFin18.lean` (`counterexample_fin18`).
- `erdos895_sat_verified` — BLOCKED (depends on barber).
- Statement reconciliation (add `a ≠ b`) still cascades through `erdos895_implies_schur_variant`
  (see S4) — defer until a session re-proves that lemma with distinct vertices or splits the
  loose/strict predicates.

---

## S7 (researcher-5, 2026-06-30) — ACT: removed the FALSE `counterexample_17` sorry from the main file (3→2 sorries)

**Mode:** ACT (integrity fix, no cascade) · **Outcome:** progress — `Erdos895Problem.lean`
is no longer carrying a `sorry` on a FALSE statement; the corrected sharp counterexample is
now machine-verified *in the main file*.

### What I did
The prior sessions established that `counterexample_17` (∃ G on `Fin 17`, triangle-free, no
loose independent additive triple) is **FALSE** (Z3 exhaustive UNSAT) and shipped the corrected
0-axiom Fin-18 witness in the companion `Erdos895CounterexampleFin18.lean`. But the main file
still held the false statement behind a `sorry`, and `threshold_sharp` built a sorry-backed proof
of a false-as-stated sharpness claim (an integrity hazard).

Using the **split-predicate** route S4 recommended (so nothing cascades into
`erdos895_implies_schur_variant`, which needs the loose `(1,1,2)` triple):
1. Added strict predicates `IsDistinctAdditiveTriple` (= loose + `a ≠ b`) and
   `HasDistinctIndependentAdditiveTriple` alongside the loose ones (loose ones untouched).
2. Replaced `counterexample_17` (FALSE, `sorry`) with `counterexample_fin18` (TRUE, **proven**):
   re-exports the companion's `decide`-verified result against this file's predicates
   (definitionally identical; bridged by `obtain`/`rintro`/`exact`). Added
   `import Proofs.Erdos895CounterexampleFin18`.
3. Updated `threshold_sharp` to pair `barber_theorem` (loose positive, still the open `sorry`)
   with the corrected strict `counterexample_fin18`.
4. Rewrote the header correctness note + gallery meta (sorries 3→2, lineCount 462→544,
   definitionCount 14→15, assumptions text).

### Build status
**VERIFIED** via Docker wrapper (`docker-build.sh Proofs.Erdos895Problem`, exit 0, 7744 jobs,
0 errors). Exactly 2 `sorry` warnings remain: `barber_theorem` (L146) and `erdos895_sat_verified`
(L529) — both the genuinely-hard positive direction. `counterexample_fin18` is sorry-free and
0-axiom (re-exports the companion's plain-`decide` proof; the bridge adds no axioms).

### Honest status (unchanged conclusion: positive direction still open)
- `barber_theorem` / `erdos895_sat_verified` — still BLOCKED/OPEN (Barber's large SAT/case
  computation; not session-sized; Aristotle has been down).
- Sharpness counterexample direction — now fully formalized & machine-verified in the main file,
  not just the companion. The file is no longer internally inconsistent.

### Files modified
- proofs/Proofs/Erdos895Problem.lean (strict predicates; counterexample_17 → counterexample_fin18;
  threshold_sharp; header note)
- src/data/proofs/erdos-895/meta.json (sorries 3→2, lineCount, definitionCount, assumptions, proofStrategy)
- research/problems/erdos-895-incomplete-01/knowledge.md (this entry)
