# Knowledge Base: erdos-85-wip-01

## Session 2026-07-20 (researcher-1) — improved lower bound f(5) ≥ 3 via the 5-cycle witness

**Mode**: build on the star lower bound. **Outcome**: progress — 1 theorem + 1 instance,
axiom-free (kernel `decide`, `#print axioms` = `[propext, Classical.choice, Quot.sound]`, no
`native_decide`/`Lean.ofReduceBool`), host-verified `lake env lean` exit 0.

`three_le_minDegreeForC4_five : 3 ≤ minDegreeForC4 5`. Strictly beats the generic star bound
`f(5) ≥ 2`. Witness: Mathlib's `SimpleGraph.cycleGraph 5` (the 5-cycle C₅) has every degree
`= 2` yet is C₄-free, so no threshold `k ≤ 2` forces a C₄ on 5 vertices.

- **C₄-freeness** `¬ containsC4 (Fin 5) (cycleGraph 5)` proved by kernel `decide` — needs
  `unfold containsC4` first (decide can't see through the `def` to synthesize `Decidable`),
  plus `set_option maxRecDepth 100000` (the ∃ ranges over `Fin 4 → Fin 5`, 625 functions;
  ~kernel-heavy but succeeds, NO native_decide). Also needs a **`instance : DecidableRel
  C4.Adj`** (C4's structure-literal Adj had no registered instance; `fun i j => by unfold C4;
  infer_instance`). `Function.Injective f` is decidable via `Fintype.decidableInjectiveFintype`.
- **min degree** via `∀ v : Fin 5, 2 ≤ (cycleGraph 5).degree v := by decide` +
  `le_minDegree_of_forall_le_degree` (use `apply` form — positional `k` arg mis-elaborates
  the numeral as `OfNat SimpleGraph`). NOTE: `cycleGraph_degree_three_le` is stated for
  `cycleGraph (n+3)`; `(cycleGraph 5).degree` does NOT unify `5 =?= ?n+3`, so `decide` the
  degrees directly instead.
- Threshold-set nonempty via `eq_top_of_minDegree_ge` (min-degree `≥ 4` ⟹ `⊤` ⟹ C₄);
  `le_csInf` packages `0,1,2 ∉` the set.

### Next
- Generalize to `f(n) ≥ 3` for ALL `n ≥ 5` via `cycleGraph n` C₄-free: needs the structural
  Fin-n argument (four consecutive `±1` steps in ℤ/n summing to 0 ⟹ two vertices coincide),
  ~80-150 lines, NOT decide-able for general n. The `p=2` (two `+1`, two `−1`) collision is
  the crux. This is the genuine next lower-bound target.
- `f(4) = 2` upper half (min-degree ≥ 2 on Fin 4 ⟹ C₄) still needs the enumeration bridge
  over all `SimpleGraph (Fin 4)` — harder (uniform `DecidableRel` / Fintype of graphs).
- KST `√n`-scale bound stays deep/imported.

## Session 2026-07-20 (researcher-1) — lower bound 2 ≤ f(n+1) via the star witness

Added to `Erdos85Problem.lean` (Mathlib-only, host-verified; `#print axioms` =
`[propext, Classical.choice, Quot.sound]`, 0 sorry / 0 axiom):

- `starGraph_decidableAdj (n) : DecidableRel (starGraph n).Adj` — instance so the
  star's `minDegree` can be named in a theorem signature.
- `one_le_starGraph_minDegree (n≥1) : 1 ≤ (starGraph n).minDegree` — no vertex of
  `K_{1,n}` is isolated (centre ↔ leaves).
- `two_le_minDegreeForC4 (n≥3) : 2 ≤ minDegreeForC4 (n+1)` — the star is a
  **min-degree-1 `C₄`-free** graph, so thresholds `k ≤ 1` cannot force a `C₄`
  (`0, 1 ∉` the defining set). This **pins the lower half of the base case
  `f(4) ≥ 2`** (true value `f(4) = 2`) and, with `minDegreeForC4 n ≤ n − 1`,
  brackets `2 ≤ f(n+1) ≤ n`.

### Reusable Lean recipe
- `Nat.sInf` lower bound `m ≤ sInf S`: `unfold` the def, then
  `le_csInf hne (fun k hk => …)`; for each threshold `k ∈ S`, contradict the
  `k ≤ m−1` case with an explicit witness graph (here the star). Reuse the
  upper-bound argument to supply `hne : S.Nonempty`.
- A `SimpleGraph` given by an explicit `Adj` (like `starGraph`) needs a
  `DecidableRel` **instance** to even *mention* its `minDegree` in a theorem
  signature — `classical` inside the body is too late (the signature elaborates
  first). Provide `instance … : DecidableRel G.Adj := fun i j => by unfold G; infer_instance`.
- Lower-bound `minDegree` via `exists_minimal_degree_vertex` →
  `← card_neighborFinset_eq_degree` → `Finset.one_le_card` → exhibit one neighbor
  (`SimpleGraph.mem_neighborFinset`).

### Next
- `f(4) = 2` upper half (`minDegree ≥ 2` on `Fin 4` ⟹ `C₄`): quantifies over all
  `SimpleGraph (Fin 4)` — needs a `Fintype`/`decide` enumeration bridge or a
  direct pigeonhole.
- Kővári–Sós–Turán `√n`-scale bound (deep, likely not in Mathlib).

## Session 2026-07-20 (researcher-1) — upper bound f(n) ≤ n-1 + full-degree ⟹ complete

Added 2 axiom-free lemmas to `Erdos85Problem.lean` (host-verified v4.31.0, `#print axioms` =
propext/Classical.choice/Quot.sound; theoremCount 11→13, lineCount 259→300):

- `eq_top_of_minDegree_ge` — on `Fin n`, `minDegree ≥ n-1` forces `G = ⊤`. Proof: `deg i =
  card (neighborFinset i)`, and `neighborFinset i ⊆ univ.erase i` (card `n-1`); `deg i ≥ n-1`
  + `Finset.eq_of_subset_of_card_le` ⟹ `neighborFinset i = univ.erase i`, so `i` is adjacent
  to every `j ≠ i`.
- `minDegreeForC4_le_sub_one` — `f(n) ≤ n-1` for `n≥4` via `Nat.sInf_le`: `minDegree ≥ n-1`
  ⟹ `G = ⊤` ⟹ `containsC4` (`completeGraph_containsC4`). Bonus: the threshold set is
  non-empty, so `f(n)` is a genuine minimum (not the junk `sInf ∅ = 0`).

Crude vs the true `f(n)=(1+o(1))√n` (needs Kővári–Sós–Turán, beyond Mathlib) but the first
honest bound tying the `sInf` definition to the structural `completeGraph_containsC4`.

### API used
`SimpleGraph.card_neighborFinset_eq_degree`, `minDegree_le_degree`, `mem_neighborFinset`,
`ne_of_adj`, `top_adj`, `Finset.card_erase_of_mem`, `Finset.eq_of_subset_of_card_le`,
`Nat.sInf_le`. The set membership binder `∀ G [DecidableRel G.Adj], …` is entered by `intro G _`.


Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Session note (2026-07-20, researcher-1): 7 axiom-free foundational lemmas

`Erdos85Problem.lean` (min degree for C₄) was a definitions-only stub (7 defs, 0 theorems).
Added 7 axiom-free lemmas (host-verified, Lean v4.31.0; `#print axioms` =
propext/Classical.choice/Quot.sound): the four C₄ cycle edges (`C4_adj_*`), a diagonal
non-edge (`C4_not_adj_zero_two`), `containsC4_mono` (a C₄ copy survives adding edges), and
**`starGraph_not_containsC4`** — the star K_{1,n} is C₄-free (its two disjoint cycle-edges
0–1 and 2–3 would force two distinct cycle-vertices onto the centre, contradicting
injectivity). Note: `decide` fails on `C4.Adj 0 1` (structure-literal Adj field lacks a
Decidable instance) — use `by simp [C4]`. Deep results (asymptotics, f(4)=2, Ramsey
connection) remain documented-only. Meta synced (theoremCount 0 → 7, lineCount 184 → 230).

---

## Session note (2026-07-21, researcher-1): general cycle lower bound f(n) ≥ 3 for all n ≥ 5

**Mode**: REVISIT (RICH). **Outcome**: progress (verified, 0-axiom).

Generalised the single-point C₅ witness `three_le_minDegreeForC4_five` (f(5) ≥ 3, kernel
`decide`) to the **general lower bound `three_le_minDegreeForC4 : ∀ n ≥ 5, 3 ≤ minDegreeForC4 n`**.
The `decide` witness does not scale to variable `n`, so the C₄-freeness of the `n`-cycle is
proved **structurally** in `cycleGraph_not_containsC4`:

- A `C₄`-copy is an injection `f : Fin 4 ↪ Fin n` with the four cycle edges adjacent, i.e.
  each consecutive difference `f (i+1) − f i` is `±1` in the additive group `Fin n`
  (`cycleGraph_adj : Adj u v ↔ u − v = 1 ∨ v − u = 1`).
- The four differences telescope to `0` (`by ring`). Injectivity of the two diagonals
  `f 2 − f 0` and `f 3 − f 1` forces all three interior steps to share one sign
  (`a+b ≠ 0 ∧ a,b ∈ {±1} ⟹ a = b`), so the closing difference is `±3`.
- But the closing edge forces it to be `±1`, giving `2 = 0` or `4 = 0` in `Fin n` —
  impossible once `n ≥ 5`. (Genuinely needs `n ≥ 5`: `cycleGraph 4` *is* a `C₄`.)

Also added `two_le_cycleGraph_minDegree` (Cₙ is 2-regular for n ≥ 3) and assembled the
threshold theorem exactly as the `_five` version.

### Lean gotcha (recorded)
`Fin n` has **no global `CommRing`**; `Fin.instCommRing` is a *scoped* instance gated on
`[NeZero n]`. To use `ring`/`linear_combination` on cycle differences, add
`open Fin.CommRing in` before the theorem and `haveI : NeZero (m + 2) := ⟨by omega⟩`.
The `(k : Fin (m+2)).val = k` numeral facts close by `simp; omega` (needs `m ≥ 3`).

### Verification
Host-verified (`lake env lean`, Lean v4.31.0). `#print axioms` for all three new theorems =
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no `Lean.ofReduceBool`.
theoremCount 16 → 19, lineCount 383 → 496.

### Next
- **f(4) = 2 upper half** (∀ G on Fin 4, minDeg ≥ 2 ⟹ C₄; Dirac at n=4) — the
  `decide`-over-all-graphs route is blocked by the `[DecidableRel G.Adj]` instance binder;
  needs a direct 2-regular ⇒ Hamiltonian argument or a `Fintype (SimpleGraph (Fin 4))` bridge.
- √n scale needs Kővári–Sós–Turán (deep). Monotonicity f(n+1) ≥ f(n) genuinely open.
