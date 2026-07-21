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

---

## Session note (2026-07-21, researcher-1): f(4) = 2 exact + sharpened upper bound f(n) ≤ n−2

**Mode**: REVISIT (RICH). **Outcome**: progress (verified, 0-axiom). Resolves the
previously documented-only base case f(4) = 2 — the **first exact value** of the
threshold function.

Three new results (theoremCount 19 → 23, still 0 axioms / 0 sorries):

- **`containsC4_of_rim`** — reusable helper: four *pairwise-distinct* vertices carrying
  the rim edges `a‑b, b‑c, c‑d, d‑a` host a `C₄` via the injective embedding
  `![a,b,c,d] : Fin 4 → V`. Only the rim edges and the six inequalities matter; the
  diagonals are irrelevant.
- **`containsC4_of_minDegree_ge`** — minimum degree `n − 2` on `Fin n` forces a `C₄`
  (`n ≥ 4`). Case split: either `G = ⊤` (use `completeGraph_containsC4`), or `G` has a
  non-adjacent distinct pair `a, c`. Since `δ ≥ n−2`, each vertex has **≤ 1**
  non-neighbour, so `a`'s only possible non-neighbour is `c` and vice versa; hence *every*
  other vertex (there are `n − 2 ≥ 2`) is a common neighbour of both `a` and `c`. Pick two
  as `b, d` → the 4-cycle `a‑b‑c‑d‑a` with the non-edges pushed onto the diagonals.
- **`minDegreeForC4_le_sub_two`** — `f(n) ≤ n − 2` for `n ≥ 4` (sharpens the crude
  complete-graph bound `f(n) ≤ n − 1`).
- **`minDegreeForC4_four`** — `f(4) = 2` exactly, combining the star lower bound
  `f(4) ≥ 2` (`two_le_minDegreeForC4`) with the `n = 4` case of the `n−2` upper bound.

### Lean gotchas (recorded)
- The `decide`-over-all-graphs route (the previously noted blocker for the f(4)=2 upper
  half) is **sidestepped entirely** by the structural non-adjacent-pair / common-neighbour
  argument — no `[DecidableRel]`-instance-binder decidability needed.
- `Finset.card_sdiff` in v4.31 is the **hypothesis-free** form `#(s \ t) = #s − #(s ∩ t)`;
  the subset-cardinality identity I wanted is `Finset.card_sdiff_add_card_eq_card (h : s ⊆ t)
  : (t \ s).card + s.card = t.card`, then `omega`.
- The `![a,b,c,d]` embedding case-bash `fin_cases i <;> fin_cases j <;> simp_all [C4]`
  (and `[Fin.ext_iff]` for injectivity) is cheap **only in a minimal context** — running it
  inside the main lemma (with the `neighborFinset`/`card` hypotheses in scope) blew the
  200000-heartbeat `simp` budget. Extracting `containsC4_of_rim` as a standalone helper with
  just the 4 edges + 6 inequalities made both obligations close instantly.

### Verification
Host-verified (`lake env lean`, Lean v4.31.0, EXIT 0). `#print axioms` for all four new
theorems = `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no `Lean.ofReduceBool`.
lineCount 496 → 610, theoremCount 19 → 23.

### Next
- **f(5) = 3, f(6) = 3?** The lower bounds f(5) ≥ 3, f(6) ≥ 3 exist; upper bounds
  f(5) ≤ 3, f(6) ≤ 3 would need a C₄-free-graph edge count (KST for small n) — the n−2
  bound gives only f(5) ≤ 3 at n=5 (since 5−2=3), so **f(5) = 3 is now also within reach**
  by combining `minDegreeForC4_le_sub_two` (n=5) with `three_le_minDegreeForC4`!
- Monotonicity core and the √n asymptotics remain genuinely open / documented-only.

## Session 2026-07-21 (researcher-1) — KST cherry-counting bound + f(6) = 3 (third exact value)

**Mode**: REVISIT (RICH). **Outcome**: progress (verified, 0-axiom) — the first upper bound
of the *correct order* `√n`, and the third exact value `f(6) = 3`. Docker-build exit 0,
`#print axioms` = `[propext, Classical.choice, Quot.sound]` on all three new theorems (no
sorry/native_decide). theoremCount 24 → 27, lineCount 621 → 722.

The linear bounds (`f(n) ≤ n − 2`) never reach `f(6) = 3` — at `n = 6` they give only `≤ 4`.
The truth `f(n) = (1+o(1))√n` needs the **Kővári–Sós–Turán double count of cherries**:

- **`containsC4_of_card_choose_two_lt`** (the KST heart): `C(|V|,2) < Σ_v C(deg v,2) ⟹ C₄`.
  Model cherries as `C := univ.sigma (fun v => (G.neighborFinset v).powersetCard 2)` — an
  element `⟨v, e⟩` is a centre `v` with a 2-element endpoint set `e ⊆ N(v)`. Then
  `C.card = Σ_v C(deg v, 2)` (`Finset.card_sigma`, `Finset.card_powersetCard`,
  `card_neighborFinset_eq_degree`). The endpoint map `⟨v,e⟩ ↦ e` lands in
  `univ.powersetCard 2` (card `C(|V|,2)`). `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`
  gives two distinct cherries `⟨v,e⟩ ≠ ⟨v',e⟩` with the same `e`; distinctness + equal `e`
  forces `v ≠ v'`, so `e = {x,y}` has two common neighbours `v, v'`, i.e. the rim
  `x–v–y–v'–x` (fed to the existing `containsC4_of_rim`).
- **`minDegreeForC4_le_of_choose_lt`**: `n.choose 2 < n * k.choose 2 ⟹ f(n) ≤ k`. If `δ ≥ k`
  then every `(deg v).choose 2 ≥ k.choose 2` (`Nat.choose_le_choose`), so
  `Σ ≥ n·C(k,2) > C(n,2)`. The hypothesis holds whenever `n ≤ k(k−1)`, giving `f(n) = O(√n)`.
- **`minDegreeForC4_six`**: `f(6) = 3`. Upper `C(6,2)=15 < 18 = 6·C(3,2)` ⟹ `f(6) ≤ 3`
  (`by decide`); lower `three_le_minDegreeForC4`.

### Lean idioms (recorded)
- Sigma-indexed Finset for "structure with a chosen sub-object": `univ.sigma (fun v => …)`;
  `Finset.card_sigma` sums the fibres, `Finset.card_powersetCard s n = s.card.choose n`.
- Pigeonhole: `Finset.exists_ne_map_eq_of_card_lt_of_maps_to (hc : t.card < s.card) (hf : ∀
  a ∈ s, f a ∈ t) : ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y`.
- `ne_of_adj G h : u ≠ v` for `h : G.Adj u v` — the direction is `u ≠ v` (no `.symm` for the
  `b ≠ a` / `d ≠ c` rim inequalities when the adjacency is `Adj v x`).

### Next
- **f(7) = 3?**: the KST count gives only `f(7) ≤ 4` (`7 ≤ 4·3 = 12`, but `7 > 3·2 = 6`); the
  true `f(7) = 3` needs the sharper C₄-free edge bound `ex(7; C₄) = 9` (min degree 3 on 7
  vertices has `≥ ⌈21/2⌉ = 11 > 9` edges) — a genuine extremal input beyond the crude cherry
  count. This is the next exact value and the point where naive KST stops being sharp.
- The general monotonicity core `f(n+1) ≥ f(n)` (the actual open Erdős question) stays open.

## Session 2026-07-21 (researcher-1-4) — explicit closed-form upper bound f(n) ≤ √n + 2

**Mode**: build on the KST cherry-count. **Outcome**: progress — 4 theorems (2 private helpers),
axiom-free (`#print axioms` = `[propext, Classical.choice, Quot.sound]`, no `native_decide`),
host-verified `lake env lean` exit 0. File 722→778 lines.

Unfolded the implicit `O(√n)` of `minDegreeForC4_le_of_choose_lt` into a quotable **closed form**:

- `minDegreeForC4_le_sqrt (hn : 1 ≤ n) : minDegreeForC4 n ≤ Nat.sqrt n + 2`. Take `k = √n + 2`:
  `Nat.lt_succ_sqrt n` gives `n < (√n+1)²`, so `n ≤ (√n)²+2√n`, while
  `k(k−1) = (√n+2)(√n+1) = (√n)²+3√n+2 ≥ n`; `nlinarith` closes it. Leading constant `1`
  matches the true `f(n)=(1+o(1))√n`; only additive `O(1)` lost vs sharp `(1+√(4n−3))/2`.
- `minDegreeForC4_le_of_le_mul_pred (hn : 1≤n) : n ≤ k(k−1) → minDegreeForC4 n ≤ k` — clean
  reformulation of the counting bound; makes the `√n` order transparent (`k(k−1)≥n ≈ k≈√n`).
- `choose_two_lt_of_le_mul_pred (hn : 1≤n) : n ≤ k(k−1) → C(n,2) < n·C(k,2)` — arithmetic
  bridge to `minDegreeForC4_le_of_choose_lt`.

### Reusable Lean recipe
- `2 * m.choose 2 = m*(m−1)`: `rw [Nat.choose_two_right]; exact Nat.mul_div_cancel' h2dvd`
  where `h2dvd : 2 ∣ m*(m−1)` (case `Even m` / `Odd m ⟹ Even (m−1)` via `Nat.Odd.sub_odd`).
- Clear the `Nat.choose 2` floor-division by DOUBLING: prove `2*LHS < 2*RHS` then
  `Nat.lt_of_mul_lt_mul_left`. Avoids fighting `/2` under `omega`/`nlinarith`.
- `mul_left_comm 2 n (k.choose 2)` to move the `2` next to `k.choose 2` before rewriting.
- Sqrt closed forms: `Nat.lt_succ_sqrt n : n < (√n+1)*(√n+1)` feeds `nlinarith` directly.

### Next
- Sharpen the additive constant toward `√n + 1` (holds when `n ≤ (√n)²+√n`, i.e. the lower
  half of each `[s²+1, (s+1)²]` window); a case split on `n ≤ √n·(√n+1)` gives `√n+1` there.
- `f(7)` exact needs `ex(7; C₄) = 9` (KST count only gives `f(7) ≤ 4`, cycle gives `≥ 3`).
- The OPEN core remains eventual monotonicity `f(n+1) ≥ f(n)` — untouched.
