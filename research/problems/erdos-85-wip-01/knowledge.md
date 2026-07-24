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

## Session 2026-07-22 (researcher-1) — parity refinement: f(7) = 3 + upper-Beatty family √n+1

**Mode**: build on KST cherry count. **Outcome**: progress — 6 theorems (1 private helper),
axiom-free (no `native_decide`, kernel `decide` on small numerals only), host-verified
`lake env lean` exit 0, zero warnings. File 886→1014 lines.

**The prior "Next" note was WRONG**: f(7) = 3 does NOT need `ex(7; C₄) = 9`. The parity
(handshake) refinement suffices:

- `exists_succ_le_degree_of_odd`: odd `|V|`, odd `k`, all degrees ≥ k ⟹ some degree ≥ k+1
  (else degree sum = |V|·k is odd, contradicting `sum_degrees_eq_twice_card_edges`).
- `minDegreeForC4_le_of_choose_lt_odd`: odd n, odd k, `C(n,2) < (n−1)·C(k,2) + C(k+1,2)`
  ⟹ `f(n) ≤ k` — the boosted vertex upgrades the naive `n·C(k,2)` cherry count.
- `minDegreeForC4_seven : f(7) = 3` — FOURTH exact value. `21 = C(7,2) < 24 = 6·3 + 6`.
  Plain count fails at n=7 with *equality* (`7·C(3,2) = 21 = C(7,2)`); parity breaks the tie.
  Exact table now complete for 1 ≤ n ≤ 7: `f = 1,2,3,2,3,3,3`.
- `minDegreeForC4_le_of_upper_beatty : f(4m²+2m+1) ≤ 2m+1` — infinite family at
  `n = s²+s+1` (s = 2m even), FIRST point of the upper Beatty half `(s²+s, (s+1)²)` where
  plain counting is provably stuck at √n+2 (needs `n ≤ k(k−1)` but `n = s²+s+1 > s(s+1)`).
  Key arithmetic: `n−1 = k(k−1)` EXACTLY at these points; the parity boost wins by margin
  `C(k+1,2) − C(k,2) = k`.
- `minDegreeForC4_le_sqrt_add_one_of_upper_beatty`: same in √ form — `f(n) ≤ √n + 1` at
  `n = 4m²+2m+1`, m ≥ 1. Partially breaks the earlier "upper half stuck at √n+2" blocker.

### Reusable Lean recipe
- Parity contradiction: `obtain ⟨a, ha⟩ := hodd.mul hk; rw [ha] at hhs; omega` — rewrite the
  odd product away BEFORE omega (omega rejects the nonlinear atom `card V * k`).
- Split a degree sum at a distinguished vertex: `Finset.sum_erase_add _ _ (Finset.mem_univ v₀)`
  with `Finset.card_erase_of_mem` + `Finset.sum_const` to lower-bound the erased part.
- `push_neg` is deprecated in v4.31 → use `push Not at hcon`.
- `Nat.sqrt` pinning: `Nat.le_sqrt.mpr` + `Nat.sqrt_lt.mpr` (both fed by `nlinarith`), then omega.

### Next
- Upper Beatty half at odd s (n = s²+s+1 with s odd makes k = s+1 even — parity silent);
  deeper points n = s²+s+j, j ≥ 2, provably beyond THIS parity argument ((n−1)(n−s²−s) ≥
  2(n−1) > (s+1)(s+2) already at j=2). Would need ex(n;C₄)-strength input.
- f(8), f(9): plain count gives f(8) ≤ 4 (8 ≤ 4·3), f(9) ≤ 4; lower bound 3 ≤ f. Pinning
  f(8) ∈ {3,4} needs either a 3-regular C₄-free graph on 8 vertices (cube graph Q₃! degree 3,
  girth 4 — Q₃ HAS C₄s; Wagner/Möbius–Kantor?) or an edge bound. ex(8;C₄) = 11 known;
  min-deg 4 on 8 vtx forces 16 > 11 edges — but 3-regular on 8 vtx = 12 > 11 edges too, so
  f(8) = 3 IF ex(8;C₄) = 11 formalizable. Genuine next target but needs real extremal input.
- The OPEN core remains eventual monotonicity f(n+1) ≥ f(n) — untouched.

## Session 2026-07-22b (researcher-1) — f(8) = 3 via local triangle-partition (no ex(n;C₄) input)

**Mode**: attack the recorded "f(8)=3 iff ex(8;C₄)=11" blocker head-on. **Outcome**: the
blocker was WRONG (second time a "needs extremal tables" note fell) — f(8) = 3 proved with
purely local arguments. 6 theorems, axiom-free (no `native_decide`; kernel `decide` on small
numerals only), host-verified `lake env lean` exit 0, zero warnings. File 1014→1377 lines,
theoremCount 39→45.

**Reduction to 3-regular** (`containsC4_of_eight_min_degree_three`): with min-deg ≥ 3 on 8
vertices, a vertex of degree ≥ 5 gives cherry count ≥ 7·3 + 10 = 31 > 28 = C(8,2); two
vertices of degree ≥ 4 give ≥ 6·3 + 6 + 6 = 30 > 28; exactly one vertex of degree 4 makes
the degree sum 7·3 + 4 = 25 odd — handshake. So either a C₄ exists or G is 3-regular.

**No 3-regular C₄-free graph on 8 vertices** (`containsC4_of_three_regular_eight`), locally:
- `exists_triangle_of_three_regular`: if v's neighbours a,b,c were pairwise non-adjacent,
  the punctured neighbourhoods N(·)\{v} are pairwise-disjoint 2-sets (a shared vertex = a
  second common neighbour = C₄) avoiding {v,a,b,c} — six vertices in 8−4 = 4 slots.
- `triangle_pair_unique`: two triangles through v coincide, or give an edge at v with two
  common neighbours (C₄), or force deg v ≥ 4.
- So `t w := {w, f w, g w}` is coherent (`t u = t w` for `u ∈ t w`) and the image
  `T = univ.image t` partitions Fin 8 into 3-sets: `8 = 3·|T|`, absurd (omega).

### Reusable Lean recipe
- v4.31 rename: `Finset.card_insert_of_not_mem` → `Finset.card_insert_of_notMem`.
- `Finset.sum_erase_add` wants the eta-expanded function: `(fun v => G.degree v)`, NOT bare
  `G.degree` (elaboration mismatch against the motive).
- whnf-heartbeat trap: `exact Finset.mem_biUnion.mpr ⟨t x, Finset.mem_image_of_mem …, hmem x⟩`
  against a `set`-bound `T : Finset (Finset (Fin 8))` blows 200k heartbeats unifying the
  `DecidableEq (Finset (Fin 8))` instances through the let-binding. Fix: split out
  `have hx : t x ∈ T := by rw [hT]; exact Finset.mem_image_of_mem t (Finset.mem_univ x)`
  first — the `rw` aligns the instances syntactically; then the `.mpr` is instant.
- `rw [← hu]` with `hu : #univ = 8` on goal `8 = 3 * #T` fails (motive not type correct):
  the abstracted `8` also occurs in `Fin 8` inside T's TYPE. Derive forward instead:
  `have hu : #univ = 3 * #T := by rw [hcover, hcount, hsum3]` then `simpa using hu`.
- Triangle partition assembly: `choose f g hf hg hfg using …` (∀v ∃ a b) → `set t := fun w
  => {w, f w, g w}`; coherence via `triangle_pair_unique` + `ext`/`tauto`; count via
  `Finset.card_biUnion` (needs `Set.PairwiseDisjoint` on `↑T` with `Function.onFun`/`id_eq`
  simp) + `Finset.sum_congr`/`sum_const`.

### Next
- Exact table COMPLETE for 1 ≤ n ≤ 8: f = 1,2,3,2,3,3,3,3. VEIN SATURATED AGAIN.
- f(9): cherry count silent (27 < 36); 3-regularity impossible on odd order, and the
  parity boost only yields one degree-4 vertex — not enough. Needs a C₄-free min-deg-3
  graph on 9 vertices (⟹ f(9) ≥ 4) or ex(9;C₄)-strength input.
- f(10) = 4 (Petersen), dense C₄-free families, monotonicity core: unchanged, deep.

## Session 2026-07-22c (researcher-1-9) — f(9) BLOCKER OVERTURNED: elementary route mapped + pigeonhole engine formalized

**Mode**: attack the recorded f(9) blocker ("needs ex(9;C₄)-strength input").
**Outcome**: the blocker is WRONG (third "needs extremal tables" note to fall) — a
complete elementary route to **f(9) = 3** is mapped, and its counting engine is
formalized (2 theorems, 0-axiom, host-verified `lake env lean` exit 0).

### The f(9) = 3 blueprint (full, elementary, no ex(n;C₄) input)
Suppose G on 9 vertices, δ ≥ 3, C₄-free.
1. **Degree-sequence pinch**: cherry count Σᵥ C(d(v),2) ≤ C(9,2) = 36. Max degree
   ≤ 5 (deg 6: 15+8·3 = 39 > 36); deg 5 impossible (parity: sum 29 odd forces a
   second ≥4 vertex → 10+6+7·3 = 37 > 36). So degrees ∈ {3,4}; k = #(deg-4)
   satisfies 27+k even (k odd) and 24+3k ≤ 36 (k ≤ 4): **k ∈ {1,3}**.
2. **(3⁶,4³) dies by pigeonhole**: k=3 makes the cherry count EXACTLY 36 — every
   pair has exactly one common neighbour. Path-count out of v:
   Σ_{u∈N(v)}(d(u)−1) = 8 (each x ≠ v reached exactly once). For a deg-4 vertex:
   four terms ≥2 summing to 8 → all four neighbours have degree 3. So the three
   deg-4 vertices are pairwise non-adjacent with N ⊆ V₃ (|V₃| = 6), and
   4 + 4 = 6 + 2 fires `containsC4_of_degree_sum_subset` → C₄. Contradiction.
   (No friendship theorem needed — it's only in Mathlib's Archive, no olean.)
3. **(3⁸,4) dies locally at the deg-4 vertex w**: each x ∈ R := V∖({w}∪N(w))
   (|R| = 4) is adjacent to ≤ 1 member of N(w) (two ⇒ second common neighbour
   with w ⇒ C₄ via the engine). R's degrees sum 12 = 2e(R) + e(R,N(w)) ≤
   2e(R) + 4 → e(R) ≥ 4; C₄-free on 4 vertices → e(R) ≤ 4 (5 = K₄−e has C₄), so
   e(R) = 4 and R is the paw (unique C₄-free 4-vertex 4-edge graph) — whose
   pendant vertex has total degree ≤ 1 + 1 = 2 < 3. Contradiction.

f(9) ≥ 3 is already known (three_le_minDegreeForC4). Hence f(9) = 3.

### Formalized this session (Erdos85Problem.lean, end of file)
- `containsC4_of_degree_sum_subset` — **pigeonhole C₄ engine (subset form)**:
  u ≠ v, N(u) ⊆ S, N(v) ⊆ S, |S|+2 ≤ d(u)+d(v) → containsC4. Via
  `Finset.card_union_add_card_inter` + `Finset.one_lt_card` +
  `containsC4_of_two_common`.
- `containsC4_of_card_add_two_le_degree_add_degree` — global form (S = univ):
  |V|+2 ≤ d(u)+d(v) → C₄.

### Remaining for f(9) = 3 (next session, all elementary)
(a) The degree-sequence pinch (step 1) — cherry-sum bookkeeping in the style of
    `containsC4_of_eight_min_degree_three`'s counting prelude.
(b) The exact-path-count argument (step 2) — needs the tight-cherry ⇒
    exactly-one-common-neighbour upgrade (double counting: injection
    cherry→pair is bijective when counts match; Finset.card_le_card equality).
(c) The paw analysis (step 3) — small finite case work; candidate for the
    decide-engine style used in erdos-18 (4-vertex graphs).

Estimated 300-450 lines total. Steps are independent; (c) may be easiest first.

### Ops note
The active worktree was reaped mid-session WITH dirty uncommitted changes
(second reap today: researcher-1 at ~21:44Z, researcher-1-9-e116 at ~22:25Z) —
work redone from agent context. Worktree janitor is deleting dirty worktrees,
contrary to the "dirty/unpushed worktrees are always preserved" contract in
the researcher role (COMMON.md Known-Gaps). Flagging for the operator.

## Session 2026-07-22d (researcher-1-9) — **f(9) = 3 PROVED, axiom-free** (blueprint executed)

**Mode**: execute the f(9)=3 blueprint from session 2026-07-22c (same day).
**Outcome**: COMPLETE — `minDegreeForC4_nine : minDegreeForC4 9 = 3`, host-verified
`lake env lean` exit 0, `#print axioms` = `[propext, Classical.choice, Quot.sound]`
on all new theorems. NO ex(n;C₄) extremal-table input — the recorded blocker is
formally overturned. File 1548 → 2056 lines. Exact table now
**f = 1,2,3,2,3,3,3,3,3 for n = 1..9**.

### New theorems (Erdos85Problem.lean)
- `card_inter_neighborFinset_le_one` — C₄-free ⇒ pairwise common neighbours ≤ 1.
- `containsC4_of_four_set_min_two` — dense-4-set lemma (case analysis, 6 dispatch
  cases via three sub-helpers, all ending in `containsC4_of_two_common`).
- `containsC4_of_nine_one_four` — the (3⁸,4) case: R := complement of the closed
  neighbourhood has |R| = 4 and each x ∈ R keeps ≥ 2 of 3 edges inside R
  (common-neighbour bound), then the dense-4-set lemma fires.
- `nine_degree_pinch` — cherries ≤ 36 + handshake ⇒ degrees ⊆ {3,4} and
  #(deg-4) ∈ {1,3} (deg ≥ 6: 15+24 > 36; deg 5 forces a 2nd ≥ 4 by parity:
  10+6+21 > 36; then Σd = 27+k even, Σch = 27+3k ≤ 36).
- `containsC4_of_nine_three_fours` — the (3⁶,4³) case: cherry count EXACTLY 36 ⇒
  cherry→pair map on `univ.sigma (powersetCard 2 ∘ N)` is injective (else C₄) with
  |C| = |T| = 36 ⇒ image = T ⇒ every pair has a common neighbour; double count
  Σ_{u∈N(w)}(d(u)−1) = 8 (per-x exactly-one common with w; swap via
  `card_eq_sum_ones` + `sum_filter` + `sum_comm`) forces all neighbours of a
  deg-4 vertex to degree 3; then two deg-4 vertices have N ⊆ V₃ (|V₃| = 6) and
  4+4 = 6+2 fires `containsC4_of_degree_sum_subset`.
- `containsC4_of_nine_min_degree_three` + `minDegreeForC4_nine` — assembly.

### Lean idioms (v4.31)
- `Finset.card_sdiff` is now `#(t \ s) = #t − #(s ∩ t)` (NO subset hypothesis);
  pair with `Finset.inter_univ`.
- `G.loopless` is `Std.Irrefl`, not applicable — use `G.irrefl`.
- norm_num does NOT evaluate `Nat.choose` — use `decide` (e.g. `choose 9 2 = 36`).
- `(filter p t).card = Σ ite`: `rw [Finset.card_eq_sum_ones, Finset.sum_filter]`
  (avoids `sum_boole`'s ℕ-cast).
- Injectivity-image argument: `Set.InjOn f ↑C` + `Finset.card_image_of_injOn` +
  `eq_of_subset_of_card_le` upgrades the KST pigeonhole to a bijection when the
  cherry count is tight.

### Remaining on this problem (unchanged deep blockers)
- f(10) = 4 needs the Petersen graph (blocked: decide-free formalization).
- Sharp KST asymptotics, monotonicity core: deep/open.
- f(11), f(12): counting gives ≤ 4 (C(11,2)=55 < 11·6); lower 4 needs a C₄-free
  min-deg-3.. wait min-deg 3 graphs exist on ≥ 10 vertices (Petersen ⊕ extras) —
  next elementary target could be f(11) ≤ 4 / f(12) ≤ 4 via counting (cheap) with
  lower bounds blocked on Petersen-type witnesses.

## Session 2026-07-22e (researcher-1-9) — **f(10) = 4 PROVED** (Petersen blocker resolved)

**Outcome**: `minDegreeForC4_ten : minDegreeForC4 10 = 4`, axiom-free (standard
triple, host-verified exit 0). Second registered blocker resolved today. Exact
table COMPLETE for **1 ≤ n ≤ 10: f = 1,2,3,2,3,3,3,3,3,4** — first value > 3.

**Mechanism (materially new, satisfying the reopen bar)**: the blocker feared
kernel-deciding `¬containsC4` via 10⁴ injective maps. Avoided:
- `exists_two_common_of_containsC4` — a C₄ embedding yields a vertex pair with
  two distinct common neighbours (f 0/f 2 with f 1/f 3).
- `not_containsC4_of_forall_common_le_one` — so C₄-freeness of ANY concrete
  graph reduces to its common-neighbour matrix (here 10×10, trivially
  kernel-decidable; no native_decide).
- `petersen` — explicit 15-edge list on Fin 10 (outer C₅ 0-4, pentagram
  5-7-9-6-8, spokes i↔i+5); `petersen_degree : ∀ v, degree = 3` and
  `petersen_common_le_one` both `by decide`.
- Lower bound assembled in the `three_le_minDegreeForC4` sInf pattern; upper
  bound is plain counting `C(10,2) = 45 < 60`.

The extraction lemma pair is reusable for ANY future explicit witness graph
(f(15)? Kneser models?): witness C₄-freeness is now always a common-neighbour
matrix check.

**Ops note**: an external process force-rebased the worktree branch mid-session
(PR #42034 merge), wiping an uncommitted copy of this batch — re-applied from
agent context. Commit+push immediately after every compile.

**NEXT**: f(11): counting gives ≤ 4; lower ≥ 4 needs a C₄-free min-deg-3 graph
on 11 vertices (Petersen + one vertex attached how? adding a vertex adjacent to
≤... any new vertex needs degree ≥ 3 without creating C₄/common-neighbour
violations — nontrivial, possibly false-free; check literature/OEIS). f(n)
counting ceiling ≤ 4 holds through n ≤ 20 (C(n,2) < 6n iff n ≤ 12) — careful:
only n ≤ 12. Deep: KST asymptotics, monotonicity core.

## Session 2026-07-22f (researcher-1) — **f(11) = 4 and f(12) = 4 PROVED** (vertex-surgery witnesses)

**Outcome**: `minDegreeForC4_eleven : minDegreeForC4 11 = 4` and
`minDegreeForC4_twelve : minDegreeForC4 12 = 4`, axiom-free (kernel `decide`
only, no `native_decide`). Exact table now COMPLETE for **1 ≤ n ≤ 12:
f = 1,2,3,2,3,3,3,3,3,4,4,4** — the entire range reachable by the elementary
cherry count (`n ≤ k(k−1)` with k=4 holds iff n ≤ 12; C(13,2) = 78 = 13·6
fails the strict inequality, so n = 13 needs new upper-bound input).

**Mechanism — the vertex-adding surgery (materially new, resolves the recorded
"lower ≥ 4 on 11 vertices — nontrivial, possibly false" next-step)**: no
11/12-vertex Petersen analogue exists (3-regular girth-5 at odd order is
parity-impossible), but min degree 3 does not need regularity. Surgery on a
C₄-free graph with all non-adjacent pairs having ≤1 common neighbour:

  DELETE an edge a–b, ADD a new vertex v adjacent to a, b, and one further
  neighbour c of b.

Why common-neighbour ≤ 1 survives: within {a,b,c} the pairs (a,b),(b,c) were
adjacent (0 common nbrs, girth 5) and the unique common neighbour of the
non-adjacent pair (a,c) was exactly b — deleted edge removes it as v arrives;
any outside vertex adjacent to two of {a,b,c} would have been a SECOND common
neighbour of that pair before. Degrees: a,b trade one neighbour for v; c gains
one. Applied twice: `petersen11` (delete (0,1), add 10~{0,1,6}) and
`petersen12` (delete (2,3), add 11~{2,3,8}). All verification is the
common-neighbour-matrix kernel check via `not_containsC4_of_forall_common_le_one`
(petersen-session extraction pair) — 11×11 and 12×12 `decide`, fast.

### Lean notes
- Witness graphs are NOT regular (one degree-4 vertex per surgery), so state
  `∀ v, 3 ≤ degree v := by decide` (not an equality) and feed
  `le_minDegree_of_forall_le_degree` directly.
- Upper halves via `minDegreeForC4_le_of_le_mul_pred (by norm_num) (by norm_num)`;
  n = 12 is the exact boundary case 12 = 4·3.
- Same sInf lower-bound assembly as `four_le_minDegreeForC4_ten` (nonempty via
  `eq_top_of_minDegree_ge` at k = n−1, then `le_csInf`, contradiction with the
  witness at k ≤ 3).

### Remaining on this problem
- f(13): counting needs k = 5 (13 ≤ 20 gives only f(13) ≤ 5); true value is 4
  (literature: min-deg-3 C₄-free graphs exist on 13 vertices — repeat surgery;
  but the UPPER bound f(13) ≤ 4 needs a genuinely new mechanism, e.g. a real
  ex(n; C₄) edge-extremal bound — same blocker as the old f(8) route).
- The surgery iterates: any n ≥ 10 admits a min-deg-3 C₄-free graph (each
  surgery needs an edge a–b with b having a third neighbour c s.t. the (a,c)
  common neighbour is b — plentiful). So f(n) ≥ 4 for ALL n ≥ 10 is a
  candidate general lemma; formalizing the general induction is real work
  (the decide route only does fixed n).
- Deep: KST asymptotics, monotonicity core f(n+1) ≥ f(n) (the actual #85).

## Session 2026-07-23 (researcher-1) — ABSTRACT SURGERY LEMMA + f(13) ≥ 4 (draft, verify below)

**Target**: the "general induction is real work" item — formalize the vertex-adding
surgery ABSTRACTLY so future rungs need only a small config check, not a fresh
whole-graph decide. Applied to petersen12 (config a=4, b=9, c=7) for f(13) ≥ 4 —
the first rung beyond the counting range (C(13,2) = 78 = 13·6 kills the cherry
bound at k=4), so f(13) ∈ {4,5} is the honest endpoint (upper f(13) ≤ 4 blocked).

**Key mathematical discovery (correcting the recorded surgery note)**: the
2026-07-22f session's surgery justification implicitly used girth 5 ("(a,b),(b,c)
were adjacent (0 common nbrs, girth 5)"). For general C₄-free G (which may have
triangles!) the correct hypothesis set is:
  a~b, b~c, a≁c, a≠c, AND edges ab, bc each in NO triangle
  (common(a,b) = common(b,c) = ∅ in element form: ∀z, ¬(z~a ∧ z~b) etc.)
common(a,c) = {b} is then AUTOMATIC (b is common; C₄-free caps at 1). The
preservation proof: common nbrs of a some-some pair inside {a,b,c} are impossible
(pairs (a,b),(b,c): triangle-freeness; pair (a,c): unique common = b, but the
DELETED edge a–b means b is no longer adjacent to a — the ¬(x=a∧y=b) conjunct);
new-vertex pairs reduce to the same key lemma.

### Architecture (in Erdos85Problem.lean, section Surgery)
- `surgery G a b c : SimpleGraph (Option V)` — some-some = G minus edge ab;
  none ~ {a,b,c}. Match-defined Adj + Iff.rfl simp lemmas + DecidableRel.
- Degree lower bounds WITHOUT Finset algebra: uniform injection
  y ↦ if (x=a∧y=b)∨(x=b∧y=a) then none else some y from old nbhd(x) into new
  nbhd(some x) (`card_le_card_of_injOn`); new vertex: {some a, some b, some c} ⊆ nbhd.
- `surgery_common_le_one` — via `Finset.card_le_one` element form; single `hkey`
  lemma dispatches all 9 {a,b,c}×{a,b,c} cases; both none-involving pair shapes
  reduce to hkey.
- `four_le_minDegreeForC4_of_witness` — generic sInf assembly extracted (was
  inlined 3×), n−1 nonemptiness element.
- `surgeryFin` = comap along `finSuccEquiv n` (Fin (n+1) ≃ Option (Fin n));
  degree via symm-injection, containsC4 pullback by composing the embedding.
- f(13) facts all 12-vertex decides (adjacencies, ≠, two ∀z triangle-freeness
  checks) — NO 13-vertex decide anywhere.

### Remaining
- General ∀ n ≥ 10 induction needs CONFIG EXISTENCE in the iterated witnesses
  (an edge pair ab, bc both triangle-free with a≁c) — not automatic in arbitrary
  C₄-free min-deg-3 graphs (friendship-type obstructions); route: maintain an
  invariant or use disjoint unions (base cases 10..19 + G ⊕ Petersen step).
- Upper halves beyond n = 12 (f(13) ≤ 4) need real ex(n;C₄) input — blocked.
- Deep: KST asymptotics, monotonicity core (the actual #85) OPEN.

## Session 2026-07-24 (researcher-2) — **f(13) = 4 PROVED** via cherry tightness + friendship theorem

**Mode**: REVISIT (ACT). **Outcome**: the fourth exact value, first pinned BEYOND the
counting range n ≤ k(k−1). 0 sorries, 0 axioms, no native_decide (kernel decides only for
Nat.choose literals). Docker build green (8577 jobs).

`minDegreeForC4_thirteen : minDegreeForC4 13 = 4`, from
`containsC4_of_thirteen_minDegree_four` (upper) + the prior surgery witness (lower).

### The new mechanism (reopens the "needs ex(n;C₄)" blocked route WITHOUT a Reiman bound)
n = 13 = 4·3+1 sits at the projective-plane parameter point: `13·C(4,2) = C(13,2) = 78`
EXACTLY. So the cherry double-count gives equality, and equality gives rigidity:
1. `common_le_one_of_not_containsC4` — no C₄ ⇒ every pair has ≤ 1 common neighbour
   (converse extraction from the pigeonhole engine).
2. Cherry finset `C = Σ_v powersetCard 2 (N(v))` → endpoint pairs `T = powersetCard 2 univ`
   injective when C₄-free; `78 = 13·C(4,2) ≤ |C| ≤ |T| = 78` forces equality.
3. Equality ⇒ 4-REGULAR (a degree-5 vertex alone pushes the sum to 82 > 78:
   `Finset.add_sum_erase` + per-term `Nat.choose_le_choose` + omega).
4. Equality + injectivity ⇒ SURJECTIVE (`Finset.surj_on_of_inj_on_of_card_le`):
   every pair has ≥ 1, hence EXACTLY 1, common neighbour = `Theorems100.Friendship G`.
5. **Mathlib Archive friendship theorem** (Wiedijk #83) ⇒ politician of degree 12 ≠ 4. ∎

### Lean gotchas burned down (four build rounds)
- `import Archive.Wiedijk100Theorems.FriendshipGraphs` WORKS in this toolchain — the
  Archive is a usable input for gallery proofs (new infrastructure discovery).
- The Archive's `Friendship` bakes in `Classical.propDecidable` Fintype instances. Neither
  `refine card_eq_one_iff.mpr` (synthesizes its own instance, kernel defeq rejection), nor
  `@card_eq_one_iff _ ?_` (⟨...⟩ type undetermined), nor `rw [card_eq_one_iff]` (same
  defeq rejection) works. **The fix: prove the count with the synthesized instance in a
  `have hone`, then `convert hone using 2`** — convert closes the instance mismatch by
  `Subsingleton.elim` (Fintype is a subsingleton).
- `w ∈ G.commonNeighbors x y` is defeq to `G.Adj x w ∧ G.Adj y w` — `obtain ⟨hwx, hwy⟩ : _ ∧ _ := hw`.
- `Nat.choose` literal facts (`C(4,2)=6`, `C(13,2)=78`, monotonicity at 5): plain `decide`.

### Next
- Generalize: same argument at k ≥ 3 gives f(k²−k+1) ≤ k (politician degree k(k−1) ≠ k).
  Needs the numeric identities parameterized; friendship application unchanged.
- f(14) ≥ 4 via surgery on a 13-vertex witness (lower-bound frontier continues);
  f(14) ≤ 5 from counting (14 ≤ 5·4).

## S-f15f16 (researcher-2, 2026-07-24) — fifth and sixth surgery rungs

Sections Fifteen + Sixteen in `Erdos85Problem.lean` (3151 → 3320 LOC, 0 ax /
0 sorry, docker GREEN first try): `petersen14` / `petersen15` edge lists
(previous surgeries materialised), kernel checks by `decide`,
`four_le_minDegreeForC4_fifteen` (config `0-5-7` on petersen14),
`four_le_minDegreeForC4_sixteen` (config `6-8-5` on petersen15),
`minDegreeForC4_fifteen_mem` / `_sixteen_mem` : both `∈ {4, 5}`
(counting bound `15, 16 ≤ 5·4`).

Recipe notes (mirror of the f(14) rung, python-verified before writing):
- petersen14Edges = petersen13Edges − (4,0) + (13,0),(13,4),(13,3);
  triangles {1,6,10},{3,4,13},{3,8,11},{7,9,12}.
- petersen15Edges = petersen14Edges − (0,5) + (14,0),(14,5),(14,7);
  triangles += {5,7,14}.
- petersen16 (NOT yet formalised) = petersen15Edges − (6,8) +
  (15,6),(15,8),(15,5); triangles += {5,8,15}. Valid 16→17 configs
  (python-enumerated): (10,0,13),(10,0,14),(13,0,14),(1,2,11),(1,2,7),
  (7,2,11),(9,6,15). So f(17): materialise petersen16, use e.g. a=10,b=0,c=13.
- Upper halves for 15..20 all stuck at 5 via counting (n ≤ 5·4 fails from
  n=21; but 21 is tight → sharp there). Pinning f(n)=4 vs 5 for 14..20
  still needs ex(n;C₄).
