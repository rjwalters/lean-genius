/-
# Erdős Problem #1092 OQ-02: Well-definedness of the threshold `fThreshold`

The parent entry (`erdos-1092`, `Erdos1092Problem.lean`) defines

  `fThreshold r n = sSup { k | ∀ G : SGraph n,
      (∀ S, CanReduceChromatic (induced S) k r) → G.hasColoring (r+1) }`

using `sSup` over `ℕ`. The parent file *documents* — in prose only — the crucial
caveat that this `sSup` is meaningful **only** when `r + 2 ≤ n`:

  * If `r + 1 ≥ n` then every `n`-vertex graph is already `(r+1)`-colorable
    (`SGraph.hasColoring_self` + monotonicity), so the defining set is **all of `ℕ`**,
    which is unbounded, and `sSup ℕ = 0` in Lean's `ConditionallyCompleteLinearOrderBot`
    — a junk value.
  * The parent's own removed axioms broke precisely because they ignored this.

The open question left implicit there is: **in the good regime `r + 2 ≤ n`, is the
defining set genuinely bounded above, so that `fThreshold` is a real maximum rather than a
`sSup`-of-an-unbounded-set artifact?**

This file answers it **yes**, rigorously and axiom-free:

* `SGraph.completeGraph`   — the complete graph `K_n`.
* `completeGraph_not_hasColoring` — `K_n` is not `r`-colorable when `r < n` (pigeonhole).
* `canReduce_removeAll`   — deleting *every* edge makes any graph `r`-colorable (`r ≥ 1`),
  so the full budget `k = n*n` reduces every induced subgraph.
* `fThresholdSet` + `fThresholdSet_downClosed` — the defining set is downward closed.
* `fThresholdSet_bddAbove` — **the defining set is bounded above by `n*n`** once
  `r + 2 ≤ n` (using `K_n` as the witness graph that fails the conclusion).
* `fThreshold_le_sq` — consequently `fThreshold r n ≤ n * n` in the good regime: the
  `sSup` is a genuine, finite maximum, not the `sSup ℕ = 0` junk value.

It then goes further and pins down the set completely:

* `fThresholdSet_zero_mem` — `0 ∈ fThresholdSet r n` **unconditionally**, so the set is
  never empty (the zero-budget hypothesis already forces `(r+1)`-colorability, via `S = univ`).
* `fThreshold_mem` — in the good regime `fThreshold r n` is *itself* a member of its
  defining set (`Nat.sSup_mem` on a nonempty bounded set): the threshold is an **attained**
  maximum, so the budget `fThreshold r n` genuinely forces `(r+1)`-colorability.
* `mem_fThresholdSet_iff` — the full characterization: in the good regime a budget `k`
  forces the conclusion **iff** `k ≤ fThreshold r n`, i.e. the defining set is exactly the
  interval `{0, …, fThreshold r n}`.

Finally, with the well-definedness theory in hand, this file **computes the threshold at
the smallest non-degenerate point** and machine-checks a refutation the parent had only
in prose:

* `fThreshold_one_three` — **`fThreshold 1 3 = 2`**, the first exact value of the
  threshold. Upper bound: `K₃` with the three-pair removal budget; lower bound: budget `2`
  cannot kill all three `K₃` edges (disjoint pair-slot counting), and every non-`K₃`
  3-vertex graph is explicitly 2-colorable.
* `trivial_lower_bound_false` — `fThreshold 1 4 < 4 - 1`: the parent's removed
  `f_trivial_lower` axiom (`n - 1 ≤ fThreshold r n`) is false, via `K₃` + isolated
  vertex — previously only a prose remark, now a theorem.
* `fThreshold_one_four` — **`fThreshold 1 4 = 2`**, the second exact value: budget `2`
  forces 2-colorability of every 4-vertex graph via the *three perfect pairings* of
  `Fin 4` (a killed pairing costs a distinct edge; three killed pairings exceed the
  budget by disjoint pair-slot counting, `three_slots_le_card`; a surviving pairing
  is an explicit 2-coloring).  So the threshold is *constant* from `n = 3` to `n = 4`.
* `fThreshold_one_eq_two` — **the complete `r = 1` row: `fThreshold 1 n = 2` for every
  `n ≥ 3`.** Lower bound: at `S = univ`, budget `2` caps the whole edge set of `G` by
  two removed ordered pairs, and a graph whose edges lie inside two ordered pairs is
  2-colorable outright (`coverColoring`). Upper bound: `K₃` plus `n - 3` isolated
  vertices (`trianglePlus`). The row is *constant* (`fThreshold_one_constant`) — no
  `n - 1`-style growth at `r = 1`, and every rung `(1, 5), (1, 6), …` is settled at
  once (`fThreshold_one_five`).

No new axioms; the parent file has 0 axioms and they are untouched (and unused here).
-/

import Mathlib
import Proofs.Erdos1092Problem

namespace Erdos1092OQ02

/-- **The complete graph `K_n`.** Every pair of distinct vertices is adjacent. -/
def SGraph.completeGraph (n : ℕ) : SGraph n where
  adj u v := u ≠ v
  symm _ _ h := h.symm
  irrefl v := by simp

/-- **`K_n` is not `r`-colorable when `r < n`.** A proper coloring of `K_n` must be
injective (distinct vertices are adjacent, hence differently colored); an injection
`Fin n ↪ Fin r` forces `n ≤ r`. -/
theorem completeGraph_not_hasColoring {n r : ℕ} (h : r < n) :
    ¬ (SGraph.completeGraph n).hasColoring r := by
  rintro ⟨c, hc⟩
  -- The coloring is injective on vertices.
  have hinj : Function.Injective c := by
    intro a b hab
    by_contra hne
    exact hc a b hne hab
  -- An injection `Fin n → Fin r` gives `n ≤ r`, contradicting `r < n`.
  have := Fintype.card_le_of_injective c hinj
  simp only [Fintype.card_fin] at this
  omega

/-- **Deleting every edge trivializes the chromatic number.** For any graph `H` on `n`
vertices and any `r ≥ 1`, removing all `n*n` candidate edges leaves the empty graph, which
is `r`-colorable. Hence `H` can have its chromatic number reduced to `≤ r` within the
budget `k = n*n`. -/
theorem canReduce_removeAll {n : ℕ} (H : SGraph n) {r : ℕ} (hr : 1 ≤ r) :
    CanReduceChromatic H (n * n) r := by
  refine ⟨Finset.univ, ?_, ?_⟩
  · -- `|Fin n × Fin n| = n * n`.
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  · -- The reduced graph has no edges (every pair is "removed"), so it is `r`-colorable.
    refine ⟨fun _ => ⟨0, by omega⟩, ?_⟩
    rintro u v ⟨_, hmem, _⟩
    exact absurd (Finset.mem_univ _) hmem

/-- The defining set of `fThreshold r n`: budgets `k` for which "every induced subgraph is
`r`-reducible with `≤ k` edge deletions" already forces `(r+1)`-colorability of the whole
graph. This is exactly the set `fThreshold r n = sSup (·)` ranges over. -/
def fThresholdSet (r n : ℕ) : Set ℕ :=
  { k : ℕ | ∀ G : SGraph n,
      (∀ S : Finset (Fin n), CanReduceChromatic
        (SGraph.mk (fun u v => u ∈ S ∧ v ∈ S ∧ G.adj u v)
          (fun u v ⟨hu, hv, h⟩ => ⟨hv, hu, G.symm u v h⟩)
          (fun v ⟨_, _, h⟩ => G.irrefl v h)) k r) →
      G.hasColoring (r + 1) }

/-- `fThresholdSet` really is the set `fThreshold` takes its `sSup` over. -/
theorem fThreshold_eq_sSup (r n : ℕ) : fThreshold r n = sSup (fThresholdSet r n) := rfl

/-- **The defining set is downward closed.** If budget `k` already forces the conclusion,
so does any smaller budget `k' ≤ k`: a smaller budget makes the hypothesis *stronger*
(fewer graphs satisfy it), via `CanReduceChromatic_mono_k`. -/
theorem fThresholdSet_downClosed {r n k k' : ℕ} (hk : k' ≤ k)
    (hmem : k ∈ fThresholdSet r n) : k' ∈ fThresholdSet r n := by
  intro G hP'
  -- Upgrade the `k'`-hypothesis to a `k`-hypothesis, then apply `hmem`.
  exact hmem G (fun S => CanReduceChromatic_mono_k _ hk (hP' S))

/-- **The defining set is bounded above by `n*n` in the non-degenerate regime
`1 ≤ r` and `r + 2 ≤ n`.**

Take `K_n` as a witness. With the full budget `k = n*n`, every induced subgraph of `K_n`
is `r`-reducible (`canReduce_removeAll`, which needs `1 ≤ r` — reducing to `0` colors is
impossible on `n ≥ 1` vertices, the *lower* degeneracy of the problem, complementing the
parent file's documented *upper* degeneracy `r + 1 ≥ n`), so `K_n` satisfies the
hypothesis; but `K_n` is *not* `(r+1)`-colorable when `r + 1 < n`
(`completeGraph_not_hasColoring`). Hence `n*n ∉ fThresholdSet`, and by downward-closedness
every element of the set is `< n*n`. -/
theorem fThresholdSet_bddAbove {r n : ℕ} (hr : 1 ≤ r) (hn : r + 2 ≤ n) :
    BddAbove (fThresholdSet r n) := by
  -- `n*n` is not in the set: `K_n` witnesses the failure.
  have hnotmem : n * n ∉ fThresholdSet r n := by
    intro hmem
    -- `K_n` satisfies the full-budget hypothesis...
    have hP : ∀ S : Finset (Fin n), CanReduceChromatic
        (SGraph.mk (fun u v => u ∈ S ∧ v ∈ S ∧ (SGraph.completeGraph n).adj u v)
          (fun u v ⟨hu, hv, h⟩ => ⟨hv, hu, (SGraph.completeGraph n).symm u v h⟩)
          (fun v ⟨_, _, h⟩ => (SGraph.completeGraph n).irrefl v h)) (n * n) r :=
      fun S => canReduce_removeAll _ hr
    -- ...so `hmem` would make `K_n` be `(r+1)`-colorable, which is false.
    exact completeGraph_not_hasColoring (by omega) (hmem (SGraph.completeGraph n) hP)
  -- `n*n` is an upper bound: any element `> n*n` would drag `n*n` into the set.
  refine ⟨n * n, ?_⟩
  intro k hk
  by_contra hlt
  push_neg at hlt   -- `n*n < k`
  exact hnotmem (fThresholdSet_downClosed (le_of_lt hlt) hk)

/-- **`fThreshold` is a genuine, finite maximum in the non-degenerate regime.** For
`1 ≤ r` and `r + 2 ≤ n`, `fThreshold r n ≤ n * n`. This upgrades the parent file's prose
caveat about the `sSup`-pathology into a proved bound: away from *both* degeneracies —
the upper `r + 1 ≥ n` (documented in the parent) and the lower `r = 0` (surfaced here) —
the threshold is a real supremum of a bounded set, not the `sSup ℕ = 0` artifact. -/
theorem fThreshold_le_sq {r n : ℕ} (hr : 1 ≤ r) (hn : r + 2 ≤ n) :
    fThreshold r n ≤ n * n := by
  rw [fThreshold_eq_sSup]
  refine csSup_le' ?_
  -- `n*n` is an upper bound of the defining set (same argument as boundedness).
  intro k hk
  by_contra hlt
  push_neg at hlt
  have hnotmem : n * n ∉ fThresholdSet r n := by
    intro hmem
    have hP : ∀ S : Finset (Fin n), CanReduceChromatic
        (SGraph.mk (fun u v => u ∈ S ∧ v ∈ S ∧ (SGraph.completeGraph n).adj u v)
          (fun u v ⟨hu, hv, h⟩ => ⟨hv, hu, (SGraph.completeGraph n).symm u v h⟩)
          (fun v ⟨_, _, h⟩ => (SGraph.completeGraph n).irrefl v h)) (n * n) r :=
      fun S => canReduce_removeAll _ hr
    exact completeGraph_not_hasColoring (by omega) (hmem (SGraph.completeGraph n) hP)
  exact hnotmem (fThresholdSet_downClosed (le_of_lt hlt) hk)

/-- **The defining set is nonempty: `0 ∈ fThresholdSet r n` unconditionally.**
The zero-budget hypothesis says every induced subgraph is `r`-colorable with *no* edge
deletions. Applied to `S = univ`, this makes `G` itself `r`-colorable (the induced graph on
`univ` has the same adjacency as `G`), hence `(r+1)`-colorable. Needs no regime hypothesis. -/
theorem fThresholdSet_zero_mem (r n : ℕ) : 0 ∈ fThresholdSet r n := by
  intro G hP
  -- Instantiate the hypothesis at `S = univ`.
  obtain ⟨removed, hcard, c, hc⟩ := hP Finset.univ
  -- A zero budget forces `removed = ∅`.
  rw [Nat.le_zero, Finset.card_eq_zero] at hcard
  subst hcard
  -- `c` is then a proper `r`-coloring of `G`: every `G`-edge is an edge of the reduced
  -- induced-on-`univ` graph, so its endpoints get different colors.
  refine SGraph.hasColoring_mono G (Nat.le_succ r) ⟨c, fun u v hadj heq => ?_⟩
  exact hc u v
    ⟨⟨Finset.mem_univ u, Finset.mem_univ v, hadj⟩,
      Finset.notMem_empty _, Finset.notMem_empty _⟩ heq

/-- The defining set is nonempty. -/
theorem fThresholdSet_nonempty (r n : ℕ) : (fThresholdSet r n).Nonempty :=
  ⟨0, fThresholdSet_zero_mem r n⟩

/-- **The threshold is an attained maximum in the non-degenerate regime.** For `1 ≤ r` and
`r + 2 ≤ n`, `fThreshold r n` is itself a member of its defining set: the `sSup` of a
nonempty (`fThresholdSet_nonempty`), bounded-above (`fThresholdSet_bddAbove`) set of naturals
is attained (`Nat.sSup_mem`). So the budget `fThreshold r n` genuinely forces
`(r+1)`-colorability — the threshold is a real maximum, not merely an upper-bounded `sSup`. -/
theorem fThreshold_mem {r n : ℕ} (hr : 1 ≤ r) (hn : r + 2 ≤ n) :
    fThreshold r n ∈ fThresholdSet r n := by
  rw [fThreshold_eq_sSup]
  exact Nat.sSup_mem (fThresholdSet_nonempty r n) (fThresholdSet_bddAbove hr hn)

/-- **Full structural characterization: the defining set is exactly the interval
`{0, 1, …, fThreshold r n}`.** In the non-degenerate regime a budget `k` forces the
conclusion iff it does not exceed the threshold. Forward: `k ≤ sSup` by `le_csSup` with the
boundedness witness. Backward: `fThreshold r n` itself lies in the set (`fThreshold_mem`) and
the set is downward closed (`fThresholdSet_downClosed`). -/
theorem mem_fThresholdSet_iff {r n : ℕ} (hr : 1 ≤ r) (hn : r + 2 ≤ n) (k : ℕ) :
    k ∈ fThresholdSet r n ↔ k ≤ fThreshold r n := by
  constructor
  · intro hk
    rw [fThreshold_eq_sSup]
    exact le_csSup (fThresholdSet_bddAbove hr hn) hk
  · intro hk
    exact fThresholdSet_downClosed hk (fThreshold_mem hr hn)

/-- **The non-degenerate defining set as an interval.** Packaging
`mem_fThresholdSet_iff` as a `Set` equality: for `1 ≤ r`, `r + 2 ≤ n`, the defining set is
exactly `Set.Iic (fThreshold r n) = {0, 1, …, fThreshold r n}`. -/
theorem fThresholdSet_eq_Iic {r n : ℕ} (hr : 1 ≤ r) (hn : r + 2 ≤ n) :
    fThresholdSet r n = Set.Iic (fThreshold r n) := by
  ext k
  rw [Set.mem_Iic]
  exact mem_fThresholdSet_iff hr hn k

/-- Every graph on at most `r + 1` vertices is `(r+1)`-colorable: colour each vertex with
its own index (`hasColoring_self`) and embed into `r + 1` colours (`hasColoring_mono`). -/
theorem hasColoring_of_card_le {r n : ℕ} (hn : n ≤ r + 1) (G : SGraph n) :
    G.hasColoring (r + 1) :=
  SGraph.hasColoring_mono G hn (SGraph.hasColoring_self G)

/-- **The degenerate (upper) regime `n ≤ r + 1`.** Every graph on `n ≤ r + 1` vertices is
already `(r+1)`-colorable, so *every* budget forces the conclusion and the defining set is all
of `ℕ`: `fThresholdSet r n = Set.univ`. This is the `sSup`-pathology the parent file documents
in prose — the degenerate counterpart of the non-degenerate interval characterization
`fThresholdSet_eq_Iic`. (Here `fThreshold r n = sSup Set.univ`, the artifact value.) -/
theorem fThresholdSet_eq_univ_of_card_le {r n : ℕ} (hn : n ≤ r + 1) :
    fThresholdSet r n = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro k G _
  exact hasColoring_of_card_le hn G

/-
## Exact values

With the well-definedness theory complete (nonempty + bounded + attained +
interval), the threshold can now actually be *computed* at the smallest
non-degenerate point. `r = 1`, `n = 3` is the first pair in the good regime
`1 ≤ r`, `r + 2 ≤ n`, and there `fThreshold 1 3 = 2`:

* **Upper bound** (`three_notMem_fThresholdSet_one_three`): with budget `3`,
  `K₃` satisfies the reduction hypothesis — removing the three ordered pairs
  `(0,1), (0,2), (1,2)` makes every induced subgraph edgeless — yet `K₃` is
  not `2`-colorable. So `3` (hence every `k ≥ 3`) is outside the defining set.
* **Lower bound** (`two_mem_fThresholdSet_one_three`): with budget `2`, the
  hypothesis *excludes* `K₃` — each removed ordered pair kills at most one of
  `K₃`'s three edges, so two pairs cannot make the `univ`-induced subgraph
  edgeless (an intersection-counting argument: the three pair-slots
  `{(u,v),(v,u)}` are disjoint, each must meet `removed`). Every other
  3-vertex graph misses some edge and is explicitly 2-colorable (three-case
  split with concrete colorings `![0,1,1]`, `![0,1,0]`, `![0,0,1]`).

The same machinery also formalizes the parent file's *prose-only* refutation
of its removed `f_trivial_lower` axiom (`n - 1 ≤ fThreshold r n`): `K₃` plus
an isolated vertex shows `fThreshold 1 4 ≤ 2 < 3 = n - 1`
(`trivial_lower_bound_false`).
-/

/-- The fixed removal set killing every edge among three vertices: with these
three ordered pairs removed, *no* edge on vertex set `Fin 3` survives. -/
def killAll3 : Finset (Fin 3 × Fin 3) := {(0, 1), (0, 2), (1, 2)}

/-- **Budget `3` does not force 3-vertex graphs to be 2-colorable: `K₃` is a
witness.** Every induced subgraph of `K₃` becomes edgeless after removing the
three pairs of `killAll3` (within budget `3`), so `K₃` satisfies the reduction
hypothesis; but `K₃` is not `2`-colorable (`completeGraph_not_hasColoring`). -/
theorem three_notMem_fThresholdSet_one_three : 3 ∉ fThresholdSet 1 3 := by
  intro hmem
  have hP : ∀ S : Finset (Fin 3), CanReduceChromatic
      (SGraph.mk (fun u v => u ∈ S ∧ v ∈ S ∧ (SGraph.completeGraph 3).adj u v)
        (fun u v ⟨hu, hv, h⟩ => ⟨hv, hu, (SGraph.completeGraph 3).symm u v h⟩)
        (fun v ⟨_, _, h⟩ => (SGraph.completeGraph 3).irrefl v h)) 3 1 := by
    intro S
    refine ⟨killAll3, by decide, ⟨fun _ => 0, ?_⟩⟩
    rintro u v ⟨⟨_, _, huv⟩, hnuv, hnvu⟩ _
    -- Each pair of distinct vertices is hit by `killAll3` in one order or the
    -- other; the diagonal contradicts `K₃`-adjacency (`u ≠ v`).
    fin_cases u <;> fin_cases v <;>
      first
        | exact huv rfl
        | exact hnuv (by decide)
        | exact hnvu (by decide)
  exact completeGraph_not_hasColoring (by omega) (hmem (SGraph.completeGraph 3) hP)

/-- Upper bound at the smallest non-degenerate point: `fThreshold 1 3 ≤ 2`
(any member `k ≥ 3` of the defining set would drag `3` in by
downward-closedness). -/
theorem fThreshold_one_three_le_two : fThreshold 1 3 ≤ 2 := by
  rw [fThreshold_eq_sSup]
  refine csSup_le' ?_
  intro k hk
  by_contra hlt
  push_neg at hlt
  exact three_notMem_fThresholdSet_one_three
    (fThresholdSet_downClosed (by omega) hk)

/-- **Budget `2` forces 3-vertex graphs to be 2-colorable.** Key: with only two
removed ordered pairs, `K₃`'s three edges cannot all be killed — each removed
pair kills at most one edge, made precise by intersecting `removed` with the
three disjoint pair-slots `{(u,v), (v,u)}`. So the reduction hypothesis
excludes `K₃`, and every other 3-vertex graph misses some edge and is
explicitly 2-colorable. -/
theorem two_mem_fThresholdSet_one_three : 2 ∈ fThresholdSet 1 3 := by
  intro G hP
  obtain ⟨removed, hcard, c₁, hc₁⟩ := hP Finset.univ
  -- Every edge of `G` is killed by some removed ordered pair: the reduced
  -- `univ`-induced graph is `1`-colorable, hence edgeless.
  have hkill : ∀ u v, G.adj u v → (u, v) ∈ removed ∨ (v, u) ∈ removed := by
    intro u v hadj
    by_contra h
    push_neg at h
    exact hc₁ u v ⟨⟨Finset.mem_univ u, Finset.mem_univ v, hadj⟩, h.1, h.2⟩
      (Subsingleton.elim _ _)
  by_cases h01 : G.adj 0 1
  · by_cases h02 : G.adj 0 2
    · by_cases h12 : G.adj 1 2
      · -- `K₃` case: three edges need three distinct removed pairs, but
        -- `removed.card ≤ 2`. Contradiction.
        exfalso
        have hm01 : (removed ∩ ({(0, 1), (1, 0)} : Finset (Fin 3 × Fin 3))).Nonempty := by
          rcases hkill 0 1 h01 with h | h
          · exact ⟨_, Finset.mem_inter.mpr ⟨h, by decide⟩⟩
          · exact ⟨_, Finset.mem_inter.mpr ⟨h, by decide⟩⟩
        have hm02 : (removed ∩ ({(0, 2), (2, 0)} : Finset (Fin 3 × Fin 3))).Nonempty := by
          rcases hkill 0 2 h02 with h | h
          · exact ⟨_, Finset.mem_inter.mpr ⟨h, by decide⟩⟩
          · exact ⟨_, Finset.mem_inter.mpr ⟨h, by decide⟩⟩
        have hm12 : (removed ∩ ({(1, 2), (2, 1)} : Finset (Fin 3 × Fin 3))).Nonempty := by
          rcases hkill 1 2 h12 with h | h
          · exact ⟨_, Finset.mem_inter.mpr ⟨h, by decide⟩⟩
          · exact ⟨_, Finset.mem_inter.mpr ⟨h, by decide⟩⟩
        obtain ⟨a, ha⟩ := hm01
        obtain ⟨b, hb⟩ := hm02
        obtain ⟨c, hc⟩ := hm12
        obtain ⟨haR, haE⟩ := Finset.mem_inter.mp ha
        obtain ⟨hbR, hbE⟩ := Finset.mem_inter.mp hb
        obtain ⟨hcR, hcE⟩ := Finset.mem_inter.mp hc
        simp only [Finset.mem_insert, Finset.mem_singleton] at haE hbE hcE
        -- The three witnesses live in disjoint slots, hence are distinct.
        have hab : a ≠ b := by
          rintro rfl
          rcases haE with rfl | rfl <;> simp_all
        have hac : a ≠ c := by
          rintro rfl
          rcases haE with rfl | rfl <;> simp_all
        have hbc : b ≠ c := by
          rintro rfl
          rcases hbE with rfl | rfl <;> simp_all
        have hsub : ({a, b, c} : Finset (Fin 3 × Fin 3)) ⊆ removed := by
          intro p hp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl | rfl
          · exact haR
          · exact hbR
          · exact hcR
        have h3 : 3 ≤ removed.card := by
          calc 3 = ({a, b, c} : Finset (Fin 3 × Fin 3)).card := by
                rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
                  Finset.card_insert_of_notMem (by simp [hbc]),
                  Finset.card_singleton]
              _ ≤ removed.card := Finset.card_le_card hsub
        omega
      · -- Edges only among `{01, 02}`: star at `0`, colour `0 ↦ 0`, `1, 2 ↦ 1`.
        refine ⟨![0, 1, 1], fun u v hadj => ?_⟩
        fin_cases u <;> fin_cases v <;>
          first
            | exact absurd hadj (G.irrefl _)
            | exact absurd hadj h12
            | exact absurd hadj (fun h => h12 (G.symm _ _ h))
            | decide
    · -- No `02` edge: colour `0, 2` alike.
      refine ⟨![0, 1, 0], fun u v hadj => ?_⟩
      fin_cases u <;> fin_cases v <;>
        first
          | exact absurd hadj (G.irrefl _)
          | exact absurd hadj h02
          | exact absurd hadj (fun h => h02 (G.symm _ _ h))
          | decide
  · -- No `01` edge: colour `0, 1` alike.
    refine ⟨![0, 0, 1], fun u v hadj => ?_⟩
    fin_cases u <;> fin_cases v <;>
      first
        | exact absurd hadj (G.irrefl _)
        | exact absurd hadj h01
        | exact absurd hadj (fun h => h01 (G.symm _ _ h))
        | decide

/-- Lower bound: `2 ≤ fThreshold 1 3`, via membership and boundedness. -/
theorem two_le_fThreshold_one_three : 2 ≤ fThreshold 1 3 := by
  rw [fThreshold_eq_sSup]
  exact le_csSup (fThresholdSet_bddAbove (by omega) (by omega))
    two_mem_fThresholdSet_one_three

/-- **The first exact threshold value: `fThreshold 1 3 = 2`.** At the smallest
non-degenerate point of the good regime, the Erdős–Hajnal–Szemerédi threshold
is exactly `2`: a per-subgraph deletion budget of `2` forces `2`-colorability
of every 3-vertex graph, and `2` is the largest budget that does. -/
theorem fThreshold_one_three : fThreshold 1 3 = 2 :=
  le_antisymm fThreshold_one_three_le_two two_le_fThreshold_one_three

/-
## The parent's removed `f_trivial_lower` axiom, refuted in Lean

The parent file removed its axiom `n - 1 ≤ fThreshold r n` with a prose
counterexample (`r = 1`, `n = 4`, `K₃` + isolated vertex). Here that
refutation is machine-checked.
-/

/-- **`K₃` plus an isolated vertex**, on 4 vertices: vertices `0, 1, 2` are
pairwise adjacent, vertex `3` is isolated. -/
def trianglePlusIsolated : SGraph 4 where
  adj u v := u ≠ v ∧ u ≠ 3 ∧ v ≠ 3
  symm _ _ h := ⟨h.1.symm, h.2.2, h.2.1⟩
  irrefl _ h := h.1 rfl

/-- The same three-pair removal set, on 4 vertices: kills every edge of
`trianglePlusIsolated` (whose edges all lie among `0, 1, 2`). -/
def killAll4 : Finset (Fin 4 × Fin 4) := {(0, 1), (0, 2), (1, 2)}

/-- **Budget `3` does not force 4-vertex graphs to be 2-colorable:** `K₃` plus
an isolated vertex satisfies the reduction hypothesis with budget `3` (its
only edges are the triangle's, all killed by `killAll4`), but contains a
triangle, so it is not `2`-colorable (pigeonhole on the three colours of
`0, 1, 2` in `Fin 2`). -/
theorem three_notMem_fThresholdSet_one_four : 3 ∉ fThresholdSet 1 4 := by
  intro hmem
  have hP : ∀ S : Finset (Fin 4), CanReduceChromatic
      (SGraph.mk (fun u v => u ∈ S ∧ v ∈ S ∧ trianglePlusIsolated.adj u v)
        (fun u v ⟨hu, hv, h⟩ => ⟨hv, hu, trianglePlusIsolated.symm u v h⟩)
        (fun v ⟨_, _, h⟩ => trianglePlusIsolated.irrefl v h)) 3 1 := by
    intro S
    refine ⟨killAll4, by decide, ⟨fun _ => 0, ?_⟩⟩
    rintro u v ⟨⟨_, _, huv⟩, hnuv, hnvu⟩ _
    -- Pairs touching vertex `3` are non-adjacent; the rest are killed.
    fin_cases u <;> fin_cases v <;>
      first
        | exact huv.1 rfl
        | exact huv.2.1 rfl
        | exact huv.2.2 rfl
        | exact hnuv (by decide)
        | exact hnvu (by decide)
  obtain ⟨c, hc⟩ := hmem trianglePlusIsolated hP
  -- The triangle `0, 1, 2` needs three distinct colours in `Fin 2`: pigeonhole.
  have h01 := hc 0 1 ⟨by decide, by decide, by decide⟩
  have h02 := hc 0 2 ⟨by decide, by decide, by decide⟩
  have h12 := hc 1 2 ⟨by decide, by decide, by decide⟩
  have v0 := (c 0).isLt
  have v1 := (c 1).isLt
  have v2 := (c 2).isLt
  have e01 : (c 0).val ≠ (c 1).val := fun h => h01 (Fin.ext h)
  have e02 : (c 0).val ≠ (c 2).val := fun h => h02 (Fin.ext h)
  have e12 : (c 1).val ≠ (c 2).val := fun h => h12 (Fin.ext h)
  omega

/-- **`fThreshold 1 4 ≤ 2`** — the parent file's prose counterexample
machine-checked. -/
theorem fThreshold_one_four_le_two : fThreshold 1 4 ≤ 2 := by
  rw [fThreshold_eq_sSup]
  refine csSup_le' ?_
  intro k hk
  by_contra hlt
  push_neg at hlt
  exact three_notMem_fThresholdSet_one_four
    (fThresholdSet_downClosed (by omega) hk)

/-- The parent's removed axiom `f_trivial_lower` (`n - 1 ≤ fThreshold r n`) is
**false**: at `r = 1`, `n = 4` the threshold is at most `2 < 3 = n - 1`. The
"remove a spanning tree" intuition fails because `fThreshold` quantifies over
*all* graphs, and `K₃` + isolated vertex needs only `3` deletions per subgraph
while refusing `2`-colorability. -/
theorem trivial_lower_bound_false : fThreshold 1 4 < 4 - 1 := by
  have := fThreshold_one_four_le_two
  omega

/-
## The second exact value: `fThreshold 1 4 = 2`

The upper bound `fThreshold 1 4 ≤ 2` is above (`K₃` + isolated vertex). The
matching lower bound needs: **budget `2` forces every 4-vertex graph to be
2-colorable.** Mechanism — the *three perfect pairings* of `Fin 4`:

    {0,1 | 2,3}   {0,2 | 1,3}   {0,3 | 1,2}

A pairing yields a proper 2-coloring (pairs = color classes) **unless** one of
its two intra-pair edges is present; and an edge kills exactly the one pairing
that puts its endpoints together.  So if all three pairings are killed, `G`
has three distinct edges — but the reduction hypothesis at `S = univ` with
budget `2` caps `G` at two edges (each removed ordered pair kills at most one
undirected edge: disjoint pair-slot counting, factored into
`three_slots_le_card`).  Hence some pairing survives and 2-colors `G`.
-/

/-- If an edge `{u, v}` is killed by `removed` (one of its two orientations is
a member), then `removed` meets the edge's two-element *pair-slot*
`{(u,v), (v,u)}`. -/
lemma slot_nonempty {n : ℕ} {removed : Finset (Fin n × Fin n)} {u v : Fin n}
    (h : (u, v) ∈ removed ∨ (v, u) ∈ removed) :
    (removed ∩ ({(u, v), (v, u)} : Finset (Fin n × Fin n))).Nonempty := by
  rcases h with h | h
  · exact ⟨(u, v), Finset.mem_inter.mpr ⟨h, Finset.mem_insert_self _ _⟩⟩
  · exact ⟨(v, u), Finset.mem_inter.mpr
      ⟨h, Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))⟩⟩

/-- **Disjoint slot counting.** If `removed` meets three pairwise-disjoint
slot sets, it has at least three elements — the witnesses live in disjoint
slots, hence are pairwise distinct.  (Generic form of the `K₃` counting inside
`two_mem_fThresholdSet_one_three`.) -/
lemma three_slots_le_card {n : ℕ} {removed s₁ s₂ s₃ : Finset (Fin n × Fin n)}
    (h₁ : (removed ∩ s₁).Nonempty) (h₂ : (removed ∩ s₂).Nonempty)
    (h₃ : (removed ∩ s₃).Nonempty)
    (d₁₂ : Disjoint s₁ s₂) (d₁₃ : Disjoint s₁ s₃) (d₂₃ : Disjoint s₂ s₃) :
    3 ≤ removed.card := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  obtain ⟨c, hc⟩ := h₃
  obtain ⟨haR, haS⟩ := Finset.mem_inter.mp ha
  obtain ⟨hbR, hbS⟩ := Finset.mem_inter.mp hb
  obtain ⟨hcR, hcS⟩ := Finset.mem_inter.mp hc
  have hab : a ≠ b := by
    rintro rfl
    exact Finset.disjoint_left.mp d₁₂ haS hbS
  have hac : a ≠ c := by
    rintro rfl
    exact Finset.disjoint_left.mp d₁₃ haS hcS
  have hbc : b ≠ c := by
    rintro rfl
    exact Finset.disjoint_left.mp d₂₃ hbS hcS
  have hsub : ({a, b, c} : Finset (Fin n × Fin n)) ⊆ removed := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact haR
    · exact hbR
    · exact hcR
  calc 3 = ({a, b, c} : Finset (Fin n × Fin n)).card := by
        rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
          Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
    _ ≤ removed.card := Finset.card_le_card hsub

/-- **Budget `2` forces 4-vertex graphs to be 2-colorable.** Case analysis on
the three perfect pairings of `Fin 4`: a surviving pairing (both intra-pair
edges absent) gives an explicit 2-coloring; if each pairing is killed by an
edge, the three killers are distinct edges and the disjoint pair-slot count
forces `removed.card ≥ 3 > 2`. -/
theorem two_mem_fThresholdSet_one_four : 2 ∈ fThresholdSet 1 4 := by
  intro G hP
  obtain ⟨removed, hcard, c₁, hc₁⟩ := hP Finset.univ
  -- Every edge of `G` is killed by one of its two orientations in `removed`.
  have hkill : ∀ u v, G.adj u v → (u, v) ∈ removed ∨ (v, u) ∈ removed := by
    intro u v hadj
    by_contra h
    push_neg at h
    exact hc₁ u v ⟨⟨Finset.mem_univ u, Finset.mem_univ v, hadj⟩, h.1, h.2⟩
      (Subsingleton.elim _ _)
  by_cases h01 : G.adj 0 1
  · by_cases h02 : G.adj 0 2
    · by_cases h03 : G.adj 0 3
      · -- killers 01, 02, 03
        exact absurd (three_slots_le_card (slot_nonempty (hkill 0 1 h01))
          (slot_nonempty (hkill 0 2 h02)) (slot_nonempty (hkill 0 3 h03))
          (Finset.disjoint_left.mpr (by decide))
          (Finset.disjoint_left.mpr (by decide))
          (Finset.disjoint_left.mpr (by decide))) (by omega)
      · by_cases h12 : G.adj 1 2
        · -- killers 01, 02, 12
          exact absurd (three_slots_le_card (slot_nonempty (hkill 0 1 h01))
            (slot_nonempty (hkill 0 2 h02)) (slot_nonempty (hkill 1 2 h12))
            (Finset.disjoint_left.mpr (by decide))
            (Finset.disjoint_left.mpr (by decide))
            (Finset.disjoint_left.mpr (by decide))) (by omega)
        · -- pairing {0,3 | 1,2} survives
          refine ⟨![0, 1, 1, 0], fun u v hadj => ?_⟩
          fin_cases u <;> fin_cases v <;>
            first
              | exact absurd hadj (G.irrefl _)
              | exact absurd hadj h03
              | exact absurd hadj (fun h => h03 (G.symm _ _ h))
              | exact absurd hadj h12
              | exact absurd hadj (fun h => h12 (G.symm _ _ h))
              | decide
    · by_cases h13 : G.adj 1 3
      · by_cases h03 : G.adj 0 3
        · -- killers 01, 13, 03
          exact absurd (three_slots_le_card (slot_nonempty (hkill 0 1 h01))
            (slot_nonempty (hkill 1 3 h13)) (slot_nonempty (hkill 0 3 h03))
            (Finset.disjoint_left.mpr (by decide))
            (Finset.disjoint_left.mpr (by decide))
            (Finset.disjoint_left.mpr (by decide))) (by omega)
        · by_cases h12 : G.adj 1 2
          · -- killers 01, 13, 12
            exact absurd (three_slots_le_card (slot_nonempty (hkill 0 1 h01))
              (slot_nonempty (hkill 1 3 h13)) (slot_nonempty (hkill 1 2 h12))
              (Finset.disjoint_left.mpr (by decide))
              (Finset.disjoint_left.mpr (by decide))
              (Finset.disjoint_left.mpr (by decide))) (by omega)
          · -- pairing {0,3 | 1,2} survives
            refine ⟨![0, 1, 1, 0], fun u v hadj => ?_⟩
            fin_cases u <;> fin_cases v <;>
              first
                | exact absurd hadj (G.irrefl _)
                | exact absurd hadj h03
                | exact absurd hadj (fun h => h03 (G.symm _ _ h))
                | exact absurd hadj h12
                | exact absurd hadj (fun h => h12 (G.symm _ _ h))
                | decide
      · -- pairing {0,2 | 1,3} survives
        refine ⟨![0, 1, 0, 1], fun u v hadj => ?_⟩
        fin_cases u <;> fin_cases v <;>
          first
            | exact absurd hadj (G.irrefl _)
            | exact absurd hadj h02
            | exact absurd hadj (fun h => h02 (G.symm _ _ h))
            | exact absurd hadj h13
            | exact absurd hadj (fun h => h13 (G.symm _ _ h))
            | decide
  · by_cases h23 : G.adj 2 3
    · by_cases h02 : G.adj 0 2
      · by_cases h03 : G.adj 0 3
        · -- killers 23, 02, 03
          exact absurd (three_slots_le_card (slot_nonempty (hkill 2 3 h23))
            (slot_nonempty (hkill 0 2 h02)) (slot_nonempty (hkill 0 3 h03))
            (Finset.disjoint_left.mpr (by decide))
            (Finset.disjoint_left.mpr (by decide))
            (Finset.disjoint_left.mpr (by decide))) (by omega)
        · by_cases h12 : G.adj 1 2
          · -- killers 23, 02, 12
            exact absurd (three_slots_le_card (slot_nonempty (hkill 2 3 h23))
              (slot_nonempty (hkill 0 2 h02)) (slot_nonempty (hkill 1 2 h12))
              (Finset.disjoint_left.mpr (by decide))
              (Finset.disjoint_left.mpr (by decide))
              (Finset.disjoint_left.mpr (by decide))) (by omega)
          · -- pairing {0,3 | 1,2} survives
            refine ⟨![0, 1, 1, 0], fun u v hadj => ?_⟩
            fin_cases u <;> fin_cases v <;>
              first
                | exact absurd hadj (G.irrefl _)
                | exact absurd hadj h03
                | exact absurd hadj (fun h => h03 (G.symm _ _ h))
                | exact absurd hadj h12
                | exact absurd hadj (fun h => h12 (G.symm _ _ h))
                | decide
      · by_cases h13 : G.adj 1 3
        · by_cases h03 : G.adj 0 3
          · -- killers 23, 13, 03
            exact absurd (three_slots_le_card (slot_nonempty (hkill 2 3 h23))
              (slot_nonempty (hkill 1 3 h13)) (slot_nonempty (hkill 0 3 h03))
              (Finset.disjoint_left.mpr (by decide))
              (Finset.disjoint_left.mpr (by decide))
              (Finset.disjoint_left.mpr (by decide))) (by omega)
          · by_cases h12 : G.adj 1 2
            · -- killers 23, 13, 12
              exact absurd (three_slots_le_card (slot_nonempty (hkill 2 3 h23))
                (slot_nonempty (hkill 1 3 h13)) (slot_nonempty (hkill 1 2 h12))
                (Finset.disjoint_left.mpr (by decide))
                (Finset.disjoint_left.mpr (by decide))
                (Finset.disjoint_left.mpr (by decide))) (by omega)
            · -- pairing {0,3 | 1,2} survives
              refine ⟨![0, 1, 1, 0], fun u v hadj => ?_⟩
              fin_cases u <;> fin_cases v <;>
                first
                  | exact absurd hadj (G.irrefl _)
                  | exact absurd hadj h03
                  | exact absurd hadj (fun h => h03 (G.symm _ _ h))
                  | exact absurd hadj h12
                  | exact absurd hadj (fun h => h12 (G.symm _ _ h))
                  | decide
        · -- pairing {0,2 | 1,3} survives
          refine ⟨![0, 1, 0, 1], fun u v hadj => ?_⟩
          fin_cases u <;> fin_cases v <;>
            first
              | exact absurd hadj (G.irrefl _)
              | exact absurd hadj h02
              | exact absurd hadj (fun h => h02 (G.symm _ _ h))
              | exact absurd hadj h13
              | exact absurd hadj (fun h => h13 (G.symm _ _ h))
              | decide
    · -- pairing {0,1 | 2,3} survives
      refine ⟨![0, 0, 1, 1], fun u v hadj => ?_⟩
      fin_cases u <;> fin_cases v <;>
        first
          | exact absurd hadj (G.irrefl _)
          | exact absurd hadj h01
          | exact absurd hadj (fun h => h01 (G.symm _ _ h))
          | exact absurd hadj h23
          | exact absurd hadj (fun h => h23 (G.symm _ _ h))
          | decide

/-- Lower bound: `2 ≤ fThreshold 1 4`, via membership and boundedness. -/
theorem two_le_fThreshold_one_four : 2 ≤ fThreshold 1 4 := by
  rw [fThreshold_eq_sSup]
  exact le_csSup (fThresholdSet_bddAbove (by omega) (by omega))
    two_mem_fThresholdSet_one_four

/-- **The second exact threshold value: `fThreshold 1 4 = 2`.** Combined with
`fThreshold 1 3 = 2`: the threshold does *not* grow from `n = 3` to `n = 4`
(at `r = 1`), refuting any `n - 1`-style growth at the next data point beyond
the parent's removed `f_trivial_lower` axiom. -/
theorem fThreshold_one_four : fThreshold 1 4 = 2 :=
  le_antisymm fThreshold_one_four_le_two two_le_fThreshold_one_four

/-- The threshold is constant across the first two non-degenerate points:
`fThreshold 1 3 = fThreshold 1 4 = 2`. -/
theorem fThreshold_constant_three_four : fThreshold 1 3 = fThreshold 1 4 := by
  rw [fThreshold_one_three, fThreshold_one_four]

#check @completeGraph_not_hasColoring
#check @canReduce_removeAll
#check @fThresholdSet_downClosed
#check @fThresholdSet_bddAbove
#check @fThreshold_le_sq
#check @fThresholdSet_zero_mem
#check @fThreshold_mem
#check @mem_fThresholdSet_iff
#check @fThresholdSet_eq_Iic
#check @hasColoring_of_card_le
#check @fThresholdSet_eq_univ_of_card_le
#check @three_notMem_fThresholdSet_one_three
#check @two_mem_fThresholdSet_one_three
#check @fThreshold_one_three
#check @three_notMem_fThresholdSet_one_four
#check @fThreshold_one_four_le_two
#check @trivial_lower_bound_false
/-
## The complete `r = 1` row: `fThreshold 1 n = 2` for every `n ≥ 3`

The two exact values above generalize: the `r = 1` threshold is `2` at *every*
non-degenerate `n`. Both halves of the (1,3)/(1,4) arguments simplify at this
level of generality:

* **Lower bound, any `n`** — at `S = univ` the reduction hypothesis with budget
  `2` says the *entire edge set* of `G` is covered by at most two removed
  ordered pairs (a `1`-coloring tolerates no surviving edge). A graph whose
  edges live inside two ordered pairs is 2-colorable *outright* — no pairings,
  no parity: an explicit coloring `coverColoring` reads the two color classes
  off the pairs, with a three-way case split on how the pairs share endpoints.
* **Upper bound, any `n ≥ 3`** — `K₃` plus `n - 3` isolated vertices
  (`trianglePlus`) satisfies the hypothesis with budget `3` (its three edges
  are killed by three ordered pairs, in every induced subgraph) but contains a
  triangle, so it is not 2-colorable.

Hence `fThreshold 1 n = 2` for all `n ≥ 3` (`fThreshold_one_eq_two`): the row
is **constant** — the strongest possible refutation of `n - 1`-style growth at
`r = 1`, subsuming `fThreshold_one_three`, `fThreshold_one_four`, and settling
every further rung `(1, 5), (1, 6), …` in one stroke
(e.g. `fThreshold_one_five`).
-/

/-- `K₃` on the first three vertices plus `n - 3` isolated vertices. -/
def trianglePlus (n : ℕ) : SGraph n where
  adj u v := u.val < 3 ∧ v.val < 3 ∧ u ≠ v
  symm _ _ h := ⟨h.2.1, h.1, h.2.2.symm⟩
  irrefl _ h := h.2.2 rfl

/-- The 2-coloring extracted from a two-element cover of the edge set: if all
edges of a graph lie (in some orientation) inside the ordered pairs `p`, `q`,
the second components essentially form one color class. The three branches
handle the ways `p` and `q` can share endpoints head-to-tail. -/
def coverColoring {n : ℕ} (p q : Fin n × Fin n) : Fin n → Fin 2 :=
  if p.1 = q.2 then fun w => if w = p.1 then 1 else 0
  else if p.2 = q.1 then fun w => if w = p.2 then 1 else 0
  else fun w => if w = p.2 ∨ w = q.2 then 1 else 0

/-- If every edge of `G` shows up (in some orientation) among the two ordered
pairs `p`, `q`, then `coverColoring p q` is a proper 2-coloring of `G` —
twelve small cases (four orientations × three coloring branches), each closed
by evaluating the two `if`s. -/
lemma coverColoring_proper {n : ℕ} {G : SGraph n} {p q : Fin n × Fin n}
    (hcov : ∀ u v, G.adj u v →
      (u, v) = p ∨ (u, v) = q ∨ (v, u) = p ∨ (v, u) = q) :
    ∀ u v, G.adj u v → coverColoring p q u ≠ coverColoring p q v := by
  intro u v hadj
  have hne : u ≠ v := fun h => G.irrefl v (h ▸ hadj)
  unfold coverColoring
  rcases hcov u v hadj with h | h | h | h
  · -- `(u, v) = p` : here `p.1 = u`, `p.2 = v`
    have hp1 : p.1 = u := by rw [← h]
    have hp2 : p.2 = v := by rw [← h]
    rw [hp1, hp2]
    by_cases hA : u = q.2
    · simp only [if_pos hA]
      rw [if_pos trivial, if_neg (show ¬v = u from fun h' => hne h'.symm)]
      decide
    · by_cases hB : v = q.1
      · simp only [if_neg hA, if_pos hB]
        rw [if_neg hne, if_pos trivial]
        decide
      · simp only [if_neg hA, if_neg hB]
        rw [if_neg (show ¬(u = v ∨ u = q.2) from fun hor => Or.elim hor hne hA),
          if_pos (Or.inl trivial)]
        decide
  · -- `(u, v) = q` : here `q.1 = u`, `q.2 = v`
    have hq1 : q.1 = u := by rw [← h]
    have hq2 : q.2 = v := by rw [← h]
    rw [hq1, hq2]
    by_cases hA : p.1 = v
    · simp only [if_pos hA]
      rw [if_neg (show ¬u = p.1 from fun h' => hne (h'.trans hA)), if_pos hA.symm]
      decide
    · by_cases hB : p.2 = u
      · simp only [if_neg hA, if_pos hB]
        rw [if_pos hB.symm,
          if_neg (show ¬v = p.2 from fun h' => hne (h'.trans hB).symm)]
        decide
      · simp only [if_neg hA, if_neg hB]
        rw [if_neg (show ¬(u = p.2 ∨ u = v) from
            fun hor => Or.elim hor (fun h' => hB h'.symm) hne),
          if_pos (Or.inr trivial)]
        decide
  · -- `(v, u) = p` : here `p.1 = v`, `p.2 = u`
    have hp1 : p.1 = v := by rw [← h]
    have hp2 : p.2 = u := by rw [← h]
    rw [hp1, hp2]
    by_cases hA : v = q.2
    · simp only [if_pos hA]
      rw [if_neg hne, if_pos trivial]
      decide
    · by_cases hB : u = q.1
      · simp only [if_neg hA, if_pos hB]
        rw [if_pos trivial, if_neg (show ¬v = u from fun h' => hne h'.symm)]
        decide
      · simp only [if_neg hA, if_neg hB]
        rw [if_pos (Or.inl trivial),
          if_neg (show ¬(v = u ∨ v = q.2) from
            fun hor => Or.elim hor (fun h' => hne h'.symm) hA)]
        decide
  · -- `(v, u) = q` : here `q.1 = v`, `q.2 = u`
    have hq1 : q.1 = v := by rw [← h]
    have hq2 : q.2 = u := by rw [← h]
    rw [hq1, hq2]
    by_cases hA : p.1 = u
    · simp only [if_pos hA]
      rw [if_pos hA.symm,
        if_neg (show ¬v = p.1 from fun h' => hne (h'.trans hA).symm)]
      decide
    · by_cases hB : p.2 = v
      · simp only [if_neg hA, if_pos hB]
        rw [if_neg (show ¬u = p.2 from fun h' => hne (h'.trans hB)), if_pos hB.symm]
        decide
      · simp only [if_neg hA, if_neg hB]
        rw [if_pos (Or.inr trivial),
          if_neg (show ¬(v = p.2 ∨ v = u) from
            fun hor => Or.elim hor (fun h' => hB h'.symm) (fun h' => hne h'.symm))]
        decide

/-- Any pair of distinct vertices among the first three is (in one of its two
orientations) one of the three ordered pairs `(v0,v1), (v0,v2), (v1,v2)`. -/
lemma mem_killTri {n : ℕ} {v0 v1 v2 u v : Fin n}
    (h0 : v0.val = 0) (h1 : v1.val = 1) (h2 : v2.val = 2)
    (hu : u.val < 3) (hv : v.val < 3) (hne : u.val ≠ v.val) :
    (u, v) ∈ ({(v0, v1), (v0, v2), (v1, v2)} : Finset (Fin n × Fin n)) ∨
      (v, u) ∈ ({(v0, v1), (v0, v2), (v1, v2)} : Finset (Fin n × Fin n)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Fin.ext_iff]
  omega

/-- **Budget `2` forces 2-colorability on any number of vertices.** At
`S = univ` the reduction hypothesis says the whole edge set of `G` is covered
by at most two removed ordered pairs; `coverColoring` of those two pairs is
then a proper 2-coloring. (No pairing combinatorics is needed at this level of
generality: two ordered pairs cannot hide an odd cycle.) -/
theorem two_mem_fThresholdSet_one {n : ℕ} (hn : 1 ≤ n) : 2 ∈ fThresholdSet 1 n := by
  intro G hP
  obtain ⟨removed, hcard, c₁, hc₁⟩ := hP Finset.univ
  have hkill : ∀ u v, G.adj u v → (u, v) ∈ removed ∨ (v, u) ∈ removed := by
    intro u v hadj
    by_contra hcon
    exact hc₁ u v ⟨⟨Finset.mem_univ u, Finset.mem_univ v, hadj⟩,
      fun hm => hcon (Or.inl hm), fun hm => hcon (Or.inr hm)⟩
      (Subsingleton.elim _ _)
  obtain ⟨p, q, hsub⟩ : ∃ p q : Fin n × Fin n, removed ⊆ {p, q} := by
    have hc : removed.card = 0 ∨ removed.card = 1 ∨ removed.card = 2 := by omega
    rcases hc with hc | hc | hc
    · exact ⟨(⟨0, by omega⟩, ⟨0, by omega⟩), (⟨0, by omega⟩, ⟨0, by omega⟩), by
        simp [Finset.card_eq_zero.mp hc]⟩
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
      exact ⟨a, a, by simp⟩
    · obtain ⟨a, b, _, rfl⟩ := Finset.card_eq_two.mp hc
      exact ⟨a, b, subset_rfl⟩
  refine ⟨coverColoring p q, coverColoring_proper fun u v hadj => ?_⟩
  rcases hkill u v hadj with h | h <;>
    · have hm := hsub h
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      tauto

/-- **Budget `3` never suffices once `n ≥ 3`:** `K₃` plus isolated vertices
satisfies the reduction hypothesis with budget `3` (three ordered pairs kill
its three edges, in every induced subgraph) but contains a triangle, so it is
not 2-colorable. -/
theorem three_notMem_fThresholdSet_one {n : ℕ} (hn : 3 ≤ n) :
    3 ∉ fThresholdSet 1 n := by
  obtain ⟨v0, hv0⟩ : ∃ w : Fin n, w.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨v1, hv1⟩ : ∃ w : Fin n, w.val = 1 := ⟨⟨1, by omega⟩, rfl⟩
  obtain ⟨v2, hv2⟩ : ∃ w : Fin n, w.val = 2 := ⟨⟨2, by omega⟩, rfl⟩
  intro hmem
  have hP : ∀ S : Finset (Fin n), CanReduceChromatic
      (SGraph.mk (fun u v => u ∈ S ∧ v ∈ S ∧ (trianglePlus n).adj u v)
        (fun u v ⟨hu, hv, h⟩ => ⟨hv, hu, (trianglePlus n).symm u v h⟩)
        (fun v ⟨_, _, h⟩ => (trianglePlus n).irrefl v h)) 3 1 := by
    intro S
    refine ⟨{(v0, v1), (v0, v2), (v1, v2)}, ?_, ⟨fun _ => 0, ?_⟩⟩
    · calc ({(v0, v1), (v0, v2), (v1, v2)} : Finset (Fin n × Fin n)).card
          ≤ ({(v0, v2), (v1, v2)} : Finset (Fin n × Fin n)).card + 1 :=
            Finset.card_insert_le _ _
        _ ≤ (({(v1, v2)} : Finset (Fin n × Fin n)).card + 1) + 1 :=
            Nat.add_le_add_right (Finset.card_insert_le _ _) 1
        _ ≤ 3 := by simp
    · rintro u v ⟨⟨_, _, hu3, hv3, hne⟩, hnuv, hnvu⟩ _
      have hcov := mem_killTri hv0 hv1 hv2 hu3 hv3 (fun h => hne (Fin.ext h))
      tauto
  obtain ⟨c, hc⟩ := hmem (trianglePlus n) hP
  have h01 : c v0 ≠ c v1 := hc v0 v1
    ⟨by omega, by omega, fun h => by have := congrArg Fin.val h; omega⟩
  have h02 : c v0 ≠ c v2 := hc v0 v2
    ⟨by omega, by omega, fun h => by have := congrArg Fin.val h; omega⟩
  have h12 : c v1 ≠ c v2 := hc v1 v2
    ⟨by omega, by omega, fun h => by have := congrArg Fin.val h; omega⟩
  have n01 : (c v0).val ≠ (c v1).val := fun h => h01 (Fin.ext h)
  have n02 : (c v0).val ≠ (c v2).val := fun h => h02 (Fin.ext h)
  have n12 : (c v1).val ≠ (c v2).val := fun h => h12 (Fin.ext h)
  have b0 : (c v0).val < 2 := (c v0).isLt
  have b1 : (c v1).val < 2 := (c v1).isLt
  have b2 : (c v2).val < 2 := (c v2).isLt
  omega

/-- Upper bound for the whole row: `fThreshold 1 n ≤ 2` once `n ≥ 3`. -/
theorem fThreshold_one_le_two {n : ℕ} (hn : 3 ≤ n) : fThreshold 1 n ≤ 2 := by
  rw [fThreshold_eq_sSup]
  refine csSup_le' ?_
  intro k hk
  by_contra hlt
  exact three_notMem_fThresholdSet_one hn (fThresholdSet_downClosed (by omega) hk)

/-- Lower bound for the whole row: `2 ≤ fThreshold 1 n` once `n ≥ 3`. -/
theorem two_le_fThreshold_one {n : ℕ} (hn : 3 ≤ n) : 2 ≤ fThreshold 1 n := by
  rw [fThreshold_eq_sSup]
  exact le_csSup (fThresholdSet_bddAbove (by omega) (by omega))
    (two_mem_fThresholdSet_one (by omega))

/-- **The complete `r = 1` row: `fThreshold 1 n = 2` for every `n ≥ 3`.**
The Erdős–Hajnal–Szemerédi threshold at `r = 1` is the constant `2` on the
whole non-degenerate regime — subsuming the pointwise values
`fThreshold_one_three` and `fThreshold_one_four` and settling all further
rungs `(1, 5), (1, 6), …` at once. -/
theorem fThreshold_one_eq_two {n : ℕ} (hn : 3 ≤ n) : fThreshold 1 n = 2 :=
  le_antisymm (fThreshold_one_le_two hn) (two_le_fThreshold_one hn)

/-- The third exact value, now for free: `fThreshold 1 5 = 2`. -/
theorem fThreshold_one_five : fThreshold 1 5 = 2 :=
  fThreshold_one_eq_two (by omega)

/-- The `r = 1` threshold row is constant on the non-degenerate regime. -/
theorem fThreshold_one_constant {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n) :
    fThreshold 1 m = fThreshold 1 n := by
  rw [fThreshold_one_eq_two hm, fThreshold_one_eq_two hn]

#check @slot_nonempty
#check @three_slots_le_card
#check @two_mem_fThresholdSet_one_four
#check @fThreshold_one_four
#check @fThreshold_constant_three_four
#check @trianglePlus
#check @coverColoring
#check @coverColoring_proper
#check @mem_killTri
#check @two_mem_fThresholdSet_one
#check @three_notMem_fThresholdSet_one
#check @fThreshold_one_eq_two
#check @fThreshold_one_five
#check @fThreshold_one_constant

/-
## The `r = 2` row opens: `fThreshold 2 4 = 1`

At `(r, n) = (2, 4)` the target is 3-colorability, and on four vertices the
ONLY graph that is not 3-colorable is `K₄`.  So the threshold is governed by a
single obstruction:

* **Upper bound** (`two_notMem_fThresholdSet_two_four`): with budget `2`,
  `K₄` itself satisfies the reduction hypothesis — removing the two opposite
  edges `{0,1}` and `{2,3}` leaves the 4-cycle `0–2–1–3–0`, which is
  2-colorable by the bipartition `{0,1} | {2,3}` (and every induced subgraph
  inherits the same removal and coloring).  Since `K₄` is not 3-colorable,
  `2 ∉ fThresholdSet 2 4`.
* **Membership of `1`** (`one_mem_fThresholdSet_two_four`): a graph with any
  non-edge `{u,v}` is explicitly 3-colorable (`u, v` share a color, the other
  two vertices get fresh colors).  And the complete graph cannot satisfy the
  budget-1 hypothesis at `S = univ`: one removed pair kills at most one edge,
  so a triangle avoiding the removed edge survives, and its three vertices
  cannot be 2-colored (pigeonhole on `Fin 2`).

Note the contrast with the `r = 1` row: `fThreshold 1 4 = 2` but
`fThreshold 2 4 = 1` — at `n = 4` the threshold strictly DROPS as `r` grows
(`fThreshold_lt_at_four`), because the weaker target (3-colorability) has a
rarer obstruction (`K₄` alone) whose own reducibility is cheap to satisfy.
-/

/-- The two removed pairs turning `K₄` into the 4-cycle `0–2–1–3–0`. -/
def killC4 : Finset (Fin 4 × Fin 4) := {(0, 1), (2, 3)}

/-- **Budget `2` fails at `(r, n) = (2, 4)`**: `K₄` becomes bipartite after
removing the two opposite edges `{0,1}`, `{2,3}` (so every induced subgraph
passes the reduction test with budget `2`), yet `K₄` is not 3-colorable. -/
theorem two_notMem_fThresholdSet_two_four : 2 ∉ fThresholdSet 2 4 := by
  intro hmem
  have hP : ∀ S : Finset (Fin 4), CanReduceChromatic
      (SGraph.mk (fun u v => u ∈ S ∧ v ∈ S ∧ (SGraph.completeGraph 4).adj u v)
        (fun u v ⟨hu, hv, h⟩ => ⟨hv, hu, (SGraph.completeGraph 4).symm u v h⟩)
        (fun v ⟨_, _, h⟩ => (SGraph.completeGraph 4).irrefl v h)) 2 2 := by
    intro S
    refine ⟨killC4, by decide,
      ⟨fun u => if u.val ≤ 1 then 0 else 1, ?_⟩⟩
    rintro u v ⟨⟨-, -, huv⟩, hnuv, hnvu⟩ hcuv
    -- The bipartition `{0,1} | {2,3}`: a monochromatic pair is either the
    -- diagonal (contradicting `K₄`-adjacency) or one of the removed edges.
    fin_cases u <;> fin_cases v <;>
      first
        | exact huv rfl
        | exact hnuv (by decide)
        | exact hnvu (by decide)
        | exact absurd hcuv (by decide)
  exact completeGraph_not_hasColoring (by omega)
    (hmem (SGraph.completeGraph 4) hP)

/-- Upper bound: `fThreshold 2 4 ≤ 1`. -/
theorem fThreshold_two_four_le_one : fThreshold 2 4 ≤ 1 := by
  rw [fThreshold_eq_sSup]
  refine csSup_le' ?_
  intro k hk
  by_contra hlt
  rw [not_le] at hlt
  exact two_notMem_fThresholdSet_two_four
    (fThresholdSet_downClosed (by omega) hk)

/-- **Budget `1` forces 4-vertex graphs to be 3-colorable.**  If some pair is
non-adjacent, an explicit 3-coloring exists outright.  Otherwise the graph is
complete, and the budget-1 hypothesis at `S = univ` is absurd: one removed
pair kills at most one edge, a triangle avoiding it survives, and `Fin 2`
pigeonhole forces a monochromatic surviving edge. -/
theorem one_mem_fThresholdSet_two_four : 1 ∈ fThresholdSet 2 4 := by
  intro G hP
  by_cases hfull : ∀ u v : Fin 4, u ≠ v → G.adj u v
  · -- `G` is complete: refute the `S = univ` budget-1 hypothesis.
    exfalso
    obtain ⟨removed, hcard, c, hc⟩ := hP Finset.univ
    obtain ⟨p, hsub⟩ := Finset.card_le_one_iff_subset_singleton.1 hcard
    -- Two vertices clear of both endpoints of the removed pair.
    have hcard2 : 1 < (Finset.univ \ ({p.1, p.2} : Finset (Fin 4))).card := by
      have h2 : ({p.1, p.2} : Finset (Fin 4)).card ≤ 2 :=
        le_trans (Finset.card_insert_le _ _) (by simp)
      rw [Finset.card_sdiff (Finset.subset_univ _)]
      have h4 : (Finset.univ : Finset (Fin 4)).card = 4 := by simp
      omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hcard2
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
      Finset.mem_singleton, true_and] at ha hb
    have ha1 : a ≠ p.1 := fun h => ha (Or.inl h)
    have ha2 : a ≠ p.2 := fun h => ha (Or.inr h)
    have hb1 : b ≠ p.1 := fun h => hb (Or.inl h)
    -- Surviving edges keep their endpoints differently colored.
    have hsurv : ∀ x y : Fin 4, (x, y) ≠ p → (y, x) ≠ p → x ≠ y →
        c x ≠ c y := by
      intro x y h1 h2 hxy
      exact hc x y ⟨⟨Finset.mem_univ x, Finset.mem_univ y, hfull x y hxy⟩,
        fun hm => h1 (Finset.mem_singleton.1 (hsub hm)),
        fun hm => h2 (Finset.mem_singleton.1 (hsub hm))⟩
    -- `Fin 2` pigeonhole on the triangle `{a, b, p.1}`.
    have h2 : ∀ x : Fin 2, x = 0 ∨ x = 1 := fun x => by omega
    have hpigeon : c a = c b ∨ c a = c p.1 ∨ c b = c p.1 := by
      rcases h2 (c a) with h1 | h1 <;> rcases h2 (c b) with h2' | h2' <;>
        rcases h2 (c p.1) with h3 | h3 <;> simp [h1, h2', h3]
    rcases hpigeon with h | h | h
    · exact hsurv a b (fun he => ha1 (congrArg Prod.fst he))
        (fun he => hb1 (congrArg Prod.fst he)) hab h
    · exact hsurv a p.1 (fun he => ha1 (congrArg Prod.fst he))
        (fun he => ha2 (congrArg Prod.snd he)) ha1 h
    · exact hsurv b p.1 (fun he => hb1 (congrArg Prod.fst he))
        (fun he => hb (Or.inr (congrArg Prod.snd he))) hb1 h
  · -- Some non-edge `{u, v}`: color `u, v` together, the rest fresh.
    push Not at hfull
    obtain ⟨u, v, hne, hnadj⟩ := hfull
    obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.1
      (show (Finset.univ \ ({u, v} : Finset (Fin 4))).card = 2 by
        rw [Finset.card_sdiff (Finset.subset_univ _)]
        have h4 : (Finset.univ : Finset (Fin 4)).card = 4 := by simp
        have h2 : ({u, v} : Finset (Fin 4)).card = 2 := Finset.card_pair hne
        omega)
    have hcover : ∀ x : Fin 4, x ≠ a → x ≠ b → x = u ∨ x = v := by
      intro x hxa hxb
      by_contra hx
      push Not at hx
      have hxin : x ∈ Finset.univ \ ({u, v} : Finset (Fin 4)) := by
        simp [hx.1, hx.2]
      rw [hset] at hxin
      simp [hxa, hxb] at hxin
    refine ⟨fun x => if x = a then 1 else if x = b then 2 else 0, ?_⟩
    intro x y hadj hcxy
    have hxy : x ≠ y := fun h => G.irrefl y (h ▸ hadj)
    by_cases hxa : x = a
    · subst hxa
      by_cases hya : y = a
      · exact hxy hya.symm
      · by_cases hyb : y = b
        · subst hyb
          simp [hab.symm] at hcxy
        · simp [hya, hyb] at hcxy
    · by_cases hxb : x = b
      · subst hxb
        by_cases hyb : y = b
        · exact hxy hyb.symm
        · by_cases hya : y = a
          · subst hya
            simp [hab.symm] at hcxy
          · simp [hab.symm, hya, hyb] at hcxy
      · by_cases hya : y = a
        · simp [hxa, hxb, hya] at hcxy
        · by_cases hyb : y = b
          · simp [hxa, hxb, hyb] at hcxy
          · rcases hcover x hxa hxb with rfl | rfl <;>
              rcases hcover y hya hyb with rfl | rfl
            · exact hxy rfl
            · exact hnadj hadj
            · exact hnadj (G.symm _ _ hadj)
            · exact hxy rfl

/-- Lower bound: `1 ≤ fThreshold 2 4`, via membership and boundedness. -/
theorem one_le_fThreshold_two_four : 1 ≤ fThreshold 2 4 := by
  rw [fThreshold_eq_sSup]
  exact le_csSup (fThresholdSet_bddAbove (by omega) (by omega))
    one_mem_fThresholdSet_two_four

/-- **The first exact value in the `r = 2` row: `fThreshold 2 4 = 1`.**  A
per-subgraph deletion budget of `1` forces 3-colorability of every 4-vertex
graph, and `1` is the largest budget that does (`K₄` passes the budget-2 test
by shedding two opposite edges, yet is not 3-colorable). -/
theorem fThreshold_two_four : fThreshold 2 4 = 1 :=
  le_antisymm fThreshold_two_four_le_one one_le_fThreshold_two_four

/-- **The threshold strictly drops as `r` grows at `n = 4`**:
`fThreshold 2 4 = 1 < 2 = fThreshold 1 4`.  The weaker target
(3-colorability) has a rarer obstruction (`K₄` alone), and that obstruction's
own reducibility is cheap — so the largest "safe" budget shrinks. -/
theorem fThreshold_lt_at_four : fThreshold 2 4 < fThreshold 1 4 := by
  rw [fThreshold_two_four, fThreshold_one_four]
  omega

#check @killC4
#check @two_notMem_fThresholdSet_two_four
#check @one_mem_fThresholdSet_two_four
#check @fThreshold_two_four
#check @fThreshold_lt_at_four

end Erdos1092OQ02
