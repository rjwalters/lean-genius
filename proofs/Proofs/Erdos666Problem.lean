/-
Erdős Problem #666: C₆ in Hypercube Subgraphs

Source: https://erdosproblems.com/666
Status: SOLVED (Answer: NO, by Chung 1992 and Brouwer-Dejter-Thomassen 1993)

Statement:
Let Qₙ be the n-dimensional hypercube graph (2ⁿ vertices, n·2ⁿ⁻¹ edges).
Is it true that for every ε > 0, if n is sufficiently large, every
subgraph of Qₙ with ≥ ε·n·2ⁿ⁻¹ edges contains a C₆?

Answer: NO

Chung (1992) and independently Brouwer-Dejter-Thomassen (1993) showed that
Qₙ can be edge-partitioned into 4 subgraphs, each containing no C₆.
This means a subgraph with 1/4 of all edges (ε = 1/4) need not contain C₆.

Further Improvement:
Conder (1993) showed that for n ≥ 3, the edges of Qₙ can be 3-colored
such that no color class contains C₄ or C₆.

References:
- Chung (1992): "Subgraphs of a hypercube containing no small even cycles"
- Brouwer-Dejter-Thomassen (1993): "Highly symmetric subgraphs of hypercubes"
- Conder (1993): 3-coloring result

Implementation note (Mathlib v4.26):
The propositional definitions `HasCycle`, `HasC6` and `EpsilonDenseSubgraph`
are marked `@[irreducible]`. Under Mathlib v4.26 the elaborator overflows its
native stack (SIGSEGV/SIGBUS, build exit 135/139) whenever a *single* type it
elaborates forces both `Nat.card H.edgeSet` (edge-set cardinality of a graph on
`Fin (2^n)`) and `HasCycle H k` (which exposes `H.Adj` over `Fin k → Fin (2^n)`)
to unfold together — e.g. `∃ H, (edge bound) ∧ ¬ HasC6 H`, or the same body at a
concrete density such as `1/4`. Keeping these definitions opaque prevents that
co-unfolding, so the file elaborates while the mathematical statements are
unchanged. See the two Chung axioms in Part IV for the crash-free packaging.
-/

import Mathlib

open Nat SimpleGraph

namespace Erdos666

/-
## Part I: Hypercube Graph
-/

/--
**n-dimensional hypercube Qₙ:**
Vertices are binary strings of length n (equivalently, elements of `Fin 2ⁿ`).
Two vertices are adjacent iff they differ in exactly one coordinate, i.e. their
bitwise XOR has exactly one set bit — equivalently, is a power of two.
-/
def Hypercube (n : ℕ) : SimpleGraph (Fin (2^n)) where
  Adj x y := ∃ i : ℕ, x.val ^^^ y.val = 2 ^ i
  symm := by
    rintro x y ⟨i, h⟩
    exact ⟨i, by rw [Nat.xor_comm]; exact h⟩
  loopless := by
    rintro x ⟨i, h⟩
    rw [Nat.xor_self] at h
    exact pow_ne_zero i (by norm_num) h.symm

/--
**Number of vertices in Qₙ:**
|V(Qₙ)| = 2ⁿ
-/
def hypercubeVertices (n : ℕ) : ℕ := 2^n

/--
**Number of edges in Qₙ:**
|E(Qₙ)| = n · 2ⁿ⁻¹
-/
def hypercubeEdges (n : ℕ) : ℕ := n * 2^(n-1)

/-- **`Qₙ` always has vertices:** `|V(Qₙ)| = 2ⁿ > 0`. -/
theorem hypercubeVertices_pos (n : ℕ) : 0 < hypercubeVertices n :=
  pow_pos (by norm_num) n

/-- **Handshake identity for the hypercube:** `2·|E(Qₙ)| = n·|V(Qₙ)|`.  Every one of
    the `2ⁿ` vertices of `Qₙ` has degree exactly `n` (one neighbour per coordinate
    flip), so the degree sum is `n·2ⁿ`, which by the handshake lemma is twice the edge
    count.  Concretely `2·(n·2ⁿ⁻¹) = n·2ⁿ`.  This ties the file's two basic counts
    `hypercubeVertices` and `hypercubeEdges` together. -/
theorem two_mul_hypercubeEdges (n : ℕ) :
    2 * hypercubeEdges n = n * hypercubeVertices n := by
  cases n with
  | zero => simp [hypercubeEdges, hypercubeVertices]
  | succ m =>
    unfold hypercubeEdges hypercubeVertices
    rw [Nat.succ_sub_one, pow_succ]
    ring

/-- **Vertices double with each dimension:** `|V(Q_{n+1})| = 2·|V(Qₙ)|`.  Passing
from `Qₙ` to `Q_{n+1}` glues two disjoint copies of `Qₙ` (the `xₙ = 0` and `xₙ = 1`
half-cubes), so the vertex count doubles.  Concretely `2^{n+1} = 2·2ⁿ`. -/
theorem hypercubeVertices_succ (n : ℕ) :
    hypercubeVertices (n + 1) = 2 * hypercubeVertices n := by
  unfold hypercubeVertices
  rw [pow_succ, Nat.mul_comm]

/-- **Recursive edge count of the hypercube:** `|E(Q_{n+1})| = 2·|E(Qₙ)| + |V(Qₙ)|`.
This encodes the fundamental product structure `Q_{n+1} = Qₙ □ K₂`: the edges of
`Q_{n+1}` are the edges *inside* the two copies of `Qₙ` (that is `2·|E(Qₙ)|`) together
with the perfect matching joining corresponding vertices across the two copies (one
edge per vertex of `Qₙ`, i.e. `|V(Qₙ)|` further edges).  Concretely
`(n+1)·2ⁿ = 2·(n·2ⁿ⁻¹) + 2ⁿ`.  Combined with `two_mul_hypercubeEdges` this pins the
edge count `n·2ⁿ⁻¹` by its Cartesian-product recurrence rather than the closed form. -/
theorem hypercubeEdges_succ (n : ℕ) :
    hypercubeEdges (n + 1) = 2 * hypercubeEdges n + hypercubeVertices n := by
  cases n with
  | zero => simp [hypercubeEdges, hypercubeVertices]
  | succ m =>
    unfold hypercubeEdges hypercubeVertices
    rw [Nat.succ_sub_one, Nat.succ_sub_one, pow_succ]
    ring

/-
**Degree in Qₙ:** every vertex has degree n.
-/

/-
## Part II: Cycles in Graphs
-/

/--
**Cycle C_k in a graph:**
A sequence of k distinct vertices forming a cycle.

Marked `@[irreducible]` (see the header note): under Mathlib v4.26 the
elaborator crashes with a native stack overflow whenever the unfolding of this
definition (which exposes `G.Adj` over `Fin k → V`) is forced to co-elaborate
with an edge-set cardinality of the same graph.
-/
@[irreducible] def HasCycle (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (cycle : Fin k → V),
    Function.Injective cycle ∧
    (∀ i : Fin k, G.Adj (cycle i)
      (cycle ⟨(i.val + 1) % k, Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) i.2)⟩)) ∧
    k ≥ 3

/--
**C₄ (4-cycle, square):**
-/
def HasC4 (G : SimpleGraph V) : Prop := HasCycle G 4

/--
**C₆ (6-cycle, hexagon):** (kept `@[irreducible]`, see `HasCycle`.)
-/
@[irreducible] def HasC6 (G : SimpleGraph V) : Prop := HasCycle G 6

/--
**C₂ₖ (even cycle of length 2k):**
-/
def HasC2k (G : SimpleGraph V) (k : ℕ) : Prop := HasCycle G (2*k)

/-
## Part III: Subgraphs and Edge Density
-/

/--
**Subgraph with edge count:**
A subgraph H of G with at least m edges.
-/
structure DenseSubgraph (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (m : ℕ) where
  graph : SimpleGraph V
  isSubgraph : ∀ x y, graph.Adj x y → G.Adj x y
  edgeCount : Nat.card graph.edgeSet ≥ m

/--
**ε-dense subgraph of Qₙ:**
A subgraph with at least ε · n · 2ⁿ⁻¹ edges.

We count edges with `Nat.card H.edgeSet`, which is well-defined for any graph on
the finite vertex type `Fin (2^n)` without carrying a `DecidableRel H.Adj`
witness. Marked `@[irreducible]` (see the header note) so its `Nat.card H.edgeSet`
body is never forced to unfold alongside `HasC6`.
-/
@[irreducible] def EpsilonDenseSubgraph (n : ℕ) (ε : ℝ) (H : SimpleGraph (Fin (2^n))) : Prop :=
  (Nat.card H.edgeSet : ℝ) ≥ ε * hypercubeEdges n

/-
## Part IV: Erdős's Conjecture (DISPROVED)
-/

/--
**"Every ε-dense subgraph of Qₙ forces C₆", for a fixed n and ε.**
The folded body `∀ H, EpsilonDenseSubgraph n ε H → HasC6 H`.
-/
def DenseForcesC6 (n : ℕ) (ε : ℝ) : Prop :=
  ∀ H : SimpleGraph (Fin (2^n)), EpsilonDenseSubgraph n ε H → HasC6 H

/--
**The conjecture at a fixed density ε:**
For some threshold N, every ε-dense subgraph of Qₙ with n ≥ N contains C₆.
-/
def ConjectureAt (ε : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, n ≥ N → DenseForcesC6 n ε

/--
**Erdős's original conjecture:**
For every ε > 0, if n is sufficiently large, every ε-dense subgraph of Qₙ
contains C₆.
-/
def ErdosConjecture : Prop :=
  ∀ ε : ℝ, ε > 0 → ConjectureAt ε

/-!
### Monotonicity of the conjecture in the density `ε`

`ConjectureAt` is monotone in `ε`: strengthening the density hypothesis (larger
`ε`) can only make the conjecture easier to satisfy.  Dually, a single
counterexample at one density refutes the conjecture at every *smaller* density.
These three lemmas are pure bookkeeping — no axioms — and are used below in two
ways: to recover Chung's `1/4` refutation as a corollary of Conder's sharper
`1/3` one (so the file needs a single deep axiom, not two), and to spread each
refutation across an entire interval of densities (Part IV.5).
-/

unseal EpsilonDenseSubgraph in
/-- **`ε`-density is antitone in `ε`.**  A subgraph that is `ε`-dense is also
`ε'`-dense for every `ε' ≤ ε`, since the required edge count `ε' · Eₙ ≤ ε · Eₙ`
only decreases (the hypercube edge count `Eₙ = n·2ⁿ⁻¹` is nonnegative). -/
theorem epsilonDense_antitone {n : ℕ} {ε ε' : ℝ} (hle : ε' ≤ ε)
    {H : SimpleGraph (Fin (2^n))} (hH : EpsilonDenseSubgraph n ε H) :
    EpsilonDenseSubgraph n ε' H :=
  le_trans (mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _)) hH

/-- **`DenseForcesC6` is monotone in `ε`.**  If every `ε'`-dense subgraph is forced
to contain `C₆`, then so is every `ε`-dense subgraph for `ε ≥ ε'` (the `ε`-dense
subgraphs form a subclass of the `ε'`-dense ones). -/
theorem denseForcesC6_mono {n : ℕ} {ε ε' : ℝ} (hle : ε' ≤ ε)
    (h : DenseForcesC6 n ε') : DenseForcesC6 n ε :=
  fun H hH => h H (epsilonDense_antitone hle hH)

/-- **`ConjectureAt` is monotone in `ε`.**  The same threshold `N` witnesses the
conjecture at the larger density `ε` once it holds at `ε' ≤ ε`. -/
theorem conjectureAt_mono {ε ε' : ℝ} (hle : ε' ≤ ε)
    (h : ConjectureAt ε') : ConjectureAt ε :=
  let ⟨N, hN⟩ := h
  ⟨N, fun n hn => denseForcesC6_mono hle (hN n hn)⟩

/--
**Conder's theorem (1993), refutation form — the sharpest known counterexample.**
For the density `ε = 1/3` there is *no* threshold `N` beyond which every
`(1/3)`-dense subgraph of `Qₙ` contains a `C₆`.

Conder (1993) refined Chung's four-part construction to a proper `3`-edge-colouring
of `Qₙ` (for `n ≥ 3`) in which no colour class contains a `C₄` or a `C₆`.  By
pigeonhole one of the three colour classes carries `≥ 1/3` of the `n·2ⁿ⁻¹` edges
while remaining `C₆`-free, so for *every* candidate threshold `N` (taking
`n = max N 3`) there is a `(1/3)`-dense `C₆`-free subgraph — hence
`ConjectureAt (1/3)` fails.  The explicit `3`-colouring is combinatorial and not
available in Mathlib, so we axiomatize this consequence directly.

This is stated in the negation form `¬ ConjectureAt (1/3)` (rather than the
mathematically-equivalent `∃ H, dense H ∧ ¬ HasC6 H`) because the latter's type
triggers a Mathlib v4.26 elaborator stack overflow; see the header note.

This is the **single** deep combinatorial input of the file: Chung's earlier `1/4`
refutation (`chung_no_threshold`) is recovered from it by monotonicity, so we
axiomatize only the strongest published result rather than each density separately.
-/
axiom conder_no_threshold : ¬ ConjectureAt (1/3)

/--
**Chung's theorem (1992), refutation form — now a corollary of Conder's.**
`ConjectureAt (1/4)` fails.  Chung's original `4`-partition of `Qₙ` yields a
`(1/4)`-dense `C₆`-free subgraph directly; here we obtain the same conclusion for
free from the sharper `conder_no_threshold` via `conjectureAt_mono` (since
`1/4 ≤ 1/3`).  Keeping this as a named theorem preserves every downstream use of
`chung_no_threshold` while letting the file rest on Conder's single axiom.
-/
theorem chung_no_threshold : ¬ ConjectureAt (1/4) :=
  fun h => conder_no_threshold (conjectureAt_mono (by norm_num : (1 : ℝ) / 4 ≤ 1 / 3) h)

/-
**C₆-free subgraphs of `Qₙ` exist (existence form).**
For every `n ≥ 3` the hypercube `Qₙ` has a subgraph containing no `C₆`.

Chung's `1992` edge-partition supplies such a subgraph carrying `≥ 1/4` of
all edges — but *that* density content is precisely what the axiom
`chung_no_threshold` captures. The bare existence statement here carries
**no edge-count data**, so it is provable outright: the empty subgraph `⊥`
(no edges) contains no cycle of any length, hence no `C₆`. We therefore
prove it rather than assume it — the deep combinatorial content stays
isolated in the single density axiom `chung_no_threshold`.

(The empty-graph witness is the honest minimal certificate for this weak
statement; the corollaries in Parts V–VII only invoke the existence form.)
-/
unseal HasC6 HasCycle in
/-- **C₆-free subgraphs of `Qₙ` exist**: witnessed by the empty subgraph `⊥`,
which contains no cycle. The density-carrying content lives in the axiom
`chung_no_threshold`. -/
theorem chung_c6free : ∀ n : ℕ, n ≥ 3 → ∃ H : SimpleGraph (Fin (2^n)), ¬ HasC6 H := by
  intro n _
  refine ⟨⊥, ?_⟩
  rintro ⟨cycle, -, hadj, -⟩
  simpa using hadj 0

/--
**The conjecture is FALSE:**
Instantiating Erdős's conjecture at `ε = 1/4` would supply a threshold `N` making
`ConjectureAt (1/4)` hold, which `chung_no_threshold` forbids.
-/
theorem erdos_conjecture_false : ¬ErdosConjecture := fun hConj =>
  chung_no_threshold (hConj (1/4) (by norm_num))

/-- **Erdős's conjecture is determined entirely by arbitrarily small densities.**
For *any* fixed positive cutoff `c`, the full conjecture `ErdosConjecture` (which
quantifies over every `ε > 0`) is equivalent to its restriction to the sliver of
small densities `0 < ε ≤ c`.  The forward direction just forgets the extra bound
`ε ≤ c`; the reverse uses monotonicity (`conjectureAt_mono`): any density `ε > c` is
handled by the cutoff instance `ConjectureAt c` pushed up to `ε`.  So the conjecture's
truth value never depends on its large-density behaviour — it is decided at the bottom
of the density scale.  In particular, coupled with `conder_no_threshold_le` (failure
throughout `(0, 1/3]`), this re-exhibits `erdos_conjecture_false` from the small-density
end.  No new axioms — pure monotonicity. -/
theorem erdosConjecture_iff_small {c : ℝ} (hc : 0 < c) :
    ErdosConjecture ↔ ∀ ε : ℝ, 0 < ε → ε ≤ c → ConjectureAt ε := by
  constructor
  · intro h ε hε _
    exact h ε hε
  · intro h ε hε
    rcases le_total ε c with hle | hge
    · exact h ε hε hle
    · exact conjectureAt_mono hge (h c hc le_rfl)

/-!
### Part IV.5: Each refutation holds on a whole interval of densities

A single counterexample at some density refutes the conjecture for *every* smaller
density: a graph that is `ε₀`-dense and `C₆`-free is automatically `ε`-dense for any
`ε ≤ ε₀`, so no threshold can work at any such `ε` (this is the monotonicity of
`ConjectureAt` proved above).  Applying it to Conder's `1/3` axiom — and to the
`1/4` corollary — spreads each refutation across an interval.  The upshot: Erdős's
conjecture fails not at isolated bad densities but robustly across the entire range
`(0, 1/3]`, with no new axioms beyond `conder_no_threshold`.
-/

/-- **Chung's refutation extends to every `ε ≤ 1/4`.**  Were the conjecture to hold
at some `ε ≤ 1/4`, monotonicity would push it up to `ε = 1/4`, contradicting
`chung_no_threshold`.  So `ConjectureAt ε` fails for the whole interval `ε ≤ 1/4` —
in particular for every positive density `0 < ε ≤ 1/4`. -/
theorem chung_no_threshold_le {ε : ℝ} (hε : ε ≤ 1/4) : ¬ ConjectureAt ε :=
  fun h => chung_no_threshold (conjectureAt_mono hε h)

/-- **Conder's refutation extends to every `ε ≤ 1/3`** — the sharpest interval.
Were the conjecture to hold at some `ε ≤ 1/3`, monotonicity would push it up to
`ε = 1/3`, contradicting `conder_no_threshold`.  So `ConjectureAt ε` fails for the
whole interval `ε ≤ 1/3`, strictly extending the `ε ≤ 1/4` range of
`chung_no_threshold_le`.  In particular Erdős's conjecture fails for every positive
density `0 < ε ≤ 1/3`. -/
theorem conder_no_threshold_le {ε : ℝ} (hε : ε ≤ 1/3) : ¬ ConjectureAt ε :=
  fun h => conder_no_threshold (conjectureAt_mono hε h)

/-- **Necessary condition: any density at which the conjecture holds exceeds `1/3`.**
The contrapositive of Conder's interval refutation `conder_no_threshold_le`.  Where the
previous lemmas assert that `ConjectureAt` *fails* at every `ε ≤ 1/3`, this records the
dual, sharp lower bound: if `ConjectureAt ε` *does* hold for some density `ε`, then
necessarily `1/3 < ε`.  Equivalently, the critical density below which no threshold `N`
can force `C₆` is at least `1/3` — Conder's construction is not merely one bad density but
a genuine lower barrier on the "good" side.  (Whether any positive `ε > 1/3` actually
works is the remaining quantitative question; here we only pin the barrier from below.) -/
theorem conjectureAt_imp_gt_third {ε : ℝ} (h : ConjectureAt ε) : 1/3 < ε :=
  not_le.mp (fun hle => conder_no_threshold_le hle h)

/-- **Conder's counterexamples recur for arbitrarily large hypercubes.**
The axiom `conder_no_threshold` is stated in the compact negation form `¬ ConjectureAt (1/3)`
(no threshold `N` works), which conceals its positive content.  Unfolding the two nested
quantifiers turns "`∃ N` fails" into the honest statement below: for *every* candidate
threshold `N` there is some `n ≥ N` at which `(1/3)`-density does not force `C₆` — i.e. a
`(1/3)`-dense `C₆`-free subgraph of `Qₙ`.  So Conder's construction is not a small-`n`
artifact: the counterexamples occur for arbitrarily large `n`.  Pure logic (De Morgan on the
`∃N ∀n≥N` shape), no new axioms. -/
theorem conder_counterexamples_unbounded :
    ∀ N : ℕ, ∃ n, N ≤ n ∧ ¬ DenseForcesC6 n (1/3) := by
  by_contra h
  push_neg at h
  obtain ⟨N, hN⟩ := h
  exact conder_no_threshold ⟨N, hN⟩

/-- **The unbounded counterexamples persist across the whole interval `ε ≤ 1/3`.**
The interval-level strengthening of `conder_counterexamples_unbounded`, standing to it
exactly as `conder_no_threshold_le` stands to `conder_no_threshold`.  For *every* density
`ε ≤ 1/3` and *every* candidate threshold `N`, some `n ≥ N` fails to force `C₆` at density
`ε`: a `C₆`-free subgraph that is already `(1/3)`-dense is a fortiori `ε`-dense, so the
Conder counterexamples witnessing `¬ DenseForcesC6 n (1/3)` witness `¬ DenseForcesC6 n ε`
too (contrapositive of `denseForcesC6_mono`).  No new axioms — pure monotonicity applied to
the single `conder_no_threshold`. -/
theorem conder_counterexamples_unbounded_le {ε : ℝ} (hε : ε ≤ 1/3) :
    ∀ N : ℕ, ∃ n, N ≤ n ∧ ¬ DenseForcesC6 n ε := by
  intro N
  obtain ⟨n, hn, hnd⟩ := conder_counterexamples_unbounded N
  exact ⟨n, hn, fun h => hnd (denseForcesC6_mono hε h)⟩

/-
## Part V: Chung's Result (1992)

The single deep combinatorial axiom of the file is `conder_no_threshold`
(Conder's sharper `1/3` result); Chung's `1/4` refutation `chung_no_threshold` is
derived from it in Part IV by monotonicity, and `chung_c6free` is proved outright
from the empty subgraph. Here we record the immediate ε = 1/4 existence
corollary.
-/

/--
**Corollary: ε = 1/4 counterexample:**
Chung's construction supplies a `C₆`-free subgraph of `Qₙ` (one of the four parts
of the edge-partition, each carrying ~1/4 of all edges).
-/
theorem chung_counterexample (n : ℕ) (hn : n ≥ 3) :
    ∃ H : SimpleGraph (Fin (2^n)), ¬HasC6 H :=
  chung_c6free n hn

/-
## Part VI: Brouwer-Dejter-Thomassen (1993)

**BDT's result (1993):** Independent of Chung, proved that Qₙ can be 4-colored
with no monochromatic C₄ or C₆.
-/

/-
## Part VII: Conder's Improvement (1993)

**Conder's 3-coloring theorem (1993):** For n ≥ 3, the edges of Qₙ can be
3-colored with no monochromatic C₄ or C₆. This improves Chung/BDT from 4
colors to 3, pushing the refuting density from `1/4` up to `1/3`.

The density content of Conder's improvement is exactly `conder_no_threshold`
(`¬ ConjectureAt (1/3)`) and its interval form `conder_no_threshold_le`, both
established in Part IV.  We record here only the honest *existence* corollary that
Conder's construction supplies a `C₆`-free subgraph of `Qₙ` — the extra density
`1/3 > 1/4` cannot be attached to the existence statement itself without the
Mathlib v4.26 elaborator crash (see the header note), so it lives in the axiom.

(The previous formulation of this corollary attached a vacuous `True` conjunct in
place of the `1/3` density claim; that placeholder is removed — the real `1/3`
content is now the axiom `conder_no_threshold` and the theorem
`conder_no_threshold_le`.)
-/

/--
**Conder's ε = 1/3 counterexample (existence form).**
Conder's `3`-colouring supplies, for every `n ≥ 3`, a `C₆`-free subgraph of `Qₙ`
(one of the three colour classes, each carrying `~1/3` of all edges).  The bare
existence statement carries no edge-count data, so it follows from the empty-graph
witness already used for Chung; the `1/3` density content is the separate axiom
`conder_no_threshold`. -/
theorem conder_counterexample (n : ℕ) (hn : n ≥ 3) :
    ∃ H : SimpleGraph (Fin (2^n)), ¬HasC6 H :=
  chung_c6free n hn

/-
## Part VIII: Erdős's Generalization
-/

/--
**Erdős's generalized conjecture:**
For every k ≥ 3, there exist c > 0 and aₖ < 1 such that every subgraph
with ≥ c · n^{aₖ} · 2ⁿ edges contains C_{2k}, where aₖ → 0 as k → ∞.

**Faithfulness note.**  The existential witness `c` must be *positive*, so the
constraint `0 < c` is a **conjunct** of the witness, not an antecedent.  An earlier
form wrote `∃ c : ℝ, c > 0 → …`, which is vacuously true (take `c = 0`: the
antecedent `0 > 0` is false, so the implication holds with no content), and hence
did **not** encode the open conjecture at all.  It is corrected here to
`∃ c : ℝ, 0 < c ∧ …` so that a proof genuinely has to exhibit a positive constant.
The generalization itself remains open. -/
def GeneralizedConjecture : Prop :=
  ∀ k : ℕ, k ≥ 3 →
    ∃ c : ℝ, 0 < c ∧ ∃ aₖ : ℝ, 0 < aₖ ∧ aₖ < 1 ∧
      ∀ n : ℕ, n ≥ 10 →
        ∀ H : SimpleGraph (Fin (2^n)),
          (Nat.card H.edgeSet : ℝ) ≥ c * (n : ℝ)^aₖ * 2^n →
          HasC2k H k

unseal HasC6 in
/-- **The `k = 3` case of the generalized conjecture is exactly the C₆ problem.**
`HasC2k H 3` (a `2·3 = 6`-cycle) coincides with `HasC6 H`, so the generalized
`C_{2k}` conjecture specialises at `k = 3` to Erdős's original — and refuted — C₆
question.  (Proved by reducing the length index `2·3` to `6`; it does **not** unfold
`HasCycle` itself, whose body is kept `irreducible` to avoid the documented
elaborator stack overflow.) -/
theorem hasC2k_three_iff_hasC6 {V : Type*} (H : SimpleGraph V) :
    HasC2k H 3 ↔ HasC6 H := by
  show HasCycle H (2 * 3) ↔ HasCycle H 6
  rfl

/-- **The generalized conjecture at `k = 3` is a `C₆`-forcing statement.**
If the generalized `C_{2k}` conjecture holds, its `k = 3` instance forces `C₆`
(not merely the syntactic `HasC2k H 3`): there is a positive constant `c` and an
exponent `a ∈ (0,1)` such that every subgraph of `Qₙ` (`n ≥ 10`) with at least
`c·n^a·2ⁿ` edges contains a `C₆`.  Obtained by specialising `GeneralizedConjecture`
at `k = 3` and rewriting its conclusion `HasC2k H 3` to `HasC6 H` via
`hasC2k_three_iff_hasC6`.  This pins down exactly how the generalization meets the
original problem: same cycle length, but a *sparser* `n^a·2ⁿ` density threshold than
the `ε·n·2ⁿ⁻¹` of `ConjectureAt`, which is why the `C₆` refutation
(`conder_no_threshold`) does **not** transfer to it.  No new axioms. -/
theorem generalizedConjecture_three_forces_c6 (h : GeneralizedConjecture) :
    ∃ c : ℝ, 0 < c ∧ ∃ a : ℝ, 0 < a ∧ a < 1 ∧
      ∀ n : ℕ, n ≥ 10 →
        ∀ H : SimpleGraph (Fin (2^n)),
          (Nat.card H.edgeSet : ℝ) ≥ c * (n : ℝ)^a * 2^n →
          HasC6 H := by
  obtain ⟨c, hc, a, ha0, ha1, hforce⟩ := h 3 (by norm_num)
  exact ⟨c, hc, a, ha0, ha1,
    fun n hn H hden => (hasC2k_three_iff_hasC6 H).mp (hforce n hn H hden)⟩

/-
**This generalization remains open.**
-/

/-
## Part IX: Related Results

**Turán-type result for C₄ in Qₙ:** the maximum number of edges in a C₄-free
subgraph of Qₙ is Θ(n^{1/2} · 2ⁿ).
-/

/-
## Part X: Summary
-/

/--
**Summary of Erdős Problem #666:**

**Question:**
Does every ε-dense subgraph of Qₙ contain C₆?

**Answer:** NO

**Results:**
- Chung (1992): 4-partition into C₆-free subgraphs (ε = 1/4 counterexample)
- Brouwer-Dejter-Thomassen (1993): Independent 4-coloring result
- Conder (1993): 3-coloring (ε = 1/3 counterexample)

**Generalized conjecture:** For C_{2k}, what density threshold forces the cycle?
This remains open.
-/
theorem erdos_666_summary :
    -- The conjecture is false
    ¬ErdosConjecture ∧
    -- Chung's construction: C₆-free graphs on 2ⁿ vertices exist
    (∀ n : ℕ, n ≥ 3 → ∃ H : SimpleGraph (Fin (2^n)), ¬HasC6 H) := by
  constructor
  · exact erdos_conjecture_false
  · intro n hn
    obtain ⟨H, hH⟩ := chung_counterexample n hn
    exact ⟨H, hH⟩

end Erdos666
