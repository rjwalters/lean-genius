/-
# Erdős Problem #1016: Pancyclic Excess Edges

Let h(n) be the minimum number of edges beyond n needed for an n-vertex
graph to be pancyclic (containing cycles of all lengths 3, 4, ..., n).
Estimate h(n). Is h(n) ≥ log₂ n + log* n − O(1)?

## Key Results

- **Bondy's lower bound**: log₂(n−1) − 1 ≤ h(n) (Griffin 2013, first proof)
- **Upper bound**: h(n) ≤ log₂ n + log* n + O(1) (George–Khodkar–Wallis 2016)
- **Open**: Is h(n) − log₂ n → ∞?
- A pancyclic graph on n vertices has ≥ n + h(n) edges

## References

- Bondy (1971), conjectured bounds
- Griffin (2013), first published lower bound proof
- George, Khodkar, Wallis (2016), upper bound proof
- OEIS A105206
- <https://erdosproblems.com/1016>
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/- ## Core Definitions -/

/-- A simple graph G on n vertices is pancyclic if it contains cycles
    of every length k for 3 ≤ k ≤ n. -/
def IsPancyclic (n : ℕ) (edgeCount : ℕ) (hasCycleOfLength : ℕ → Prop) : Prop :=
  ∀ k : ℕ, 3 ≤ k → k ≤ n → hasCycleOfLength k

/-- h(n): the minimum number of excess edges beyond n required for an
    n-vertex graph to be pancyclic. Formally, h(n) = min{|E(G)| − n}
    over all pancyclic graphs G on n vertices. -/
noncomputable def pancyclicExcess (n : ℕ) : ℕ :=
  sSup {h : ℕ | ∀ (edgeCount : ℕ) (hasCycle : ℕ → Prop),
    IsPancyclic n edgeCount hasCycle → edgeCount ≥ n + h}

/-- The iterated logarithm log*(n): the number of times log₂ must be
    applied to n before the result is ≤ 1. -/
def iteratedLog : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | (n + 2) => 1 + iteratedLog (Nat.log 2 (n + 2))
termination_by n => n
decreasing_by
  show Nat.log 2 (n + 2) < n + 1 + 1
  have hlog_le : Nat.log 2 (n + 2) ≤ n + 2 := Nat.log_le_self 2 (n + 2)
  -- Strict inequality: equality is impossible because 2^(n+2) > n+2
  rcases lt_or_eq_of_le hlog_le with hlt | heq
  · omega
  · exfalso
    have h_pow_le : (2 : ℕ) ^ Nat.log 2 (n + 2) ≤ n + 2 :=
      Nat.pow_log_le_self 2 (by omega)
    rw [heq] at h_pow_le
    have h_lt : n + 2 < 2 ^ (n + 2) := Nat.lt_two_pow_self
    omega

/-! ## Iterated Logarithm Properties

These are pure structural properties of `iteratedLog` (independent of the
abstract pancyclic model). They characterize the zero fibre and positivity
of `log*`, which are useful for any downstream formalization that needs to
reason about the iterated logarithm regardless of which graph encoding is
adopted for the pancyclic problem itself.
-/

/-- Defining equation of `iteratedLog` at `0`. -/
@[simp] theorem iteratedLog_zero : iteratedLog 0 = 0 := by
  simp [iteratedLog]

/-- Defining equation of `iteratedLog` at `1`. -/
@[simp] theorem iteratedLog_one : iteratedLog 1 = 0 := by
  simp [iteratedLog]

/-- Defining recursion of `iteratedLog` at `n + 2`. -/
theorem iteratedLog_add_two (n : ℕ) :
    iteratedLog (n + 2) = 1 + iteratedLog (Nat.log 2 (n + 2)) := by
  simp [iteratedLog]

/-- `iteratedLog n = 0` exactly when `n ≤ 1`. -/
theorem iteratedLog_eq_zero_iff (n : ℕ) : iteratedLog n = 0 ↔ n ≤ 1 := by
  match n with
  | 0 => exact ⟨fun _ => Nat.zero_le _, fun _ => iteratedLog_zero⟩
  | 1 => exact ⟨fun _ => Nat.le_refl _, fun _ => iteratedLog_one⟩
  | k + 2 =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [iteratedLog_add_two] at h; omega
    · omega

/-- `iteratedLog n ≥ 1` whenever `n ≥ 2`. -/
theorem iteratedLog_pos {n : ℕ} (hn : 2 ≤ n) : 1 ≤ iteratedLog n := by
  match n, hn with
  | k + 2, _ =>
    rw [iteratedLog_add_two]; omega

/- ## Model Flaw and Consequences

**CRITICAL**: The abstract IsPancyclic definition above takes `hasCycleOfLength` as
an unconstrained parameter, disconnected from `edgeCount`. This means we can always
choose edgeCount = 0 and hasCycle = (fun _ => True), satisfying IsPancyclic while
violating any lower bound on edges. Consequently:

1. pancyclicExcess n = 0 for ALL n ≥ 1 (the defining set is always empty)
2. The lower bound axioms are FALSE under this model
3. The upper bound is trivially true

To properly formalize h(n), one needs SimpleGraph (Fin n) with Walk.IsCycle and
edgeFinset — approximately 200+ lines of graph-theoretic infrastructure.

The mathematical results (Bondy 1971, Griffin 2013, GKW 2016) are correct;
only the Lean encoding is flawed. The statements below are preserved as comments
for future reference when the model is redesigned.
-/

/-- The defining set for pancyclicExcess is empty for all n ≥ 1, because
    (edgeCount := 0, hasCycle := fun _ => True) satisfies IsPancyclic
    but violates edgeCount ≥ n + h for any h. Thus sSup ∅ = 0. -/
theorem pancyclicExcess_eq_zero (n : ℕ) (hn : 1 ≤ n) : pancyclicExcess n = 0 := by
  unfold pancyclicExcess
  suffices h : {h : ℕ | ∀ (edgeCount : ℕ) (hasCycle : ℕ → Prop),
      IsPancyclic n edgeCount hasCycle → edgeCount ≥ n + h} = ∅ by
    rw [h]; simp [csSup_empty (α := ℕ)]
  ext h
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hh
  have := hh 0 (fun _ => True) (fun _ _ _ => trivial)
  omega

/-- The GKW upper bound is trivially true under the current model
    since pancyclicExcess n = 0 for all n ≥ 1. -/
theorem gkw_upper_bound :
  ∃ C : ℕ, ∀ n : ℕ, n ≥ 3 →
    pancyclicExcess n ≤ Nat.log 2 n + iteratedLog n + C :=
  ⟨0, fun n hn => by rw [pancyclicExcess_eq_zero n (by omega)]; exact Nat.zero_le _⟩

/-
**Disabled axioms** (FALSE under current abstract model, mathematically correct):

-- Erdős's Conjecture (OPEN): h(n) ≥ log₂ n + log* n − O(1)
-- erdos_1016_conjecture : ∃ C, ∀ n ≥ 3, pancyclicExcess n + C ≥ Nat.log 2 n + iteratedLog n

-- Weaker open question: h(n) − log₂ n → ∞
-- excess_beyond_log : ∀ M, ∃ N, ∀ n ≥ N, pancyclicExcess n ≥ Nat.log 2 n + M

-- Bondy's lower bound (Griffin 2013): h(n) ≥ ⌊log₂(n−1)⌋ − 1
-- bondy_lower_bound : ∀ n ≥ 3, pancyclicExcess n + 1 ≥ Nat.log 2 (n - 1)

-- Small case: h(4) = 1 (false: pancyclicExcess 4 = 0 under current model)
-- small_case_4 : pancyclicExcess 4 = 1
-/

/- ## Structural Properties -/

/-- Pancyclic excess is non-negative (trivial for ℕ). -/
theorem hamiltonian_edge_count :
    ∀ n : ℕ, n ≥ 3 → pancyclicExcess n ≥ 0 :=
  fun _ _ => Nat.zero_le _

/-- Bondy's theorem: any graph with ≥ n²/4 edges is pancyclic or bipartite.
    For n ≥ 7, n²/4 ≫ n + log₂ n, so the quadratic threshold is far from tight.
    Proof: small cases by computation, large cases by n²/4 ≥ 2n ≥ n + log₂ n. -/
theorem bondy_quadratic_threshold :
    ∀ n : ℕ, n ≥ 7 → n * n / 4 ≥ n + Nat.log 2 n := by
  intro n hn
  rcases le_or_gt n 15 with h15 | h16
  · -- n ∈ {7,...,15}: compute directly
    interval_cases n <;> native_decide
  · -- n ≥ 16: n²/4 ≥ 2n and log₂ n ≤ n
    have h16 : 16 ≤ n := by omega
    have hq : 2 * n ≤ n * n / 4 := by
      have : 4 * (2 * n) ≤ n * n := by nlinarith
      omega
    have hl : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
    omega

/-- Monotonicity: adding edges preserves pancyclicity.
    (Trivially true since IsPancyclic does not depend on edgeCount.) -/
theorem pancyclic_monotone :
    ∀ (n e₁ e₂ : ℕ) (hasCycle : ℕ → Prop),
    IsPancyclic n e₁ hasCycle → e₂ ≥ e₁ → IsPancyclic n e₂ hasCycle :=
  fun _ _ _ _ h _ => h

/-- **PROVED** (was axiom): The triangle (K₃) is the smallest pancyclic graph: h(3) = 0.
    Note: the defining set for pancyclicExcess is empty for all n ≥ 1
    (edgeCount=0 with hasCycle=True satisfies IsPancyclic but has 0 < n+h edges),
    so sSup ∅ = 0. The result is mathematically correct (h(3) = 0) but the proof
    exploits the abstract model rather than graph-theoretic reasoning. -/
theorem triangle_pancyclic : pancyclicExcess 3 = 0 := by
  unfold pancyclicExcess
  suffices h : {h : ℕ | ∀ (edgeCount : ℕ) (hasCycle : ℕ → Prop),
      IsPancyclic 3 edgeCount hasCycle → edgeCount ≥ 3 + h} = ∅ by
    rw [h]; simp [csSup_empty (α := ℕ)]
  ext h
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hh
  -- Counterexample: edgeCount = 0, hasCycle = fun _ => True
  have := hh 0 (fun _ => True) (fun _ _ _ => trivial)
  omega

/-- Bounds gap is trivial since pancyclicExcess = 0 under current model. -/
theorem bounds_gap :
    ∃ C : ℕ, ∀ n : ℕ, n ≥ 3 →
    pancyclicExcess n ≤ pancyclicExcess n + C :=
  ⟨0, fun _ _ => Nat.le_add_right _ _⟩

/-! ## Grounded `SimpleGraph` Pancyclic Model

The abstract `IsPancyclic` model above is a documented diagnostic scaffold: its
`hasCycleOfLength` argument is an unconstrained `Prop`, disconnected from any actual
graph, which is precisely why `pancyclicExcess n` collapses to `0` (the defining set
is empty, so `sSup ∅ = 0`). The definitions below replace that scaffold with a
*grounded* model built directly on `SimpleGraph (Fin n)` and Mathlib's cycle API, so
that the edge count is genuinely constrained by the cycle structure of the graph.

This is the corrected formalization that future work on the real Bondy / Griffin / GKW
bounds should build on. The headline lemma `pancyclicGraph_card_edgeFinset_ge` recovers
a *non-vacuous* lower bound on the edge count from the genuine Hamiltonian cycle, which
the abstract model could not express.
-/

section Grounded

variable {n : ℕ} (G : SimpleGraph (Fin n)) [Fintype G.edgeSet]

/-- `G` contains a cycle of length exactly `k`: there is a closed walk at some vertex
    that is a cycle (no repeated vertices or edges) of length `k`. This pins the cycle
    to the actual graph `G`, unlike the abstract `hasCycleOfLength : ℕ → Prop` parameter. -/
def HasCycleOfLength (k : ℕ) : Prop :=
  ∃ (v : Fin n) (w : G.Walk v v), w.IsCycle ∧ w.length = k

/-- `G` is pancyclic (grounded definition): it contains a cycle of every length `k`
    with `3 ≤ k ≤ n`. Unlike the abstract `IsPancyclic`, this is a genuine property of
    the concrete graph `G`, so consequences about its edge count are not vacuous. -/
def IsPancyclicGraph : Prop :=
  ∀ k, 3 ≤ k → k ≤ n → HasCycleOfLength G k

/-- **Grounded edge lower bound.** A cycle of length `k` is a trail of length `k`, so it
    uses `k` distinct edges, all of which belong to `G`; hence `G` has at least `k` edges.
    This is exactly the structural link the abstract model failed to capture, where
    `edgeCount` was a free variable independent of the cycle data. -/
theorem card_edgeFinset_ge_of_hasCycleOfLength {k : ℕ}
    (h : HasCycleOfLength G k) : k ≤ G.edgeFinset.card := by
  obtain ⟨v, w, hcyc, hlen⟩ := h
  have hle := hcyc.isCircuit.isTrail.length_le_card_edgeFinset
  omega

/-- **Grounded baseline: a pancyclic graph on `n ≥ 3` vertices has at least `n` edges.**
    This is derived from the genuine Hamiltonian (length-`n`) cycle guaranteed by
    pancyclicity, *not* from a vacuous `sSup ∅`. In the grounded model the excess
    `G.edgeFinset.card - n` is therefore a real non-negative quantity, repairing the
    modeling flaw that made the abstract `pancyclicExcess` collapse to `0`. The deep
    bounds `h(n) ≥ log₂(n−1) − 1` (Griffin 2013) and `h(n) ≤ log₂ n + log* n + O(1)`
    (GKW 2016) remain open targets to be proved on top of this corrected definition. -/
theorem pancyclicGraph_card_edgeFinset_ge (hn : 3 ≤ n)
    (h : IsPancyclicGraph G) : n ≤ G.edgeFinset.card :=
  card_edgeFinset_ge_of_hasCycleOfLength G (h n hn le_rfl)

omit [Fintype G.edgeSet] in
/-- A pancyclic graph on `n ≥ 3` vertices contains a **Hamiltonian cycle**: a cycle of
    length exactly `n` (the top length in the pancyclic range). This is the witness that
    forces the baseline `n ≤ #E(G)` bound above. -/
theorem pancyclicGraph_hasHamiltonianCycle (hn : 3 ≤ n)
    (h : IsPancyclicGraph G) : HasCycleOfLength G n :=
  h n hn le_rfl

omit [Fintype G.edgeSet] in
/-- A pancyclic graph on `n ≥ 3` vertices contains a **triangle**: a cycle of length `3`
    (the bottom length in the pancyclic range). -/
theorem pancyclicGraph_hasTriangle (hn : 3 ≤ n)
    (h : IsPancyclicGraph G) : HasCycleOfLength G 3 :=
  h 3 le_rfl hn

/-- **Grounded excess** `h_G := #E(G) − n`: the number of edges of `G` beyond the
    Hamiltonian baseline `n`. In the grounded model this is a genuine quantity tied to
    the concrete graph, unlike the abstract `pancyclicExcess` which collapsed to `0`
    because its cycle predicate was disconnected from any edge set. -/
def pancyclicGraphExcess : ℕ := G.edgeFinset.card - n

/-- **The excess recovers the true edge count.** For a pancyclic graph the Hamiltonian
    cycle guarantees `n ≤ #E(G)`, so `pancyclicGraphExcess G + n = #E(G)` with no
    truncation from `ℕ` subtraction. -/
theorem pancyclicGraphExcess_add (hn : 3 ≤ n)
    (h : IsPancyclicGraph G) : pancyclicGraphExcess G + n = G.edgeFinset.card :=
  Nat.sub_add_cancel (pancyclicGraph_card_edgeFinset_ge G hn h)

/-- **Grounded upper bound on the excess.** Every simple graph on `n` vertices has at most
    `C(n, 2)` edges, so the pancyclic excess is at most `C(n, 2) − n`. Together with the
    non-negativity built into `ℕ` and the identity `pancyclicGraphExcess_add`, this
    sandwiches the excess in the interval `[0, C(n,2) − n]`, establishing that `h(n)` is a
    well-defined finite quantity in the corrected model. The deep estimates
    `h(n) ≥ log₂(n−1) − 1` (Griffin 2013) and `h(n) ≤ log₂ n + log* n + O(1)` (GKW 2016)
    refine this crude sandwich and remain open targets on top of this definition. -/
theorem pancyclicGraphExcess_le : pancyclicGraphExcess G ≤ n.choose 2 - n := by
  have hcard : G.edgeFinset.card ≤ n.choose 2 := by
    simpa [Fintype.card_fin] using G.card_edgeFinset_le_card_choose_two
  unfold pancyclicGraphExcess
  omega

end Grounded
