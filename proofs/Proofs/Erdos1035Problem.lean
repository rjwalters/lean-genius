/-
# Erdős Problem 1035: Hypercube Subgraphs in Dense Graphs

Is there a constant `c > 0` such that every graph on `2^n` vertices with
minimum degree greater than `(1 - c) * 2^n` contains the `n`-dimensional
hypercube `Q_n` as a subgraph?

If the conjecture is false, two alternatives: find the smallest `m > 2^n`
such that min degree `> (1 - c) * 2^n` on `m` vertices forces `Q_n`, or
find `u_n` such that min degree `> 2^n - u_n` on `2^n` vertices forces `Q_n`.

*Reference:* [erdosproblems.com/1035](https://www.erdosproblems.com/1035)
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open SimpleGraph Finset

/- ## Hypercube graph -/

/-- The `n`-dimensional hypercube graph `Q_n` on `Fin (2^n)` vertices, where two
vertices are adjacent iff their XOR has exactly one bit set. -/
def hypercubeAdj (n : ℕ) (u v : Fin (2 ^ n)) : Prop :=
    u ≠ v ∧ ∃ k : Fin n, u.val ^^^ v.val = 2 ^ k.val

/-- The hypercube graph `Q_n` as a SimpleGraph. -/
def hypercubeGraph (n : ℕ) : SimpleGraph (Fin (2 ^ n)) where
  Adj := hypercubeAdj n
  symm := by
    intro u v ⟨hne, k, hk⟩
    exact ⟨hne.symm, k, by rw [Nat.xor_comm]; exact hk⟩
  loopless := by
    intro v ⟨hne, _⟩
    exact hne rfl

/- ## Minimum degree -/

/-- A simple graph on `Fin N` has minimum degree at least `d` if every vertex
has at least `d` neighbours. -/
def HasMinDegree (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (d : ℕ) : Prop :=
    ∀ v : Fin N, d ≤ (univ.filter (G.Adj v)).card

/- ## Subgraph containment -/

/-- Graph `H` on `Fin M` is a subgraph of `G` on `Fin N` (via an injective
vertex map preserving adjacency). -/
def ContainsAsSubgraph (G : SimpleGraph (Fin N)) (H : SimpleGraph (Fin M)) : Prop :=
    ∃ f : Fin M → Fin N, Function.Injective f ∧
      ∀ u v : Fin M, H.Adj u v → G.Adj (f u) (f v)

/- ## Main conjecture -/

/-- Erdős Problem 1035: There exists `c > 0` such that every graph on `2^n`
vertices with min degree `> (1-c) * 2^n` contains `Q_n`. -/
def ErdosProblem1035 : Prop :=
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n →
      ∀ (G : SimpleGraph (Fin (2 ^ n))) [DecidableRel G.Adj],
        HasMinDegree G ⌈((1 - c) * (2 ^ n : ℝ))⌉₊ →
          ContainsAsSubgraph G (hypercubeGraph n)

/- ## Alternative questions -/

/-- If the conjecture fails: what is the smallest `m > 2^n` such that
min degree `> (1-c) * 2^n` on `m` vertices forces `Q_n`? -/
def ErdosProblem1035_alt1 (c : ℝ) (hc : 0 < c) : Prop :=
    ∀ n : ℕ, 0 < n →
      ∃ m : ℕ, 2 ^ n < m ∧
        ∀ (G : SimpleGraph (Fin m)) [DecidableRel G.Adj],
          HasMinDegree G ⌈((1 - c) * (2 ^ n : ℝ))⌉₊ →
            ContainsAsSubgraph G (hypercubeGraph n)

/-- If the conjecture fails: find `u_n` such that min degree `> 2^n - u_n`
on `2^n` vertices forces `Q_n`. -/
def ErdosProblem1035_alt2 : Prop :=
    ∃ u : ℕ → ℕ, (∀ n, 0 < u n) ∧
      ∀ n : ℕ, 0 < n →
        ∀ (G : SimpleGraph (Fin (2 ^ n))) [DecidableRel G.Adj],
          HasMinDegree G (2 ^ n - u n) →
            ContainsAsSubgraph G (hypercubeGraph n)

/- ## Basic properties -/

/-- The hypercube `Q_n` is a subgraph of itself (via the identity embedding). -/
theorem hypercube_self_subgraph (n : ℕ) :
    ContainsAsSubgraph (hypercubeGraph n) (hypercubeGraph n) :=
  ⟨id, Function.injective_id, fun _ _ h => h⟩

/-- The complete graph on `2^n` vertices contains `Q_n` (via the identity map,
    since every non-diagonal pair is adjacent in a complete graph). -/
theorem complete_contains_hypercube (n : ℕ) :
    ∀ (G : SimpleGraph (Fin (2 ^ n))),
      (∀ u v : Fin (2 ^ n), u ≠ v → G.Adj u v) →
        ContainsAsSubgraph G (hypercubeGraph n) := by
  intro G hG
  exact ⟨id, Function.injective_id, fun u v huv => hG u v huv.1⟩

/-- `Q_1` is the complete graph on `Fin 2`: two vertices are adjacent iff distinct.
    Proved by case analysis on `Fin 2`. -/
theorem hypercube_one_is_edge :
    ∀ u v : Fin (2 ^ 1), (hypercubeGraph 1).Adj u v ↔ u ≠ v := by
  intro u v
  constructor
  · exact fun h => h.1
  · intro hne
    refine ⟨hne, ⟨0, by omega⟩, ?_⟩
    simp [Pow.pow]
    fin_cases u <;> fin_cases v <;> simp_all

/- ## Decidability -/

/-- Decidability of `hypercubeAdj`: enables `decide` and `native_decide` for
    computational verification of Q_n properties. -/
instance hypercubeAdjDecidable (n : ℕ) (u v : Fin (2 ^ n)) :
    Decidable (hypercubeAdj n u v) := by
  unfold hypercubeAdj
  infer_instance

instance hypercubeGraphDecidableAdj (n : ℕ) : DecidableRel (hypercubeGraph n).Adj :=
  fun u v => hypercubeAdjDecidable n u v

/- ## Q_n structural properties -/

/-- Q_2 is the 4-cycle: edges are 0-1, 0-2, 1-3, 2-3. Verified computationally.
    The vertices {00, 01, 10, 11} are adjacent when they differ in exactly one bit. -/
theorem hypercube_two_edges :
    (hypercubeGraph 2).Adj (0 : Fin 4) (1 : Fin 4) ∧
    (hypercubeGraph 2).Adj (0 : Fin 4) (2 : Fin 4) ∧
    ¬(hypercubeGraph 2).Adj (0 : Fin 4) (3 : Fin 4) ∧
    (hypercubeGraph 2).Adj (1 : Fin 4) (3 : Fin 4) ∧
    (hypercubeGraph 2).Adj (2 : Fin 4) (3 : Fin 4) ∧
    ¬(hypercubeGraph 2).Adj (1 : Fin 4) (2 : Fin 4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> {
    simp only [hypercubeGraph, hypercubeAdj]
    decide
  }

/-- Each vertex of Q_1 has exactly 1 neighbor (Q_1 is 1-regular). -/
theorem hypercube_one_regular :
    ∀ v : Fin (2 ^ 1),
      (Finset.univ.filter (fun w => (hypercubeGraph 1).Adj v w)).card = 1 := by
  intro v; fin_cases v <;> native_decide

/-- Each vertex of Q_2 has exactly 2 neighbors (Q_2 is 2-regular). -/
theorem hypercube_two_regular :
    ∀ v : Fin (2 ^ 2),
      (Finset.univ.filter (fun w => (hypercubeGraph 2).Adj v w)).card = 2 := by
  intro v; fin_cases v <;> native_decide

/-- Q_2 has exactly 4 edges (each of the 4 vertices has degree 2, and 4·2/2 = 4). -/
theorem hypercube_two_edge_count :
    (Finset.univ.filter (fun p : Fin 4 × Fin 4 =>
      (hypercubeGraph 2).Adj p.1 p.2)).card = 8 := by
  native_decide

/-- Each vertex of Q_3 has exactly 3 neighbors (Q_3 is 3-regular). -/
theorem hypercube_three_regular :
    ∀ v : Fin (2 ^ 3),
      (Finset.univ.filter (fun w => (hypercubeGraph 3).Adj v w)).card = 3 := by
  intro v; fin_cases v <;> native_decide

/-- The total number of directed edges in Q_3 is 24 (= 8 vertices × 3 neighbors).
    So Q_3 has 12 undirected edges. -/
theorem hypercube_three_edge_count :
    (Finset.univ.filter (fun p : Fin 8 × Fin 8 =>
      (hypercubeGraph 3).Adj p.1 p.2)).card = 24 := by
  native_decide

/- ## Adjacency characterization -/

/-- Adjacent vertices in Q_n differ in exactly one bit position. Restates
    the definition in terms of explicit bit positions. -/
theorem hypercube_adj_iff (n : ℕ) (u v : Fin (2 ^ n)) :
    (hypercubeGraph n).Adj u v ↔ u ≠ v ∧ ∃ k : Fin n, u.val ^^^ v.val = 2 ^ k.val :=
  Iff.rfl

/-- XOR with a power of 2 gives a distinct value (flipping a nonzero bit).
    For any v and k, v XOR 2^k ≠ v since 2^k > 0. -/
theorem xor_pow2_ne_self (v k : ℕ) : v ^^^ 2 ^ k ≠ v := by
  intro h
  have hpow : (2 : ℕ) ^ k = 0 := by
    have h1 : v ^^^ (v ^^^ 2 ^ k) = v ^^^ v := by rw [h]
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at h1
    exact h1
  exact (Nat.two_pow_pos k).ne' hpow

/- ## General Q_n regularity (proved for all n) -/

/-- Flipping bit `k` in vertex `v` gives a valid vertex in `Q_n`. -/
theorem hypercube_flip_lt (n : ℕ) (v : Fin (2 ^ n)) (k : Fin n) :
    v.val ^^^ 2 ^ k.val < 2 ^ n :=
  Nat.xor_lt_two_pow v.isLt (Nat.pow_lt_pow_right (by omega) k.isLt)

/-- The bit-flip function: flip bit `k` of vertex `v` in `Q_n`. -/
def hypercubeFlip (n : ℕ) (v : Fin (2 ^ n)) (k : Fin n) : Fin (2 ^ n) :=
  ⟨v.val ^^^ 2 ^ k.val, hypercube_flip_lt n v k⟩

/-- Flipping bit `k` gives a neighbor: `v` is adjacent to `v ⊕ 2^k` in `Q_n`. -/
theorem hypercube_flip_adj (n : ℕ) (v : Fin (2 ^ n)) (k : Fin n) :
    (hypercubeGraph n).Adj v (hypercubeFlip n v k) := by
  refine ⟨?_, k, ?_⟩
  · intro h
    have hval : v.val = v.val ^^^ 2 ^ k.val := by
      have := congr_arg Fin.val h; simp only [hypercubeFlip] at this; exact this
    exact absurd hval.symm (xor_pow2_ne_self v.val k.val)
  · simp only [hypercubeFlip]
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

/-- Every neighbor of `v` in `Q_n` comes from a single bit flip. -/
theorem hypercube_adj_of_flip (n : ℕ) (v w : Fin (2 ^ n))
    (h : (hypercubeGraph n).Adj v w) :
    ∃ k : Fin n, w = hypercubeFlip n v k := by
  obtain ⟨_, k, hk⟩ := h
  refine ⟨k, Fin.ext ?_⟩
  simp only [hypercubeFlip]
  have h1 : v.val ^^^ (v.val ^^^ w.val) = v.val ^^^ 2 ^ k.val := by rw [hk]
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at h1
  exact h1

/-- Distinct bit positions give distinct neighbors (the flip map is injective). -/
theorem hypercube_flip_injective (n : ℕ) (v : Fin (2 ^ n)) :
    Function.Injective (hypercubeFlip n v) := by
  intro i j h
  have h1 : v.val ^^^ 2 ^ i.val = v.val ^^^ 2 ^ j.val := by
    have := congr_arg Fin.val h; simp only [hypercubeFlip] at this; exact this
  have h2 : (2 : ℕ) ^ i.val = 2 ^ j.val := by
    have h3 : v.val ^^^ (v.val ^^^ 2 ^ i.val) = v.val ^^^ (v.val ^^^ 2 ^ j.val) := by
      rw [h1]
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor,
        ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at h3
    exact h3
  ext
  by_contra h3
  rcases lt_or_gt_of_ne h3 with h4 | h4
  · exact absurd h2 (Nat.pow_lt_pow_right (by omega) h4).ne
  · exact absurd h2.symm (Nat.pow_lt_pow_right (by omega) h4).ne

/-- **Q_n is n-regular**: every vertex has exactly `n` neighbors.
    Proved for all `n`, subsuming the computational checks for `n ≤ 3` above. -/
theorem hypercube_n_regular_general (n : ℕ) (v : Fin (2 ^ n)) :
    (univ.filter (fun w => (hypercubeGraph n).Adj v w)).card = n := by
  have h_eq : univ.filter (fun w => (hypercubeGraph n).Adj v w) =
      univ.image (hypercubeFlip n v) := by
    ext w
    constructor
    · intro hw
      rw [mem_filter] at hw
      rw [mem_image]
      obtain ⟨k, hk⟩ := hypercube_adj_of_flip n v w hw.2
      exact ⟨k, mem_univ _, hk.symm⟩
    · intro hw
      rw [mem_image] at hw
      rw [mem_filter]
      obtain ⟨k, _, hk⟩ := hw
      exact ⟨mem_univ _, by rw [← hk]; exact hypercube_flip_adj n v k⟩
  rw [h_eq, card_image_of_injective _ (hypercube_flip_injective n v),
      card_univ, Fintype.card_fin]

/- ## General Q_n edge count -/

/-- **Q_n has `n · 2^n` directed edges** (equivalently, `n · 2^(n-1)` undirected edges).
    This generalizes `hypercube_two_edge_count` (n=2: 8 = 2·4) and
    `hypercube_three_edge_count` (n=3: 24 = 3·8) to all `n`.

    Proof: bijection between directed edges and pairs `(v, k) ∈ Fin(2^n) × Fin n`,
    sending `(v, k)` to `(v, v ⊕ 2^k)`. Surjectivity uses `hypercube_adj_of_flip`;
    injectivity uses `hypercube_flip_injective`. -/
theorem hypercube_n_edge_count (n : ℕ) :
    (univ.filter (fun p : Fin (2 ^ n) × Fin (2 ^ n) =>
      (hypercubeGraph n).Adj p.1 p.2)).card = n * 2 ^ n := by
  let f : Fin (2 ^ n) × Fin n → Fin (2 ^ n) × Fin (2 ^ n) :=
    fun p => (p.1, hypercubeFlip n p.1 p.2)
  have hf_inj : Function.Injective f := by
    rintro ⟨v1, k1⟩ ⟨v2, k2⟩ heq
    simp only [f, Prod.mk.injEq] at heq
    obtain ⟨hv, hw⟩ := heq
    subst hv
    exact Prod.mk.injEq .. |>.mpr ⟨rfl, hypercube_flip_injective n v1 hw⟩
  have h_eq : (univ : Finset (Fin (2 ^ n) × Fin n)).image f =
      univ.filter (fun p : Fin (2 ^ n) × Fin (2 ^ n) =>
        (hypercubeGraph n).Adj p.1 p.2) := by
    ext ⟨v, w⟩
    simp only [mem_image, mem_filter, mem_univ, true_and, f, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨v', k⟩, hv, hw⟩
      subst hv; subst hw
      exact hypercube_flip_adj n v' k
    · intro h
      obtain ⟨k, hk⟩ := hypercube_adj_of_flip n v w h
      exact ⟨(v, k), rfl, hk.symm⟩
  rw [← h_eq, card_image_of_injective _ hf_inj,
      card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  ring

/- ## Handshaking lemma for Q_n -/

/-- **Handshaking lemma for Q_n**: twice the number of undirected edges equals `n · 2^n`
    (the sum of all vertex degrees).

    This is the handshaking lemma applied to the `n`-regular graph `Q_n`:
    `2 · |E(Q_n)| = ∑_v deg(v) = 2^n · n`. -/
theorem hypercube_handshaking (n : ℕ) :
    2 * (hypercubeGraph n).edgeFinset.card = n * 2 ^ n := by
  have hdeg : ∀ v : Fin (2 ^ n), (hypercubeGraph n).degree v = n := fun v => by
    simp only [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
    exact hypercube_n_regular_general n v
  have hshake := (hypercubeGraph n).sum_degrees_eq_twice_card_edges
  simp_rw [hdeg] at hshake
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hshake
  linarith

/- ## Bipartiteness of Q_n -/

/-- The bit-count sum for vertex `v`: the number of set bits in the first `n` positions.
    Used to define the 2-coloring of Q_n by popcount parity. -/
def hypercubeBitCount (n : ℕ) (v : ℕ) : ℕ :=
  ∑ k : Fin n, if v.testBit k.val then 1 else 0

/-- The 2-coloring of Q_n by bit-count parity: vertex `v` has color 0 (even) or 1 (odd)
    according to the parity of the number of set bits in `v`. -/
def hypercubeColor (n : ℕ) (v : Fin (2 ^ n)) : Fin 2 :=
  ⟨hypercubeBitCount n v.val % 2, Nat.mod_lt _ (by norm_num)⟩

/-- XOR with `2^k` changes `hypercubeBitCount` by exactly 1: flipping bit `k` either
    increments or decrements the count by 1, so the parity always changes. -/
private lemma hypercubeBitCount_xor_pow_parity (n k : ℕ) (hk : k < n) (v : ℕ) :
    hypercubeBitCount n (v ^^^ 2 ^ k) % 2 ≠ hypercubeBitCount n v % 2 := by
  simp only [hypercubeBitCount]
  -- The erase-k sum is identical for v and v ^^^ 2^k (bits j ≠ k are unchanged)
  have h_rest : ∑ j ∈ Finset.univ.erase (⟨k, hk⟩ : Fin n),
      if (v ^^^ 2 ^ k).testBit j.val then 1 else 0 =
      ∑ j ∈ Finset.univ.erase (⟨k, hk⟩ : Fin n),
      if v.testBit j.val then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro ⟨j, _⟩ hmem
    simp only [Finset.mem_erase, ne_eq, Fin.mk.injEq] at hmem
    rw [Nat.testBit_xor, Nat.testBit_two_pow_of_ne hmem.1, Bool.xor_false]
  -- The k-th bit flips: testBit (v ^^^ 2^k) k = !testBit v k
  have h_flip : (v ^^^ 2 ^ k).testBit k = !(v.testBit k) := by
    rw [Nat.testBit_xor, Nat.testBit_two_pow_self, Bool.true_xor]
  -- Expand both sums: isolate k-th term + erase sum
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨k, hk⟩ : Fin n)),
      show (⟨k, hk⟩ : Fin n).val = k from rfl, h_flip, h_rest,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨k, hk⟩ : Fin n)),
      show (⟨k, hk⟩ : Fin n).val = k from rfl]
  -- Now: (if !(v.testBit k) then 1 else 0 + X) % 2 ≠ (if v.testBit k then 1 else 0 + X) % 2
  -- where X = ∑ j ∈ erase ⟨k⟩, if v.testBit j then 1 else 0
  -- Case split: bit k is false or true
  cases hb : v.testBit k
  · -- bit k = false → !bit k = true → sum_new = 1 + X, sum_old = 0 + X
    simp only [hb, Bool.not_false, ite_true, ite_false, zero_add]
    omega
  · -- bit k = true → !bit k = false → sum_new = 0 + X, sum_old = 1 + X
    simp only [hb, Bool.not_true, ite_true, ite_false, zero_add]
    omega

/-- **Q_n is bipartite** (2-colorable): the vertex set splits into two independent sets
    according to the parity of the number of set bits (popcount parity).

    Coloring: vertex `v` gets color `(bitcount parity of v.val) ∈ Fin 2`.
    Adjacent vertices differ in exactly one bit, so their parities differ. -/
theorem hypercube_bipartite (n : ℕ) : (hypercubeGraph n).IsBipartite :=
  ⟨SimpleGraph.Coloring.mk
    (hypercubeColor n)
    (fun {u v} hadj => by
      obtain ⟨_, k, hk⟩ := hadj
      -- v.val = u.val ^^^ 2^k.val (from u.val ^^^ v.val = 2^k.val)
      have hv : v.val = u.val ^^^ 2 ^ k.val := by
        have h1 : u.val ^^^ (u.val ^^^ v.val) = u.val ^^^ 2 ^ k.val := by rw [hk]
        rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at h1
        exact h1
      simp only [hypercubeColor, Fin.mk.injEq, hv]
      exact hypercubeBitCount_xor_pow_parity n k.val k.isLt u.val)⟩
