/-
  Aristotle targets for Erdős Problem #895
  Routine supporting lemmas for automated proof search.
  See Erdos895Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main conjecture (Barber's theorem on independent additive triples)
  - NOT the counterexample construction (n=17, requires SAT-like reasoning)
  - Routine graph theory and combinatorics from Mathlib
  - Clean theorem statements with no definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos895Aristotle

open Finset SimpleGraph

/-
  Routine: Mantel's theorem — a triangle-free graph on n vertices
  has at most n^2/4 edges. This is a classical result (1907).
  Mathlib has SimpleGraph.IsCliqueFree and edge counting machinery.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

-- Routine: Triangle-free implies no 3-clique
theorem triangleFree_isCliqueFree_three (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) : ∀ (s : Finset V), s.card = 3 → ¬G.IsClique s := by
  intro s hs hcl
  exact hG s ⟨hcl, hs⟩

/-
PROBLEM
Routine: In a triangle-free graph, the neighborhood of any vertex is independent
This is a fundamental graph theory fact: if N(v) had an edge {a,b},
then {v, a, b} would form a triangle.

PROVIDED SOLUTION
If a and b are both neighbors of v and also adjacent to each other, then {v,a,b} forms a 3-clique, contradicting CliqueFree 3. Construct the IsNClique witness explicitly.
-/
theorem triangleFree_neighborhood_independent (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (v : V) :
    ∀ a b : V, G.Adj v a → G.Adj v b → a ≠ b → ¬G.Adj a b := by
  intro a b h1 h2 hab h3; have := hG { v, a, b } ; simp_all +decide [ Finset.card_insert_of_notMem ] ;
  simp_all +decide [ SimpleGraph.isNClique_iff, Set.insert_subset_iff ];
  rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] at this <;> aesop

/-
PROBLEM
Routine: A sum-free set in {1,...,n} has size at most n/2
The odd numbers form a sum-free set of size ⌈n/2⌉, and this is optimal.

PROVIDED SOLUTION
Consider the map f : S → {1,...,n} \ S sending x to n+1-x. Since S is sum-free (no a+b in S for a,b in S), if both x and n+1-x were in S, then x + (n+1-x) = n+1 which is not in range, but actually we need a pairing argument. Alternative approach: pair each element x in S∩{1,...,⌊n/2⌋} with n+1-x. Since S is sum-free and all elements are positive, at most one of {x, n+1-x} can be in S for each pair (because if both x and n+1-x are in S, then x + (n+1-x) = n+1 which may or may not be in range). Actually, the standard proof: consider pairs (i, n+1-i) for i=1,...,⌊n/2⌋. There are ⌊n/2⌋ such pairs plus possibly the middle element if n is odd. At most one from each pair can be in S (if both i and n+1-i are in S, then i + (n+1-i) = n+1; but n+1 is not in range(n+1), so this doesn't give a contradiction directly).

Actually, the standard sum-free bound is |S| ≤ ⌈n/2⌉ not ⌊(n+1)/2⌋. For S ⊆ {1,...,n}, the bound is |S| ≤ ⌈n/2⌉. And ⌈n/2⌉ = (n+1)/2 in natural number division. So the bound (n+1)/2 is correct.

A simpler approach: consider the injection from S to Finset.range((n+1)/2+1)\{0} defined by sending x to... Actually this is hard to formalize directly. Let me try a different approach.

Consider the map x ↦ min(x, n+1-x) from S to {1,...,⌊n/2⌋}. This map is injective on S because S is sum-free: if min(a, n+1-a) = min(b, n+1-b) and a ≠ b, then either a = n+1-b (so a+b = n+1 > n, and n+1 ∉ range(n+1)) which doesn't directly contradict sum-free. Hmm.

Actually let me try: for a sum-free subset of {1,...,n}, pair i with n-i for i=1,...,⌊(n-1)/2⌋. At most one of i, n-i can be in S because if both are, i + (n-i) = n ∈ {1,...,n} and S is sum-free. This gives at most ⌊(n-1)/2⌋ + 1 elements (including possibly n itself if n isn't paired). Hmm, this gets complicated.

Let me just try omega or decide-based approaches, or let the subagent figure it out.
-/
theorem sumFree_card_bound (n : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range (n + 1))
    (hpos : ∀ x ∈ S, x > 0)
    (hsf : ∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) :
    S.card ≤ (n + 1) / 2 := by
  -- Consider the maximum element $m \in S$. By definition, $m \leq n$.
  by_cases hS_empty : S = ∅
  aesop;
  -- Let $m$ be the largest element in $S$.
  obtain ⟨m, hm⟩ : ∃ m ∈ S, ∀ x ∈ S, x ≤ m := by
    exact ⟨ Finset.max' _ <| Finset.nonempty_of_ne_empty hS_empty, Finset.max'_mem _ _, fun x hx => Finset.le_max' _ _ hx ⟩;
  -- Consider the set $T = \{m - x \mid x \in S, x < m\}$. Since $S$ is sum-free, $T$ is disjoint from $S$.
  set T := Finset.image (fun x => m - x) (S.erase m) with hT_def
  have hT_disjoint : Disjoint S T := by
    simp_all +decide [ Finset.disjoint_left ];
    grind +ring;
  -- Since $T$ is disjoint from $S$ and $S \cup T \subseteq \{1, \ldots, n\}$, we have $|S| + |T| \leq n$.
  have h_union_card : S.card + T.card ≤ n := by
    have h_union_subset : S ∪ T ⊆ Finset.Ico 1 (n + 1) := by
      exact Finset.union_subset ( fun x hx => Finset.mem_Ico.mpr ⟨ hpos x hx, Finset.mem_range.mp ( hS hx ) ⟩ ) ( Finset.image_subset_iff.mpr fun x hx => Finset.mem_Ico.mpr ⟨ Nat.sub_pos_of_lt ( lt_of_le_of_ne ( hm.2 x ( Finset.mem_of_mem_erase hx ) ) ( by aesop ) ), Nat.lt_succ_of_le ( Nat.sub_le_of_le_add <| by linarith [ Finset.mem_range.mp ( hS ( Finset.mem_of_mem_erase hx ) ), Finset.mem_range.mp ( hS hm.1 ) ] ) ⟩ );
    have := Finset.card_mono h_union_subset; aesop;
  rw [ Finset.card_image_of_injOn ] at h_union_card;
  · rw [ Finset.card_erase_of_mem hm.1 ] at h_union_card ; omega;
  · exact fun x hx y hy hxy => by rw [ tsub_right_inj ] at hxy <;> aesop;

-- Routine: The set of odd numbers in {1,...,n} is sum-free
-- Because odd + odd = even, and all elements are odd.
theorem odd_set_sumFree (n : ℕ) :
    let S := (Finset.range (n + 1)).filter (fun x => x > 0 ∧ x % 2 = 1)
    ∀ a ∈ S, ∀ b ∈ S, a + b ∉ S := by
  intro S a ha b hb
  simp only [S, Finset.mem_filter, Finset.mem_range] at ha hb ⊢
  intro ⟨_, ⟨_, hmod⟩⟩
  omega

/-
PROBLEM
Routine: Cardinality of odd numbers in {1,...,n}
There are ⌈n/2⌉ odd numbers in {1,...,n}.

PROVIDED SOLUTION
Prove by induction on n. Base case n=0: filter of range 1 for odd positive numbers is empty, (0+1)/2 = 0. Inductive step: consider whether n+1 is odd and positive. If n+1 is odd, the new element is added and the count increases by 1. Track that (n+2)/2 = (n+1)/2 + 1 when n+1 is odd, and (n+2)/2 = (n+1)/2 when n+1 is even. Use Finset.filter properties and range_succ.
-/
theorem odd_count_in_range (n : ℕ) :
    ((Finset.range (n + 1)).filter (fun x => x > 0 ∧ x % 2 = 1)).card = (n + 1) / 2 := by
  rw [ Finset.card_eq_of_bijective ];
  use fun i hi => 2 * i + 1;
  · exact fun a ha => ⟨ a / 2, by norm_num at *; omega, by linarith [ Nat.mod_add_div a 2, Finset.mem_filter.mp ha ] ⟩;
  · exact fun i hi => Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( by linarith [ Nat.div_mul_le_self ( n + 1 ) 2 ] ), Nat.succ_pos _, by norm_num [ Nat.add_mod ] ⟩;
  · grind +ring

-- Routine: If a, b, a+b are all in {0,...,n-1} then a+b < n
-- Simple arithmetic used in Fin-based additive triple definitions.
theorem additive_triple_bound (n : ℕ) (a b : ℕ) (ha : a < n) (hb : b < n)
    (hab : a + b < n) (hpa : a > 0) (hpb : b > 0) :
    a + b > 0 ∧ a + b < n := by
  exact ⟨by omega, hab⟩

-- Routine: Independent set in complement has clique in original
-- If S is independent in G, then S is a clique in Gᶜ.
omit [Fintype V] [DecidableEq V] in
theorem independent_is_complement_clique (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V)
    (hind : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬G.Adj a b) :
    Gᶜ.IsClique (S : Set V) := by
  intro a ha b hb hab
  simp only [SimpleGraph.compl_adj]
  exact ⟨hab, hind a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) hab⟩

/-
PROBLEM
Schur's theorem for 2 colors — S(2) = 4.
    Any 2-coloring of {1,2,3,4,5} contains a monochromatic Schur triple (a, b, a+b).
    We use Fin 6 = {0,...,5} with the constraint a.val > 0 and b.val > 0 to represent {1,...,5}.
    (The original statement used Fin 5, which only gives {1,...,4} and is false.)

PROVIDED SOLUTION
This is a finite decidability check over all 2-colorings of Fin 6. Use `decide` or `native_decide`.
-/
theorem schur_two_colors :
    ∀ c : Fin 6 → Fin 2,
    ∃ a b : Fin 6, ∃ (h1 : a.val > 0) (h2 : b.val > 0) (h3 : a.val + b.val < 6),
      c a = c b ∧ c a = c ⟨a.val + b.val, h3⟩ := by
  native_decide +revert

/-
PROBLEM
Routine: Pigeonhole — if n items are colored with k colors,
some color class has at least ⌈n/k⌉ items.

PROVIDED SOLUTION
By contradiction/pigeonhole: if every color class has card * k < n, then summing over all k colors gives total < n, but the total is exactly n (since every element of Fin n gets some color). Use Finset.card_univ, the partition of Fin n by color classes, and the pigeonhole principle. Key lemma: Finset.exists_le_card_fiber_of_nsmul_le_card or similar from Mathlib.
-/
theorem pigeonhole_coloring (n k : ℕ) (hk : k > 0) (c : Fin n → Fin k) :
    ∃ color : Fin k, ((Finset.univ.filter (fun i => c i = color)).card : ℕ) * k ≥ n := by
  by_contra! h_contra;
  -- Summing over all colors, we get that the total number of elements is less than $n$.
  have h_sum : ∑ color : Fin k, (Finset.univ.filter (fun i => c i = color)).card * k < n * k := by
    simpa [ mul_comm ] using Finset.sum_lt_sum_of_nonempty ⟨ ⟨ 0, hk ⟩, Finset.mem_univ _ ⟩ fun x hx => h_contra x;
  rw [ ← Finset.sum_mul _ _ _ ] at h_sum;
  convert h_sum.ne ?_;
  simp +decide only [card_eq_sum_ones, sum_filter];
  rw [ Finset.sum_comm ] ; aesop

end Erdos895Aristotle