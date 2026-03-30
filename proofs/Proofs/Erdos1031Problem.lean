/-
Erdős Problem #1031: Induced Regular Subgraphs in Non-Ramsey Graphs

If G is a graph on n vertices with no trivial (empty or complete) subgraph on
≥ 10 log n vertices, must G contain an induced non-trivial regular subgraph
on ≫ log n vertices?

**Status**: SOLVED (YES)
**Answer**: Prömel-Rödl (1999) proved the stronger result that such G contains
all graphs with O(log n) vertices as induced subgraphs.

Reference: https://erdosproblems.com/1031
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset Classical

namespace Erdos1031

/-
## Simple Graphs

We work with simple graphs (no loops, undirected).
-/

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The complete graph on a vertex set. -/
def completeGraph (S : Finset V) : SimpleGraph S :=
  ⊤

/-- The empty graph on a vertex set. -/
def emptyGraph (S : Finset V) : SimpleGraph S :=
  ⊥

/-
## Trivial Subgraphs

A trivial subgraph is either empty or complete.
-/

/-- An induced subgraph on S is trivial if it's empty or complete. -/
def isTrivialInduced (G : SimpleGraph V) (S : Finset V) : Prop :=
  (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬G.Adj x y) ∨
  (∀ x ∈ S, ∀ y ∈ S, x ≠ y → G.Adj x y)

/-- S is an independent set. -/
def isIndependentSet (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬G.Adj x y

/-- S is a clique. -/
def isClique (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → G.Adj x y

/-- Trivial = independent or clique. -/
theorem trivial_iff_ind_or_clique (G : SimpleGraph V) (S : Finset V) :
    isTrivialInduced G S ↔ isIndependentSet G S ∨ isClique G S := by
  rfl

/-- The trivial property is monotone: subsets of trivial sets are trivial. -/
theorem isTrivialInduced_subset (G : SimpleGraph V) (S T : Finset V)
    (hST : S ⊆ T) (hT : isTrivialInduced G T) : isTrivialInduced G S := by
  rcases hT with hInd | hClq
  · left; intro x hx y hy hne; exact hInd x (hST hx) y (hST hy) hne
  · right; intro x hx y hy hne; exact hClq x (hST hx) y (hST hy) hne

/-- Independent sets are monotone: subsets of independent sets are independent. -/
theorem isIndependentSet_subset (G : SimpleGraph V) (S T : Finset V)
    (hST : S ⊆ T) (hT : isIndependentSet G T) : isIndependentSet G S :=
  fun x hx y hy hne => hT x (hST hx) y (hST hy) hne

/-- Cliques are monotone: subsets of cliques are cliques. -/
theorem isClique_subset (G : SimpleGraph V) (S T : Finset V)
    (hST : S ⊆ T) (hT : isClique G T) : isClique G S :=
  fun x hx y hy hne => hT x (hST hx) y (hST hy) hne

/-- The empty set is trivially independent (vacuous truth). -/
theorem empty_is_trivial (G : SimpleGraph V) : isTrivialInduced G ∅ :=
  Or.inl (fun _ h => absurd h (Finset.not_mem_empty _))

/-- A singleton set is trivially both independent and a clique. -/
theorem singleton_is_trivial (G : SimpleGraph V) (v : V) :
    isTrivialInduced G {v} :=
  Or.inl (fun x hx y hy hne => by
    rw [Finset.mem_singleton] at hx hy; exact absurd (hx.trans hy.symm) hne)

/-
## The Non-Ramsey Property

G has no large trivial subgraph.
-/

/-- G has no trivial subgraph of size ≥ k. -/
def noLargeTrivial (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ S : Finset V, S.card ≥ k → ¬isTrivialInduced G S

/-- If noLargeTrivial holds for k, it holds for any k' ≥ k. -/
theorem noLargeTrivial_mono (G : SimpleGraph V) (k k' : ℕ) (hk : k ≤ k')
    (h : noLargeTrivial G k) : noLargeTrivial G k' :=
  fun S hS => h S (le_trans hk hS)

/-
## Regular Subgraphs

A graph is regular if all vertices have the same degree.
-/

/-- Degree of a vertex in the induced subgraph on S. -/
noncomputable def inducedDegree (G : SimpleGraph V) (S : Finset V) (v : V) : ℕ :=
  (S.filter (fun u => G.Adj v u)).card

/-- An induced subgraph is k-regular. -/
def isKRegularInduced (G : SimpleGraph V) (S : Finset V) (k : ℕ) : Prop :=
  ∀ v ∈ S, inducedDegree G S v = k

/-- An induced subgraph is regular. -/
def isRegularInduced (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ k : ℕ, isKRegularInduced G S k

/-- A non-trivial regular subgraph (not 0-regular on ≥2 vertices, not complete). -/
def isNontrivialRegular (G : SimpleGraph V) (S : Finset V) : Prop :=
  isRegularInduced G S ∧ ¬isTrivialInduced G S

/-- The Ramsey bound: every graph has a trivial subgraph of size ≫ log n. -/
axiom ramsey_trivial_bound : ∃ c > 0, ∀ n : ℕ, ∀ (V : Type*) [DecidableEq V] [Fintype V],
  Fintype.card V = n →
  ∀ G : SimpleGraph V,
  ∃ S : Finset V, isTrivialInduced G S ∧ (S.card : ℝ) ≥ c * Real.log n

/-
## The Main Conjecture

Graphs with no large trivial subgraph contain induced regular subgraphs.
-/

/-- The original question: existence of non-trivial regular subgraph. -/
def erdos_1031_conjecture : Prop :=
  ∃ c > 0, ∀ n : ℕ, ∀ (V : Type*) [DecidableEq V] [Fintype V],
  Fintype.card V = n →
  ∀ G : SimpleGraph V,
  noLargeTrivial G (Nat.ceil (10 * Real.log n)) →
  ∃ S : Finset V, isNontrivialRegular G S ∧ (S.card : ℝ) ≥ c * Real.log n

/-
## Prömel-Rödl Theorem (1999)

Much stronger: such graphs are c log n - universal.
-/

/-- H is an induced subgraph of G on vertex set S. -/
def isInducedSubgraph (G : SimpleGraph V) (S : Finset V) (H : SimpleGraph S) : Prop :=
  ∀ x y : S, H.Adj x y ↔ G.Adj x.val y.val

/-- G contains H as an induced subgraph. -/
def containsInduced (G : SimpleGraph V) (H : SimpleGraph W) [Fintype W] : Prop :=
  ∃ S : Finset V, S.card = Fintype.card W ∧
  ∃ (f : W ≃ S), ∀ x y : W, H.Adj x y ↔ G.Adj (f x).val (f y).val

/-- G is k-universal: contains all graphs on k vertices as induced subgraphs. -/
def isKUniversal (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (W : Type*) [DecidableEq W] [Fintype W],
  Fintype.card W = k →
  ∀ H : SimpleGraph W, containsInduced G H

/-- Prömel-Rödl (1999): Non-Ramsey graphs are c log n - universal. -/
axiom promel_rodl : ∀ c > 0, ∃ c' > 0, ∃ N : ℕ, ∀ n ≥ N,
  ∀ (V : Type*) [DecidableEq V] [Fintype V],
  Fintype.card V = n →
  ∀ G : SimpleGraph V,
  noLargeTrivial G (Nat.ceil (c * Real.log n)) →
  isKUniversal G (Nat.floor (c' * Real.log n))

/-
## The Solution

The conjecture follows from Prömel-Rödl.
-/

/-- Any k ≥ 3 has a non-trivial k-regular graph. -/
/-
## Connection to Ramsey Theory

Ramsey's theorem guarantees trivial subgraphs.
-/

/-- Ramsey number R(k,k). -/
noncomputable def ramseyNumber (k : ℕ) : ℕ :=
  Nat.find (ramsey_exists k)
  where
  ramsey_exists (k : ℕ) : ∃ N : ℕ, ∀ (V : Type*) [DecidableEq V] [Fintype V],
    Fintype.card V ≥ N →
    ∀ G : SimpleGraph V,
    ∃ S : Finset V, S.card = k ∧ isTrivialInduced G S := by
    obtain ⟨c, hc, hbound⟩ := ramsey_trivial_bound
    refine ⟨Nat.ceil (Real.exp (↑k / c)) + 1, ?_⟩
    intro V _ _ hV G
    obtain ⟨S, htriv, hsize⟩ := hbound (Fintype.card V) V rfl G
    have hk_le : k ≤ S.card := by
      suffices h : (↑k : ℝ) ≤ ↑(S.card) by exact_mod_cast h
      calc (↑k : ℝ) = c * (↑k / c) := by field_simp
        _ = c * Real.log (Real.exp (↑k / c)) := by rw [Real.log_exp]
        _ ≤ c * Real.log ↑(Fintype.card V) := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hc)
            apply Real.log_le_log (Real.exp_pos _)
            calc Real.exp (↑k / c)
                ≤ ↑(Nat.ceil (Real.exp (↑k / c))) := Nat.le_ceil _
              _ ≤ ↑(Nat.ceil (Real.exp (↑k / c)) + 1) := by push_cast; linarith
              _ ≤ ↑(Fintype.card V) := by exact_mod_cast hV
        _ ≤ ↑(S.card) := hsize
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hk_le
    exact ⟨T, hTcard, isTrivialInduced_subset G T S hTsub htriv⟩

/-- R(k,k) ≤ 4^k (crude bound). -/
axiom ramsey_upper_bound (k : ℕ) : ramseyNumber k ≤ 4^k

/-- R(k,k) ≥ 2^(k/2) (probabilistic lower bound). -/
/-- Ramsey implies log n trivial subgraph. -/
theorem ramsey_log_trivial (n : ℕ) (hn : n ≥ 4) :
    ∀ (V : Type*) [DecidableEq V] [Fintype V],
    Fintype.card V = n →
    ∀ G : SimpleGraph V,
    ∃ S : Finset V, isTrivialInduced G S ∧ S.card ≥ Nat.log 4 n / 2 := by
  intro V _ _ hVn G
  set k := Nat.log 4 n / 2 with hk_def
  have hRk_le_n : ramseyNumber k ≤ n := calc
    ramseyNumber k ≤ 4 ^ k := ramsey_upper_bound k
    _ ≤ 4 ^ (Nat.log 4 n) := by
        apply Nat.pow_le_pow_right (by norm_num : 1 ≤ 4)
        exact Nat.div_le_self _ _
    _ ≤ n := Nat.pow_log_le_self 4 (by omega)
  have hV_ge : Fintype.card V ≥ ramseyNumber k := by omega
  have hSpec := Nat.find_spec (ramseyNumber.ramsey_exists k)
  have hV_ge' : Fintype.card V ≥ Nat.find (ramseyNumber.ramsey_exists k) := hV_ge
  obtain ⟨S, hScard, hStriv⟩ := hSpec V hV_ge' G
  exact ⟨S, hStriv, by omega⟩

/-
## Non-Ramsey Graphs

Graphs avoiding large trivial subgraphs are "non-Ramsey".
-/

/-- A non-Ramsey graph has no trivial subgraph of size ≥ c log n. -/
def isNonRamsey (G : SimpleGraph V) (c : ℝ) : Prop :=
  noLargeTrivial G (Nat.ceil (c * Real.log (Fintype.card V)))

/-- Non-Ramsey graphs are rare but exist. -/
/-
## Universality

Non-Ramsey graphs contain all small graphs.
-/

/-- The stronger conclusion: all graphs appear as induced subgraphs. -/
theorem nonRamsey_universal (c : ℝ) (hc : c > 0) :
    ∃ c' > 0, ∃ N : ℕ, ∀ n ≥ N,
    ∀ (V : Type*) [DecidableEq V] [Fintype V],
    Fintype.card V = n →
    ∀ G : SimpleGraph V,
    isNonRamsey G c →
    isKUniversal G (Nat.floor (c' * Real.log n)) := by
  obtain ⟨c', hc', N, hN⟩ := promel_rodl c hc
  use c', hc', N
  intro n hn V _ _ hV G hG
  unfold isNonRamsey at hG
  rw [hV] at hG
  exact hN n hn V hV G hG

/-
## Regular Subgraphs from Universality

Universality implies regular subgraphs exist.
-/

/-- Cycle adjacency: i and j are adjacent iff they differ by 1 mod k. -/
private def cycleAdj (k : ℕ) (i j : Fin k) : Prop :=
  (i.val + 1) % k = j.val ∨ (j.val + 1) % k = i.val

private theorem cycleAdj_symm (k : ℕ) (i j : Fin k) :
    cycleAdj k i j → cycleAdj k j i := by
  intro h; cases h with | inl h => exact Or.inr h | inr h => exact Or.inl h

private theorem cycleAdj_loopless (k : ℕ) (hk : k ≥ 3) (i : Fin k) :
    ¬cycleAdj k i i := by
  intro h
  have h' : (i.val + 1) % k = i.val := by rcases h with h | h <;> exact h
  have := i.isLt
  by_cases h2 : i.val + 1 < k
  · rw [Nat.mod_eq_of_lt h2] at h'; omega
  · rw [show i.val + 1 = k from by omega, Nat.mod_self] at h'; omega

/-- The predecessor cycles back: ((i + k - 1) % k + 1) % k = i. -/
private theorem pred_succ_cancel (i k : ℕ) (hi : i < k) (hk : k ≥ 3) :
    ((i + k - 1) % k + 1) % k = i := by
  by_cases h : i = 0
  · rw [h, show 0 + k - 1 = k - 1 from by omega,
        Nat.mod_eq_of_lt (show k - 1 < k by omega),
        show k - 1 + 1 = k from by omega, Nat.mod_self]
  · rw [show i + k - 1 = (i - 1) + k from by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (show i - 1 < k by omega),
        show i - 1 + 1 = i from by omega, Nat.mod_eq_of_lt hi]

/-- Successor and predecessor are distinct when k ≥ 3. -/
private theorem succ_ne_pred (i k : ℕ) (hi : i < k) (hk : k ≥ 3) :
    (i + 1) % k ≠ (i + k - 1) % k := by
  by_cases h0 : i = 0
  · rw [h0, show 0 + 1 = 1 from rfl, Nat.mod_eq_of_lt (show 1 < k by omega),
        show 0 + k - 1 = k - 1 from by omega,
        Nat.mod_eq_of_lt (show k - 1 < k by omega)]; omega
  · by_cases h1 : i + 1 < k
    · rw [Nat.mod_eq_of_lt h1,
          show i + k - 1 = (i - 1) + k from by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (show i - 1 < k by omega)]; omega
    · rw [show i + 1 = k from by omega, Nat.mod_self,
          show i + k - 1 = (k - 2) + k from by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (show k - 2 < k by omega)]; omega

/-- If (j+1)%k = i then j = (i+k-1)%k. -/
private theorem adj_gives_pred (i j k : ℕ) (hi : i < k) (hj : j < k) (hk : k ≥ 3)
    (h : (j + 1) % k = i) : j = (i + k - 1) % k := by
  by_cases hj1 : j + 1 < k
  · rw [Nat.mod_eq_of_lt hj1] at h
    rw [← h, show j + 1 + k - 1 = j + k from by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hj]
  · rw [show j + 1 = k from by omega, Nat.mod_self] at h
    rw [← h, show 0 + k - 1 = k - 1 from by omega,
        Nat.mod_eq_of_lt (show k - 1 < k by omega)]
    omega

/-- The cycle graph on k vertices. -/
private def cycleGraph' (k : ℕ) (hk : k ≥ 3) : SimpleGraph (Fin k) where
  Adj := cycleAdj k
  symm := cycleAdj_symm k
  loopless := cycleAdj_loopless k hk

/-- Universal graphs contain regular subgraphs. -/
theorem universal_has_regular (G : SimpleGraph V) (k : ℕ) (hk : k ≥ 6) :
    isKUniversal G k →
    ∃ S : Finset V, isNontrivialRegular G S ∧ S.card = k := by
  intro huniv
  have hk3 : k ≥ 3 := by omega
  -- Lift cycle to universe of V
  let W := ULift.{_, 0} (Fin k)
  let H : SimpleGraph W := {
    Adj := fun a b => cycleAdj k a.down b.down
    symm := fun a b h => cycleAdj_symm k a.down b.down h
    loopless := fun a h => cycleAdj_loopless k hk3 a.down h
  }
  have hWcard : Fintype.card W = k := by
    change Fintype.card (ULift (Fin k)) = k
    rw [Fintype.card_ulift, Fintype.card_fin]
  -- Get embedding of cycle into G
  obtain ⟨S, hScard, f, hf⟩ := huniv W hWcard H
  -- S has k ≥ 6 ≥ 3 vertices
  refine ⟨S, ⟨⟨2, ?reg⟩, ?nontriv⟩, ?size⟩
  case size => rw [hScard, hWcard]
  case nontriv =>
    -- Not trivial: has both edges and non-edges
    let v0 : W := ULift.up ⟨0, by omega⟩
    let v1 : W := ULift.up ⟨1, by omega⟩
    let v2 : W := ULift.up ⟨2, by omega⟩
    intro htriv
    rcases htriv with hInd | hClq
    · -- Not independent: 0 and 1 are adjacent in the cycle
      have h01 : H.Adj v0 v1 := by
        show cycleAdj k (⟨0, by omega⟩ : Fin k) ⟨1, by omega⟩
        left; rw [show (0 : ℕ) + 1 = 1 from rfl, Nat.mod_eq_of_lt (show 1 < k by omega)]
      have hadj := (hf v0 v1).mp h01
      have hne : (f v0).val ≠ (f v1).val := by
        intro heq
        have h := congrArg (fun (w : W) => w.down.val) (f.injective (Subtype.val_injective heq))
        dsimp [v0, v1] at h; omega
      exact hInd _ (f v0).prop _ (f v1).prop hne hadj
    · -- Not complete: 0 and 2 are NOT adjacent in the cycle
      have h02 : ¬H.Adj v0 v2 := by
        intro h
        change cycleAdj k (⟨0, by omega⟩ : Fin k) ⟨2, by omega⟩ at h
        rcases h with h | h
        · simp only [cycleAdj] at h
          rw [show (0 : ℕ) + 1 = 1 from rfl, Nat.mod_eq_of_lt (show 1 < k from by linarith)] at h
          exact absurd h (by norm_num)
        · simp only [cycleAdj] at h
          rw [show (2 : ℕ) + 1 = 3 from rfl, Nat.mod_eq_of_lt (show 3 < k from by linarith)] at h
          exact absurd h (by norm_num)
      have hne : (f v0).val ≠ (f v2).val := by
        intro heq
        have h := congrArg (fun (w : W) => w.down.val) (f.injective (Subtype.val_injective heq))
        dsimp [v0, v2] at h; omega
      exact h02 ((hf v0 v2).mpr (hClq _ (f v0).prop _ (f v2).prop hne))
  case reg =>
    -- Each vertex in S has induced degree 2
    intro v hv
    -- v = (f w).val for some w : W
    have ⟨w, hw⟩ : ∃ w : W, (f w).val = v := ⟨f.symm ⟨v, hv⟩, by simp⟩
    subst hw
    let i := w.down  -- the Fin k index
    -- inducedDegree counts neighbors in S
    unfold inducedDegree
    -- The filter {u ∈ S | G.Adj (f w).val u} bijects with {j : W | H.Adj w j}
    have hfilt : S.filter (fun u => G.Adj (f w).val u) =
        (Finset.univ.filter (fun j : W => H.Adj w j)).map
          ⟨fun j => (f j).val, fun a b h => by
            have := f.injective (Subtype.val_injective h); exact this⟩ := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and,
        Function.Embedding.coeFn_mk]
      constructor
      · intro ⟨hu, hadj⟩
        exact ⟨f.symm ⟨u, hu⟩, (hf w _).mpr (by simp [hadj]), by simp⟩
      · intro ⟨j, hadj, hj⟩
        exact ⟨hj ▸ (f j).prop, hj ▸ (hf w j).mp hadj⟩
    rw [hfilt, Finset.card_map]
    -- Count cycle neighbors: exactly 2
    -- Neighbors of i in cycle are (i+1)%k and (i+k-1)%k
    have succ_val : ((i.val + 1) % k) < k := Nat.mod_lt _ (by omega)
    have pred_val : ((i.val + k - 1) % k) < k := Nat.mod_lt _ (by omega)
    let succW : W := ULift.up ⟨(i.val + 1) % k, succ_val⟩
    let predW : W := ULift.up ⟨(i.val + k - 1) % k, pred_val⟩
    -- succ is a neighbor
    have h_succ : H.Adj w succW := by
      show cycleAdj k i ⟨(i.val + 1) % k, succ_val⟩
      left; rfl
    -- pred is a neighbor
    have h_pred : H.Adj w predW := by
      show cycleAdj k i ⟨(i.val + k - 1) % k, pred_val⟩
      right; exact pred_succ_cancel i.val k i.isLt hk3
    -- succ ≠ pred (requires k ≥ 3)
    have h_ne : succW ≠ predW := by
      intro heq
      have hvals : (i.val + 1) % k = (i.val + k - 1) % k := by
        have := congrArg (fun w : W => w.down.val) heq; simpa [succW, predW] using this
      exact absurd hvals (succ_ne_pred i.val k i.isLt hk3)
    -- No other neighbors
    have h_only : ∀ j : W, H.Adj w j → j = succW ∨ j = predW := by
      intro j haj
      have haj' : cycleAdj k i j.down := haj
      rcases haj' with h1 | h2
      · left; apply ULift.ext; apply Fin.ext; simpa [succW] using h1.symm
      · right; apply ULift.ext; apply Fin.ext; simp [predW]
        exact adj_gives_pred i.val j.down.val k i.isLt j.down.isLt hk3 h2
    -- Filter equals {succW, predW}
    have hfilt_eq : Finset.univ.filter (fun j => H.Adj w j) = {succW, predW} := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      exact ⟨h_only j, fun h => by rcases h with rfl | rfl; exact h_succ; exact h_pred⟩
    rw [hfilt_eq, Finset.card_pair h_ne]

/-
## The Solution (continued)

Using universal_has_regular + Prömel-Rödl.
-/

/-- Simplified statement using Prömel-Rödl. -/
theorem erdos_1031_via_promel_rodl :
    ∀ c > 0, ∃ c' > 0, ∃ N : ℕ, ∀ n ≥ N,
    ∀ (V : Type*) [DecidableEq V] [Fintype V],
    Fintype.card V = n →
    ∀ G : SimpleGraph V,
    noLargeTrivial G (Nat.ceil (c * Real.log n)) →
    ∃ S : Finset V, isNontrivialRegular G S ∧ (S.card : ℝ) ≥ c' * Real.log n := by
  intro c hc
  -- Apply Prömel-Rödl to get universality constant c'' and threshold N₁
  obtain ⟨c'', hc'', N₁, hPR⟩ := promel_rodl c hc
  -- Output constant c' = c''/2
  refine ⟨c'' / 2, by linarith, ?_⟩
  -- Choose N large enough: c'' * log n ≥ 6 for n ≥ N
  refine ⟨max N₁ (Nat.ceil (Real.exp (6 / c'')) + 1), ?_⟩
  intro n hn V _ _ hV G hG
  have hn1 : n ≥ N₁ := le_trans (le_max_left _ _) hn
  have hn2 : n ≥ Nat.ceil (Real.exp (6 / c'')) + 1 := le_trans (le_max_right _ _) hn
  -- Key bound: c'' * log n ≥ 6
  have hn_pos : (0 : ℝ) < ↑n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hexp_le : Real.exp (6 / c'') ≤ ↑n := by
    calc Real.exp (6 / c'')
        ≤ ↑(Nat.ceil (Real.exp (6 / c''))) := Nat.le_ceil _
      _ < ↑(Nat.ceil (Real.exp (6 / c'')) + 1) := by push_cast; linarith
      _ ≤ ↑n := by exact_mod_cast hn2
  have hlog_bound : c'' * Real.log ↑n ≥ 6 := by
    calc c'' * Real.log ↑n
        ≥ c'' * Real.log (Real.exp (6 / c'')) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hc'')
          exact Real.log_le_log (Real.exp_pos _) hexp_le
      _ = c'' * (6 / c'') := by rw [Real.log_exp]
      _ = 6 := by field_simp
  -- ⌊c'' * log n⌋₊ ≥ 6
  set k := Nat.floor (c'' * Real.log ↑n)
  have hk_ge : k ≥ 6 := by
    exact Nat.le_floor (by push_cast; linarith)
  -- G is k-universal from Prömel-Rödl
  have huniv : isKUniversal G k := hPR n hn1 V hV G hG
  -- Universal → regular subgraph
  obtain ⟨S, hS, hScard⟩ := universal_has_regular G k hk_ge huniv
  refine ⟨S, hS, ?_⟩
  -- S.card = k ≥ c''/2 * log n
  rw [hScard]
  have hfloor_ge : (k : ℝ) ≥ c'' * Real.log ↑n - 1 := by
    have h := Nat.lt_floor_add_one (c'' * Real.log ↑n)
    change c'' * Real.log ↑n < ↑(k + 1) at h
    push_cast at h
    linarith
  calc (k : ℝ) ≥ c'' * Real.log ↑n - 1 := hfloor_ge
    _ ≥ c'' * Real.log ↑n / 2 := by linarith
    _ = c'' / 2 * Real.log ↑n := by ring

/-- The conjecture is true. -/
theorem erdos_1031_solved : erdos_1031_conjecture := by
  sorry

/-
## Summary

This file formalizes Erdős Problem #1031 on induced regular subgraphs.

**Status**: SOLVED

**The Question**: If G has no trivial subgraph on ≥ 10 log n vertices,
must G have an induced non-trivial regular subgraph on ≫ log n vertices?

**The Answer**: YES (Prömel-Rödl 1999).

**Stronger Result**: Such G contains ALL graphs on O(log n) vertices
as induced subgraphs (c log n - universality).

**Key Results**:
- Ramsey: every graph has trivial subgraph on ≫ log n vertices
- Prömel-Rödl: non-Ramsey graphs are c log n - universal
- Universality implies existence of all regular subgraphs

**Related Topics**:
- Ramsey theory
- Graph universality
- Regular graphs
- Problem 82 (general induced regular subgraph bounds)
-/

end Erdos1031
