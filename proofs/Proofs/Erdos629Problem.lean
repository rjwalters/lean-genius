/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d55e28ad-0e80-4cde-82fb-b474dc0d7f2a

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem bipartite_chromatic_le_two {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsBipartite G) : G.chromaticNumber ≤ 2

- theorem bipartite_list_chromatic_unbounded :
    ∀ k : ℕ, ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
      IsBipartite G ∧ listChromaticNumber G > k

- theorem n_well_defined (k : ℕ) : n k > 0

- theorem n_mono {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) : n k₁ ≤ n k₂

- theorem n_2_eq_6 : n 2 = 6

- theorem ert_lower_bound (k : ℕ) (hk : k ≥ 1) : 2 ^ (k - 1) < n k
-/

/-
  Erdős Problem #629: List Chromatic Number of Bipartite Graphs

  Source: https://erdosproblems.com/629
  Status: OPEN (asymptotic behavior not fully determined)

  Statement:
  The list chromatic number χ_L(G) is the minimal k such that for any assignment
  of a list of k colors to each vertex, a proper coloring can be chosen from the
  lists. Determine the minimal number of vertices n(k) of a bipartite graph G
  such that χ_L(G) > k.

  Known Results:
  - n(2) = 6 (Erdős-Rubin-Taylor 1980)
  - n(3) = 14 (Hanson-MacGillivray-Toft 1996)
  - Original bounds: 2^{k-1} < n(k) < k² · 2^{k+2}
  - Improved lower: 2^k · (k/log k)^{1/2} ≪ n(k) (Radhakrishnan-Srinivasan 2000)
  - Recursive upper: n(k) ≤ k · n(k-2) + 2^k

  Related to Problem #901 via: m(k) ≤ n(k) ≤ m(k+1)
  where m(k) is the smallest family of k-sets without Property B.

  Tags: graph-theory, chromatic-number, list-coloring, bipartite-graphs
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic


namespace Erdos629

open SimpleGraph Finset

/- ## Part I: List Coloring Definitions -/

/-- A color list assignment gives each vertex a set of available colors. -/
def ColorListAssignment (V : Type*) (C : Type*) := V → Finset C

/-- A coloring respects a list assignment if each vertex gets a color from its list. -/
def RespectsLists {V C : Type*} (L : ColorListAssignment V C) (f : V → C) : Prop :=
  ∀ v : V, f v ∈ L v

/-- A coloring is proper if adjacent vertices have different colors. -/
def IsProperColoring {V : Type*} [DecidableEq V] (G : SimpleGraph V) (f : V → C) : Prop :=
  ∀ u v : V, G.Adj u v → f u ≠ f v

/-- A graph is k-list-colorable if for any k-list assignment, a proper coloring exists. -/
def IsKListColorable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (C : Type) [Fintype C] [DecidableEq C] (L : ColorListAssignment V C),
    (∀ v, (L v).card ≥ k) →
    ∃ f : V → C, RespectsLists L f ∧ IsProperColoring G f

/-- The list chromatic number χ_L(G) is the minimal k for k-list-colorability. -/
noncomputable def listChromaticNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | IsKListColorable G k}

/- ## Part II: Bipartite Graphs -/

/-- A graph is bipartite if its vertices can be 2-colored. -/
def IsBipartite {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∃ f : V → Fin 2, IsProperColoring G f

/-- Every bipartite graph has chromatic number at most 2. -/
theorem bipartite_chromatic_le_two {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsBipartite G) : G.chromaticNumber ≤ 2 := by
  obtain ⟨ f, hf ⟩ := hG;
  convert SimpleGraph.Colorable.chromaticNumber_le _;
  use f;
  exact fun { a b } hab => by have := hf a b hab; aesop;

/- For bipartite graphs, ordinary χ(G) ≤ 2 but χ_L(G) can be arbitrarily large! -/
noncomputable section AristotleLemmas

/-
Definitions of the vertices (subsets of size k+1 from 2k+1) and the graph (complete bipartite graph on these vertices).
-/
def MyVertices (k : ℕ) := {s : Finset (Fin (2*k+1)) // s.card = k + 1}

def MyGraph (k : ℕ) : SimpleGraph (MyVertices k ⊕ MyVertices k) := completeBipartiteGraph (MyVertices k) (MyVertices k)

/-
If a set X intersects every subset of size k+1 of a set C of size 2k+1, then X must have size at least k+1.
-/
lemma hitting_set_lemma {k : ℕ} {C : Finset (Fin (2*k+1))} (hC : C.card = 2*k+1) (X : Finset (Fin (2*k+1)))
    (hX : ∀ S ⊆ C, S.card = k + 1 → (S ∩ X).Nonempty) : X.card ≥ k + 1 := by
      contrapose! hX;
      -- Since $|X| < k + 1$, we can choose a subset $Y \subseteq C \setminus X$ with $|Y| = k + 1$.
      obtain ⟨Y, hY⟩ : ∃ Y ⊆ C \ X, Y.card = k + 1 := by
        have hY : (C \ X).card ≥ k + 1 := by
          grind;
        exact?;
      exact ⟨ Y, Finset.Subset.trans hY.1 ( Finset.sdiff_subset ), hY.2, fun ⟨ z, hz ⟩ => by have := hY.1 ( Finset.mem_of_mem_inter_left hz ) ; aesop ⟩

/-
Fintype instance for MyVertices.
-/
instance (k : ℕ) : Fintype (MyVertices k) :=
  show Fintype {s : Finset (Fin (2*k+1)) // s.card = k + 1} from inferInstance

/-
DecidableEq instance for MyVertices.
-/
instance (k : ℕ) : DecidableEq (MyVertices k) :=
  show DecidableEq {s : Finset (Fin (2*k+1)) // s.card = k + 1} from inferInstance

/-
The constructed graph MyGraph k is not (k+1)-list-colorable.
-/
lemma MyGraph_not_colorable (k : ℕ) : ¬ IsKListColorable (MyGraph k) (k + 1) := by
  -- Let's choose the specific list assignment where each vertex $v$ is assigned the set of elements in its subset $v$.
  let L : ColorListAssignment (MyVertices k ⊕ MyVertices k) (Fin (2 * k + 1)) := fun v => match v with | Sum.inl v => v.val | Sum.inr v => v.val;
  -- Assume for contradiction that there exists a proper coloring $f$ of $MyGraph k$ with $k+1$ colors.
  by_contra h_contra
  obtain ⟨f, hf_lists, hf_proper⟩ := h_contra (Fin (2 * k + 1)) L (by
  rintro ( v | v ) <;> exact v.2.ge);
  -- Let $X_L$ be the set of colors used on the left partition, and $X_R$ on the right.
  set XL := Finset.image (fun v => f (Sum.inl v)) (Finset.univ : Finset (MyVertices k))
  set XR := Finset.image (fun v => f (Sum.inr v)) (Finset.univ : Finset (MyVertices k));
  -- By `hitting_set_lemma`, $|X_L| \ge k+1$ and $|X_R| \ge k+1$.
  have hXL : XL.card ≥ k + 1 := by
    apply hitting_set_lemma;
    any_goals exact Finset.univ;
    · simp +decide [ Finset.card_univ ];
    · intro S hS hS'; obtain ⟨ v, hv ⟩ := Finset.card_pos.mp ( by linarith ) ; use f ( Sum.inl ⟨ S, by aesop ⟩ ) ; aesop;
  have hXR : XR.card ≥ k + 1 := by
    -- By `hitting_set_lemma`, $|X_R| \ge k+1$.
    have hXR : ∀ S : Finset (Fin (2 * k + 1)), S.card = k + 1 → (S ∩ XR).Nonempty := by
      intro S hS_card
      obtain ⟨v, hv⟩ : ∃ v : MyVertices k, v.val = S := by
        exact ⟨ ⟨ S, hS_card ⟩, rfl ⟩;
      use f (Sum.inr v);
      aesop;
    have := @hitting_set_lemma k ( Finset.univ : Finset ( Fin ( 2 * k + 1 ) ) ) ; aesop;
  -- Since the total number of colors is $2k+1$, $X_L$ and $X_R$ must intersect.
  have h_inter : XL ∩ XR ≠ ∅ := by
    exact Finset.Nonempty.ne_empty <| Finset.card_pos.mp <| by have := Finset.card_union_add_card_inter XL XR; linarith [ show Finset.card ( XL ∪ XR ) ≤ 2 * k + 1 from le_trans ( Finset.card_le_univ _ ) ( by simp +arith +decide ) ] ;
  obtain ⟨ c, hc ⟩ := Finset.nonempty_iff_ne_empty.mpr h_inter; simp_all +decide [ Finset.ext_iff ] ;
  obtain ⟨ ⟨ v, _, rfl ⟩, ⟨ w, _, hw ⟩ ⟩ := Finset.mem_image.mp hc.1, Finset.mem_image.mp hc.2; specialize hf_proper ( Sum.inl v ) ( Sum.inr w ) ; simp_all +decide [ Erdos629.MyGraph ] ;

/-
List colorability is monotonic: if G is k₁-list-colorable and k₁ ≤ k₂, then G is k₂-list-colorable.
-/
lemma IsKListColorable_mono {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) (hk₁ : IsKListColorable G k₁) : IsKListColorable G k₂ := by
  intro C _ _ L hL
  apply hk₁
  intro v
  exact le_trans h (hL v)

/-
MyGraph k is bipartite.
-/
lemma MyGraph_bipartite (k : ℕ) : IsBipartite (MyGraph k) := by
  use fun v => match v with
    | Sum.inl _ => 0
    | Sum.inr _ => 1
  intro u v huv
  simp [MyGraph, completeBipartiteGraph] at huv
  cases u <;> cases v <;> simp_all

/-
Every graph G on V is |V|-list-colorable.
-/
lemma IsKListColorable_card {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : IsKListColorable G (Fintype.card V) := by
  intro C _ _ L hL;
  -- Since $|L(v)| \geq |V|$ for all $v$, we can choose a distinct color from $L(v)$ for each $v$.
  obtain ⟨g, hg⟩ : ∃ g : V → C, ∀ v, g v ∈ L v ∧ ∀ u, u ≠ v → g u ≠ g v := by
    have h_distinct_colors : ∀ (S : Finset V), S.Nonempty → ∃ g : V → C, ∀ v ∈ S, g v ∈ L v ∧ ∀ u ∈ S, u ≠ v → g u ≠ g v := by
      intro S hS_nonempty
      induction' S using Finset.induction with v S ih;
      · exact False.elim ( Finset.not_nonempty_empty hS_nonempty );
      · by_cases hS_empty : S.Nonempty;
        · obtain ⟨ g, hg ⟩ := ‹S.Nonempty → ∃ g : V → C, ∀ v ∈ S, g v ∈ L v ∧ ∀ u ∈ S, u ≠ v → g u ≠ g v› hS_empty;
          -- Choose a color from $L(v)$ that is not used by any vertex in $S$.
          obtain ⟨c, hc⟩ : ∃ c ∈ L v, ∀ u ∈ S, g u ≠ c := by
            have h_card : (Finset.image g S).card ≤ Fintype.card V - 1 := by
              exact le_trans ( Finset.card_image_le ) ( Nat.le_sub_one_of_lt ( Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.subset_univ _, fun h => by have := Finset.mem_univ v; aesop ⟩ ) ) );
            have h_card : (Finset.image g S).card < (L v).card := by
              exact lt_of_le_of_lt h_card ( Nat.lt_of_lt_of_le ( Nat.pred_lt ( ne_bot_of_gt ( Fintype.card_pos_iff.mpr ⟨ v ⟩ ) ) ) ( hL v ) );
            contrapose! h_card;
            exact Finset.card_le_card fun x hx => by obtain ⟨ u, hu, rfl ⟩ := h_card x hx; exact Finset.mem_image_of_mem _ hu;
          use fun u => if u = v then c else g u;
          simp_all +decide [ Finset.mem_insert ];
          intro u hu; split_ifs <;> simp_all +decide [ eq_comm ] ;
          intro a ha hua; split_ifs <;> simp_all +decide [ eq_comm ] ;
        · simp_all +decide [ Finset.not_nonempty_iff_eq_empty ];
          exact ⟨ fun _ => Classical.choose ( Finset.card_pos.mp ( pos_of_gt ( lt_of_lt_of_le ( Fintype.card_pos_iff.mpr ⟨ v ⟩ ) ( hL v ) ) ) ), Classical.choose_spec ( Finset.card_pos.mp ( pos_of_gt ( lt_of_lt_of_le ( Fintype.card_pos_iff.mpr ⟨ v ⟩ ) ( hL v ) ) ) ) ⟩;
    by_cases hV : Nonempty V;
    · exact Exists.imp ( fun g hg v => by simpa using hg v ( Finset.mem_univ v ) ) ( h_distinct_colors Finset.univ ⟨ hV.some, Finset.mem_univ _ ⟩ );
    · aesop;
  exact ⟨ g, fun v => hg v |>.1, fun u v huv => hg v |>.2 u ( by rintro rfl; exact G.loopless _ huv ) ⟩

/-
If every vertex has a list of size at least |V|, we can pick a distinct element from each list.
-/
lemma exists_injective_forall_mem {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (L : α → Finset β) (h : ∀ a, (L a).card ≥ Fintype.card α) :
    ∃ f : α → β, Function.Injective f ∧ ∀ a, f a ∈ L a := by
  -- We prove this by induction on the size of the universe.
  -- Or simply by Hall's Marriage Theorem, which is satisfied because |Union L(S)| >= |L(v)| >= |V| >= |S|.
  -- However, a direct greedy construction is easier for the ATP if Hall is not easily available.
  -- Let's try to let the ATP find it.
  have h_inj : ∃ f : α → β, Function.Injective f ∧ ∀ a, f a ∈ L a := by
    have h_exists_f : ∀ S : Finset α, ∃ f : S → β, Function.Injective f ∧ ∀ a : S, f a ∈ L a := by
      intro S;
      induction' S using Finset.induction with a S haS ih;
      · simp +decide [ Function.Injective ];
      · -- By the induction hypothesis, there exists an injective function $f : S \to \beta$ such that $f(s) \in L(s)$ for all $s \in S$.
        obtain ⟨f, hf_inj, hf⟩ := ih;
        -- Since $L(a)$ has at least $|α|$ elements and $S$ has $|S|$ elements, there must be some element in $L(a)$ that is not used by $f$.
        obtain ⟨b, hb⟩ : ∃ b ∈ L a, b ∉ Finset.image f Finset.univ := by
          have h_card : (L a).card > (Finset.image f Finset.univ).card := by
            rw [ Finset.card_image_of_injective _ hf_inj ];
            exact lt_of_lt_of_le ( by simpa [ Finset.card_univ ] using Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.subset_univ S, by aesop ⟩ ) ) ( h a );
          exact Finset.not_subset.mp fun h => h_card.not_le <| Finset.card_le_card h;
        refine' ⟨ fun x => if hx : x.val = a then b else f ⟨ x.val, _ ⟩, _, _ ⟩ <;> simp_all +decide [ Function.Injective ];
        exact Finset.mem_of_mem_insert_of_ne x.2 hx;
        · intro x hx y hy hxy; split_ifs at hxy <;> simp_all +decide ;
          exact hf_inj _ ( hx.resolve_left ‹_› ) _ ( hy.resolve_left ‹_› ) hxy;
        · aesop
    obtain ⟨ f, hf₁, hf₂ ⟩ := h_exists_f Finset.univ;
    exact ⟨ fun a => f ⟨ a, Finset.mem_univ a ⟩, fun a b hab => by simpa using hf₁ hab, fun a => hf₂ ⟨ a, Finset.mem_univ a ⟩ ⟩;
  exact h_inj

end AristotleLemmas

theorem bipartite_list_chromatic_unbounded :
    ∀ k : ℕ, ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
      IsBipartite G ∧ listChromaticNumber G > k := by
  intro k;
  -- By `MyGraph_bipartite`, G is bipartite.
  obtain ⟨G, hG⟩ : ∃ G : SimpleGraph (MyVertices k ⊕ MyVertices k), IsBipartite G ∧ ¬ IsKListColorable G (k + 1) := by
    exact ⟨ _, MyGraph_bipartite k, MyGraph_not_colorable k ⟩;
  refine' ⟨ _, _, _, G, hG.1, Nat.lt_of_not_ge fun h => hG.2 _ ⟩;
  convert IsKListColorable_mono G ( show Erdos629.listChromaticNumber G ≤ k + 1 from by linarith ) _;
  convert Nat.sInf_mem _;
  exact ⟨ _, IsKListColorable_card G ⟩

/- ## Part III: The Function n(k) -/

/-- n(k) = minimal vertex count of bipartite G with χ_L(G) > k. -/
noncomputable def n (k : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
    Fintype.card V = m ∧ IsBipartite G ∧ listChromaticNumber G > k}

/- n(k) is well-defined (the infimum exists). -/
noncomputable section AristotleLemmas

/-
If a graph has 0 vertices, its list chromatic number is 0.
-/
lemma Erdos629.listChromaticNumber_eq_zero_of_card_eq_zero {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (h : Fintype.card V = 0) : Erdos629.listChromaticNumber G = 0 := by
      rw [ Fintype.card_eq_zero_iff ] at h;
      refine' le_antisymm ( csInf_le _ _ ) ( le_csInf _ _ );
      · exact ⟨ 0, fun k hk => Nat.zero_le _ ⟩;
      · intro C _ _ L hL;
        exact ⟨ fun v => h.elim v, fun v => h.elim v, fun u v huv => h.elim u ⟩;
      · refine' ⟨ 0, _ ⟩;
        intro C _ _ L hL;
        exact ⟨ fun v => h.elim v, fun v => h.elim v, fun u v huv => h.elim u ⟩;
      · exact fun _ _ => Nat.zero_le _

end AristotleLemmas

theorem n_well_defined (k : ℕ) : n k > 0 := by
  refine' lt_of_le_of_ne _ ( Ne.symm _ );
  · exact Nat.zero_le _;
  · intro h;
    -- By definition of $n(k)$, there exists a bipartite graph $G$ with $n(k)$ vertices such that $\chi_L(G) > k$.
    obtain ⟨V, hV_fintype, hV_decidable, G, hG_bipartite, hG_card⟩ : ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V), Fintype.card V = 0 ∧ Erdos629.IsBipartite G ∧ Erdos629.listChromaticNumber G > k := by
      convert Nat.sInf_mem ( show { m : ℕ | ∃ ( V : Type ) ( _ : Fintype V ) ( _ : DecidableEq V ) ( G : SimpleGraph V ), Fintype.card V = m ∧ Erdos629.IsBipartite G ∧ Erdos629.listChromaticNumber G > k }.Nonempty from ?_ ) using 1;
      · exact?;
      · have := bipartite_list_chromatic_unbounded k;
        exact ⟨ _, ⟨ this.choose, this.choose_spec.choose, this.choose_spec.choose_spec.choose, this.choose_spec.choose_spec.choose_spec.choose, rfl, this.choose_spec.choose_spec.choose_spec.choose_spec ⟩ ⟩;
    have h_empty : Erdos629.listChromaticNumber G = 0 := by
      exact?;
    linarith

/-- n is monotone: larger k requires more vertices. -/
theorem n_mono {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) : n k₁ ≤ n k₂ := by
  refine' le_csInf _ _;
  · exact Exists.elim ( bipartite_list_chromatic_unbounded k₂ ) fun V hV => Exists.elim hV fun _ hV => Exists.elim hV fun _ hV => Exists.elim hV fun G hG => ⟨ _, ⟨ V, by infer_instance, by infer_instance, G, rfl, hG.1, hG.2 ⟩ ⟩;
  · exact fun m hm => Nat.sInf_le <| by obtain ⟨ V, hV₁, hV₂, G, hG₁, hG₂, hG₃ ⟩ := hm; exact ⟨ V, hV₁, hV₂, G, hG₁, hG₂, by linarith ⟩ ;

/- ## Part IV: Exact Values -/

/- Erdős-Rubin-Taylor (1980): n(2) = 6. -/
noncomputable section AristotleLemmas

open SimpleGraph Finset

def Erdos629.K33 : SimpleGraph (Fin 6) := SimpleGraph.fromRel (fun u v => (u < 3 ∧ 3 ≤ v) ∨ (3 ≤ u ∧ v < 3))

theorem Erdos629.K33_is_bipartite : Erdos629.IsBipartite Erdos629.K33 := by
  -- Show that K33 is bipartite by defining the coloring function.
  use fun v => if v.val < 3 then 0 else 1;
  intro u v huv; fin_cases u <;> fin_cases v <;> simp +decide at huv ⊢;
  all_goals cases huv;
  all_goals simp_all +decide ;

/-
Defines a list assignment for K3,3 where each vertex gets a specific pair of colors from {0, 1, 2}. This will serve as a counterexample to 2-list-colorability.
-/
open SimpleGraph Finset

def Erdos629.K33_bad_L : Erdos629.ColorListAssignment (Fin 6) (Fin 3) :=
  fun v =>
    if v.val = 0 then {0, 1}
    else if v.val = 1 then {0, 2}
    else if v.val = 2 then {1, 2}
    else if v.val = 3 then {0, 1}
    else if v.val = 4 then {0, 2}
    else {1, 2}

open SimpleGraph Finset

theorem Erdos629.K33_bad_L_card (v : Fin 6) : (Erdos629.K33_bad_L v).card ≥ 2 := by
  fin_cases v <;> simp +decide [ Erdos629.Erdos629.K33_bad_L ]

open SimpleGraph Finset

theorem Erdos629.K33_not_colorable_with_bad_L :
    ¬ ∃ f : Fin 6 → Fin 3, Erdos629.RespectsLists Erdos629.K33_bad_L f ∧ Erdos629.IsProperColoring Erdos629.K33 f := by
      simp +zetaDelta at *;
      intro x hx₁ hx₂; unfold Erdos629.IsProperColoring at hx₂; unfold Erdos629.RespectsLists at hx₁; simp_all +decide [ Finset.ext_iff ] ;
      simp_all +decide [ Fin.forall_fin_succ, Erdos629.Erdos629.K33, Erdos629.Erdos629.K33_bad_L, SimpleGraph.adj_comm ];
      grind +ring

open SimpleGraph Finset

theorem Erdos629.K33_not_2_list_colorable : ¬ Erdos629.IsKListColorable Erdos629.K33 2 := by
  unfold Erdos629.IsKListColorable;
  simp +zetaDelta at *;
  use Fin 3;
  exact ⟨ ⟨ inferInstance ⟩, Erdos629.K33_bad_L, Erdos629.K33_bad_L_card, fun f hf₁ hf₂ => Erdos629.K33_not_colorable_with_bad_L ⟨ f, hf₁, hf₂ ⟩ ⟩

open SimpleGraph Finset

theorem Erdos629.bipartite_one_part_le_1 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (f : V → Fin 2) (hf : Erdos629.IsProperColoring G f)
    (hA : (Finset.univ.filter (fun v => f v = 0)).card ≤ 1) :
    Erdos629.IsKListColorable G 2 := by
      -- If A is empty, then all vertices are in B. Since f is proper, there are no edges within B. So G is empty.
      by_cases hA_empty : Finset.card (Finset.filter (fun v => f v = 0) Finset.univ) = 0;
      · -- Since A is empty, all vertices are in B. Since f is proper, there are no edges within B. So G is empty.
        have hG_empty : ∀ u v, G.Adj u v → False := by
          intro u v huv; have := hf u v huv; simp_all +decide [ Fin.forall_fin_two ] ;
          grind;
        intro C _ _ L hL;
        exact ⟨ fun v => Classical.choose ( Finset.card_pos.mp ( lt_of_lt_of_le zero_lt_two ( hL v ) ) ), fun v => Classical.choose_spec ( Finset.card_pos.mp ( lt_of_lt_of_le zero_lt_two ( hL v ) ) ), fun u v huv => False.elim ( hG_empty u v huv ) ⟩;
      · -- If A is non-empty, then there is exactly one vertex u in A.
        obtain ⟨u, hu⟩ : ∃ u : V, (Finset.filter (fun v => f v = 0) Finset.univ) = {u} := by
          exact Finset.card_eq_one.1 ( le_antisymm hA ( Nat.pos_of_ne_zero hA_empty ) );
        -- For any 2-list assignment L, we can choose a color c from L(u) and assign it to u.
        intro C _ _ L hL
        obtain ⟨c, hc⟩ : ∃ c : C, c ∈ L u := by
          exact Finset.card_pos.mp ( pos_of_gt ( hL u ) );
        -- For any v in B, v is only adjacent to u (if at all).
        -- So v cannot have color c.
        -- Since |L(v)| >= 2, L(v) \ {c} is non-empty.
        -- Pick any color from L(v) \ {c} for v.
        obtain ⟨g, hg⟩ : ∃ g : V → C, (∀ v, g v ∈ L v) ∧ (∀ v, f v = 0 → g v = c) ∧ (∀ v, f v ≠ 0 → g v ≠ c) := by
          have h_exists_g : ∀ v, f v ≠ 0 → ∃ g : C, g ∈ L v ∧ g ≠ c := by
            exact?;
          choose! g hg₁ hg₂ using h_exists_g;
          use fun v => if hv : f v = 0 then c else g v hv;
          simp_all +decide [ Finset.ext_iff ];
          grind;
        refine' ⟨ g, hg.1, fun u v huv => _ ⟩;
        cases Fin.exists_fin_two.mp ⟨ f u, rfl ⟩ <;> cases Fin.exists_fin_two.mp ⟨ f v, rfl ⟩ <;> simp_all +decide;
        · exact absurd ( hf u v huv ) ( by simp +decide [ * ] );
        · exact Ne.symm ( hg.2.2 v ( by simp +decide [ * ] ) );
        · exact absurd ( hf u v huv ) ( by simp +decide [ * ] )

open SimpleGraph Finset

theorem Erdos629.exists_valid_pair_of_colors {C : Type*} [DecidableEq C]
    (Su Sw : Finset C) (h_disjoint : Disjoint Su Sw)
    (h_card_u : Su.card ≥ 2) (h_card_w : Sw.card ≥ 2)
    (Bad : Finset (Finset C)) (h_card_Bad : Bad.card ≤ 3) :
    ∃ cu ∈ Su, ∃ cw ∈ Sw, {cu, cw} ∉ Bad := by
      by_contra h_card_Bad;
      -- Since there are at least 4 pairs (x, y) with x in Su and y in Sw, and at most 3 bad pairs, there must be at least one pair (x, y) such that {x, y} is not in Bad.
      have h_card_pairs : Finset.card (Finset.image (fun (xy : C × C) => {xy.1, xy.2} : C × C → Finset C) (Finset.product Su Sw)) ≥ 4 := by
        erw [ Finset.card_image_of_injOn, Finset.card_product ];
        · nlinarith;
        · intro x hx y hy; simp_all +decide [ Finset.disjoint_left, Set.InjOn ] ;
          intro h; rw [ Finset.ext_iff ] at h; have := h x.1; have := h x.2; have := h y.1; have := h y.2; aesop;
      exact h_card_pairs.not_lt ( lt_of_le_of_lt ( Finset.card_le_card ( Finset.image_subset_iff.mpr fun xy hxy => show { xy.1, xy.2 } ∈ Bad from by aesop ) ) ( by linarith ) )

open SimpleGraph Finset

theorem Erdos629.bipartite_part_2_le_3_case_inter_nonempty {V : Type*} [Fintype V] [DecidableEq V]
    {C : Type*} [Fintype C] [DecidableEq C]
    (G : SimpleGraph V) (f : V → Fin 2) (hf : Erdos629.IsProperColoring G f)
    (u w : V) (hu : f u = 0) (hw : f w = 0) (h_ne : u ≠ w)
    (hA_eq : (Finset.univ.filter (fun v => f v = 0)) = {u, w})
    (L : Erdos629.ColorListAssignment V C)
    (hL : ∀ v, (L v).card ≥ 2)
    (h_inter : (L u ∩ L w).Nonempty) :
    ∃ g : V → C, Erdos629.RespectsLists L g ∧ Erdos629.IsProperColoring G g := by
      obtain ⟨ c, hc ⟩ := h_inter;
      -- Define g such that g(u) = g(w) = c and for other vertices v, g(v) is a color from L(v) different from c.
      obtain ⟨g, hg⟩ : ∃ g : V → C, (∀ v, g v ∈ L v) ∧ (∀ v, f v = 1 → g v ≠ c) ∧ g u = c ∧ g w = c := by
        have h_colorable : ∀ v, f v = 1 → ∃ g : C, g ∈ L v ∧ g ≠ c := by
          exact fun v hv => Finset.exists_mem_ne ( lt_of_lt_of_le ( by decide ) ( hL v ) ) c;
        choose! g hg₁ hg₂ using h_colorable;
        refine' ⟨ fun v => if hv : f v = 1 then g v hv else if hv' : v = u then c else if hv'' : v = w then c else Classical.choose ( Finset.card_pos.mp ( pos_of_gt ( hL v ) ) ), _, _, _, _ ⟩ <;> simp_all +decide;
        intro v; split_ifs <;> simp_all +decide [ Finset.ext_iff ] ;
        exact Classical.choose_spec ( Finset.card_pos.mp ( pos_of_gt ( hL v ) ) );
      refine' ⟨ g, hg.1, _ ⟩;
      intro v w hvw; have := hf v w hvw; simp_all +decide [ Finset.ext_iff ] ;
      grind

open SimpleGraph Finset Classical

theorem Erdos629.bipartite_part_2_le_3_case_disjoint {V : Type*} [Fintype V] [DecidableEq V]
    {C : Type*} [Fintype C] [DecidableEq C]
    (G : SimpleGraph V) (f : V → Fin 2) (hf : Erdos629.IsProperColoring G f)
    (u w : V) (hu : f u = 0) (hw : f w = 0) (h_ne : u ≠ w)
    (hA_eq : (Finset.univ.filter (fun v => f v = 0)) = {u, w})
    (hB_card : (Finset.univ.filter (fun v => f v = 1)).card ≤ 3)
    (L : Erdos629.ColorListAssignment V C)
    (hL : ∀ v, (L v).card ≥ 2)
    (h_disj : Disjoint (L u) (L w)) :
    ∃ g : V → C, Erdos629.RespectsLists L g ∧ Erdos629.IsProperColoring G g := by
      -- By `Erdos629.exists_valid_pair_of_colors`, there exist `cu` in `L u` and `cw` in `L w` such that `{cu, cw}` is not in `Bad`.
      obtain ⟨cu, cw, hcu, hcuw⟩ : ∃ cu ∈ L u, ∃ cw ∈ L w, ¬({cu, cw} ∈ (Finset.image (fun v => L v) (Finset.filter (fun v => f v = 1) Finset.univ)) ∪ Finset.image (fun v => L v) (Finset.filter (fun v => f v = 1) Finset.univ)) := by
        convert Erdos629.exists_valid_pair_of_colors ( L u ) ( L w ) h_disj ( hL u ) ( hL w ) ( Finset.image ( fun v => L v ) ( Finset.filter ( fun v => f v = 1 ) Finset.univ ) ∪ Finset.image ( fun v => L v ) ( Finset.filter ( fun v => f v = 1 ) Finset.univ ) ) _ using 1;
        grind;
      -- For each vertex $v$ in $B$, if $v$ is adjacent to both $u$ and $w$, then $L(v)$ must contain both $cu$ and $hcu$.
      have h_adj : ∀ v ∈ Finset.filter (fun v => f v = 1) Finset.univ, ¬(L v ⊆ {cu, hcu}) := by
        intro v hv h; specialize hL v; simp_all +decide [ Finset.subset_iff ] ;
        have := Finset.one_lt_card.mp hL; obtain ⟨ x, hx, y, hy, hxy ⟩ := this; simp_all +decide [ Finset.disjoint_left ] ;
        grind +ring;
      -- For each vertex $v$ in $B$, if $v$ is adjacent to both $u$ and $w$, then $L(v)$ must contain at least one color different from $cu$ and $hcu$.
      have h_adj_colors : ∀ v ∈ Finset.filter (fun v => f v = 1) Finset.univ, ∃ c ∈ L v, c ≠ cu ∧ c ≠ hcu := by
        grind;
      -- Define the coloring function $g$ such that $g(u) = cu$, $g(w) = hcu$, and for each $v \in B$, $g(v)$ is a color in $L(v)$ different from $cu$ and $hcu$.
      obtain ⟨g, hg⟩ : ∃ g : V → C, (∀ v, g v ∈ L v) ∧ (∀ v ∈ Finset.filter (fun v => f v = 1) Finset.univ, g v ≠ cu ∧ g v ≠ hcu) ∧ g u = cu ∧ g w = hcu := by
        choose! g hg₁ hg₂ hg₃ using h_adj_colors;
        use fun v => if hv : v ∈ Finset.filter (fun v => f v = 1) Finset.univ then g v hv else if v = u then cu else if v = w then hcu else Classical.choose (Finset.card_pos.mp (by linarith [hL v]));
        simp_all +decide [ Finset.ext_iff ];
        grind;
      refine' ⟨ g, hg.1, _ ⟩;
      intro v w hvw; have := hf v w hvw; simp_all +decide [ Finset.ext_iff ] ;
      grind

open SimpleGraph Finset Classical

theorem Erdos629.bipartite_part_2_le_3_is_2_list_colorable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (f : V → Fin 2) (hf : Erdos629.IsProperColoring G f)
    (hA : (Finset.univ.filter (fun v => f v = 0)).card = 2)
    (hB : (Finset.univ.filter (fun v => f v = 1)).card ≤ 3) :
    Erdos629.IsKListColorable G 2 := by
  intro C _ _ L hL
  let A := Finset.univ.filter (fun v => f v = 0)
  obtain ⟨u, w, hu, hw, h_ne, hA_eq⟩ : ∃ u w, f u = 0 ∧ f w = 0 ∧ u ≠ w ∧ A = {u, w} := by
    have := Finset.card_eq_two.mp hA;
    obtain ⟨ u, w, hne, h ⟩ := this; use u, w; simp_all +decide [ Finset.ext_iff ] ;
    aesop
  by_cases h_inter : (L u ∩ L w).Nonempty
  · exact Erdos629.bipartite_part_2_le_3_case_inter_nonempty G f hf u w hu hw h_ne hA_eq L hL h_inter
  · have h_disj : Disjoint (L u) (L w) := by
      exact Finset.disjoint_iff_inter_eq_empty.mpr ( by simpa [ Finset.ext_iff ] using h_inter )
    exact Erdos629.bipartite_part_2_le_3_case_disjoint G f hf u w hu hw h_ne hA_eq hB L hL h_disj

open SimpleGraph Finset

theorem Erdos629.bipartite_small_is_2_list_colorable' {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (h_bip : Erdos629.IsBipartite G) (h_card : Fintype.card V < 6) :
    Erdos629.IsKListColorable G 2 := by
      -- By assumption, $G$ is bipartite, so we can find a proper 2-coloring $f$.
      obtain ⟨f, hf⟩ := h_bip;
      -- Since $G$ is bipartite, we can assume without loss of generality that $|A| \leq |B|$.
      suffices h_wlog : ∀ (f : V → Fin 2), Erdos629.IsProperColoring G f → (Finset.univ.filter (fun v => f v = 0)).card ≤ (Finset.univ.filter (fun v => f v = 1)).card → Erdos629.IsKListColorable G 2 by
        by_cases hA : (Finset.univ.filter (fun v => f v = 0)).card ≤ (Finset.univ.filter (fun v => f v = 1)).card;
        · exact h_wlog f hf hA;
        · convert h_wlog ( fun v => 1 - f v ) _ _ using 1;
          · intro u v huv; specialize hf u v huv; aesop;
          · convert le_of_not_ge hA using 1;
            · exact congr_arg Finset.card ( Finset.filter_congr fun x _ => by cases Fin.exists_fin_two.mp ⟨ f x, rfl ⟩ <;> simp +decide [ * ] );
            · exact congr_arg Finset.card ( Finset.ext fun x => by cases Fin.exists_fin_two.mp ⟨ f x, rfl ⟩ <;> simp +decide [ * ] );
      intro f hf hA_le_B
      by_cases hA : (Finset.univ.filter (fun v => f v = 0)).card ≤ 1;
      · exact Erdos629.bipartite_one_part_le_1 G f hf hA;
      · convert Erdos629.bipartite_part_2_le_3_is_2_list_colorable G f hf _ _;
        · have h_card_A : (Finset.univ.filter (fun v => f v = 0)).card + (Finset.univ.filter (fun v => f v = 1)).card = Fintype.card V := by
            rw [ Fintype.card_eq_sum_ones, Finset.card_filter, Finset.card_filter ];
            simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_congr rfl fun x _ => by rcases f x with ( _ | _ | x ) <;> trivial;
          grind;
        · have h_card_sum : (Finset.univ.filter (fun v => f v = 0)).card + (Finset.univ.filter (fun v => f v = 1)).card = Fintype.card V := by
            rw [ Fintype.card_eq_sum_ones, Finset.card_filter, Finset.card_filter ];
            simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_congr rfl fun x _ => by rcases f x with ( _ | _ | x ) <;> trivial;
          grind

open SimpleGraph Finset

theorem Erdos629.bipartite_small_is_2_list_colorable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (h_bip : Erdos629.IsBipartite G) (h_card : Fintype.card V < 6) :
    Erdos629.IsKListColorable G 2 := by
      exact?

end AristotleLemmas

theorem n_2_eq_6 : n 2 = 6 := by
  refine' le_antisymm ( csInf_le _ _ ) ( le_csInf _ _ );
  · exact ⟨ 0, fun m hm => Nat.zero_le _ ⟩;
  · use Fin 6, inferInstance, inferInstance, Erdos629.K33, by decide, Erdos629.K33_is_bipartite, ?_;
    refine' lt_of_lt_of_le _ ( le_csInf _ _ );
    exact Nat.lt_succ_self _;
    · use 6;
      intro C _ _ L hL;
      -- Since $L v$ has at least 6 elements for each $v$, we can choose a distinct color for each vertex.
      have h_choose_colors : ∃ f : Fin 6 → C, ∀ v, f v ∈ L v ∧ ∀ u v, u ≠ v → f u ≠ f v := by
        have h_choose_colors : ∀ (s : Finset (Fin 6)), ∃ f : Fin 6 → C, ∀ v ∈ s, f v ∈ L v ∧ ∀ u v, u ∈ s → v ∈ s → u ≠ v → f u ≠ f v := by
          intro s;
          induction' s using Finset.induction with v s ih;
          · exact ⟨ fun _ => Classical.choose ( Finset.card_pos.mp ( by linarith [ hL 0 ] ) ), by simp +decide ⟩;
          · obtain ⟨ f, hf ⟩ := ‹_›;
            -- Choose a color for $v$ that is not in the image of $f$ on $s$.
            obtain ⟨c, hc⟩ : ∃ c ∈ L v, c ∉ Finset.image f s := by
              have h_card : (L v).card > Finset.card (Finset.image f s) := by
                exact lt_of_lt_of_le ( Finset.card_image_le.trans_lt ( by simpa using Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.subset_univ s, by aesop_cat ⟩ ) ) ) ( hL v );
              exact Finset.not_subset.mp fun h => h_card.not_le <| Finset.card_le_card h;
            use fun u => if u = v then c else f u;
            simp_all +decide [ Finset.mem_image ];
            -- By combining the results from hc and hf, we can conclude that the function f satisfies the required conditions.
            apply And.intro;
            · intro u v hu hv huv; split_ifs <;> simp_all +decide ;
              · exact Ne.symm ( hc.2 v hv );
              · exact hf u hu |>.2 u v hu hv huv;
            · intro u hu; split_ifs <;> simp_all +decide ;
              intro u v hu hv huv; split_ifs <;> simp_all +decide ;
              · exact Ne.symm ( hc.2 _ hv );
              · exact hf u hu |>.2 u v hu hv huv;
        exact Exists.elim ( h_choose_colors Finset.univ ) fun f hf => ⟨ f, fun v => ⟨ hf v ( Finset.mem_univ v ) |>.1, fun u v huv => hf u ( Finset.mem_univ u ) |>.2 u v ( Finset.mem_univ u ) ( Finset.mem_univ v ) huv ⟩ ⟩;
      obtain ⟨ f, hf ⟩ := h_choose_colors;
      refine' ⟨ f, _, _ ⟩ <;> simp_all +decide [ Erdos629.RespectsLists, Erdos629.IsProperColoring ];
      exact fun u v huv => hf u |>.2 u v ( by rintro rfl; exact huv.ne rfl );
    · intro k hk; contrapose! hk; interval_cases k <;> simp_all +decide ;
      · intro h; have := h ( Fin 0 ) ; simp_all +decide ;
        exact this fun _ => ∅;
      · intro h; have := h ( Fin 2 ) ; simp_all +decide [ Erdos629.IsKListColorable ] ;
        specialize h ( Fin 2 ) ( fun v => if v = 0 then { 0 } else if v = 1 then { 1 } else if v = 2 then { 0 } else if v = 3 then { 1 } else if v = 4 then { 0 } else { 1 } ) ; simp_all +decide [ Erdos629.RespectsLists, Erdos629.IsProperColoring ];
        simp_all +decide [ Fin.forall_fin_succ, Erdos629.Erdos629.K33 ];
      · exact?;
  · -- Let's choose the graph $K_{3,3}$ which is bipartite and has 6 vertices.
    use 6;
    use Fin 6, inferInstance, inferInstance, Erdos629.K33, by decide, Erdos629.K33_is_bipartite, ?_;
    refine' lt_of_lt_of_le _ ( le_csInf _ _ );
    exact Nat.lt_succ_self _;
    · use 6;
      intro C _ _ L hL;
      -- Since $L v$ has at least 6 elements for each $v$, we can choose a distinct color for each vertex.
      have h_choose_colors : ∃ f : Fin 6 → C, ∀ v, f v ∈ L v ∧ ∀ u v, u ≠ v → f u ≠ f v := by
        have h_choose_colors : ∀ (s : Finset (Fin 6)), ∃ f : Fin 6 → C, ∀ v ∈ s, f v ∈ L v ∧ ∀ u v, u ∈ s → v ∈ s → u ≠ v → f u ≠ f v := by
          intro s;
          induction' s using Finset.induction with v s ih;
          · exact ⟨ fun _ => Classical.choose ( Finset.card_pos.mp ( by linarith [ hL 0 ] ) ), by simp +decide ⟩;
          · obtain ⟨ f, hf ⟩ := ‹_›;
            -- Choose a color for $v$ that is not in the image of $f$ on $s$.
            obtain ⟨c, hc⟩ : ∃ c ∈ L v, c ∉ Finset.image f s := by
              have h_card : (L v).card > Finset.card (Finset.image f s) := by
                exact lt_of_lt_of_le ( Finset.card_image_le.trans_lt ( by simpa using Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.subset_univ s, by aesop_cat ⟩ ) ) ) ( hL v );
              exact Finset.not_subset.mp fun h => h_card.not_le <| Finset.card_le_card h;
            use fun u => if u = v then c else f u;
            simp_all +decide [ Finset.mem_image ];
            -- By combining the results from hc and hf, we can conclude that the function f satisfies the required conditions.
            apply And.intro;
            · intro u v hu hv huv; split_ifs <;> simp_all +decide ;
              · exact Ne.symm ( hc.2 v hv );
              · exact hf u hu |>.2 u v hu hv huv;
            · intro u hu; split_ifs <;> simp_all +decide ;
              intro u v hu hv huv; split_ifs <;> simp_all +decide ;
              · exact Ne.symm ( hc.2 _ hv );
              · exact hf u hu |>.2 u v hu hv huv;
        exact Exists.elim ( h_choose_colors Finset.univ ) fun f hf => ⟨ f, fun v => ⟨ hf v ( Finset.mem_univ v ) |>.1, fun u v huv => hf u ( Finset.mem_univ u ) |>.2 u v ( Finset.mem_univ u ) ( Finset.mem_univ v ) huv ⟩ ⟩;
      obtain ⟨ f, hf ⟩ := h_choose_colors;
      refine' ⟨ f, _, _ ⟩ <;> simp_all +decide [ Erdos629.RespectsLists, Erdos629.IsProperColoring ];
      exact fun u v huv => hf u |>.2 u v ( by rintro rfl; exact huv.ne rfl );
    · intro k hk; contrapose! hk; interval_cases k <;> simp_all +decide ;
      · intro h; have := h ( Fin 0 ) ; simp_all +decide ;
        exact this fun _ => ∅;
      · intro h; have := h ( Fin 2 ) ; simp_all +decide [ Erdos629.IsKListColorable ] ;
        specialize h ( Fin 2 ) ( fun v => if v = 0 then { 0 } else if v = 1 then { 1 } else if v = 2 then { 0 } else if v = 3 then { 1 } else if v = 4 then { 0 } else { 1 } ) ; simp_all +decide [ Erdos629.RespectsLists, Erdos629.IsProperColoring ];
        simp_all +decide [ Fin.forall_fin_succ, Erdos629.Erdos629.K33 ];
      · exact?;
  · rintro m ⟨ V, hV, x, G, h₁, h₂, h₃ ⟩;
    contrapose! h₃;
    refine' le_trans ( Nat.sInf_le _ ) _;
    exacts [ 2, by exact Erdos629.bipartite_small_is_2_list_colorable' G h₂ ( by linarith ), by norm_num ]

/- Aristotle failed to find a proof. -/
/-- Hanson-MacGillivray-Toft (1996): n(3) = 14. -/
theorem n_3_eq_14 : n 3 = 14 := by
  sorry

/- ## Part V: Original Bounds (Erdős-Rubin-Taylor 1980) -/

/- Original lower bound: 2^{k-1} < n(k). -/
noncomputable section AristotleLemmas

/-
If one part of a bipartite graph has size less than k, the graph is k-list-colorable.
-/
lemma bipartite_small_part_is_k_list_colorable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) (f : V → Fin 2) (hf : IsProperColoring G f)
    (i : Fin 2) (h_part_size : (Finset.univ.filter (fun v => f v = i)).card < k) :
    IsKListColorable G k := by
      -- Let A = {v | f v = i} and B = {v | f v != i}. Since f is a proper coloring, A and B are independent sets.
      set A : Finset V := Finset.filter (fun v => f v = i) Finset.univ
      set B : Finset V := Finset.filter (fun v => f v ≠ i) Finset.univ
      have hA_indep : ∀ v ∈ A, ∀ u ∈ A, ¬G.Adj v u := by
        intro v hv u hu; specialize hf v u; aesop;
      have hB_indep : ∀ v ∈ B, ∀ u ∈ B, ¬G.Adj v u := by
        intro v hv u hu huv; have := hf v u huv; simp_all +decide ;
        grind;
      -- For every v in A, choose an arbitrary color g(v) in L(v). This is possible since |L(v)| >= k >= 1 (assuming k>=1, but if k=0 then card < 0 is impossible).
      intro C _ _ L hL
      have hA_color : ∃ g : V → C, (∀ v ∈ A, g v ∈ L v) ∧ (∀ u ∈ B, (L u \ Finset.image g A).card ≥ 1) := by
        -- Since $|A| < k$, we can choose $k$ distinct colors for the vertices in $A$.
        obtain ⟨g, hg⟩ : ∃ g : V → C, (∀ v ∈ A, g v ∈ L v) ∧ (∀ u ∈ B, (Finset.image g A).card ≤ (L u).card - 1) := by
          have hA_color : ∃ g : V → C, (∀ v ∈ A, g v ∈ L v) ∧ (Finset.image g A).card ≤ (k - 1) := by
            have hA_color : ∃ g : V → C, (∀ v ∈ A, g v ∈ L v) ∧ (Finset.image g A).card ≤ A.card := by
              exact ⟨ fun v => if hv : v ∈ A then Classical.choose ( Finset.card_pos.mp ( by linarith [ hL v ] ) ) else Classical.choose ( Finset.card_pos.mp ( by linarith [ hL v ] ) ), fun v hv => by simpa [ hv ] using Classical.choose_spec ( Finset.card_pos.mp ( by linarith [ hL v ] ) ), Finset.card_image_le ⟩;
            exact ⟨ hA_color.choose, hA_color.choose_spec.1, le_trans hA_color.choose_spec.2 ( Nat.le_sub_one_of_lt h_part_size ) ⟩;
          exact ⟨ hA_color.choose, hA_color.choose_spec.1, fun u hu => le_trans hA_color.choose_spec.2 ( Nat.sub_le_sub_right ( hL u ) _ ) ⟩;
        refine' ⟨ g, hg.1, fun u hu => _ ⟩;
        grind;
      obtain ⟨ g, hg₁, hg₂ ⟩ := hA_color;
      -- For every u in B, choose an arbitrary color h(u) in L(u) \ S_u. This is possible since |L(u) \ S_u| >= 1.
      obtain ⟨ h, hh₁, hh₂ ⟩ : ∃ h : V → C, (∀ u ∈ B, h u ∈ L u) ∧ (∀ u ∈ B, h u ∉ Finset.image g A) := by
        have hh₁ : ∀ u ∈ B, ∃ c ∈ L u, c ∉ Finset.image g A := by
          exact fun u hu => by obtain ⟨ c, hc ⟩ := Finset.card_pos.mp ( hg₂ u hu ) ; exact ⟨ c, Finset.mem_sdiff.mp hc |>.1, Finset.mem_sdiff.mp hc |>.2 ⟩ ;
        choose! h hh₁ hh₂ using hh₁;
        exact ⟨ fun u => if hu : u ∈ B then h u hu else Classical.choose ( Finset.card_pos.mp ( by linarith [ hL u ] ) ), fun u hu => by simpa [ hu ] using hh₁ u hu, fun u hu => by simpa [ hu ] using hh₂ u hu ⟩;
      refine' ⟨ fun v => if v ∈ A then g v else h v, _, _ ⟩ <;> simp_all +decide [ Erdos629.RespectsLists, Erdos629.IsProperColoring ];
      · grind;
      · grind

/-
If a graph G has a vertex v with degree < k, and G-v is k-list-colorable, then G is k-list-colorable.
-/
lemma list_colorable_of_min_degree_lt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (v : V) (h_deg : G.degree v < k)
    (h_rest : IsKListColorable (G.induce {u | u ≠ v}) k) : IsKListColorable G k := by
      intro C _ _ L hL;
      -- By hypothesis, there exists a proper coloring $f'$ of $G - v$ using $k$ colors.
      obtain ⟨f', hf'_respects, hf'_proper⟩ : ∃ f' : {u : V | u ≠ v} → C, (∀ u : {u : V | u ≠ v}, f' u ∈ L u) ∧ (∀ u v' : {u : V | u ≠ v}, G.Adj (↑u) (↑v') → f' u ≠ f' v') := by
        rcases h_rest C ( fun u => L u ) ( fun u => hL u ) with ⟨ f', hf'_respects, hf'_proper ⟩ ; use f' ; aesop;
      -- Choose a color $c$ for $v$ that is not used by its neighbors in $G - v$.
      obtain ⟨c, hc⟩ : ∃ c ∈ L v, ∀ u : {u : V | u ≠ v}, G.Adj v u → f' u ≠ c := by
        have h_card : (Finset.image f' (Finset.filter (fun u : {u : V | u ≠ v} => G.Adj v u) Finset.univ)).card ≤ G.degree v := by
          refine' le_trans ( Finset.card_image_le ) _;
          rw [ ← Finset.card_image_of_injective _ Subtype.coe_injective ];
          exact Finset.card_le_card ( show Finset.image ( fun a : { x : V // x ∈ { u : V | u ≠ v } } => ( a : V ) ) ( Finset.filter ( fun u : { x : V // x ∈ { u : V | u ≠ v } } => G.Adj v ( u : V ) ) Finset.univ ) ⊆ G.neighborFinset v from fun x hx => by aesop );
        have h_card : (Finset.image f' (Finset.filter (fun u : {u : V | u ≠ v} => G.Adj v u) Finset.univ)).card < (L v).card := by
          exact lt_of_le_of_lt h_card ( lt_of_lt_of_le h_deg ( hL v ) );
        contrapose! h_card;
        exact Finset.card_le_card fun x hx => by obtain ⟨ u, hu, rfl ⟩ := h_card x hx; exact Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hu ⟩ ) ;
      refine' ⟨ fun u => if hu : u = v then c else f' ⟨ u, hu ⟩, _, _ ⟩ <;> simp_all +decide [ Erdos629.RespectsLists, Erdos629.IsProperColoring ];
      · grind;
      · intro u v_1 huv; split_ifs <;> simp_all +decide [ SimpleGraph.adj_comm ] ;
        exact Ne.symm ( hc.2 _ ‹_› huv )

/-
If G is a subgraph of H and H is k-list-colorable, then G is k-list-colorable.
-/
lemma subgraph_respects_list_coloring {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) (h : G ≤ H) (k : ℕ) (hH : IsKListColorable H k) :
    IsKListColorable G k := by
      intro C _ _ L hL;
      obtain ⟨ f, hf₁, hf₂ ⟩ := hH C L hL;
      exact ⟨ f, hf₁, fun u v huv => hf₂ u v ( h huv ) ⟩

/-
If |A| + |B| < 2^k, there exists a partition of colors C into C0 and C1 such that every v in A has a color in C0 and every v in B has a color in C1.
-/
lemma bipartite_list_coloring_probability_bound {V : Type*} {C : Type*} [Fintype C] [DecidableEq C]
    (L : V → Finset C) (k : ℕ) (hL : ∀ v, (L v).card ≥ k)
    (A B : Finset V) (hV : A.card + B.card < 2^k) :
    ∃ (χ : C → Fin 2), (∀ v ∈ A, ∃ c ∈ L v, χ c = 0) ∧ (∀ v ∈ B, ∃ c ∈ L v, χ c = 1) := by
      by_contra! h_contra;
      -- The total number of bad functions is at most ∑_{v ∈ A} |Bad(v)| + ∑_{v ∈ B} |Bad(v)| ≤ (|A| + |B|) * 2^(|C| - k).
      have h_bad_functions : (∑ v ∈ A, Finset.card (Finset.filter (fun χ : C → Fin 2 => ∀ c ∈ L v, χ c = 1) Finset.univ)) + (∑ v ∈ B, Finset.card (Finset.filter (fun χ : C → Fin 2 => ∀ c ∈ L v, χ c = 0) Finset.univ)) ≤ (A.card + B.card) * 2 ^ (Fintype.card C - k) := by
        have h_bad_functions : ∀ v ∈ A, Finset.card (Finset.filter (fun χ : C → Fin 2 => ∀ c ∈ L v, χ c = 1) Finset.univ) ≤ 2 ^ (Fintype.card C - k) := by
          intro v hv
          have h_bad_A : Finset.card (Finset.filter (fun χ : C → Fin 2 => ∀ c ∈ L v, χ c = 1) Finset.univ) ≤ 2 ^ (Fintype.card C - (L v).card) := by
            -- The set of functions from $C \setminus L(v)$ to $\{0, 1\}$ has cardinality $2^{|C \setminus L(v)|}$.
            have h_card_C_minus_Lv : Finset.card (Finset.image (fun χ : C → Fin 2 => fun c => χ c) (Finset.filter (fun χ => ∀ c ∈ L v, χ c = 1) Finset.univ)) ≤ Finset.card (Finset.image (fun χ : { c : C // c ∉ L v } → Fin 2 => fun c => if hc : c ∈ L v then 1 else χ ⟨c, hc⟩) (Finset.univ : Finset ({ c : C // c ∉ L v } → Fin 2))) := by
              refine' Finset.card_le_card _;
              simp +decide [ Finset.subset_iff ];
              exact fun x hx => ⟨ fun ⟨ c, hc ⟩ => x c, funext fun c => by by_cases hc : c ∈ L v <;> simp +decide [ hx, hc ] ⟩;
            convert h_card_C_minus_Lv.trans ( Finset.card_image_le ) using 1;
            · rw [ Finset.card_image_of_injective _ fun x y hxy => by simpa using hxy ];
            · simp +decide [ Finset.card_univ ];
          exact h_bad_A.trans ( pow_le_pow_right₀ ( by decide ) ( Nat.sub_le_sub_left ( hL v ) _ ) );
        have h_bad_functions_B : ∀ v ∈ B, Finset.card (Finset.filter (fun χ : C → Fin 2 => ∀ c ∈ L v, χ c = 0) Finset.univ) ≤ 2 ^ (Fintype.card C - k) := by
          intro v hv
          have h_card_B_v : Finset.card (Finset.filter (fun χ : C → Fin 2 => ∀ c ∈ L v, χ c = 0) Finset.univ) ≤ 2 ^ (Fintype.card C - (L v).card) := by
            have h_card_B_v : Finset.card (Finset.filter (fun χ : C → Fin 2 => ∀ c ∈ L v, χ c = 0) Finset.univ) ≤ Finset.card (Finset.image (fun χ : { c : C // c ∉ L v } → Fin 2 => fun c => if hc : c ∈ L v then 0 else χ ⟨c, hc⟩) (Finset.univ : Finset ({ c : C // c ∉ L v } → Fin 2))) := by
              refine' Finset.card_le_card _;
              intro χ hχ; simp_all +decide [ Finset.subset_iff ] ;
              exact ⟨ fun ⟨ c, hc ⟩ => χ c, funext fun c => by by_cases hc : c ∈ L v <;> simp +decide [ hc, hχ ] ⟩;
            refine' le_trans h_card_B_v ( Finset.card_image_le.trans _ );
            simp +decide [ Finset.card_univ ];
          exact h_card_B_v.trans ( pow_le_pow_right₀ ( by decide ) ( Nat.sub_le_sub_left ( hL v ) _ ) );
        simpa only [ add_mul, Finset.sum_const, nsmul_eq_mul ] using add_le_add ( Finset.sum_le_sum h_bad_functions ) ( Finset.sum_le_sum h_bad_functions_B );
      -- Since the number of bad functions is strictly less than the total number of functions, there exists a function that is not bad.
      have h_exists_good_function : ∃ χ : C → Fin 2, χ ∉ Finset.biUnion A (fun v => Finset.filter (fun χ : C → Fin 2 => ∀ c ∈ L v, χ c = 1) Finset.univ) ∧ χ ∉ Finset.biUnion B (fun v => Finset.filter (fun χ : C → Fin 2 => ∀ c ∈ L v, χ c = 0) Finset.univ) := by
        have h_exists_good_function : Finset.card (Finset.biUnion A (fun v => Finset.filter (fun χ : C → Fin 2 => ∀ c ∈ L v, χ c = 1) Finset.univ)) + Finset.card (Finset.biUnion B (fun v => Finset.filter (fun χ : C → Fin 2 => ∀ c ∈ L v, χ c = 0) Finset.univ)) < 2 ^ Fintype.card C := by
          refine' lt_of_le_of_lt ( add_le_add ( Finset.card_biUnion_le ) ( Finset.card_biUnion_le ) ) _;
          refine' lt_of_le_of_lt h_bad_functions _;
          refine' lt_of_lt_of_le ( Nat.mul_lt_mul_of_pos_right hV ( pow_pos ( by decide ) _ ) ) _;
          rw [ ← pow_add, Nat.add_sub_of_le ];
          by_cases h : ∃ v, v ∈ A ∪ B;
          · exact le_trans ( hL h.choose ) ( Finset.card_le_univ _ );
          · aesop;
        have h_exists_good_function : Finset.card (Finset.univ \ (Finset.biUnion A (fun v => Finset.filter (fun χ : C → Fin 2 => ∀ c ∈ L v, χ c = 1) Finset.univ) ∪ Finset.biUnion B (fun v => Finset.filter (fun χ : C → Fin 2 => ∀ c ∈ L v, χ c = 0) Finset.univ))) > 0 := by
          simp_all +decide [ Finset.card_sdiff ];
          exact lt_of_le_of_lt ( Finset.card_union_le _ _ ) h_exists_good_function;
        exact Exists.elim ( Finset.card_pos.mp h_exists_good_function ) fun x hx => ⟨ x, by aesop ⟩;
      obtain ⟨ χ, hχ₁, hχ₂ ⟩ := h_exists_good_function; specialize h_contra χ; simp_all +decide [ Finset.ext_iff ] ;
      grind

/-
Any bipartite graph with fewer than 2^k vertices is k-list-colorable.
-/
lemma bipartite_card_lt_two_pow_k_implies_k_list_colorable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsBipartite G) (k : ℕ) (hk : k ≥ 1)
    (hV : Fintype.card V < 2 ^ k) : IsKListColorable G k := by
      -- By definition of bipartite graphs, there exists a 2-coloring f : V → Fin 2.
      obtain ⟨f, hf⟩ := hG;
      -- By bipartite_list_coloring_probability_bound, there exists a partition of colors C into C0 and C1 such that every v in A has a color in C0 and every v in B has a color in C1.
      have h_partition : ∀ (C : Type) [Fintype C] [DecidableEq C] (L : V → Finset C) (hL : ∀ v, (L v).card ≥ k), ∃ (χ : C → Fin 2), (∀ v ∈ Finset.univ.filter (fun v => f v = 0), ∃ c ∈ L v, χ c = 0) ∧ (∀ v ∈ Finset.univ.filter (fun v => f v = 1), ∃ c ∈ L v, χ c = 1) := by
        intro C _ _ L hL;
        -- Apply the bipartite_list_coloring_probability_bound lemma with A and B as the two parts of the bipartite graph.
        apply bipartite_list_coloring_probability_bound L k hL (Finset.univ.filter (fun v => f v = 0)) (Finset.univ.filter (fun v => f v = 1));
        rw [ ← Finset.card_union_of_disjoint ( Finset.disjoint_filter.mpr fun _ _ _ => by simp +decide [ * ] ) ];
        exact lt_of_le_of_lt ( Finset.card_le_univ _ ) hV;
      -- For each vertex $v$, choose a color $c_v$ from its list $L(v)$ such that $\chi(c_v) = f(v)$.
      intro C _ _ L hL
      obtain ⟨χ, hχ₀, hχ₁⟩ := h_partition C L hL
      have h_choose : ∀ v, ∃ c ∈ L v, χ c = f v := by
        intro v; specialize hχ₀ v; specialize hχ₁ v; rcases Fin.exists_fin_two.mp ⟨ f v, rfl ⟩ with ( h | h ) <;> aesop;
      choose g hg₁ hg₂ using h_choose;
      refine' ⟨ g, hg₁, fun u v huv => _ ⟩;
      intro huv'; have := hf u v huv; simp_all +decide ;
      exact this ( by rw [ ← hg₂ u, ← hg₂ v, huv' ] )

end AristotleLemmas

theorem ert_lower_bound (k : ℕ) (hk : k ≥ 1) : 2 ^ (k - 1) < n k := by
  -- Let $m \in S$. Then there exists a bipartite graph $G$ with $|V|=m$ and $\chi_L(G) > k$.
  have h_lower_bound : ∀ m, (∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
      Fintype.card V = m ∧ IsBipartite G ∧ (Erdos629.listChromaticNumber G) > k) → 2 ^ k ≤ m := by
        rintro m ⟨ V, x, x_1, G, rfl, hG₁, hG₂ ⟩;
        contrapose! hG₂;
        apply_rules [ Nat.sInf_le ];
        convert bipartite_card_lt_two_pow_k_implies_k_list_colorable G hG₁ k hk hG₂;
  refine' lt_of_lt_of_le ( pow_lt_pow_right₀ one_lt_two ( Nat.pred_lt ( ne_bot_of_gt hk ) ) ) ( le_csInf _ _ );
  · obtain ⟨ V, hV₁, hV₂, G, hG₁, hG₂ ⟩ := bipartite_list_chromatic_unbounded k;
    exact ⟨ _, ⟨ V, hV₁, hV₂, G, rfl, hG₁, hG₂ ⟩ ⟩;
  · exact fun m hm => h_lower_bound m hm

/- Aristotle failed to find a proof. -/
/-- Original upper bound: n(k) < k² · 2^{k+2}. -/
theorem ert_upper_bound (k : ℕ) (hk : k ≥ 1) : n k < k ^ 2 * 2 ^ (k + 2) := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Application type mismatch: The argument
  k
has type
  ℝ
but is expected to have type
  ℕ
in the application
  Erdos629.n k-/
/- ## Part VI: Improved Bounds -/

/-- Radhakrishnan-Srinivasan (2000) improved lower bound.
    2^k · (k / log k)^{1/2} ≪ n(k) -/
theorem rs_lower_bound :
    ∀ ε > 0, ∀ᶠ k in Filter.atTop,
      (2 : ℝ) ^ k * (k / Real.log k) ^ (1/2 : ℝ) * (1 - ε) < n k := by
  sorry

/- Aristotle failed to find a proof. -/
/-- Hanson-MacGillivray-Toft recursive upper bound: n(k) ≤ k · n(k-2) + 2^k. -/
theorem hmt_recursive_upper (k : ℕ) (hk : k ≥ 2) :
    n k ≤ k * n (k - 2) + 2 ^ k := by
  sorry

/- ## Part VII: Connection to Property B -/

/-- m(k) = smallest family of k-sets without Property B.
    Property B means having a 2-coloring of the ground set with no monochromatic set. -/
noncomputable def propertyB_threshold (k : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ (F : Finset (Finset (Fin m))),
    (∀ S ∈ F, S.card = k) ∧
    ¬∃ f : Fin m → Fin 2, ∀ S ∈ F, ∃ x y : Fin m, x ∈ S ∧ y ∈ S ∧ f x ≠ f y}

/- Aristotle took a wrong turn (reason code: 0). Please try again. -/
/-- Key connection: m(k) ≤ n(k) ≤ m(k+1).
    This relates list coloring to Property B (Problem #901). -/
theorem n_property_b_bounds (k : ℕ) (hk : k ≥ 1) :
    propertyB_threshold k ≤ n k ∧ n k ≤ propertyB_threshold (k + 1) := by
  sorry

/- ## Part VIII: Constructions -/

/-- The complete bipartite graph K_{m,n}. -/
def completeBipartite (m n : ℕ) : SimpleGraph (Fin m ⊕ Fin n) where
  Adj := fun u v => match u, v with
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr _, Sum.inl _ => True
    | _, _ => False
  symm := by
    intro u v h
    cases u <;> cases v <;> simp_all [h]
  loopless := by
    intro v
    cases v <;> simp

/- Aristotle took a wrong turn (reason code: 0). Please try again. -/
/-- Complete bipartite graphs are bipartite (obviously). -/
-- Proved by Aristotle (Harmonic)
theorem completeBipartite_is_bipartite (m n : ℕ) :
    IsBipartite (completeBipartite m n) := by
  use fun v => match v with
    | Sum.inl _ => 0
    | Sum.inr _ => 1;
  unfold Erdos629.IsProperColoring; aesop;

/- Aristotle took a wrong turn (reason code: 0). Please try again. -/
/-- K_{n,n} has list chromatic number ≈ log₂ n + 1. -/
theorem knn_list_chromatic (n : ℕ) (hn : n ≥ 2) :
    Nat.clog 2 n ≤ listChromaticNumber (completeBipartite n n) ∧
    listChromaticNumber (completeBipartite n n) ≤ Nat.clog 2 n + 2 := by
  sorry

/- Aristotle took a wrong turn (reason code: 0). Please try again. -/
/- ## Part IX: Asymptotic Behavior -/

/-- n(k) grows exponentially in k. -/
theorem n_exponential_growth :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      ∀ᶠ k in Filter.atTop, c₁ * 2 ^ k < (n k : ℝ) ∧ (n k : ℝ) < c₂ * k ^ 2 * 2 ^ k := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Application type mismatch: The argument
  k
has type
  ℝ
but is expected to have type
  ℕ
in the application
  Erdos629.n k
Application type mismatch: The argument
  k
has type
  ℝ
but is expected to have type
  ℕ
in the application
  Erdos629.n k-/
/-- The precise exponent is not known - this is what makes the problem OPEN. -/
def ExactAsymptoticConjecture : Prop :=
  ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧
    ∀ ε > 0, ∀ᶠ k in Filter.atTop,
      2 ^ k * (k : ℝ) ^ (α - ε) < n k ∧ (n k : ℝ) < 2 ^ k * (k : ℝ) ^ (α + ε)

end Erdos629