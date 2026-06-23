/-
Erdős Problem #667: Clique Density Exponent c(p,q)

Source: https://erdosproblems.com/667
Status: OPEN

Statement:
For fixed integers p, q ≥ 1, define H(n; p, q) as the largest m such that
every graph on n vertices where every set of p vertices spans at least q
edges must contain a complete graph on m vertices.

Define c(p, q) = lim inf (log H(n; p, q)) / (log n).

Is c(p, q) strictly increasing in q for 1 ≤ q ≤ C(p-1, 2) + 1?

Known results:
- q = 1: reduces to classical Ramsey; 1/(p-1) ≤ c(p,1) ≤ 2/(p+1)
- q = C(p-1,2) + 1: every p-set spans a complete graph, so c(p,q) = 1
- Erdős-Faudree-Rousseau-Schelp: c(p, C(p-1,2)) ≤ 1/2

Reference: [Er97f], https://erdosproblems.com/667

Adapted from erdosproblems.com (Apache 2.0 License)
-/

import Mathlib

open Finset SimpleGraph Filter

namespace Erdos667

/-
## Part I: Graph-Theoretic Foundations

We formalize the edge density condition: every p-subset spans at least q edges.
-/

/-- The number of edges a graph G induces on a subset S of vertices. -/
def edgeCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  ((S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ G.Adj p.1 p.2)).card / 2

/-- A graph satisfies the (p,q)-density condition if every p-element subset
    spans at least q edges. -/
def HasDensity {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p q : ℕ) : Prop :=
  ∀ S : Finset V, S.card = p → edgeCount G S ≥ q

/-
## Part II: The Function H(n; p, q)

H(n; p, q) is the largest m such that every n-vertex graph with the
(p,q)-density condition contains a complete subgraph on m vertices.
-/

/-- H(n; p, q): the largest clique size guaranteed in any n-vertex graph
    satisfying the (p,q)-density condition.
    Defined as: sup {m ≤ n | every n-vertex graph with (p,q)-density has an m-clique}.

    Previously axiomatized; now defined concretely using sSup.
    Uses Classical.dec for decidability of graph predicates. -/
open scoped Classical in
noncomputable def cliqueGuarantee (n p q : ℕ) : ℕ :=
  sSup {m : ℕ | m ≤ n ∧ ∀ (G : SimpleGraph (Fin n)),
    HasDensity G p q → ¬G.CliqueFree m}

-- Notation: H(n; p, q) = cliqueGuarantee n p q

/-- H is monotone in n: more vertices can only help.
    Proof sketch: S_n ⊆ S_{n+1} because for any G on Fin (n+1) with density,
    pulling back to G' = G.comap castSucc on Fin n preserves the density condition
    (edgeCount unchanged by injective embedding). Any m-clique in G' lifts to G. -/
open scoped Classical in
theorem cliqueGuarantee_mono_n (p q n : ℕ) :
    cliqueGuarantee n p q ≤ cliqueGuarantee (n + 1) p q := by
  simp only [cliqueGuarantee]
  by_cases hne : {m : ℕ | m ≤ n ∧ ∀ (G : SimpleGraph (Fin n)),
      HasDensity G p q → ¬G.CliqueFree m}.Nonempty
  · apply csSup_le_csSup
    · exact ⟨n + 1, fun m ⟨hm, _⟩ => hm⟩
    · exact hne
    · -- S_n ⊆ S_{n+1}
      intro m ⟨hm_le, hm⟩
      refine ⟨by omega, fun G hd => ?_⟩
      -- Pull back G to Fin n via castSucc: G' = G.comap castSucc
      -- HasDensity G' p q because edgeCount (G.comap f) S = edgeCount G (S.map f)
      -- for injective f (castSucc preserves the pair structure bijectively)
      have hcf := hm (G.comap Fin.castSucc) (by
        intro S hS
        -- edgeCount (G.comap castSucc) S = edgeCount G (S.map castSucc) ≥ q
        let emb : Fin n ↪ Fin (n + 1) := ⟨Fin.castSucc, Fin.castSucc_injective n⟩
        suffices h : edgeCount (G.comap Fin.castSucc) S =
            edgeCount G (S.map emb) by
          rw [h]; exact hd _ (by rw [Finset.card_map]; exact hS)
        -- Edge count preserved: comap pullback bijects with mapped product
        simp only [edgeCount, ← Finset.prodMap_map_product emb emb,
          Finset.filter_map, Finset.card_map]
        congr 1
        apply Finset.filter_congr
        intro ⟨a, b⟩ _
        simp only [Function.comp, Function.Embedding.prodMap_apply, Prod.map,
          SimpleGraph.comap_adj, (Fin.castSucc_injective n).ne_iff])
      -- Lift: ¬CliqueFree (G.comap castSucc) m → ¬CliqueFree G m
      intro hcfG
      apply hcf
      intro s hs
      apply hcfG (s.map ⟨Fin.castSucc, Fin.castSucc_injective n⟩)
      refine ⟨?_, by rw [Finset.card_map]; exact hs.card_eq⟩
      -- IsClique: castSucc preserves adjacency from G.comap castSucc to G
      intro a ha b hb hab
      simp only [Finset.coe_map, Set.mem_image, Function.Embedding.coeFn_mk] at ha hb
      obtain ⟨a', ha', rfl⟩ := ha
      obtain ⟨b', hb', rfl⟩ := hb
      exact hs.isClique (Finset.mem_coe.mpr ha') (Finset.mem_coe.mpr hb')
        (fun h => hab (congrArg Fin.castSucc h))
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, sSup_empty]; exact bot_le

/-- H is monotone in q: more edges per p-set yields larger cliques.
    Proof: HasDensity G p (q+1) implies HasDensity G p q, so the density
    condition for q+1 is strictly more restrictive. Universal quantification
    over a smaller class of graphs makes it easier to guarantee larger cliques. -/
theorem cliqueGuarantee_mono_q (n p q : ℕ) :
    cliqueGuarantee n p q ≤ cliqueGuarantee n p (q + 1) := by
  simp only [cliqueGuarantee]
  set Sq := {m : ℕ | m ≤ n ∧ ∀ (G : SimpleGraph (Fin n)),
    HasDensity G p q → ¬G.CliqueFree m}
  set Sq1 := {m : ℕ | m ≤ n ∧ ∀ (G : SimpleGraph (Fin n)),
    HasDensity G p (q + 1) → ¬G.CliqueFree m}
  by_cases hne : Sq.Nonempty
  · apply csSup_le_csSup
    · -- Sq1 is bounded above by n
      exact ⟨n, fun m ⟨hm, _⟩ => hm⟩
    · exact hne
    · -- Sq ⊆ Sq1: HasDensity G p (q+1) → HasDensity G p q (more edges ≥ fewer)
      intro m ⟨hm, hG⟩
      exact ⟨hm, fun G hd => hG G fun S hS => le_trans (Nat.le_succ q) (hd S hS)⟩
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, sSup_empty]; exact bot_le

/-- H(n; p, q) ≤ n: cannot guarantee a clique larger than the graph.
    Follows directly from the m ≤ n constraint in the sSup definition. -/
theorem cliqueGuarantee_le_n (n p q : ℕ) :
    cliqueGuarantee n p q ≤ n := by
  simp only [cliqueGuarantee]
  set S := {m : ℕ | m ≤ n ∧ ∀ (G : SimpleGraph (Fin n)),
    HasDensity G p q → ¬G.CliqueFree m}
  by_cases hne : S.Nonempty
  · exact csSup_le hne fun m ⟨hm, _⟩ => hm
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, sSup_empty]; exact bot_le

/-
## Part III: Boundary Values

The function c(p,q) has known values at the endpoints.
-/

/-- REMOVED (FALSE): Previously claimed H(n; p, C(p-1,2)+1) = n (i.e., graph must
    be complete). Counterexample: C₄ (4-cycle on Fin 4) satisfies HasDensity 3 2
    (every triple spans exactly 2 edges) but has clique number 2, not 4.

    The correct fact is that the *exponent* c(p, C(p-1,2)+1) = 1, meaning H(n) ~ n
    (grows linearly), but H(n) ≠ n exactly. This is captured by axiom `cpq_at_max`.

    For p=3, q=C(2,2)+1=2: the complement of any satisfying graph is a matching,
    giving clique number ⌈n/2⌉, so c(3,2) = lim inf log(⌈n/2⌉)/log(n) = 1. -/

/-- When q = 0, there is no constraint, so H(n; p, 0) = 1 trivially.
    Every graph has at least one vertex (when n ≥ 1), forming a trivial 1-clique.
    The empty graph on n vertices shows we can't guarantee 2-cliques.
    Proof: S = {m ≤ n | ∀ G, ¬CliqueFree G m} = {0, 1} since the empty graph
    is CliqueFree m for m ≥ 2, and every nonempty graph has a 0-clique and 1-clique. -/
open scoped Classical in
theorem cliqueGuarantee_zero (n p : ℕ) (hn : 1 ≤ n) :
    cliqueGuarantee n p 0 = 1 := by
  simp only [cliqueGuarantee]
  apply le_antisymm
  · -- Upper bound: sSup S ≤ 1
    apply csSup_le
    · -- S is nonempty: 0 ∈ S (empty set is a 0-clique in any graph)
      exact ⟨0, Nat.zero_le n, fun G _ hcf =>
        hcf ∅ ⟨Set.pairwise_empty _, rfl⟩⟩
    · -- All elements of S are ≤ 1
      intro m ⟨_, hm⟩
      by_contra hgt
      push_neg at hgt
      -- m ≥ 2: the empty graph ⊥ satisfies HasDensity but is CliqueFree m
      apply hm (⊥ : SimpleGraph (Fin n)) (fun _ _ => Nat.zero_le _)
      -- Goal: CliqueFree ⊥ m
      intro s hs
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by rw [hs.card_eq]; omega)
      exact hs.isClique (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab
  · -- Lower bound: 1 ≤ sSup S
    apply le_csSup ⟨n, fun m ⟨hm, _⟩ => hm⟩
    -- 1 ∈ S: singleton {⟨0, _⟩} is a 1-clique in any graph on Fin n (n ≥ 1)
    exact ⟨hn, fun G _ hcf =>
      hcf {⟨0, by omega⟩} ⟨Set.pairwise_singleton _ _, Finset.card_singleton _⟩⟩

/-- Extended monotonicity: H(n; p, q1) ≤ H(n; p, q2) for q1 ≤ q2. -/
theorem cliqueGuarantee_mono_q_general (n p q1 q2 : ℕ) (h : q1 ≤ q2) :
    cliqueGuarantee n p q1 ≤ cliqueGuarantee n p q2 := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (cliqueGuarantee_mono_q n p _)

/-- H(n; p, q) ≥ 1 for any non-empty graph.
    Proved: H(n,p,0) = 1 and H is monotone in q, so H(n,p,q) ≥ 1 for all q.
    (Previously axiomatized; now derived from cliqueGuarantee_zero + monotonicity.) -/
theorem cliqueGuarantee_pos (n p q : ℕ) (hn : 1 ≤ n) :
    1 ≤ cliqueGuarantee n p q := by
  have h0 : cliqueGuarantee n p 0 = 1 := cliqueGuarantee_zero n p hn
  have hmono := cliqueGuarantee_mono_q_general n p 0 q (Nat.zero_le q)
  linarith

/-
## Part IV: The Exponent c(p, q)

c(p, q) = lim inf (log H(n; p, q)) / (log n) as n tends to infinity.
Previously axiomatized as a ℝ-valued function with 4 structural axioms.
Now defined concretely via Filter.liminf over ℝ, with the structural
properties proved from the definition. This eliminates 4 axioms.
-/

/-- The sequence whose liminf defines c(p,q): n ↦ log(H(n;p,q)) / log(n). -/
private noncomputable def cpqSeq (p q : ℕ) (n : ℕ) : ℝ :=
  Real.log ↑(cliqueGuarantee n p q) / Real.log ↑n

/-- c(p, q) = lim inf log(H(n;p,q)) / log(n) as n → ∞.
    Previously axiomatized; now defined via Filter.liminf. -/
noncomputable def cpq (p q : ℕ) : ℝ :=
  liminf (cpqSeq p q) atTop

section CpqProperties

/-- The cpq sequence is eventually nonneg: for n ≥ 1, H ≥ 1 and log n ≥ 0. -/
private lemma cpqSeq_eventually_nonneg (p q : ℕ) :
    ∀ᶠ n in atTop, 0 ≤ cpqSeq p q n := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact div_nonneg
    (Real.log_nonneg (by exact_mod_cast cliqueGuarantee_pos n p q hn))
    (Real.log_nonneg (by exact_mod_cast hn))

/-- The cpq sequence is eventually ≤ 1: H(n) ≤ n implies log H / log n ≤ 1. -/
private lemma cpqSeq_eventually_le_one (p q : ℕ) :
    ∀ᶠ n in atTop, cpqSeq p q n ≤ 1 := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hH_pos : (0 : ℝ) < ↑(cliqueGuarantee n p q) := by
    have := cliqueGuarantee_pos n p q hn
    exact_mod_cast (show 0 < cliqueGuarantee n p q by omega)
  exact div_le_one_of_le
    (Real.log_le_log hH_pos (by exact_mod_cast cliqueGuarantee_le_n n p q))
    (Real.log_nonneg (by exact_mod_cast hn))

/-- The cpq sequence is bounded below (for Filter.liminf API). -/
private lemma cpq_isBoundedUnder_ge (p q : ℕ) :
    IsBoundedUnder (· ≥ ·) atTop (cpqSeq p q) :=
  ⟨0, cpqSeq_eventually_nonneg p q⟩

/-- The cpq sequence is cobounded below: any eventual lower bound ≤ 1,
    since the sequence is eventually ≤ 1. -/
private lemma cpq_isCoboundedUnder_ge (p q : ℕ) :
    IsCoboundedUnder (· ≥ ·) atTop (cpqSeq p q) :=
  ⟨1, fun a ha => by
    obtain ⟨N, hN⟩ := eventually_atTop.mp (ha.and (cpqSeq_eventually_le_one p q))
    have ⟨h1, h2⟩ := hN N le_rfl; linarith⟩

/-- c(p,q) ≥ 0 (H(n;p,q) ≥ 1 for all n ≥ 1).
    Proved from the definition: the sequence is eventually ≥ 0. -/
theorem cpq_nonneg (p q : ℕ) : 0 ≤ cpq p q :=
  le_liminf_of_le (cpq_isCoboundedUnder_ge p q) (cpqSeq_eventually_nonneg p q)

/-- c(p,q) ≤ 1 (H(n;p,q) ≤ n for all n).
    Proved from the definition: the sequence is eventually ≤ 1. -/
theorem cpq_le_one (p q : ℕ) : cpq p q ≤ 1 :=
  liminf_le_of_frequently_le (cpqSeq_eventually_le_one p q).frequently
    (cpq_isBoundedUnder_ge p q)

/-- c is weakly increasing in q (from monotonicity of H in q).
    Proved from the definition: H(n;p,q) ≤ H(n;p,q+1) implies the
    sequence is pointwise monotone, and liminf preserves ≤. -/
theorem cpq_mono_q (p q : ℕ) : cpq p q ≤ cpq p (q + 1) := by
  apply liminf_le_liminf
  · -- Pointwise: cpqSeq p q n ≤ cpqSeq p (q+1) n for all n
    filter_upwards with n
    simp only [cpqSeq]
    by_cases hlog : Real.log (↑n : ℝ) = 0
    · simp [hlog]
    · have hn2 : 2 ≤ n := by
        by_contra h; push_neg at h
        exact hlog (by
          have : n = 0 ∨ n = 1 := by omega
          rcases this with rfl | rfl <;> simp)
      have hlog_pos : 0 < Real.log (↑n : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      rw [div_le_div_right hlog_pos]
      have hH_pos : (0 : ℝ) < ↑(cliqueGuarantee n p q) := by
        have := cliqueGuarantee_pos n p q (by omega : 1 ≤ n)
        exact_mod_cast (show 0 < cliqueGuarantee n p q by omega)
      exact Real.log_le_log hH_pos (by exact_mod_cast cliqueGuarantee_mono_q n p q)
  · exact cpq_isBoundedUnder_ge p q
  · exact cpq_isCoboundedUnder_ge p (q + 1)

end CpqProperties

/-
## Part V: Known Bounds

Established results on c(p,q).
-/

/-- c(p, 1) ≥ 1/(p-1) (Ramsey lower bound). -/
axiom cpq_lower_ramsey (p : ℕ) (hp : 2 ≤ p) :
    (1 : ℝ) / ((p : ℝ) - 1) ≤ cpq p 1

/-- c(p, 1) ≤ 2/(p+1) (Ramsey upper bound). -/
axiom cpq_upper_ramsey (p : ℕ) (hp : 2 ≤ p) :
    cpq p 1 ≤ (2 : ℝ) / ((p : ℝ) + 1)

/-- c(p, C(p-1,2)+1) = 1: at maximum density, full clique is guaranteed. -/
axiom cpq_at_max (p : ℕ) (hp : 2 ≤ p) :
    cpq p (Nat.choose (p - 1) 2 + 1) = 1

/-- Erdos-Faudree-Rousseau-Schelp: c(p, C(p-1,2)) ≤ 1/2.
    The second-to-last value of q already forces c ≤ 1/2. -/
axiom efrs_bound (p : ℕ) (hp : 3 ≤ p) :
    cpq p (Nat.choose (p - 1) 2) ≤ (1 : ℝ) / 2

/-
## Part VI: Proved Consequences

Theorems derived from the axiomatized facts.
-/

/-- c(p,q) increases from the Ramsey value to 1 as q ranges from 1 to C(p-1,2)+1.
    Specifically: c(p,1) ≤ 1 and c(p, C(p-1,2)+1) = 1 for p ≥ 2. -/
theorem cpq_range (p : ℕ) (hp : 2 ≤ p) :
    cpq p 1 ≤ 1 ∧ cpq p (Nat.choose (p - 1) 2 + 1) = 1 :=
  ⟨cpq_le_one p 1, cpq_at_max p hp⟩

/-- The EFRS bound implies a gap: c(p, C(p-1,2)) < c(p, C(p-1,2)+1) for p ≥ 3.
    This is a strict increase at the last step. -/
theorem cpq_strict_at_top (p : ℕ) (hp : 3 ≤ p) :
    cpq p (Nat.choose (p - 1) 2) < cpq p (Nat.choose (p - 1) 2 + 1) := by
  have h1 := efrs_bound p hp
  have h2 := cpq_at_max p (le_trans (by omega : 2 ≤ 3) hp)
  rw [h2]
  linarith

/-- For p ≥ 3, the Ramsey lower bound gives c(p,1) > 0. -/
theorem cpq_pos_at_one (p : ℕ) (hp : 3 ≤ p) : (0 : ℝ) < cpq p 1 := by
  have h := cpq_lower_ramsey p (le_trans (by omega : 2 ≤ 3) hp)
  have : (0 : ℝ) < (1 : ℝ) / ((p : ℝ) - 1) := by
    apply div_pos
    · exact one_pos
    · have : (p : ℝ) ≥ 3 := by exact_mod_cast hp
      linarith
  linarith

/-- Weak monotonicity extended: c(p, q1) ≤ c(p, q2) for q1 ≤ q2. -/
theorem cpq_mono_q_general (p q1 q2 : ℕ) (h : q1 ≤ q2) :
    cpq p q1 ≤ cpq p q2 := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (cpq_mono_q p _)

/-- The Ramsey bound interval: for p ≥ 2, c(p,1) lies in [1/(p-1), 2/(p+1)]. -/
theorem cpq_ramsey_interval (p : ℕ) (hp : 2 ≤ p) :
    (1 : ℝ) / ((p : ℝ) - 1) ≤ cpq p 1 ∧ cpq p 1 ≤ (2 : ℝ) / ((p : ℝ) + 1) :=
  ⟨cpq_lower_ramsey p hp, cpq_upper_ramsey p hp⟩

/-
## Part VII: Small Cases

For small values of p, we can compute the range of q and verify structure.
-/

/-- For p = 3: C(2,2) + 1 = 2. So q ranges over {1, 2}.
    c(3,2) = 1 (the graph must be complete). -/
theorem p3_max : cpq 3 (Nat.choose 2 2 + 1) = 1 := cpq_at_max 3 (by omega)

/-- For p = 3: the conjecture reduces to c(3,1) < c(3,2) = 1. -/
theorem p3_strict : cpq 3 1 < cpq 3 2 := by
  have h2 : cpq 3 2 = 1 := by
    have : Nat.choose 2 2 + 1 = 2 := by native_decide
    rw [← this]; exact cpq_at_max 3 (by omega)
  rw [h2]
  have := cpq_upper_ramsey 3 (by omega)
  have : (2 : ℝ) / ((3 : ℝ) + 1) = 1 / 2 := by norm_num
  linarith

/-- For p = 4: C(3,2) + 1 = 4. So q ranges over {1, 2, 3, 4}.
    c(4,4) = 1. -/
theorem p4_max : cpq 4 (Nat.choose 3 2 + 1) = 1 := cpq_at_max 4 (by omega)

/-- For p = 4: EFRS gives c(4,3) ≤ 1/2, and c(4,4) = 1. -/
theorem p4_efrs : cpq 4 (Nat.choose 3 2) ≤ (1 : ℝ) / 2 :=
  efrs_bound 4 (by omega)

/-- For p = 4: strict increase at the top: c(4,3) < c(4,4) = 1. -/
theorem p4_strict_at_top : cpq 4 (Nat.choose 3 2) < cpq 4 (Nat.choose 3 2 + 1) :=
  cpq_strict_at_top 4 (by omega)

/-- For p = 5: C(4,2) + 1 = 7. So q ranges over {1, 2, 3, 4, 5, 6, 7}.
    c(5,7) = 1. -/
theorem p5_max : cpq 5 (Nat.choose 4 2 + 1) = 1 := cpq_at_max 5 (by omega)

/-- For p = 5: EFRS gives c(5,6) ≤ 1/2. -/
theorem p5_efrs : cpq 5 (Nat.choose 4 2) ≤ (1 : ℝ) / 2 :=
  efrs_bound 5 (by omega)

/-- For p = 5: strict increase at the top: c(5,6) < c(5,7) = 1. -/
theorem p5_strict_at_top : cpq 5 (Nat.choose 4 2) < cpq 5 (Nat.choose 4 2 + 1) :=
  cpq_strict_at_top 5 (by omega)

/-- For p = 5: the Ramsey lower bound gives c(5,1) ≥ 1/4. -/
theorem p5_ramsey_lower : (1 : ℝ) / 4 ≤ cpq 5 1 := by
  have h := cpq_lower_ramsey 5 (by omega)
  norm_num at h ⊢
  exact h

/-- For p = 5: the Ramsey upper bound gives c(5,1) ≤ 1/3. -/
theorem p5_ramsey_upper : cpq 5 1 ≤ (1 : ℝ) / 3 := by
  have h := cpq_upper_ramsey 5 (by omega)
  norm_num at h ⊢
  exact h

/-- For p = 4: Ramsey bounds give c(4,1) ∈ [1/3, 2/5]. -/
theorem p4_ramsey_lower : (1 : ℝ) / 3 ≤ cpq 4 1 := by
  have h := cpq_lower_ramsey 4 (by omega)
  norm_num at h ⊢; exact h

theorem p4_ramsey_upper : cpq 4 1 ≤ (2 : ℝ) / 5 := by
  have h := cpq_upper_ramsey 4 (by omega)
  norm_num at h ⊢; exact h

/-- For p = 3: cpq_strict already proves the FULL conjecture for p=3
    (there is only one step: q goes from 1 to 2). -/
theorem erdos667_holds_for_p3 :
    ∀ q, 1 ≤ q → q < Nat.choose 2 2 + 1 → cpq 3 q < cpq 3 (q + 1) := by
  intro q hq1 hq_lt
  have hq_eq : q = 1 := by
    have : Nat.choose 2 2 + 1 = 2 := by native_decide
    omega
  subst hq_eq
  exact p3_strict

/-
## Part VIII: The Main Conjecture (Erdos Problem 667)
-/

/-- Erdos Problem 667 (OPEN): c(p, q) is strictly increasing in q for
    1 ≤ q ≤ C(p-1, 2) + 1. -/
def ErdosProblem667 : Prop :=
    ∀ (p : ℕ) (_ : 3 ≤ p),
      ∀ (q : ℕ), 1 ≤ q → q < Nat.choose (p - 1) 2 + 1 →
        cpq p q < cpq p (q + 1)

/-- A weaker version: c(p,q) is non-constant (already known for the endpoints). -/
theorem erdos667_weak_evidence (p : ℕ) (hp : 3 ≤ p) :
    cpq p 1 < cpq p (Nat.choose (p - 1) 2 + 1) := by
  have h := cpq_at_max p (le_trans (by omega : 2 ≤ 3) hp)
  rw [h]
  have := cpq_upper_ramsey p (le_trans (by omega : 2 ≤ 3) hp)
  have hp' : (p : ℝ) ≥ 3 := by exact_mod_cast hp
  have : (2 : ℝ) / ((p : ℝ) + 1) < 1 := by
    rw [div_lt_one (by linarith : (0 : ℝ) < (p : ℝ) + 1)]
    linarith
  linarith

/-
## Part IX: Structural Consequences

General results about the gap structure of c(p,q).
-/

/-- The total gap: for p ≥ 3, c(p,1) is bounded away from c(p,q_max) = 1.
    Specifically, c(p,q_max) - c(p,1) ≥ 1 - 2/(p+1). -/
theorem cpq_total_gap (p : ℕ) (hp : 3 ≤ p) :
    1 - (2 : ℝ) / ((p : ℝ) + 1) ≤
    cpq p (Nat.choose (p - 1) 2 + 1) - cpq p 1 := by
  have h1 := cpq_at_max p (le_trans (by omega : 2 ≤ 3) hp)
  have h2 := cpq_upper_ramsey p (le_trans (by omega : 2 ≤ 3) hp)
  linarith

/-- The gap is positive: c(p,q_max) - c(p,1) > 0 for p ≥ 3. -/
theorem cpq_gap_pos (p : ℕ) (hp : 3 ≤ p) :
    (0 : ℝ) < cpq p (Nat.choose (p - 1) 2 + 1) - cpq p 1 := by
  linarith [erdos667_weak_evidence p hp]

/-- For p ≥ 3, there exists at least one strict step in c(p,·).
    The EFRS bound ensures c(p, C(p-1,2)) < c(p, C(p-1,2)+1) = 1. -/
theorem erdos667_at_least_one_strict_step (p : ℕ) (hp : 3 ≤ p) :
    ∃ q, 1 ≤ q ∧ q ≤ Nat.choose (p - 1) 2 ∧ cpq p q < cpq p (q + 1) := by
  exact ⟨Nat.choose (p - 1) 2,
    Nat.one_le_iff_ne_zero.mpr (by
      intro h
      have := Nat.choose_pos (by omega : 2 ≤ p - 1)
      simp [h] at this),
    le_refl _,
    cpq_strict_at_top p hp⟩

/-- Summary of known results for c(p,q). -/
theorem erdos667_summary (p : ℕ) (hp : 3 ≤ p) :
    -- c(p,1) is in the Ramsey interval
    ((1 : ℝ) / ((p : ℝ) - 1) ≤ cpq p 1 ∧ cpq p 1 ≤ (2 : ℝ) / ((p : ℝ) + 1)) ∧
    -- c(p,q_max) = 1
    cpq p (Nat.choose (p - 1) 2 + 1) = 1 ∧
    -- c is weakly increasing
    (∀ q, cpq p q ≤ cpq p (q + 1)) ∧
    -- There is a gap at the top
    cpq p (Nat.choose (p - 1) 2) < cpq p (Nat.choose (p - 1) 2 + 1) := by
  refine ⟨cpq_ramsey_interval p (le_trans (by omega : 2 ≤ 3) hp),
          cpq_at_max p (le_trans (by omega : 2 ≤ 3) hp),
          fun q => cpq_mono_q p q,
          cpq_strict_at_top p hp⟩

end Erdos667
