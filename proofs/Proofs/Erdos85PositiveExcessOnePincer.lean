import Proofs.Erdos85PositiveExcessOneServiceTrace

/-!
# The excess-one service/chord pincer

This file isolates the arithmetic core of the odd excess-one rigidity
argument.  If `q` is the number of antipodal centres whose two antipodes
are joined by the triangle-free matching and `δ` is the number of
double-service slots, the mixed trace identity gives

`δ = 2 (n - q)`.

On the other hand, a chordal centre supports no double-service slot and
`C₄`-freeness allows at most one over every other centre, so
`δ ≤ n - q`.  The two bounds force every centre to be chordal.

The graph-facing files following this one establish the three counting
identities used by the abstract terminal below.
-/

namespace Erdos85

open SimpleGraph

/-- A centre of the antipodal two-factor is *matching-chordal* when its
two antipodal neighbours form a triangle-free matching edge.  The
quantified formulation avoids choosing an orientation of the cycle. -/
def IsMatchingChordalCenter
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : V) : Prop :=
  ∀ a ∈ antipodalNeighbors G X, ∀ b ∈ antipodalNeighbors G X,
    a ≠ b → b ∈ triangleFreeNeighbors G a

/-- The set of matching-chordal antipodal centres. -/
noncomputable def matchingChordalCenters
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V := by
  classical
  exact Finset.univ.filter (IsMatchingChordalCenter G)

/-- Ordered root/target pairs for which the root hits every antipodal
neighbour of the target.  Actual double-service slots form a subfinset of
this one. -/
noncomputable def antipodalDoubleHitPairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (V × V) := by
  classical
  exact (Finset.univ.product Finset.univ).filter fun p =>
    ∀ z ∈ antipodalNeighbors G p.2, G.Adj p.1 z

@[simp] theorem mem_antipodalDoubleHitPairs_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : V × V) :
    p ∈ antipodalDoubleHitPairs G ↔
      ∀ z ∈ antipodalNeighbors G p.2, G.Adj p.1 z := by
  classical
  simp [antipodalDoubleHitPairs]

/-- A triangle-free matching chord has no common original neighbour.
Consequently a chordal centre cannot carry a double-service root. -/
theorem not_adj_both_of_triangleFree_chord
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a b u : V} (hab : b ∈ triangleFreeNeighbors G a) :
    ¬(G.Adj u a ∧ G.Adj u b) := by
  rintro ⟨hua, hub⟩
  have humem : u ∈ G.neighborFinset a ∩ G.neighborFinset b :=
    Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset a u).mpr hua.symm,
        (G.mem_neighborFinset b u).mpr hub.symm⟩
  have hpos : 0 < (G.neighborFinset a ∩ G.neighborFinset b).card :=
    Finset.card_pos.mpr ⟨u, humem⟩
  have hzero := (mem_triangleFreeNeighbors G a b).mp hab |>.2
  omega

/-- Graph-facing no-double lemma for a matching-chordal antipodal centre. -/
theorem matchingChordalCenter_no_doubleHit
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {X a b u : V} (hX : IsMatchingChordalCenter G X)
    (ha : a ∈ antipodalNeighbors G X)
    (hb : b ∈ antipodalNeighbors G X) (hab : a ≠ b) :
    ¬(G.Adj u a ∧ G.Adj u b) :=
  not_adj_both_of_triangleFree_chord G (hX a ha b hb hab)

/-- In a `C₄`-free graph two distinct vertices cannot both hit the same
two distinct antipodal endpoints.  This is the pointwise source of the
one-slot-per-nonchordal-centre capacity bound. -/
theorem eq_of_two_doubleHits
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {u v a b : V} (hab : a ≠ b)
    (hua : G.Adj u a) (hub : G.Adj u b)
    (hva : G.Adj v a) (hvb : G.Adj v b) :
    u = v := by
  by_contra huv
  exact hfree (containsC4_of_two_common
    (x := u) (y := v) (v := a) (v' := b)
    huv hab hua.symm hva.symm hub.symm hvb.symm)

/-- There is at most one double-hitting root over each target, and a
matching-chordal target has none.  Hence all double-hit pairs inject into
the nonchordal targets. -/
theorem card_antipodalDoubleHitPairs_le_nonchordal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hanti : ∀ X, (antipodalNeighbors G X).card = 2) :
    (antipodalDoubleHitPairs G).card ≤
      Fintype.card V - (matchingChordalCenters G).card := by
  classical
  let N : Finset V := Finset.univ.filter fun X =>
    ¬ IsMatchingChordalCenter G X
  have hNcard : N.card = Fintype.card V - (matchingChordalCenters G).card := by
    have hpart := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset V))
      (p := IsMatchingChordalCenter G)
    change (matchingChordalCenters G).card + N.card = Fintype.card V at hpart
    omega
  rw [← hNcard]
  apply Finset.card_le_card_of_injOn (fun p : V × V => p.2)
  · intro p hp
    change p ∈ antipodalDoubleHitPairs G at hp
    rw [mem_antipodalDoubleHitPairs_iff] at hp
    change p.2 ∈ N
    simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]
    intro hchord
    obtain ⟨a, b, hab, hpairs⟩ := Finset.card_eq_two.mp (hanti p.2)
    have ha : a ∈ antipodalNeighbors G p.2 := by simp [hpairs]
    have hb : b ∈ antipodalNeighbors G p.2 := by simp [hpairs]
    exact matchingChordalCenter_no_doubleHit G hchord ha hb hab
      ⟨hp a ha, hp b hb⟩
  · intro p hp r hr hpr
    change p ∈ antipodalDoubleHitPairs G at hp
    change r ∈ antipodalDoubleHitPairs G at hr
    rw [mem_antipodalDoubleHitPairs_iff] at hp hr
    change p.2 = r.2 at hpr
    apply Prod.ext
    · obtain ⟨a, b, hab, hpairs⟩ := Finset.card_eq_two.mp (hanti p.2)
      have ha : a ∈ antipodalNeighbors G p.2 := by simp [hpairs]
      have hb : b ∈ antipodalNeighbors G p.2 := by simp [hpairs]
      have hpHit := hp
      have hrHit := hr
      have hra : a ∈ antipodalNeighbors G r.2 := by
        rw [← hpr]
        exact ha
      have hrb : b ∈ antipodalNeighbors G r.2 := by
        rw [← hpr]
        exact hb
      apply eq_of_two_doubleHits G hfree hab
          (hpHit a ha) (hpHit b hb)
      · exact hrHit a hra
      · exact hrHit b hrb
    · exact hpr

/-- Arithmetic heart of the service/chord pincer. -/
theorem service_chord_pincer
    {n q δ : ℕ} (hq : q ≤ n)
    (htrace : δ = 2 * (n - q))
    (hcapacity : δ ≤ n - q) :
    q = n ∧ δ = 0 := by
  omega

/-- A form matching the two raw trace counts.  Here `s` is the service
moment and `t` is the matching--antipodal-square moment. -/
theorem service_chord_pincer_of_moments
    {n d q δ s t : ℕ} (hd : 1 ≤ d) (hq : q ≤ n)
    (hservice : s = n * (d - 1) + δ)
    (hchord : t = 2 * q)
    (hmoment : s + t = n * (d + 1))
    (hcapacity : δ ≤ n - q) :
    q = n ∧ δ = 0 := by
  apply service_chord_pincer hq
  · have hdsub : d = (d - 1) + 1 := by omega
    have hnd : n * d = n * (d - 1) + n := by
      calc
        n * d = n * ((d - 1) + 1) := congrArg (n * ·) hdsub
        _ = n * (d - 1) + n := by rw [Nat.mul_add, Nat.mul_one]
    rw [hservice, hchord, Nat.mul_add, hnd] at hmoment
    omega
  · exact hcapacity

/-- Integer-valued trace wrapper.  This version avoids natural-number
subtraction in the graph-to-trace bridge. -/
theorem service_chord_pincer_of_int_moments
    {n d q δ : ℕ} {s t : ℤ} (hd : 1 ≤ d) (hq : q ≤ n)
    (hservice : s = (n : ℤ) * ((d : ℤ) - 1) + δ)
    (hchord : t = 2 * q)
    (hmoment : s + t = (n : ℤ) * ((d : ℤ) + 1))
    (hcapacity : δ ≤ n - q) :
    q = n ∧ δ = 0 := by
  have htraceZ : (δ : ℤ) = 2 * ((n : ℤ) - q) := by
    rw [hservice, hchord] at hmoment
    push_cast at hmoment
    ring_nf at hmoment ⊢
    omega
  have htrace : δ = 2 * (n - q) := by
    have hcast : (δ : ℤ) = ((2 * (n - q) : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hq]
      exact htraceZ
    exact_mod_cast hcast
  exact service_chord_pincer hq htrace hcapacity

end Erdos85
