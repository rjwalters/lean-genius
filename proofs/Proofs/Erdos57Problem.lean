/-
  Erdős Problem #57: Odd Cycles in Graphs with Infinite Chromatic Number

  Source: https://erdosproblems.com/57
  Status: SOLVED (Liu-Montgomery 2020)

  Statement:
  If G is a graph with infinite chromatic number and a₁ < a₂ < ⋯ are the
  lengths of the odd cycles of G, then ∑ 1/aᵢ = ∞.

  History:
  - Erdős-Hajnal (1966): Conjectured this result
  - Erdős (1981): Asked if odd cycle lengths have positive upper density
  - Erdős (1995-96): Speculated upper density might be ≥ 1/2
  - Liu-Montgomery (2020): SOLVED - proved the conjecture

  Key insight: Graphs with infinite chromatic number must have "many" odd
  cycles in the sense that their reciprocal lengths diverge.

  This file formalizes the definitions and main result.
-/

import Mathlib

open Set BigOperators SimpleGraph

namespace Erdos57

variable {V : Type*}

/- ## Core Definitions -/

/-- The set of all cycle lengths in a graph using Mathlib's Walk.IsCycle. -/
def cycleLengths (G : SimpleGraph V) : Set ℕ :=
  { n | ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ p.length = n }

/-- The set of all odd cycle lengths in a graph. -/
def oddCycleLengths (G : SimpleGraph V) : Set ℕ :=
  { n ∈ cycleLengths G | Odd n }

/- ## Chromatic Number -/

/-- A graph is k-colorable if it admits a proper k-coloring. -/
def IsColorable (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ f : V → Fin k, ∀ u v, G.Adj u v → f u ≠ f v

/-- A graph has infinite chromatic number if it's not k-colorable for any finite k. -/
def HasInfiniteChromaticNumber (G : SimpleGraph V) : Prop :=
  ∀ k : ℕ, ¬IsColorable G k

/- ## The Harmonic Sum -/

/-- The sum ∑ 1/aᵢ where aᵢ are the odd cycle lengths. -/
noncomputable def oddCycleHarmonicSum (G : SimpleGraph V) : ENNReal :=
  ∑' n : (oddCycleLengths G), (1 : ENNReal) / n.val

/- ## Main Results -/

/--
**Erdős-Hajnal Conjecture (1966) - SOLVED by Liu-Montgomery (2020)**:
If G has infinite chromatic number, then ∑ 1/aᵢ = ∞ where aᵢ are odd cycle lengths.
-/
axiom erdos_57 (G : SimpleGraph V) :
    HasInfiniteChromaticNumber G → oddCycleHarmonicSum G = ⊤

/--
A finite sum of reciprocals is finite (not ⊤).
-/
lemma finite_reciprocal_sum_ne_top (S : Set ℕ) (hS : S.Finite) (hpos : ∀ n ∈ S, 0 < n) :
    ∑' n : S, (1 : ENNReal) / n.val ≠ ⊤ := by
  -- Convert tsum over finite subtype to Finset.sum
  have h_sum : ∑' n : S, (1 : ENNReal) / n.val =
      ∑ n ∈ hS.toFinset, (1 : ENNReal) / n := by
    rw [tsum_subtype S (fun n => (1 : ENNReal) / n)]
    rw [tsum_eq_sum (s := hS.toFinset)]
    · apply Finset.sum_congr rfl
      intro n hn
      simp only [Set.Finite.mem_toFinset] at hn ⊢
      simp [hn]
    · intro n hn
      simp only [Set.Finite.mem_toFinset] at hn
      simp [hn]
  rw [h_sum]
  -- Each term is finite, and finite sum of finite terms is finite
  have h_lt : ∑ n ∈ hS.toFinset, (1 : ENNReal) / n < ⊤ := by
    rw [ENNReal.sum_lt_top]
    intro n hn
    simp only [Set.Finite.mem_toFinset] at hn
    have hn_pos : 0 < n := hpos n hn
    apply ENNReal.div_lt_top (by norm_num)
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  exact h_lt.ne

/--
All odd cycle lengths are positive (≥ 3 actually, since minimum odd cycle is a triangle).
-/
lemma oddCycleLengths_pos (G : SimpleGraph V) : ∀ n ∈ oddCycleLengths G, 0 < n := by
  intro n hn
  simp only [oddCycleLengths, cycleLengths, Set.mem_setOf_eq] at hn
  obtain ⟨⟨u, p, hp, hlen⟩, hodd⟩ := hn
  rw [← hlen]
  -- A cycle has length ≥ 3, and odd cycles are at least 3
  have hge3 : 3 ≤ p.length := hp.three_le_length
  omega

/--
**Corollary**: A graph with infinite chromatic number has infinitely many
distinct odd cycle lengths.
-/
theorem infinite_odd_cycle_lengths (G : SimpleGraph V)
    (hG : HasInfiniteChromaticNumber G) : (oddCycleLengths G).Infinite := by
  by_contra h
  push_neg at h
  have h_sum := erdos_57 G hG
  -- If oddCycleLengths G is finite, the harmonic sum is finite (≠ ⊤)
  have h_ne_top := finite_reciprocal_sum_ne_top (oddCycleLengths G) h (oddCycleLengths_pos G)
  -- But h_sum says the harmonic sum = ⊤, contradiction
  exact h_ne_top h_sum

/- ## Related Questions (OPEN) -/

/-- Upper density of a set of natural numbers. -/
noncomputable def upperDensity (S : Set ℕ) : ℝ :=
  Filter.limsup (fun N => (Set.ncard (S ∩ Set.Icc 1 N) : ℝ) / N) Filter.atTop

/--
**Open Question (Erdős 1981)**:
Must odd cycle lengths have positive upper density?
-/
def UpperDensityConjecture : Prop :=
  ∀ (V : Type*) (G : SimpleGraph V),
    HasInfiniteChromaticNumber G → 0 < upperDensity (oddCycleLengths G)

/--
**Stronger Conjecture (Erdős 1995-96)**:
Upper density of odd cycle lengths is at least 1/2.
-/
def HalfDensityConjecture : Prop :=
  ∀ (V : Type*) (G : SimpleGraph V),
    HasInfiniteChromaticNumber G → 1/2 ≤ upperDensity (oddCycleLengths G)

/- ## Bipartite Characterization -/

/--
A `Bool`-coloring forbids odd cycles: by `Coloring.even_length_iff_congr`, every
closed walk `u → u` has even length (since `c u ↔ c u` holds trivially), so no
odd cycle length can occur.
-/
lemma noOddCycles_of_boolColoring {G : SimpleGraph V} (c : G.Coloring Bool) :
    oddCycleLengths G = ∅ := by
  rw [Set.eq_empty_iff_forall_not_mem]
  intro n hn
  simp only [oddCycleLengths, cycleLengths, Set.mem_setOf_eq] at hn
  obtain ⟨⟨u, p, _, hlen⟩, hodd⟩ := hn
  rw [← hlen] at hodd
  have hEven : Even p.length := (c.even_length_iff_congr p).mpr Iff.rfl
  exact (Nat.not_even_iff_odd.mpr hodd) hEven

/-- Rotating a closed walk preserves its length (auxiliary for the crux lemma). -/
theorem aux_length_rotate [DecidableEq V] {G : SimpleGraph V} {z y : V}
    (c : G.Walk y y) (h : z ∈ c.support) : (c.rotate h).length = c.length := by
  have hspec := congrArg Walk.length (c.take_spec h)
  rw [Walk.length_append] at hspec
  rw [show (c.rotate h) = (c.dropUntil z h).append (c.takeUntil z h) from rfl,
    Walk.length_append]
  omega

/-- A path between two vertices that uses the edge directly joining its two endpoints
must be the single-edge path (auxiliary for the crux lemma). -/
theorem isPath_length_one_of_mem_edges {G : SimpleGraph V} {v u : V} (p : G.Walk v u)
    (hp : p.IsPath) (he : s(u, v) ∈ p.edges) : p.length = 1 := by
  cases p with
  | nil => simp at he
  | @cons _ w _ e q =>
    rw [Walk.edges_cons, List.mem_cons] at he
    rw [Walk.cons_isPath_iff] at hp
    rcases he with heq | hmem
    · rw [Sym2.eq_iff] at heq
      have hvw : v ≠ w := e.ne
      have huw : u = w := by
        rcases heq with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact absurd h2 hvw
        · exact h1
      subst huw
      rw [Walk.isPath_iff_eq_nil] at hp
      have : q = Walk.nil := hp.1
      subst this
      simp
    · exact absurd (Walk.snd_mem_support_of_mem_edges q hmem) hp.2

/-- Strong-induction workhorse for `exists_odd_cycle_of_odd_closed_walk`: an odd-length
closed walk of length `n` contains an odd cycle. -/
theorem exists_odd_cycle_aux [DecidableEq V] {G : SimpleGraph V} (n : ℕ) :
    ∀ {u : V} (w : G.Walk u u),
      w.length = n → Odd n → ∃ (x : V) (c : G.Walk x x), c.IsCycle ∧ Odd c.length := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u w hlen hodd
    by_cases hcyc : w.IsCycle
    · exact ⟨u, w, hcyc, by rw [hlen]; exact hodd⟩
    · cases w with
      | nil => rw [Walk.length_nil] at hlen; obtain ⟨k, hk⟩ := hodd; omega
      | @cons _ v _ h p =>
        -- `w = cons h p` with `h : G.Adj u v`, `p : G.Walk v u`
        rw [Walk.cons_isCycle_iff] at hcyc
        -- since `w` is odd it is not a cycle, hence `p` is not a path: it repeats a vertex
        have hnp : ¬ p.IsPath := by
          intro hpath
          have hin : s(u, v) ∈ p.edges := by
            by_contra hnin
            exact hcyc ⟨hpath, hnin⟩
          have h1 : p.length = 1 := isPath_length_one_of_mem_edges p hpath hin
          rw [Walk.length_cons, h1] at hlen
          obtain ⟨k, hk⟩ := hodd; omega
        rw [Walk.isPath_def, List.nodup_iff_count_le_one] at hnp
        push_neg at hnp
        obtain ⟨z, hz2⟩ := hnp
        have hzp : z ∈ p.support := List.count_pos_iff.mp (by omega)
        have hzw : z ∈ (Walk.cons h p).support := by
          rw [Walk.support_cons]; exact List.mem_cons_of_mem _ hzp
        -- rotate the walk so it is based at the repeated vertex `z`
        set r : G.Walk z z := (Walk.cons h p).rotate hzw with hrdef
        have hlenr : r.length = n := by rw [hrdef, aux_length_rotate]; exact hlen
        have hcount : r.support.tail.count z = p.support.count z := by
          have hperm : r.support.tail ~r p.support := by
            have h0 := Walk.support_rotate (Walk.cons h p) hzw
            rw [← hrdef] at h0
            simpa only [Walk.support_cons, List.tail_cons] using h0
          exact hperm.perm.count_eq z
        clear_value r
        clear hrdef
        cases r with
        | nil => rw [Walk.length_nil] at hlenr; obtain ⟨k, hk⟩ := hodd; omega
        | @cons _ m _ e r' =>
          -- split the rotated walk `cons e r'` at the second occurrence of `z`
          have hlenr' : r'.length + 1 = n := by rw [Walk.length_cons] at hlenr; exact hlenr
          have hcz : 1 < r'.support.count z := by
            rw [Walk.support_cons, List.tail_cons] at hcount
            rw [hcount]; exact hz2
          have hz' : z ∈ r'.support := List.count_pos_iff.mp (by omega)
          have hts : (r'.takeUntil z hz').length + (r'.dropUntil z hz').length = r'.length := by
            have := congrArg Walk.length (r'.take_spec hz')
            rwa [Walk.length_append] at this
          have htailcount : 1 ≤ (r'.dropUntil z hz').support.tail.count z := by
            have hsplit : r'.support.count z
                = (r'.takeUntil z hz').support.count z
                  + (r'.dropUntil z hz').support.tail.count z := by
              conv_lhs => rw [← r'.take_spec hz']
              rw [Walk.support_append, List.count_append]
            rw [Walk.count_support_takeUntil_eq_one] at hsplit
            omega
          have hdr1 : 1 ≤ (r'.dropUntil z hz').length := by
            have hc1 : (r'.dropUntil z hz').support.tail.count z
                ≤ (r'.dropUntil z hz').support.tail.length := List.count_le_length
            rw [List.length_tail, Walk.length_support] at hc1
            omega
          have hra1 : 1 ≤ (Walk.cons e (r'.takeUntil z hz')).length := by
            rw [Walk.length_cons]; omega
          have hsum : (Walk.cons e (r'.takeUntil z hz')).length
              + (r'.dropUntil z hz').length = n := by
            rw [Walk.length_cons]; omega
          -- the two pieces are closed walks at `z`, strictly shorter, summing to an odd length;
          -- one of them is therefore odd, and the induction hypothesis applies
          rcases Nat.even_or_odd (r'.dropUntil z hz').length with hev | hod
          · have hraodd : Odd (Walk.cons e (r'.takeUntil z hz')).length := by
              have hno : Odd ((Walk.cons e (r'.takeUntil z hz')).length
                  + (r'.dropUntil z hz').length) := by rw [hsum]; exact hodd
              rw [Nat.odd_add] at hno
              exact hno.mpr hev
            exact ih (Walk.cons e (r'.takeUntil z hz')).length (by omega)
              (Walk.cons e (r'.takeUntil z hz')) rfl hraodd
          · exact ih (r'.dropUntil z hz').length (by omega)
              (r'.dropUntil z hz') rfl hod

/--
**Crux lemma (classical, Mathlib gap), now proved:** every odd closed walk contains an
odd cycle.

This is the only genuinely nonelementary ingredient of the bipartite characterization,
and Mathlib lists this exact statement as future work
(`Mathlib.Combinatorics.SimpleGraph.Bipartite`). The proof is strong induction on the walk
length (`exists_odd_cycle_aux`): if the walk is already a cycle we are done; otherwise it is
odd hence not a cycle, so by `cons_isCycle_iff` it repeats an interior vertex. Rotating to
that vertex and splitting at its second occurrence (`Walk.takeUntil`/`Walk.dropUntil`) yields
two strictly shorter closed walks whose lengths sum to the original odd length, so one of
them is an odd closed walk of smaller length and the induction hypothesis applies.
-/
theorem exists_odd_cycle_of_odd_closed_walk {G : SimpleGraph V} {u : V}
    (w : G.Walk u u) (hodd : Odd w.length) :
    ∃ (x : V) (c : G.Walk x x), c.IsCycle ∧ Odd c.length := by
  classical
  exact exists_odd_cycle_aux w.length w rfl hodd

/--
A graph is bipartite iff it has no odd cycles.

The forward direction is the elementary parity argument (a proper 2-coloring forces every
closed walk to have even length). The reverse direction is the classical direction. Rather
than rebuild a component-wise distance-parity coloring by hand, we route through Mathlib's
`two_colorable_iff_forall_loop_even` (which already supplies that construction): bipartite is
equivalent to "every closed walk has even length", and the contrapositive of that is exactly
`exists_odd_cycle_of_odd_closed_walk` — an odd loop would yield an odd cycle, contradicting
`oddCycleLengths G = ∅`. The whole reverse direction is therefore reduced to the single
classical walk lemma above (Mathlib lists this characterization as future work,
`Mathlib.Combinatorics.SimpleGraph.Bipartite`).
-/
theorem bipartite_iff_no_odd_cycles (G : SimpleGraph V) :
    G.IsBipartite ↔ oddCycleLengths G = ∅ := by
  constructor
  · intro hbip
    obtain ⟨c⟩ := hbip
    exact noOddCycles_of_boolColoring (G.recolorOfEquiv finTwoEquiv c)
  · intro hno
    refine SimpleGraph.two_colorable_iff_forall_loop_even.mpr ?_
    intro x w
    by_contra hne
    rw [Nat.not_even_iff_odd] at hne
    obtain ⟨y, c, hcyc, hcodd⟩ := exists_odd_cycle_of_odd_closed_walk w hne
    have hmem : c.length ∈ oddCycleLengths G := ⟨⟨y, c, hcyc, rfl⟩, hcodd⟩
    rw [hno] at hmem
    exact hmem

/-- 2-colorable graphs have no odd cycles. -/
theorem colorable_two_no_odd_cycles (G : SimpleGraph V)
    (h : IsColorable G 2) : oddCycleLengths G = ∅ := by
  obtain ⟨f, hf⟩ := h
  have hbip : G.IsBipartite :=
    ⟨SimpleGraph.Coloring.mk (G := G) f (fun {a b} hab => hf a b hab)⟩
  exact (bipartite_iff_no_odd_cycles G).mp hbip

/- ## Historical Notes

The Liu-Montgomery proof uses sophisticated techniques from extremal
combinatorics. The connection between chromatic number and odd cycles
is fundamental: bipartite iff no odd cycles iff χ(G) ≤ 2.

References:
- Erdős-Hajnal (1966): Original conjecture
- Liu-Montgomery (2020): "A solution to Erdős and Hajnal's odd cycle problem"
-/

end Erdos57
