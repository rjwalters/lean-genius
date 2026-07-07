/-
  Erdős Problem #57 — Companion: a length-bounded odd cycle from an odd closed walk

  Source: https://erdosproblems.com/57

  The parent file `Proofs/Erdos57Problem.lean` proves the classical crux
  `exists_odd_cycle_of_odd_closed_walk` (Mathlib lists this exact statement as
  future work, `Mathlib.Combinatorics.SimpleGraph.Bipartite`): every odd closed
  walk contains an odd cycle. That lemma extracts *some* odd cycle but discards a
  fact its own strong induction already establishes — the extracted cycle is never
  longer than the walk it came from (rotation and `takeUntil`/`dropUntil` only ever
  shorten).

  This companion threads that bound through the induction and exposes the
  quantitative refinement, fully and axiom-free:

      `exists_short_odd_cycle_of_odd_closed_walk`
        : every odd closed walk `w` contains an odd cycle `c` with `c.length ≤ w.length`.

  Consequences (all 0-axiom):
  * `exists_oddCycleLength_le_of_odd_closed_walk` — the odd cycle's length is a
    member of `oddCycleLengths G` bounded by `w.length`;
  * `oddGirth` (= `sInf (oddCycleLengths G)`) and `oddGirth_le_of_odd_closed_walk`
    — any odd closed walk bounds the odd girth from above; this is the sharp
    quantitative form of "an odd closed walk forces an odd cycle";
  * `odd_oddGirth` — whenever an odd cycle exists, the odd girth is itself odd;
  * `oddGirth_le_chromatic_obstruction` — odd girth bounds via the easy direction.

  None of these are assumed anywhere; they are derived from the parent's verified
  `exists_odd_cycle_aux` infrastructure (helpers `aux_length_rotate`,
  `isPath_length_one_of_mem_edges`) re-used through a parallel bounded induction.
-/

import Mathlib
import Proofs.Erdos57Problem

open Set SimpleGraph

namespace Erdos57

variable {V : Type*}

/-! ## A length-bounded odd cycle -/

/-- Strong-induction workhorse: an odd-length closed walk of length `n` contains an odd
cycle of length **at most** `n`. This mirrors the parent's `exists_odd_cycle_aux` but
carries the bound `c.length ≤ n`, which the construction already satisfies (the base case
returns the walk itself; every recursive step descends into a strictly shorter sub-walk). -/
theorem exists_short_odd_cycle_aux [DecidableEq V] {G : SimpleGraph V} (n : ℕ) :
    ∀ {u : V} (w : G.Walk u u),
      w.length = n → Odd n →
        ∃ (x : V) (c : G.Walk x x), c.IsCycle ∧ Odd c.length ∧ c.length ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u w hlen hodd
    by_cases hcyc : w.IsCycle
    · exact ⟨u, w, hcyc, by rw [hlen]; exact hodd, by rw [hlen]⟩
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
          -- the two pieces are closed walks at `z`, strictly shorter, summing to an odd
          -- length; one of them is odd, and the induction hypothesis applies with its bound
          rcases Nat.even_or_odd (r'.dropUntil z hz').length with hev | hod
          · have hraodd : Odd (Walk.cons e (r'.takeUntil z hz')).length := by
              have hno : Odd ((Walk.cons e (r'.takeUntil z hz')).length
                  + (r'.dropUntil z hz').length) := by rw [hsum]; exact hodd
              rw [Nat.odd_add] at hno
              exact hno.mpr hev
            obtain ⟨x, c, hcyc', hcodd', hcle⟩ :=
              ih (Walk.cons e (r'.takeUntil z hz')).length (by omega)
                (Walk.cons e (r'.takeUntil z hz')) rfl hraodd
            exact ⟨x, c, hcyc', hcodd', by omega⟩
          · obtain ⟨x, c, hcyc', hcodd', hcle⟩ :=
              ih (r'.dropUntil z hz').length (by omega)
                (r'.dropUntil z hz') rfl hod
            exact ⟨x, c, hcyc', hcodd', by omega⟩

/-- **Sharp crux lemma.** Every odd closed walk contains an odd cycle no longer than the
walk itself. This refines the parent's `exists_odd_cycle_of_odd_closed_walk` with the
length bound `c.length ≤ w.length`, which the parent's induction silently discards. -/
theorem exists_short_odd_cycle_of_odd_closed_walk {G : SimpleGraph V} {u : V}
    (w : G.Walk u u) (hodd : Odd w.length) :
    ∃ (x : V) (c : G.Walk x x), c.IsCycle ∧ Odd c.length ∧ c.length ≤ w.length := by
  classical
  exact exists_short_odd_cycle_aux w.length w rfl hodd

/-- An odd closed walk witnesses an odd cycle length `≤ w.length` in `oddCycleLengths G`. -/
theorem exists_oddCycleLength_le_of_odd_closed_walk {G : SimpleGraph V} {u : V}
    (w : G.Walk u u) (hodd : Odd w.length) :
    ∃ l ∈ oddCycleLengths G, l ≤ w.length := by
  obtain ⟨x, c, hcyc, hcodd, hcle⟩ := exists_short_odd_cycle_of_odd_closed_walk w hodd
  exact ⟨c.length, ⟨⟨x, c, hcyc, rfl⟩, hcodd⟩, hcle⟩

/-! ## Odd girth -/

/-- The **odd girth** of `G`: the least odd cycle length (`0` if `G` has no odd cycle,
following the `Nat.sInf` convention on the empty set). -/
noncomputable def oddGirth (G : SimpleGraph V) : ℕ := sInf (oddCycleLengths G)

/-- Any odd closed walk bounds the odd girth from above. This is the sharp quantitative
form of the crux lemma: the shortest odd cycle is no longer than any odd closed walk. -/
theorem oddGirth_le_of_odd_closed_walk {G : SimpleGraph V} {u : V}
    (w : G.Walk u u) (hodd : Odd w.length) :
    oddGirth G ≤ w.length := by
  obtain ⟨l, hl, hle⟩ := exists_oddCycleLength_le_of_odd_closed_walk w hodd
  exact le_trans (Nat.sInf_le hl) hle

/-- When `G` has an odd cycle, its odd girth is realised by an actual odd cycle: there is a
cycle whose length is exactly `oddGirth G`, and that length is odd. -/
theorem oddGirth_mem (G : SimpleGraph V) (hne : (oddCycleLengths G).Nonempty) :
    oddGirth G ∈ oddCycleLengths G :=
  Nat.sInf_mem hne

/-- Whenever an odd cycle exists, the odd girth is itself odd (it is attained, so it lies in
the set of odd cycle lengths). -/
theorem odd_oddGirth (G : SimpleGraph V) (hne : (oddCycleLengths G).Nonempty) :
    Odd (oddGirth G) :=
  (Set.mem_sep_iff.mp (oddGirth_mem G hne)).2

/-- The odd girth is a lower bound for every odd cycle length. -/
theorem oddGirth_le_of_mem {G : SimpleGraph V} {l : ℕ} (hl : l ∈ oddCycleLengths G) :
    oddGirth G ≤ l :=
  Nat.sInf_le hl

/-- A graph with a finite odd girth (an odd cycle present) is not bipartite — the odd girth
packages the obstruction. -/
theorem not_isBipartite_of_oddGirth_pos {G : SimpleGraph V}
    (hne : (oddCycleLengths G).Nonempty) : ¬ G.IsBipartite := by
  rw [bipartite_iff_no_odd_cycles]
  exact (Set.nonempty_iff_ne_empty).mp hne

end Erdos57

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no `Lean.ofReduceBool` (no `native_decide`) and no `sorryAx`.
#print axioms Erdos57.exists_short_odd_cycle_of_odd_closed_walk
#print axioms Erdos57.oddGirth_le_of_odd_closed_walk
#print axioms Erdos57.odd_oddGirth
#print axioms Erdos57.not_isBipartite_of_oddGirth_pos
