/-
  Probabilistic Method Applications — Work in Progress completion.

  The companion file `ProbMethodApplications.lean` states several headline
  consequences of the probabilistic method (Ramsey lower bounds, Property B,
  tournament domination, ...), but the theorems there are *vacuous*: e.g.
  `ramsey_lower_bound` only asserts `∃ n, n ≥ 2^((k-1)/2)`, discharged by
  `⟨2^((k-1)/2), le_refl _⟩`, and none of the stated hypotheses are used.

  This file supplies the genuine engine those statements were standing in for:
  the **first-moment / union-bound existence principle** in its exact counting
  form, together with an honest, non-vacuous Ramsey-style application proved
  from it.

  Counting form of the first moment method:
    if the total size of finitely many "bad" subsets of a finite sample space
    is strictly smaller than the size of the whole space, then some sample
    point avoids every bad set.

  Everything here is `0 sorry`, `0 axiom`.
-/
import Mathlib

open Finset

namespace ProbMethod.Core

/-! ## The first-moment / union-bound existence principle -/

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {ι : Type*}

/-- **First-moment existence (counting union bound).**
If the cardinalities of finitely many subsets `A i` of a finite sample space
`Ω` sum to strictly less than `|Ω|`, then there is a point `ω` lying in none of
them. This is the combinatorial heart of the probabilistic method: a "bad
event" that is rare on average must be avoidable. -/
theorem exists_avoiding_all (s : Finset ι) (A : ι → Finset Ω)
    (h : ∑ i ∈ s, (A i).card < Fintype.card Ω) :
    ∃ ω : Ω, ∀ i ∈ s, ω ∉ A i := by
  have hbu : (s.biUnion A).card < Fintype.card Ω :=
    lt_of_le_of_lt (Finset.card_biUnion_le) h
  have hne : (s.biUnion A)ᶜ.Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl]
    omega
  obtain ⟨ω, hω⟩ := hne
  refine ⟨ω, ?_⟩
  intro i hi
  rw [Finset.mem_compl, Finset.mem_biUnion] at hω
  push_neg at hω
  exact hω i hi

/-- **Uniform union bound.** If every bad set has size at most `B` and
`|s| * B < |Ω|`, then a good point exists. This is the form most directly used
in applications, where each bad event has the same size bound. -/
theorem exists_good_of_card_bound (s : Finset ι) (A : ι → Finset Ω) (B : ℕ)
    (hbound : ∀ i ∈ s, (A i).card ≤ B)
    (h : s.card * B < Fintype.card Ω) :
    ∃ ω : Ω, ∀ i ∈ s, ω ∉ A i := by
  apply exists_avoiding_all s A
  calc ∑ i ∈ s, (A i).card
      ≤ ∑ _i ∈ s, B := Finset.sum_le_sum hbound
    _ = s.card * B := by rw [Finset.sum_const, smul_eq_mul]
    _ < Fintype.card Ω := h

/-! ## Counting two-colourings (sample space `Finset E`)

We model a 2-colouring of a finite "edge" set `E` as a `Finset E` (the edges
coloured `true`).  A block `K ⊆ E` is *monochromatic* under colouring `S` when
`S` is constant on `K`, i.e. `K ⊆ S` (all `true`) or `Disjoint K S` (all
`false`).  The number of colourings making a fixed `K` monochromatic is small,
which is exactly what the union bound needs. -/

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- A colouring `S` makes the block `K` monochromatic. Marked reducible so that
`DecidablePred (Mono K)` is found by instance search when filtering. -/
@[reducible] def Mono (K S : Finset E) : Prop := K ⊆ S ∨ Disjoint K S

/-- At most `2 ^ (|E| - |K|)` colourings contain `K` (all-`true` on `K`). -/
theorem card_supersets_le (K : Finset E) :
    ((univ : Finset (Finset E)).filter (fun S => K ⊆ S)).card
      ≤ 2 ^ (Fintype.card E - K.card) := by
  calc ((univ : Finset (Finset E)).filter (fun S => K ⊆ S)).card
      ≤ ((univ \ K).powerset).card := by
        apply Finset.card_le_card_of_injOn (fun S => S \ K)
        · intro S _hS
          have hsub : S \ K ⊆ univ \ K := by
            intro x hx; rw [mem_sdiff] at hx ⊢; exact ⟨mem_univ x, hx.2⟩
          simp only [Finset.mem_coe, Finset.mem_powerset]
          exact hsub
        · intro S hS S' hS' hSS'
          simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ,
            true_and] at hS hS'
          dsimp only at hSS'
          have hrec : (S \ K) ∪ K = (S' \ K) ∪ K := by rw [hSS']
          rwa [Finset.sdiff_union_of_subset hS, Finset.sdiff_union_of_subset hS']
            at hrec
    _ = 2 ^ (Fintype.card E - K.card) := by
        rw [card_powerset, ← Finset.compl_eq_univ_sdiff, Finset.card_compl]

/-- At most `2 ^ (|E| - |K|)` colourings are disjoint from `K` (all-`false` on
`K`). -/
theorem card_disjoint_le (K : Finset E) :
    ((univ : Finset (Finset E)).filter (fun S => Disjoint K S)).card
      ≤ 2 ^ (Fintype.card E - K.card) := by
  have hsub : (univ : Finset (Finset E)).filter (fun S => Disjoint K S)
      ⊆ (Kᶜ).powerset := by
    intro S hS
    rw [mem_filter] at hS
    rw [mem_powerset]
    intro x hx
    rw [mem_compl]
    intro hxK
    exact (Finset.disjoint_left.mp hS.2) hxK hx
  calc ((univ : Finset (Finset E)).filter (fun S => Disjoint K S)).card
      ≤ (Kᶜ).powerset.card := card_le_card hsub
    _ = 2 ^ (Fintype.card E - K.card) := by
        rw [card_powerset, card_compl]

/-- The number of colourings making `K` monochromatic is at most
`2 ^ (|E| - |K| + 1)`. -/
theorem card_mono_le (K : Finset E) :
    ((univ : Finset (Finset E)).filter (fun S => Mono K S)).card
      ≤ 2 ^ (Fintype.card E - K.card + 1) := by
  have hsplit : (univ : Finset (Finset E)).filter (fun S => Mono K S)
      = ((univ : Finset (Finset E)).filter (fun S => K ⊆ S))
        ∪ ((univ : Finset (Finset E)).filter (fun S => Disjoint K S)) := by
    rw [← Finset.filter_or]
  have h1 := card_supersets_le K
  have h2 := card_disjoint_le K
  have hpow : 2 ^ (Fintype.card E - K.card) + 2 ^ (Fintype.card E - K.card)
      = 2 ^ (Fintype.card E - K.card + 1) := by
    rw [pow_succ]; ring
  rw [hsplit]
  calc (((univ : Finset (Finset E)).filter (fun S => K ⊆ S))
          ∪ ((univ : Finset (Finset E)).filter (fun S => Disjoint K S))).card
      ≤ ((univ : Finset (Finset E)).filter (fun S => K ⊆ S)).card
        + ((univ : Finset (Finset E)).filter (fun S => Disjoint K S)).card :=
        Finset.card_union_le _ _
    _ ≤ 2 ^ (Fintype.card E - K.card + 1) := by omega

/-! ## Ramsey-style avoidance (honest probabilistic existence) -/

/-- **Ramsey lower bound, avoidance form.**
Let `E` be a finite set of "edges" and `cliques` a family of `m`-element blocks.
If the expected number of monochromatic blocks is below one — concretely if
`|cliques| * 2 ^ (|E| - m + 1) < 2 ^ |E|` — then there is a 2-colouring of `E`
in which *no* block is monochromatic.

Instantiating `E` as the edge set of `K_n` (so `|E| = C(n,2)`) and `cliques` as
the `C(n,m)` copies of `K_m`, the hypothesis becomes
`C(n,m) * 2 ^ (C(n,2) - C(m,2) + 1) < 2 ^ C(n,2)`, i.e. the classical
`C(n,m) * 2^(1 - C(m,2)) < 1`, and the conclusion is the Erdős (1947) lower
bound `R(m,m) > n`.  Unlike the placeholder `ramsey_lower_bound`, every
hypothesis here does real work. -/
theorem ramsey_avoidance
    (cliques : Finset (Finset E)) (m : ℕ)
    (hm : ∀ K ∈ cliques, K.card = m)
    (h : cliques.card * (2 ^ (Fintype.card E - m + 1)) < 2 ^ (Fintype.card E)) :
    ∃ S : Finset E, ∀ K ∈ cliques, ¬ Mono K S := by
  have hcard : Fintype.card (Finset E) = 2 ^ Fintype.card E := Fintype.card_finset
  have hbound : ∀ K ∈ cliques,
      ((univ : Finset (Finset E)).filter (fun S => Mono K S)).card
        ≤ 2 ^ (Fintype.card E - m + 1) := by
    intro K hK
    have := card_mono_le K
    rwa [hm K hK] at this
  have hlt : cliques.card * (2 ^ (Fintype.card E - m + 1))
      < Fintype.card (Finset E) := by rw [hcard]; exact h
  obtain ⟨S, hS⟩ := exists_good_of_card_bound (Ω := Finset E) cliques
    (fun K => (univ : Finset (Finset E)).filter (fun S => Mono K S))
    (2 ^ (Fintype.card E - m + 1)) hbound hlt
  refine ⟨S, fun K hK => ?_⟩
  have hmem := hS K hK
  rw [mem_filter] at hmem
  push_neg at hmem
  exact not_or.mpr (hmem (mem_univ S))

end ProbMethod.Core
