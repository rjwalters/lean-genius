/-
  Erdős Problem #131 — Non-Dividing Sets
  Follow-up (oq-01-oq-01-oq-01-oq-04-oq-01): the GENERAL direct-sum Davenport
  lower bound

      D(G₁ ⊕ G₂) ≥ D(G₁) + D(G₂) − 1            for additive groups G₁, G₂.

  Source: https://erdosproblems.com/131
  Companion to:
    * `Proofs.Erdos131DavenportRank2`     — the rank-2 CYCLIC lower bound
      `D(ℤ/aℤ ⊕ ℤ/bℤ) ≥ a + b − 1`, proved with an explicit extremal sequence;
    * `Proofs.Erdos131DavenportConstant`  — the EXACT cyclic value `D(ℤ/nℤ) = n`.

  NOTE.  This file is deliberately SELF-CONTAINED (only `import Mathlib`); it does
  not import the companions, which keeps it independently verifiable and
  axiom-free.

  ## What this file adds

  The rank-2 companion proves `D(ℤ/aℤ ⊕ ℤ/bℤ) ≥ a + b − 1` by exhibiting *one*
  concrete extremal sequence in `ℤ/aℤ ⊕ ℤ/bℤ`.  Here we prove the underlying
  STRUCTURAL principle in full generality, for ARBITRARY additive groups:

      D(G₁ ⊕ G₂) ≥ D(G₁) + D(G₂) − 1.

  The engine is the **concatenation principle** for zero-sum-free sequences: if
  `f₁` is a zero-sum-free sequence over `G₁` and `f₂` is one over `G₂`, then the
  sequence `(f₁ i, 0)` followed by `(0, f₂ j)` is zero-sum-free over `G₁ ⊕ G₂`.
  The proof reindexes a candidate zero-sum subset along `Fin m₁ ⊕ Fin m₂ ≃ Fin
  (m₁ + m₂)`, splits it into its `G₁`- and `G₂`-blocks (`Finset.toLeft` /
  `Finset.toRight`), reads off the two coordinates, and uses zero-sum-freeness of
  each factor to force both blocks empty.

  Specialising `G₁ = ℤ/aℤ`, `G₂ = ℤ/bℤ` with the cyclic value `D(ℤ/nℤ) = n`
  recovers the rank-2 bound `a + b − 1`; the upper bound `D(ℤ/aℤ ⊕ ℤ/bℤ) = a+b−1`
  for `a ∣ b` is Olson's theorem, a substantial result not in Mathlib and not
  formalized here.

  All results are unconditional and axiom-free.
-/

import Mathlib

namespace Erdos131DavenportDirectSum

open Finset

/-- A sequence `f : Fin m → G` *has a nonempty zero-sum subsequence* if some
nonempty index set `s` has `∑ i ∈ s, f i = 0`. -/
def HasZeroSumSubseq {G : Type*} [AddCommMonoid G] {m : ℕ} (f : Fin m → G) : Prop :=
  ∃ s : Finset (Fin m), s.Nonempty ∧ ∑ i ∈ s, f i = 0

/-- The **Davenport set** of `G`: the lengths `m` such that *every* length-`m`
sequence over `G` has a nonempty zero-sum subsequence.  The Davenport constant
`D(G)` is the least element of this set. -/
def DavenportSet (G : Type*) [AddCommMonoid G] : Set ℕ :=
  {m | ∀ f : Fin m → G, HasZeroSumSubseq f}

/-- **The Davenport set is upward closed.**  If every length-`m` sequence has a
nonempty zero-sum subsequence, then so does every length-`m'` sequence for
`m ≤ m'`.

Restrict `f : Fin m' → G` to its first `m` entries via `Fin.castLE`, obtain a
zero-sum subset `s : Finset (Fin m)`, and re-embed it into `Fin m'` with the
order embedding `Fin.castLEEmb`; `Finset.sum_map` keeps the sum unchanged. -/
theorem davenport_set_mono {G : Type*} [AddCommMonoid G] {m m' : ℕ} (h : m ≤ m')
    (hm : m ∈ DavenportSet G) : m' ∈ DavenportSet G := by
  intro f
  obtain ⟨s, hne, hsum⟩ := hm (fun i => f (Fin.castLE h i))
  refine ⟨s.map (Fin.castLEEmb h), Finset.map_nonempty.mpr hne, ?_⟩
  rw [Finset.sum_map]
  simpa [Fin.coe_castLEEmb] using hsum

/-- **Length `0` is never a Davenport length.**  The empty sequence has no
nonempty index subset at all, so `HasZeroSumSubseq` fails vacuously. -/
theorem zero_not_mem_davenportSet (G : Type*) [AddCommMonoid G] :
    0 ∉ DavenportSet G := by
  intro h
  obtain ⟨s, hne, _⟩ := h (fun _ => 0)
  obtain ⟨i, _⟩ := hne
  exact absurd i.2 (by omega)

/-- **The least Davenport length is positive.**  Since `0 ∉ DavenportSet G`, the
least element of a nonempty Davenport set is at least `1`. -/
theorem one_le_of_isLeast_davenport {G : Type*} [AddCommMonoid G] {d : ℕ}
    (hd : IsLeast (DavenportSet G) d) : 1 ≤ d := by
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · exact absurd (h0 ▸ hd.1) (zero_not_mem_davenportSet G)
  · exact hpos

/-- **The concatenated sequence.**  Place `f₁` in the first coordinate over the
first block, and `f₂` in the second coordinate over the second block:
`concatSeq f₁ f₂` sends the `i`-th index (`i < m₁`) to `(f₁ i, 0)` and the
`(m₁ + j)`-th index to `(0, f₂ j)`. -/
def concatSeq {G₁ G₂ : Type*} [Zero G₁] [Zero G₂] {m₁ m₂ : ℕ}
    (f₁ : Fin m₁ → G₁) (f₂ : Fin m₂ → G₂) : Fin (m₁ + m₂) → G₁ × G₂ :=
  Fin.addCases (fun i => (f₁ i, 0)) (fun j => (0, f₂ j))

/-- **Concatenation preserves zero-sum-freeness.**  If `f₁` over `G₁` and `f₂`
over `G₂` each have no nonempty zero-sum subsequence, then neither does their
concatenation over `G₁ ⊕ G₂`.

A candidate zero-sum subset `s ⊆ Fin (m₁ + m₂)` is reindexed along
`finSumFinEquiv : Fin m₁ ⊕ Fin m₂ ≃ Fin (m₁ + m₂)` to `t ⊆ Fin m₁ ⊕ Fin m₂`,
split into `t.toLeft` and `t.toRight`.  The first coordinate of the total sum is
`∑_{j ∈ t.toLeft} f₁ j`, the second is `∑_{k ∈ t.toRight} f₂ k`; both vanish, so
zero-sum-freeness of `f₁`, `f₂` forces both blocks empty, hence `t = ∅` and
`s = ∅`. -/
theorem concat_not_hasZeroSum {G₁ G₂ : Type*} [AddCommGroup G₁] [AddCommGroup G₂]
    {m₁ m₂ : ℕ} {f₁ : Fin m₁ → G₁} {f₂ : Fin m₂ → G₂}
    (h₁ : ¬ HasZeroSumSubseq f₁) (h₂ : ¬ HasZeroSumSubseq f₂) :
    ¬ HasZeroSumSubseq (concatSeq f₁ f₂) := by
  rintro ⟨s, hne, hsum⟩
  -- Reindex `s` along `Fin m₁ ⊕ Fin m₂ ≃ Fin (m₁ + m₂)`.
  set t : Finset (Fin m₁ ⊕ Fin m₂) := s.map finSumFinEquiv.symm.toEmbedding with ht
  have hmap : t.map finSumFinEquiv.toEmbedding = s := by
    rw [ht, Finset.map_map]; ext x; simp
  rw [← hmap, Finset.sum_map, ← Finset.toLeft_disjSum_toRight (u := t),
      Finset.sum_disjSum] at hsum
  simp only [Equiv.coe_toEmbedding, finSumFinEquiv_apply_left,
    finSumFinEquiv_apply_right, concatSeq, Fin.addCases_left, Fin.addCases_right]
    at hsum
  -- Read off the two coordinates of the (vanishing) total.
  have hL : ∑ j ∈ t.toLeft, f₁ j = 0 := by
    have h := congrArg Prod.fst hsum
    simpa [Prod.fst_sum] using h
  have hR : ∑ k ∈ t.toRight, f₂ k = 0 := by
    have h := congrArg Prod.snd hsum
    simpa [Prod.snd_sum] using h
  -- Zero-sum-freeness forces each block empty.
  have hLempty : t.toLeft = ∅ := by
    by_contra h0
    exact h₁ ⟨t.toLeft, Finset.nonempty_of_ne_empty h0, hL⟩
  have hRempty : t.toRight = ∅ := by
    by_contra h0
    exact h₂ ⟨t.toRight, Finset.nonempty_of_ne_empty h0, hR⟩
  -- Hence `t = ∅`, so `s = ∅`, contradicting nonemptiness.
  have htempty : t = ∅ := by
    rw [← Finset.toLeft_disjSum_toRight (u := t), Finset.disjSum_eq_empty]
    exact ⟨hLempty, hRempty⟩
  have hsempty : s = ∅ := by rw [← hmap, htempty, Finset.map_empty]
  exact absurd hne (hsempty ▸ Finset.not_nonempty_empty)

/-- **General direct-sum Davenport lower bound: `D(G₁ ⊕ G₂) ≥ D(G₁) + D(G₂) − 1`.**

Let `d₁ = D(G₁)`, `d₂ = D(G₂)`, `d = D(G₁ ⊕ G₂)` be the least Davenport lengths.
Since `d₁` is least, length `d₁ − 1` admits a zero-sum-free sequence `f₁`;
likewise `f₂` of length `d₂ − 1`.  Their concatenation is a zero-sum-free
sequence over `G₁ ⊕ G₂` of length `(d₁ − 1) + (d₂ − 1) = d₁ + d₂ − 2`, so that
length is NOT a Davenport length.  Were `d ≤ d₁ + d₂ − 2`, upward closure would
make `d₁ + d₂ − 2` a Davenport length — contradiction.  Hence `d ≥ d₁+d₂−1`. -/
theorem davenport_directSum_lower {G₁ G₂ : Type*} [AddCommGroup G₁]
    [AddCommGroup G₂] {d₁ d₂ d : ℕ}
    (h₁ : IsLeast (DavenportSet G₁) d₁) (h₂ : IsLeast (DavenportSet G₂) d₂)
    (hd : IsLeast (DavenportSet (G₁ × G₂)) d) :
    d₁ + d₂ - 1 ≤ d := by
  have hd₁ : 1 ≤ d₁ := one_le_of_isLeast_davenport h₁
  have hd₂ : 1 ≤ d₂ := one_le_of_isLeast_davenport h₂
  -- `d₁ − 1` is below the least Davenport length, so it is not in the set:
  -- there is a zero-sum-free sequence `f₁` of length `d₁ − 1`.
  have hns₁ : (d₁ - 1) ∉ DavenportSet G₁ := fun hmem =>
    absurd (h₁.2 hmem) (by omega)
  have hns₂ : (d₂ - 1) ∉ DavenportSet G₂ := fun hmem =>
    absurd (h₂.2 hmem) (by omega)
  rw [DavenportSet, Set.mem_setOf_eq, not_forall] at hns₁ hns₂
  obtain ⟨f₁, hf₁⟩ := hns₁
  obtain ⟨f₂, hf₂⟩ := hns₂
  -- The concatenation is zero-sum-free, so its length is not a Davenport length.
  have hfree : ¬ HasZeroSumSubseq (concatSeq f₁ f₂) := concat_not_hasZeroSum hf₁ hf₂
  by_contra hlt
  push_neg at hlt
  -- `d ≤ (d₁ − 1) + (d₂ − 1)`, so upward closure makes that a Davenport length.
  have hdle : d ≤ (d₁ - 1) + (d₂ - 1) := by omega
  have hmem : ((d₁ - 1) + (d₂ - 1)) ∈ DavenportSet (G₁ × G₂) :=
    davenport_set_mono hdle hd.1
  exact hfree (hmem (concatSeq f₁ f₂))

/-- **Recovering the rank-2 cyclic bound.**  Given the cyclic Davenport values
`D(ℤ/aℤ) = a` and `D(ℤ/bℤ) = b` (companion `Erdos131DavenportConstant`), the
general bound specialises to `D(ℤ/aℤ ⊕ ℤ/bℤ) ≥ a + b − 1`. -/
theorem davenport_rank2_lower_of_cyclic {a b d : ℕ}
    (ha : IsLeast (DavenportSet (ZMod a)) a) (hb : IsLeast (DavenportSet (ZMod b)) b)
    (hd : IsLeast (DavenportSet (ZMod a × ZMod b)) d) :
    a + b - 1 ≤ d :=
  davenport_directSum_lower ha hb hd

/-- **Diagonal special case: `D(G ⊕ G) ≥ 2·D(G) − 1`.**  For `G = ℤ/nℤ` this is
the sharp bound `D(ℤ/nℤ ⊕ ℤ/nℤ) ≥ 2n − 1` (Olson's theorem gives equality; the
matching upper bound is not formalized here). -/
theorem davenport_directSum_diag_lower {G : Type*} [AddCommGroup G] {c d : ℕ}
    (hc : IsLeast (DavenportSet G) c) (hd : IsLeast (DavenportSet (G × G)) d) :
    2 * c - 1 ≤ d := by
  have := davenport_directSum_lower hc hc hd
  omega

end Erdos131DavenportDirectSum
