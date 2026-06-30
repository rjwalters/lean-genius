/-
  Erdős Problem #131 — Non-Dividing Sets
  Follow-up (oq-01-oq-01-oq-01-oq-04-oq-03-oq-01): the homogeneous-power
  Davenport lower bound

      D(Gⁿ) ≥ n·(D(G) − 1) + 1            for an additive group G,

  where `Gⁿ = Fin n → G` is the `n`-fold direct power.

  Source: https://erdosproblems.com/131
  Companion to:
    * `Proofs.Erdos131DavenportDirectSum` — the BINARY direct-sum lower bound
      `D(G₁ ⊕ G₂) ≥ D(G₁) + D(G₂) − 1`;
    * `Proofs.Erdos131DavenportRank2`     — the rank-2 cyclic instance;
    * `Proofs.Erdos131DavenportConstant`  — the exact cyclic value `D(ℤ/nℤ) = n`.

  NOTE.  This file is deliberately SELF-CONTAINED (only `import Mathlib`); it does
  not import the companions, which keeps it independently verifiable and
  axiom-free.  The three small helper lemmas about `DavenportSet` are reproduced
  here verbatim from the direct-sum companion.

  ## What this file adds

  Iterating the binary bound `D(G₁ ⊕ G₂) ≥ D(G₁) + D(G₂) − 1` over `n` copies of
  `G` gives `D(Gⁿ) ≥ n·(D(G) − 1) + 1`.  Such an induction would, however, need
  the Davenport constant of every intermediate power `Gᵏ` to exist (i.e.
  `IsLeast` hypotheses at each stage), which forces a separate finiteness
  argument.  Here we instead prove the bound in **one shot** with an explicit
  extremal construction, the **power sequence** `powerSeq n f`.

  Given a zero-sum-free sequence `f : Fin ℓ → G`, the power sequence is indexed by
  `Fin n × Fin ℓ ≃ Fin (n·ℓ)` and sends `(i, k) ↦ Pi.single i (f k)` — i.e. it
  places `f k` in coordinate `i` of `Gⁿ` and `0` elsewhere.  Evaluating any
  candidate zero-sum subset coordinatewise turns the `j`-th coordinate of the
  total into the sum of `f` over the slice `{k : (j, k) ∈ s}`; zero-sum-freeness
  of `f` forces every slice empty, hence the subset empty.  So `powerSeq n f` is
  a zero-sum-free sequence over `Gⁿ` of length `n·ℓ`; taking `ℓ = D(G) − 1`
  yields the bound.

  Specialising `G = ℤ/pℤ` with `D(ℤ/pℤ) = p` gives

      D((ℤ/pℤ)ⁿ) ≥ n·(p − 1) + 1,

  the lower-bound half of Olson's theorem for elementary abelian `p`-groups
  (where equality in fact holds — the matching upper bound is a substantial
  result not in Mathlib and not formalized here).

  All results are unconditional and axiom-free.
-/

import Mathlib

namespace Erdos131DavenportPower

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

/-- **The Davenport set is upward closed.** -/
theorem davenport_set_mono {G : Type*} [AddCommMonoid G] {m m' : ℕ} (h : m ≤ m')
    (hm : m ∈ DavenportSet G) : m' ∈ DavenportSet G := by
  intro f
  obtain ⟨s, hne, hsum⟩ := hm (fun i => f (Fin.castLE h i))
  refine ⟨s.map (Fin.castLEEmb h), Finset.map_nonempty.mpr hne, ?_⟩
  rw [Finset.sum_map]
  simpa [Fin.coe_castLEEmb] using hsum

/-- **Length `0` is never a Davenport length.** -/
theorem zero_not_mem_davenportSet (G : Type*) [AddCommMonoid G] :
    0 ∉ DavenportSet G := by
  intro h
  obtain ⟨s, hne, _⟩ := h (fun _ => 0)
  obtain ⟨i, _⟩ := hne
  exact absurd i.2 (by omega)

/-- **The least Davenport length is positive.** -/
theorem one_le_of_isLeast_davenport {G : Type*} [AddCommMonoid G] {d : ℕ}
    (hd : IsLeast (DavenportSet G) d) : 1 ≤ d := by
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · exact absurd (h0 ▸ hd.1) (zero_not_mem_davenportSet G)
  · exact hpos

/-- **The power sequence.**  Given `f : Fin ℓ → G`, the sequence
`powerSeq n f : Fin (n·ℓ) → (Fin n → G)` sends the index `x`, decoded as
`(i, k) : Fin n × Fin ℓ` via `finProdFinEquiv`, to the vector `Pi.single i (f k)`
— i.e. `f k` in coordinate `i` and `0` in all other coordinates. -/
def powerSeq {G : Type*} [Zero G] {ℓ : ℕ} (n : ℕ) (f : Fin ℓ → G) :
    Fin (n * ℓ) → (Fin n → G) :=
  fun x => Pi.single (finProdFinEquiv.symm x : Fin n × Fin ℓ).1
                     (f (finProdFinEquiv.symm x : Fin n × Fin ℓ).2)

/-- **The power sequence is zero-sum-free.**  If `f` over `G` has no nonempty
zero-sum subsequence, then neither does `powerSeq n f` over `Gⁿ`.

A candidate zero-sum subset `s ⊆ Fin (n·ℓ)` is reindexed along
`finProdFinEquiv : Fin n × Fin ℓ ≃ Fin (n·ℓ)` to `t ⊆ Fin n × Fin ℓ`.  The total
sum is then `∑_{(i,k) ∈ t} Pi.single i (f k)`; reading off its `j`-th coordinate
keeps only the terms with `i = j`, giving `∑_{k : (j,k) ∈ t} f k = 0` for every
`j`.  Zero-sum-freeness of `f` forces each such slice empty, hence `t = ∅` and
`s = ∅`, contradicting nonemptiness. -/
theorem powerseq_not_hasZeroSum {G : Type*} [AddCommGroup G] {ℓ n : ℕ}
    {f : Fin ℓ → G} (hf : ¬ HasZeroSumSubseq f) :
    ¬ HasZeroSumSubseq (powerSeq n f) := by
  rintro ⟨s, hne, hsum⟩
  -- Reindex `s` along `Fin n × Fin ℓ ≃ Fin (n·ℓ)`.
  set t : Finset (Fin n × Fin ℓ) := s.map finProdFinEquiv.symm.toEmbedding with ht
  have hmap : t.map finProdFinEquiv.toEmbedding = s := by
    rw [ht, Finset.map_map]; ext x; simp
  rw [← hmap, Finset.sum_map] at hsum
  simp only [Equiv.coe_toEmbedding, powerSeq, Equiv.symm_apply_apply] at hsum
  -- `hsum : ∑ x ∈ t, Pi.single x.1 (f x.2) = 0`
  -- For each coordinate `j`, the slice over `j` has vanishing sum.
  have hcoord : ∀ j : Fin n,
      ∑ x ∈ t, (Pi.single x.1 (f x.2) : Fin n → G) j = 0 := by
    intro j
    have h := congrFun hsum j
    rwa [Finset.sum_apply, Pi.zero_apply] at h
  have hslice : ∀ j : Fin n, ∑ x ∈ t.filter (fun x => j = x.1), f x.2 = 0 := by
    intro j
    have h := hcoord j
    simp only [Pi.single_apply] at h
    rwa [← Finset.sum_filter] at h
  -- Zero-sum-freeness forces every slice (filter) empty.
  have hfemp : ∀ j : Fin n, t.filter (fun x => j = x.1) = ∅ := by
    intro j
    by_contra hnz
    obtain ⟨x0, hx0⟩ := Finset.nonempty_of_ne_empty hnz
    -- The image of the slice under `Prod.snd` is a zero-sum subset of `f`.
    have hinj : ∀ a ∈ t.filter (fun x => j = x.1),
        ∀ b ∈ t.filter (fun x => j = x.1), a.2 = b.2 → a = b := by
      intro a ha b hb hab
      rw [Finset.mem_filter] at ha hb
      have hfst : a.1 = b.1 := by rw [← ha.2, ← hb.2]
      exact Prod.ext_iff.mpr ⟨hfst, hab⟩
    set K := (t.filter (fun x => j = x.1)).image Prod.snd with hK
    have hKsum : ∑ k ∈ K, f k = 0 := by
      rw [hK, Finset.sum_image hinj]; exact hslice j
    have hKne : K.Nonempty := ⟨x0.2, by rw [hK]; exact Finset.mem_image_of_mem _ hx0⟩
    exact hf ⟨K, hKne, hKsum⟩
  -- Hence `t = ∅`, so `s = ∅`, contradicting nonemptiness.
  have htempty : t = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    have hxmem : x ∈ t.filter (fun y => x.1 = y.1) :=
      Finset.mem_filter.mpr ⟨hx, rfl⟩
    rw [hfemp x.1] at hxmem
    exact absurd hxmem (Finset.notMem_empty _)
  have hsempty : s = ∅ := by rw [← hmap, htempty, Finset.map_empty]
  exact absurd hne (hsempty ▸ Finset.not_nonempty_empty)

/-- **Homogeneous-power Davenport lower bound: `D(Gⁿ) ≥ n·(D(G) − 1) + 1`.**

Let `d = D(G)` and `dₙ = D(Gⁿ)` be the least Davenport lengths.  Since `d` is
least, length `d − 1` admits a zero-sum-free sequence `f`.  Its power sequence
`powerSeq n f` is a zero-sum-free sequence over `Gⁿ` of length `n·(d − 1)`, so
that length is NOT a Davenport length.  Were `dₙ ≤ n·(d − 1)`, upward closure
would make `n·(d − 1)` a Davenport length — contradiction.  Hence
`dₙ ≥ n·(d − 1) + 1`. -/
theorem davenport_pow_lower {G : Type*} [AddCommGroup G] {d dₙ n : ℕ}
    (hG : IsLeast (DavenportSet G) d)
    (hpow : IsLeast (DavenportSet (Fin n → G)) dₙ) :
    n * (d - 1) + 1 ≤ dₙ := by
  have hd1 : 1 ≤ d := one_le_of_isLeast_davenport hG
  -- `d − 1` is below the least Davenport length, so a zero-sum-free `f` exists.
  have hns : (d - 1) ∉ DavenportSet G := fun hmem => absurd (hG.2 hmem) (by omega)
  rw [DavenportSet, Set.mem_setOf_eq, not_forall] at hns
  obtain ⟨f, hf⟩ := hns
  have hfree : ¬ HasZeroSumSubseq (powerSeq n f) := powerseq_not_hasZeroSum hf
  by_contra hlt
  push_neg at hlt
  -- `dₙ ≤ n·(d − 1)`, so upward closure makes that length a Davenport length.
  have hdle : dₙ ≤ n * (d - 1) := by omega
  have hmem : (n * (d - 1)) ∈ DavenportSet (Fin n → G) :=
    davenport_set_mono hdle hpow.1
  exact hfree (hmem (powerSeq n f))

/-- **Lower-bound half of Olson's theorem for elementary abelian `p`-groups.**
Given the cyclic Davenport value `D(ℤ/pℤ) = p` (companion
`Erdos131DavenportConstant`), the power bound specialises to

    D((ℤ/pℤ)ⁿ) ≥ n·(p − 1) + 1.

Equality in fact holds (Olson); the matching upper bound is not formalized. -/
theorem davenport_elementary_abelian_lower {p n dₙ : ℕ}
    (hp : IsLeast (DavenportSet (ZMod p)) p)
    (hpow : IsLeast (DavenportSet (Fin n → ZMod p)) dₙ) :
    n * (p - 1) + 1 ≤ dₙ :=
  davenport_pow_lower hp hpow

/-- **Recovering the binary diagonal bound.**  Taking `n = 2` gives
`D(G²) ≥ 2·(D(G) − 1) + 1 = 2·D(G) − 1`, matching the diagonal special case of
the binary direct-sum companion. -/
theorem davenport_pow_two_lower {G : Type*} [AddCommGroup G] {d d₂ : ℕ}
    (hG : IsLeast (DavenportSet G) d)
    (hpow : IsLeast (DavenportSet (Fin 2 → G)) d₂) :
    2 * d - 1 ≤ d₂ := by
  have h := davenport_pow_lower (n := 2) hG hpow
  have hd1 : 1 ≤ d := one_le_of_isLeast_davenport hG
  omega

end Erdos131DavenportPower
