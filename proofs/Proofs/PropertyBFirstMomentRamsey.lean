/-
  The Erdős (1947) Ramsey lower bound via the *same* first-moment template

  This file answers the open question `property-b-first-moment-oq-02`: reuse the
  exact counting template of `Proofs.PropertyBFirstMoment` (Erdős' Property B
  theorem) to prove the random-coloring diagonal Ramsey lower bound

      C(n,k) · 2^(1 - C(k,2)) < 1   ⟹   R(k,k) > n,

  i.e. there is a red/blue 2-coloring of the edges of the complete graph `K_n`
  with **no** monochromatic `k`-clique. Clearing the fraction (valid for
  `k ≥ 2`, where `C(k,2) ≥ 1`), the hypothesis reads `C(n,k) · 2 < 2^(C(k,2))`.

  The key observation is that this is *literally* an instance of the Property B
  theorem applied to a derived hypergraph:

    • the "vertices" being 2-colored are the **edges** of `K_n`
      (`Edge P := {e : Finset P // e.card = 2}`);
    • each `k`-subset `S` of the points contributes one "hyperedge", namely the
      bundle `edgesWithin S` of its `C(k,2)` internal edges;
    • a coloring is *monochromatic on `S`* exactly when it is `Mono` on that
      bundle — the parent file's notion verbatim.

  So the parent's exact count `card_mono` (number of colorings monochromatic on
  a bundle of size `t` is `2 · 2^(N - t)`) and its `first moment principle`
  `exists_zero_of_sum_lt_card` carry the entire argument. The only genuinely new
  content is the combinatorial identity `|edgesWithin S| = C(|S|, 2)`.

  Status: 0 sorries, 0 axioms. No `native_decide`.
-/
import Mathlib
import Proofs.PropertyBFirstMoment

namespace ProbMethod.Ramsey

open Finset BigOperators
open ProbMethod.PropertyB  -- Mono, card_mono, exists_zero_of_sum_lt_card

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- The **edges of the complete graph** on the point set `P`: the 2-element
    subsets. Coloring these with `Bool` is a red/blue 2-coloring of `K_n`. -/
abbrev Edge (P : Type*) [Fintype P] [DecidableEq P] := {e : Finset P // e.card = 2}

/-- The bundle of edges lying **inside** a vertex set `S`. For `|S| = k` this is
    the edge set of the clique `K_S`, of size `C(k,2)`. -/
def edgesWithin (S : Finset P) : Finset (Edge P) :=
  univ.filter (fun e : Edge P => (e : Finset P) ⊆ S)

/-- A coloring is **monochromatic on the clique `S`** when all of `S`'s internal
    edges receive a single color. This is the parent file's `Mono` notion on the
    derived "vertex set" `Edge P`. -/
def MonoClique (S : Finset P) (c : Edge P → Bool) : Prop := Mono (edgesWithin S) c

instance (S : Finset P) (c : Edge P → Bool) : Decidable (MonoClique S c) := by
  unfold MonoClique; infer_instance

-- ═══════════════════════════════════════════════════
-- The one new identity: a k-clique has C(k,2) edges
-- ═══════════════════════════════════════════════════

/-- **Edge count of a clique.** The number of edges contained in a vertex set
    `S` is `C(|S|, 2)`: each internal edge is exactly a 2-subset of `S`. -/
theorem card_edgesWithin (S : Finset P) :
    (edgesWithin S).card = S.card.choose 2 := by
  -- `Subtype.val` carries `edgesWithin S` bijectively onto `S.powersetCard 2`.
  have himg : (edgesWithin S).image (Subtype.val) = S.powersetCard 2 := by
    ext t
    simp only [edgesWithin, mem_image, mem_filter, mem_univ, true_and,
      Finset.mem_powersetCard]
    constructor
    · rintro ⟨e, hsub, rfl⟩
      exact ⟨hsub, e.2⟩
    · rintro ⟨hsub, hcard⟩
      exact ⟨⟨t, hcard⟩, hsub, rfl⟩
  rw [← Finset.card_image_of_injective (edgesWithin S) Subtype.coe_injective,
      himg, Finset.card_powersetCard]

-- ═══════════════════════════════════════════════════
-- The Ramsey lower bound (same template as Property B)
-- ═══════════════════════════════════════════════════

/-- **Erdős 1947: the probabilistic diagonal Ramsey lower bound.**
    If `C(n,k) · 2 < 2^(C(k,2))` (equivalently `C(n,k)·2^(1-C(k,2)) < 1`) then
    there is a 2-coloring `c` of the edges of `K_n` under which **no** `k`-subset
    of the vertices is monochromatic. Hence `R(k,k) > n`.

    Proof: over the `2^(C(n,2))` edge-colorings the total number of
    (coloring, monochromatic `k`-clique) incidences is
    `C(n,k) · 2 · 2^(C(n,2) - C(k,2))`. The hypothesis makes this `< 2^(C(n,2))`,
    so the parent file's first moment principle yields a coloring with zero
    monochromatic cliques. The count per clique is the parent's `card_mono`
    applied to the `C(k,2)`-edge bundle `edgesWithin S`. -/
theorem ramsey_lower_bound
    (k : ℕ) (hk : 2 ≤ k)
    (hsmall : (Fintype.card P).choose k * 2 < 2 ^ (k.choose 2)) :
    ∃ c : Edge P → Bool, ∀ S ∈ powersetCard k (univ : Finset P), ¬ MonoClique S c := by
  -- If there are no `k`-cliques at all, any coloring works (vacuously).
  rcases (powersetCard k (univ : Finset P)).eq_empty_or_nonempty with hempty | hne
  · exact ⟨fun _ => true, by rw [hempty]; simp⟩
  -- Otherwise fix one clique to extract `C(k,2) ≤ #edges`.
  obtain ⟨S₀, hS₀⟩ := hne
  have hS₀card : S₀.card = k := (mem_powersetCard.mp hS₀).2
  -- per-clique count: exactly `2 · 2^(N - C(k,2))` colorings are mono on `S`.
  have hinner : ∀ S ∈ powersetCard k (univ : Finset P),
      (∑ c : Edge P → Bool, ite (MonoClique S c) 1 0)
        = 2 * 2 ^ (Fintype.card (Edge P) - k.choose 2) := by
    intro S hS
    have hSk : S.card = k := (mem_powersetCard.mp hS).2
    have hne' : (edgesWithin S).Nonempty := by
      rw [← Finset.card_pos, card_edgesWithin, hSk]
      exact Nat.choose_pos hk
    rw [← Finset.card_filter]
    show (univ.filter (fun c : Edge P → Bool => Mono (edgesWithin S) c)).card = _
    rw [card_mono (edgesWithin S) hne', card_edgesWithin, hSk]
  -- first-moment sum over all `k`-cliques.
  have hsum :
      (∑ c : Edge P → Bool,
          ((powersetCard k (univ : Finset P)).filter (fun S => MonoClique S c)).card)
        = (powersetCard k (univ : Finset P)).card
            * (2 * 2 ^ (Fintype.card (Edge P) - k.choose 2)) := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm, Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]
  -- the sample space `Edge P → Bool` has `2^(#edges)` points.
  have hcard : (univ : Finset (Edge P → Bool)).card = 2 ^ Fintype.card (Edge P) := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
  -- `C(k,2) ≤ #edges`, since the clique's edge bundle sits inside `univ`.
  have hle : k.choose 2 ≤ Fintype.card (Edge P) := by
    have h := Finset.card_le_card (Finset.subset_univ (edgesWithin S₀))
    rwa [card_edgesWithin, hS₀card, Finset.card_univ] at h
  have h2 : 0 < (2 : ℕ) ^ (Fintype.card (Edge P) - k.choose 2) := pow_pos (by norm_num) _
  -- the strict first-moment inequality.
  have hlt :
      (∑ c : Edge P → Bool,
          ((powersetCard k (univ : Finset P)).filter (fun S => MonoClique S c)).card)
        < (univ : Finset (Edge P → Bool)).card := by
    rw [hsum, hcard, Finset.card_powersetCard, Finset.card_univ]
    have e1 : (2 : ℕ) ^ Fintype.card (Edge P)
        = 2 ^ (k.choose 2) * 2 ^ (Fintype.card (Edge P) - k.choose 2) := by
      rw [← pow_add]; congr 1; omega
    calc (Fintype.card P).choose k * (2 * 2 ^ (Fintype.card (Edge P) - k.choose 2))
          = ((Fintype.card P).choose k * 2) * 2 ^ (Fintype.card (Edge P) - k.choose 2) := by
            ring
      _ < 2 ^ (k.choose 2) * 2 ^ (Fintype.card (Edge P) - k.choose 2) :=
            (Nat.mul_lt_mul_right h2).mpr hsmall
      _ = 2 ^ Fintype.card (Edge P) := e1.symm
  -- first moment principle: some coloring is monochromatic on no clique.
  obtain ⟨c, -, hc⟩ := exists_zero_of_sum_lt_card hlt
  refine ⟨c, ?_⟩
  have hempty : (powersetCard k (univ : Finset P)).filter (fun S => MonoClique S c) = ∅ :=
    Finset.card_eq_zero.mp hc
  intro S hS
  exact (Finset.filter_eq_empty_iff.mp hempty) hS

/-- **Corollary: the diagonal Ramsey number exceeds `n`.**
    Phrased as the existence of a Ramsey witness: under the same hypothesis the
    complete graph `K_n` admits a red/blue edge 2-coloring with no monochromatic
    `K_k`. We record it as `R(k,k) > n` in the self-contained sense that some
    coloring avoids all monochromatic `k`-cliques. -/
theorem exists_ramsey_coloring
    (k : ℕ) (hk : 2 ≤ k)
    (hsmall : (Fintype.card P).choose k * 2 < 2 ^ (k.choose 2)) :
    ∃ c : Edge P → Bool,
      ∀ S : Finset P, S.card = k → ¬ MonoClique S c := by
  obtain ⟨c, hc⟩ := ramsey_lower_bound (P := P) k hk hsmall
  refine ⟨c, fun S hSk => ?_⟩
  exact hc S (mem_powersetCard.mpr ⟨Finset.subset_univ S, hSk⟩)

end ProbMethod.Ramsey
