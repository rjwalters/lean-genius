/-
  Probabilistic Method Applications — WIP OQ-01

  Open question (prob-method-applications-wip-01-oq-01):
    "Instantiate `ramsey_avoidance` to `K_n`:
       C(n,m)·2^(1-C(m,2)) < 1  ⟹  R(m,m) > n."

  The companion file `ProbMethodApplicationsWIP.lean` proves the *abstract*
  first-moment avoidance engine

      ProbMethod.Core.ramsey_avoidance :
        (cliques : Finset (Finset E)) (m : ℕ)
        (∀ K ∈ cliques, K.card = m)
        (cliques.card * 2^(|E| - m + 1) < 2^|E|)
        ⟹ ∃ S : Finset E, ∀ K ∈ cliques, ¬ (K ⊆ S ∨ Disjoint K S),

  over an arbitrary finite "edge" set `E`, where a block `K` is monochromatic
  under the colouring `S` (= the set of `true`-coloured edges) exactly when
  `K ⊆ S` (all `true`) or `Disjoint K S` (all `false`).  Its docstring *claims*
  that instantiating `E` as the edge set of `K_n` recovers the Erdős (1947)
  lower bound `R(m,m) > n`, but never carries out that instantiation.

  This file supplies the missing bridge.  Taking
    * `E := ` the edges of `K_n` (the 2-subsets of `Fin n`, from
      `RamseyFirstMoment.Edges`), so `|E| = C(n,2)`;
    * `blocks := ` the images `EdgesIn n K` of the vertex `k`-subsets `K`, each a
      genuine `K_k`-clique of `C(k,2)` edges;
  the abstract hypothesis `blocks.card · 2^(C(n,2)-C(k,2)+1) < 2^(C(n,2))`
  follows from the classical criterion `2·C(n,k) < 2^(C(k,2))` (i.e.
  `C(n,k)·2^(1-C(k,2)) < 1`), and `ramsey_avoidance` then yields a 2-colouring of
  `K_n` with no monochromatic `K_k`.  Translating the abstract "`S`-membership"
  colouring back into `RamseyFirstMoment.Coloring`, we obtain *exactly* the
  conclusion of `RamseyFirstMoment.first_moment_ramsey` — but now derived from the
  abstract engine rather than re-proved by a bespoke count.  This verifies the
  WIP file's standing claim and unifies the two formalisations.

  Status: 0 sorries, 0 axioms, no native_decide.
-/
import Mathlib
import Proofs.ProbMethodApplicationsWIP
import Proofs.RamseyFirstMoment

open Finset

namespace ProbMethod.ApplicationsWIPOQ01

variable {n k : ℕ}

/-- **K_n instantiation of the abstract avoidance engine.**
    If `2·C(n,k) < 2^(C(k,2))` (equivalently `C(n,k)·2^(1-C(k,2)) < 1`), then
    there is a 2-colouring of the edges of `K_n` with no monochromatic `K_k`,
    i.e. `R(k,k) > n`.  The proof instantiates `ProbMethod.Core.ramsey_avoidance`
    over the edge set of `K_n`; the family of "bad blocks" is the set of induced
    clique-edge sets `EdgesIn n K` over vertex `k`-subsets `K`.

    (The usual side condition `2 ≤ k` is omitted as redundant: the counting
    hypothesis `2·C(n,k) < 2^(C(k,2))` already fails for `k ∈ {0,1}`, where the
    right-hand side is `2^0 = 1`.) -/
theorem ramsey_avoidance_Kn (hkn : k ≤ n)
    (hbound : 2 * n.choose k < 2 ^ (k.choose 2)) :
    ∃ c : RamseyFirstMoment.Coloring n,
      ∀ K : Finset (Fin n), K.card = k → ¬ RamseyFirstMoment.Mono c K := by
  classical
  -- The clique-edge blocks: image of the vertex `k`-subsets under `EdgesIn n`.
  set blocks :=
    ((univ : Finset (Fin n)).powersetCard k).image (RamseyFirstMoment.EdgesIn n)
    with hblocks
  -- `|E| = C(n,2)` where `E` is the edge subtype.
  have hcardE : Fintype.card (↥(RamseyFirstMoment.Edges n)) = n.choose 2 := by
    rw [Fintype.card_coe, RamseyFirstMoment.card_Edges]
  -- Every block is a `K_k`-clique, hence has exactly `C(k,2)` edges.
  have hm : ∀ B ∈ blocks, B.card = k.choose 2 := by
    intro B hB
    rw [hblocks, mem_image] at hB
    obtain ⟨K, hK, rfl⟩ := hB
    rw [mem_powersetCard] at hK
    rw [RamseyFirstMoment.card_EdgesIn, hK.2]
  -- There are at most `C(n,k)` blocks (the image can only shrink the count).
  have hblock_card : blocks.card ≤ n.choose k := by
    rw [hblocks]
    refine le_trans card_image_le ?_
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hb_le_a : k.choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 hkn
  -- Discharge the counting hypothesis of `ramsey_avoidance`.
  have hcount : blocks.card *
      (2 ^ (Fintype.card (↥(RamseyFirstMoment.Edges n)) - k.choose 2 + 1))
        < 2 ^ (Fintype.card (↥(RamseyFirstMoment.Edges n))) := by
    rw [hcardE]
    have key : n.choose k * (2 ^ (n.choose 2 - k.choose 2 + 1)) < 2 ^ (n.choose 2) := by
      have hsplit : (2 : ℕ) ^ n.choose 2
          = 2 ^ k.choose 2 * 2 ^ (n.choose 2 - k.choose 2) := by
        rw [← pow_add, Nat.add_sub_cancel' hb_le_a]
      have hpos : 0 < 2 ^ (n.choose 2 - k.choose 2) := pow_pos (by norm_num) _
      rw [hsplit]
      calc n.choose k * (2 ^ (n.choose 2 - k.choose 2 + 1))
          = (2 * n.choose k) * 2 ^ (n.choose 2 - k.choose 2) := by
            rw [pow_succ]; ring
        _ < 2 ^ k.choose 2 * 2 ^ (n.choose 2 - k.choose 2) :=
            (Nat.mul_lt_mul_right hpos).mpr hbound
    calc blocks.card * (2 ^ (n.choose 2 - k.choose 2 + 1))
        ≤ n.choose k * (2 ^ (n.choose 2 - k.choose 2 + 1)) := by gcongr
      _ < 2 ^ (n.choose 2) := key
  -- Apply the abstract avoidance engine.
  obtain ⟨S, hS⟩ :=
    ProbMethod.Core.ramsey_avoidance blocks (k.choose 2) hm hcount
  -- Translate the avoiding set `S` into an honest edge colouring.
  refine ⟨fun e => decide (e ∈ S), ?_⟩
  intro K hKcard hmono
  -- `EdgesIn n K` is one of the blocks.
  have hKblock : RamseyFirstMoment.EdgesIn n K ∈ blocks := by
    rw [hblocks]
    exact mem_image_of_mem _ (by rw [mem_powersetCard]; exact ⟨subset_univ K, hKcard⟩)
  -- so it is not monochromatic for the abstract `Mono`.
  have hnotmono :
      ¬ ((RamseyFirstMoment.EdgesIn n K) ⊆ S ∨ Disjoint (RamseyFirstMoment.EdgesIn n K) S) :=
    hS _ hKblock
  rw [not_or] at hnotmono
  obtain ⟨hnsub, hndisj⟩ := hnotmono
  -- a `false` edge (not in `S`) and a `true` edge (in `S`) inside the same clique
  obtain ⟨e, heB, heS⟩ := Finset.not_subset.mp hnsub
  obtain ⟨f, hfB, hfS⟩ := Finset.not_disjoint_iff.mp hndisj
  -- but `hmono` forces them to share a colour — contradiction.
  have hcol : decide (e ∈ S) = decide (f ∈ S) := hmono e heB f hfB
  rw [decide_eq_decide] at hcol
  exact heS (hcol.mpr hfS)

/-- **Concrete witness, via the abstract engine.** `2·C(6,4) = 30 < 64 = 2^(C(4,2))`,
    so there is a 2-colouring of `K_6` with no monochromatic `K_4`, i.e.
    `R(4,4) > 6` — recovered here purely from `ProbMethod.Core.ramsey_avoidance`. -/
theorem ramsey_four_gt_six_via_avoidance :
    ∃ c : RamseyFirstMoment.Coloring 6,
      ∀ K : Finset (Fin 6), K.card = 4 → ¬ RamseyFirstMoment.Mono c K :=
  ramsey_avoidance_Kn (by norm_num) (by decide)

end ProbMethod.ApplicationsWIPOQ01
