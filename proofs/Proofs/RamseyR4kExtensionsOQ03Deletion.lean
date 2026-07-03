/-
  The Deletion (Alteration) Method for Diagonal Ramsey Lower Bounds
  (ramsey-r4k-extensions-oq-03)

  The parent entry `Proofs/RamseyR4kExtensions.lean` states the Erdős
  probabilistic lower bound `R(k,k) > 2^⌊k/2⌋` and, alongside it, points to the
  Lovász Local Lemma as the next tool for sharpening probabilistic Ramsey lower
  bounds.  The *first-moment* half of that programme is already fully discharged
  (see `Proofs/ErdosRamseyLowerBound.lean`, which de-axiomatizes
  `erdos_probabilistic_lower_bound`): if `2·C(n,k) < 2^C(k,2)` then a good
  colouring of `Kₙ` exists.

  This file formalizes the **next** classical strengthening — the alteration /
  deletion method (Erdős) — which strictly improves the first-moment bound and is
  the natural stepping stone toward the LLL improvement.  The idea:

    * Over the `2^C(n,2)` edge 2-colourings of `Kₙ`, the *average* number of
      monochromatic `k`-cliques is `2·C(n,k)·2^(-C(k,2))`.  Hence some colouring
      `c` has at most `M := ⌊2·C(n,k) / 2^C(k,2)⌋` monochromatic `k`-cliques.
    * Delete one vertex from each of those (at most `M`) bad cliques.  The
      surviving vertex set `R` has `|R| ≥ n − M`, and **no** `k`-subset of `R`
      is monochromatic under `c`: every bad clique lost a vertex.

  So `Kₙ` restricted to `R` is a monochromatic-`Kₖ`-free 2-coloured complete
  graph on `≥ n − M` vertices, i.e.

        R(k,k) > n − ⌊2·C(n,k) / 2^C(k,2)⌋.

  Taking `n` past the first-moment threshold (where `M = 0` and this reduces to
  first-moment) gives the extra factor of roughly `k` that the alteration method
  buys over the union bound alone.

  Engine reuse: the counting core `card_mono_le` — the number of colourings
  monochromatic on a fixed `k`-clique is `≤ 2·2^(C(n,2)−C(k,2))` — is imported
  verbatim from `Proofs/RamseyFirstMoment.lean`.  Everything here is a direct
  `ℕ` averaging + a deterministic vertex-deletion; no probability measure, no
  `native_decide`.

  Status: 0 sorries, 0 axioms.
-/
import Mathlib
import Proofs.RamseyFirstMoment

namespace ProbMethod.RamseyDeletion

open Finset
open ProbMethod.RamseyFirstMoment

variable {n k : ℕ}

/-- The `k`-cliques (as vertex sets) of `Kₙ`. -/
def Cliques (n k : ℕ) : Finset (Finset (Fin n)) := (univ : Finset (Fin n)).powersetCard k

/-- The number of monochromatic `k`-cliques of `Kₙ` under a fixed colouring `c`. -/
def badCount (c : Coloring n) : ℕ := ((Cliques n k).filter (fun K => Mono c K)).card

/-- **Averaged union bound.**  Summing the number of monochromatic `k`-cliques
    over *all* colourings is at most `C(n,k) · 2 · 2^(C(n,2)−C(k,2))`.
    (Double counting: swap the sum over colourings with the sum over cliques and
    apply the per-clique count `card_mono_le`.) -/
theorem sum_badCount_le (hk : 2 ≤ k) :
    ∑ c : Coloring n, badCount (k := k) c
      ≤ n.choose k * (2 * 2 ^ (n.choose 2 - k.choose 2)) := by
  classical
  have hedge_card : ∀ K ∈ Cliques n k, (EdgesIn n K).card = k.choose 2 := by
    intro K hKc
    simp only [Cliques, Finset.mem_powersetCard] at hKc
    rw [card_EdgesIn, hKc.2]
  calc
    ∑ c : Coloring n, badCount (k := k) c
        = ∑ c : Coloring n, ∑ K ∈ Cliques n k, (if Mono c K then 1 else 0) := by
          refine Finset.sum_congr rfl (fun c _ => ?_)
          show ((Cliques n k).filter (fun K => Mono c K)).card = _
          rw [Finset.card_filter]
    _ = ∑ K ∈ Cliques n k, ∑ c : Coloring n, (if Mono c K then 1 else 0) :=
          Finset.sum_comm
    _ = ∑ K ∈ Cliques n k, (univ.filter (fun c : Coloring n => Mono c K)).card := by
          refine Finset.sum_congr rfl (fun K _ => ?_)
          rw [Finset.card_filter]
    _ ≤ ∑ _K ∈ Cliques n k, 2 * 2 ^ (n.choose 2 - k.choose 2) := by
          refine Finset.sum_le_sum (fun K hKc => ?_)
          have hne : (EdgesIn n K).Nonempty := by
            rw [← Finset.card_pos, hedge_card K hKc]; exact Nat.choose_pos hk
          have := card_mono_le K hne
          rwa [card_Edges, hedge_card K hKc] at this
    _ = (Cliques n k).card * (2 * 2 ^ (n.choose 2 - k.choose 2)) := by
          rw [Finset.sum_const, smul_eq_mul]
    _ = n.choose k * (2 * 2 ^ (n.choose 2 - k.choose 2)) := by
          simp only [Cliques, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- **Averaging step.**  Some colouring has at most `M := ⌊2·C(n,k)/2^C(k,2)⌋`
    monochromatic `k`-cliques. -/
theorem exists_few_bad (hk : 2 ≤ k) (hkn : k ≤ n) :
    ∃ c : Coloring n, badCount (k := k) c
      ≤ (2 * n.choose k) / 2 ^ (k.choose 2) := by
  classical
  set M := (2 * n.choose k) / 2 ^ (k.choose 2) with hM
  by_contra hcon
  push_neg at hcon
  -- every colouring has strictly more than `M` bad cliques
  have hall : ∀ c : Coloring n, M + 1 ≤ badCount (k := k) c := by
    intro c; have := hcon c; omega
  have hb_le : k.choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 hkn
  have hpos : 0 < 2 ^ (n.choose 2 - k.choose 2) := pow_pos (by norm_num) _
  -- total number of colourings is 2^C(n,2)
  have htotal : Fintype.card (Coloring n) = 2 ^ n.choose 2 := by
    show Fintype.card (↥(Edges n) → Bool) = 2 ^ n.choose 2
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, card_Edges]
  -- lower bound on the total from the averaging assumption
  have hlow : (M + 1) * 2 ^ n.choose 2 ≤ ∑ c : Coloring n, badCount (k := k) c := by
    have hconst : ∑ _c : Coloring n, (M + 1) = (M + 1) * 2 ^ n.choose 2 := by
      rw [Finset.sum_const, Finset.card_univ, htotal, smul_eq_mul]; ring
    calc (M + 1) * 2 ^ n.choose 2
        = ∑ _c : Coloring n, (M + 1) := hconst.symm
      _ ≤ ∑ c : Coloring n, badCount (k := k) c :=
          Finset.sum_le_sum (fun c _ => hall c)
  -- upper bound on the total (previous lemma)
  have hup := sum_badCount_le (n := n) (k := k) hk
  -- combine
  have hcomb : (M + 1) * 2 ^ n.choose 2
      ≤ n.choose k * (2 * 2 ^ (n.choose 2 - k.choose 2)) := le_trans hlow hup
  -- rewrite 2^C(n,2) = 2^C(k,2) · 2^(C(n,2)-C(k,2)) and cancel the common factor
  have hsplit : (2 : ℕ) ^ n.choose 2
      = 2 ^ k.choose 2 * 2 ^ (n.choose 2 - k.choose 2) := by
    rw [← pow_add, Nat.add_sub_cancel' hb_le]
  have hcancel : (M + 1) * 2 ^ (k.choose 2) ≤ 2 * n.choose k := by
    have h2 : (M + 1) * 2 ^ (k.choose 2) * 2 ^ (n.choose 2 - k.choose 2)
        ≤ (2 * n.choose k) * 2 ^ (n.choose 2 - k.choose 2) := by
      calc (M + 1) * 2 ^ (k.choose 2) * 2 ^ (n.choose 2 - k.choose 2)
          = (M + 1) * 2 ^ n.choose 2 := by rw [hsplit]; ring
        _ ≤ n.choose k * (2 * 2 ^ (n.choose 2 - k.choose 2)) := hcomb
        _ = (2 * n.choose k) * 2 ^ (n.choose 2 - k.choose 2) := by ring
    exact Nat.le_of_mul_le_mul_right h2 hpos
  -- but M = ⌊2C(n,k)/2^C(k,2)⌋ means 2C(n,k) < (M+1)·2^C(k,2)
  have hbpos : 0 < 2 ^ (k.choose 2) := pow_pos (by norm_num) _
  have hlt : 2 * n.choose k < (M + 1) * 2 ^ (k.choose 2) := by
    have hexpand : (M + 1) * 2 ^ (k.choose 2)
        = 2 ^ (k.choose 2) * M + 2 ^ (k.choose 2) := by ring
    have hdm' : 2 ^ (k.choose 2) * M + (2 * n.choose k) % 2 ^ (k.choose 2)
        = 2 * n.choose k := by
      rw [hM]; exact Nat.div_add_mod (2 * n.choose k) (2 ^ (k.choose 2))
    have hmod : (2 * n.choose k) % 2 ^ (k.choose 2) < 2 ^ (k.choose 2) :=
      Nat.mod_lt _ hbpos
    rw [hexpand]; linarith
  linarith

/-- **Diagonal Ramsey lower bound via the deletion method.**
    For `2 ≤ k ≤ n` there is an edge 2-colouring `c` of `Kₙ` and a surviving
    vertex set `R` with

        `|R| ≥ n − ⌊2·C(n,k) / 2^C(k,2)⌋`

    such that **no** `k`-subset of `R` is monochromatic under `c`.  Equivalently,
    the complete graph on `R` is 2-coloured with no monochromatic `Kₖ`, so
    `R(k,k) > |R| ≥ n − ⌊2·C(n,k) / 2^C(k,2)⌋`.  This strictly improves the
    first-moment bound (recovered when the floor is `0`). -/
theorem ramsey_deletion (hk : 2 ≤ k) (hkn : k ≤ n) :
    ∃ (c : Coloring n) (R : Finset (Fin n)),
      n - (2 * n.choose k) / 2 ^ (k.choose 2) ≤ R.card ∧
      ∀ K : Finset (Fin n), K ⊆ R → K.card = k → ¬ Mono c K := by
  classical
  obtain ⟨c, hc⟩ := exists_few_bad (n := n) (k := k) hk hkn
  set M := (2 * n.choose k) / 2 ^ (k.choose 2) with hM
  set Bad : Finset (Finset (Fin n)) := (Cliques n k).filter (fun K => Mono c K) with hBad
  have hBadcard : Bad.card ≤ M := hc
  have hn0 : 0 < n := lt_of_lt_of_le (by omega : 0 < k) hkn
  -- pick a vertex out of every clique (default value never used on `Bad`)
  set pick : Finset (Fin n) → Fin n :=
    fun K => if h : K.Nonempty then K.min' h else ⟨0, hn0⟩ with hpick
  set D : Finset (Fin n) := Bad.image pick with hD
  have hDcard : D.card ≤ M := by
    rw [hD]; exact le_trans Finset.card_image_le hBadcard
  refine ⟨c, univ \ D, ?_, ?_⟩
  · -- surviving set is large: |univ \ D| = n - |D| ≥ n - M
    have hcard : (univ \ D).card = n - D.card := by
      rw [Finset.card_univ_diff, Fintype.card_fin]
    rw [hcard]
    exact Nat.sub_le_sub_left hDcard n
  · -- and monochromatic-clique free
    intro K hKR hKcard hmono
    have hKcliq : K ∈ Cliques n k := by
      simp only [Cliques, Finset.mem_powersetCard]; exact ⟨Finset.subset_univ K, hKcard⟩
    have hKBad : K ∈ Bad := by rw [hBad, Finset.mem_filter]; exact ⟨hKcliq, hmono⟩
    have hKne : K.Nonempty := Finset.card_pos.mp (by omega)
    have hpk : pick K = K.min' hKne := by rw [hpick]; exact dif_pos hKne
    have hpickK : pick K ∈ K := by rw [hpk]; exact K.min'_mem hKne
    have hpickD : pick K ∈ D := by
      rw [hD]; exact Finset.mem_image_of_mem pick hKBad
    have hmem : pick K ∈ univ \ D := hKR hpickK
    rw [Finset.mem_sdiff] at hmem
    exact hmem.2 hpickD

/-- **Consistency with the first moment.**  When `2·C(n,k) < 2^C(k,2)` (the
    first-moment regime) the deletion count `M` is `0`, so the whole vertex set
    survives and `ramsey_deletion` recovers `first_moment_ramsey`: a colouring of
    all of `Kₙ` with no monochromatic `Kₖ`. -/
theorem ramsey_deletion_generalizes_first_moment
    (hk : 2 ≤ k) (hkn : k ≤ n) (hbound : 2 * n.choose k < 2 ^ (k.choose 2)) :
    ∃ c : Coloring n, ∀ K : Finset (Fin n), K.card = k → ¬ Mono c K := by
  obtain ⟨c, R, hRcard, hR⟩ := ramsey_deletion (n := n) (k := k) hk hkn
  have hM0 : (2 * n.choose k) / 2 ^ (k.choose 2) = 0 := Nat.div_eq_of_lt hbound
  rw [hM0, Nat.sub_zero] at hRcard
  -- R has ≥ n vertices, so R = univ
  have hRuniv : R = univ := by
    apply Finset.eq_univ_of_card
    have : R.card ≤ Fintype.card (Fin n) := by
      simpa using Finset.card_le_univ R
    have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
    omega
  refine ⟨c, fun K hKcard => ?_⟩
  exact hR K (by rw [hRuniv]; exact Finset.subset_univ K) hKcard

#check @ramsey_deletion
#check @ramsey_deletion_generalizes_first_moment

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no `sorryAx`, no `Lean.ofReduceBool`, no `decide`, no `native_decide`.
#print axioms ramsey_deletion
#print axioms ramsey_deletion_generalizes_first_moment

end ProbMethod.RamseyDeletion
