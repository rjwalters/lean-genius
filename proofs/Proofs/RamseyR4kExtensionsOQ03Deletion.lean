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

/-- **The general deletion-window theorem.**  Fix a window index `M` and suppose
    `n` sits in the `M`-th deletion window, i.e.

        `M · 2^C(k,2) ≤ 2·C(n,k) < (M+1) · 2^C(k,2)`.

    These two inequalities pin the deletion count `⌊2·C(n,k)/2^C(k,2)⌋ = M` exactly,
    so `ramsey_deletion` keeps a monochromatic-`Kₖ`-free set of `n − M` vertices, i.e.
    `R(k,k) > n − M`.  This is the single mechanism behind the whole deletion
    hierarchy: `M = 0` is the first-moment/union regime (whole graph survives), `M = 1`
    is the first strict improvement past the union threshold, and larger `M` are the
    successive windows.  Stated in terms of the window index `M` rather than the raw
    floor, it makes `ramsey_deletion_generalizes_first_moment` (`M = 0`) and
    `ramsey_deletion_one_past` (`M = 1`) immediate corollaries. -/
theorem ramsey_deletion_window (hk : 2 ≤ k) (hkn : k ≤ n) (M : ℕ)
    (hlo : M * 2 ^ (k.choose 2) ≤ 2 * n.choose k)
    (hhi : 2 * n.choose k < (M + 1) * 2 ^ (k.choose 2)) :
    ∃ (c : Coloring n) (R : Finset (Fin n)),
      n - M ≤ R.card ∧
      ∀ K : Finset (Fin n), K ⊆ R → K.card = k → ¬ Mono c K := by
  have hbpos : 0 < 2 ^ (k.choose 2) := pow_pos (by norm_num) _
  -- the two window inequalities force the deletion count to be exactly `M`
  have hMeq : (2 * n.choose k) / 2 ^ (k.choose 2) = M := by
    have h1 : M ≤ (2 * n.choose k) / 2 ^ (k.choose 2) := by
      rw [Nat.le_div_iff_mul_le hbpos]; exact hlo
    have h2 : (2 * n.choose k) / 2 ^ (k.choose 2) < M + 1 := by
      rw [Nat.div_lt_iff_lt_mul hbpos]; exact hhi
    omega
  obtain ⟨c, R, hRcard, hR⟩ := ramsey_deletion (n := n) (k := k) hk hkn
  rw [hMeq] at hRcard
  exact ⟨c, R, hRcard, hR⟩

/-- **Consistency with the first moment.**  When `2·C(n,k) < 2^C(k,2)` (the
    first-moment regime) the deletion count `M` is `0`, so the whole vertex set
    survives and `ramsey_deletion` recovers `first_moment_ramsey`: a colouring of
    all of `Kₙ` with no monochromatic `Kₖ`.  This is the `M = 0` case of
    `ramsey_deletion_window`. -/
theorem ramsey_deletion_generalizes_first_moment
    (hk : 2 ≤ k) (hkn : k ≤ n) (hbound : 2 * n.choose k < 2 ^ (k.choose 2)) :
    ∃ c : Coloring n, ∀ K : Finset (Fin n), K.card = k → ¬ Mono c K := by
  obtain ⟨c, R, hRcard, hR⟩ :=
    ramsey_deletion_window (n := n) (k := k) hk hkn 0 (by simp) (by simpa using hbound)
  rw [Nat.sub_zero] at hRcard
  -- R has ≥ n vertices, so R = univ
  have hRuniv : R = univ := by
    apply Finset.eq_univ_of_card
    have : R.card ≤ Fintype.card (Fin n) := by
      simpa using Finset.card_le_univ R
    have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
    omega
  refine ⟨c, fun K hKcard => ?_⟩
  exact hR K (by rw [hRuniv]; exact Finset.subset_univ K) hKcard

-- ═══════════════════════════════════════════════════════════════════
-- DELETION STRICTLY BEATS THE SHARP UNION BOUND (concrete, axiom-free)
-- ═══════════════════════════════════════════════════════════════════

/-  The sibling file `Proofs/RamseyR4kExtensionsOQ03.lean` (PART VII) records an
    honest limitation: the *symmetric Lovász Local Lemma as set up there* does NOT
    beat the sharp first-moment/union bound at small `k` — its factor-`Θ(k)` gain is
    asymptotic and has not kicked in by `k = 6, 7` (the LLL test caps at `R(6,6)>13`,
    `R(7,7)>22`, while the sharp union bound already gives `R(6,6)>17`, `R(7,7)>27`).

    The *deletion method* of this file, by contrast, **does** strictly beat the sharp
    union bound at exactly those `k`.  The union bound (the `M = 0` case of
    `ramsey_deletion`) certifies a monochromatic-`Kₖ`-free colouring of *all* of `Kₙ`
    only when `2·C(n,k) < 2^{C(k,2)}`; deletion instead keeps a *surviving set* of
    size `deletionBound n k = n − ⌊2·C(n,k)/2^{C(k,2)}⌋`, which is maximised past that
    threshold.  The theorems below discharge the strict gain at `k = 6`: deletion
    reaches an 18-vertex mono-free set where the union bound stops at 17.  (The same
    phenomenon holds at `k = 7`, where `deletionBound 30 7 = 29` beats the union
    bound's cap of 27 — `2·C(27,7) = 1776060 < 2^{21}` but `2·C(28,7) = 2368080 ≥ 2^{21}`
    — but the `k = 7` binomials are large enough that a kernel `decide` is
    impractical, so only `k = 6` is discharged as a theorem here.)  Everything is
    settled by kernel `decide` on `ℕ`, so the results remain axiom-free (no
    `native_decide`).  -/

/-- The guaranteed surviving-set size of the deletion method: a monochromatic-`Kₖ`-free
    2-colouring exists on `deletionBound n k` vertices.  This is exactly the lower
    bound proved in `ramsey_deletion`. -/
def deletionBound (n k : ℕ) : ℕ := n - (2 * n.choose k) / 2 ^ (k.choose 2)

/-- Restatement of `ramsey_deletion` in terms of `deletionBound`: for `2 ≤ k ≤ n`
    there is a 2-colouring `c` of `Kₙ` and a set `R` of at least `deletionBound n k`
    vertices with no monochromatic `k`-clique. -/
theorem ramsey_deletion_bound (hk : 2 ≤ k) (hkn : k ≤ n) :
    ∃ (c : Coloring n) (R : Finset (Fin n)),
      deletionBound n k ≤ R.card ∧
      ∀ K : Finset (Fin n), K ⊆ R → K.card = k → ¬ Mono c K :=
  ramsey_deletion hk hkn

/-- **The general "one step past the union threshold" gain.**  Suppose `n` sits in the
    first deletion window past the sharp union bound, i.e.

        `2 ^ C(k,2) ≤ 2·C(n,k) < 2·2 ^ C(k,2)`.

    The left inequality says the union-bound test `2·C(n,k) < 2 ^ C(k,2)` *fails* at `n`
    (so the first moment certifies nothing on all of `Kₙ`); the two together pin the
    deletion count `M = ⌊2·C(n,k)/2 ^ C(k,2)⌋ = 1`.  Deleting that single bad-clique
    representative leaves a monochromatic-`Kₖ`-free set of `n − 1` vertices — a strict
    improvement over the union bound precisely where the union bound gives out.

    This is the *general* mechanism behind the concrete `k = 6` (`n = 19`), `k = 7`
    (`n = 30`) and `k = 8` (`n = 46`) witnesses below: all land in exactly this `M = 1`
    window, so `deletion_no_mono_K6/K7/K8` are instances of this theorem.  No large
    `decide` is needed here — the `M = 1` collapse is pure `ℕ`-division reasoning, valid
    for every `k`.  It is the `M = 1` case of `ramsey_deletion_window`. -/
theorem ramsey_deletion_one_past (hk : 2 ≤ k) (hkn : k ≤ n)
    (hlo : 2 ^ (k.choose 2) ≤ 2 * n.choose k)
    (hhi : 2 * n.choose k < 2 * 2 ^ (k.choose 2)) :
    ∃ (c : Coloring n) (R : Finset (Fin n)),
      n - 1 ≤ R.card ∧
      ∀ K : Finset (Fin n), K ⊆ R → K.card = k → ¬ Mono c K :=
  ramsey_deletion_window hk hkn 1 (by simpa using hlo) (by simpa using hhi)

/-- **The deletion window advances by exactly one vertex per step while the
    `(k−1)`-clique first moment stays subthreshold.**  Recall the deletion bound is
    `deletionBound n k = n − ⌊2·C(n,k) / 2^C(k,2)⌋`.  Its increment in `n` is governed by
    Pascal's rule `C(n+1,k) = C(n,k) + C(n,k−1)`: the deleted-vertex count `⌊2·C(n,k)/q⌋`
    (where `q = 2^C(k,2)`) can jump by at most one per step precisely when the *added*
    mass `2·C(n,k−1)` is still below one full quantum `q`.  Hence, as long as

        `2·C(n,k−1) < 2^C(k,2)`,

    we have `deletionBound n k ≤ deletionBound (n+1) k`: adding a vertex never hurts the
    guaranteed monochromatic-`Kₖ`-free set.

    This is the *quantitative* content of the deletion window.  The sharp union bound
    stalls at the largest `n` with `2·C(n,k) < q`; this lemma shows the deletion optimum
    instead runs out to the largest `n` with `2·C(n,k−1) < q`.  Since in the Ramsey regime
    `C(n,k−1) < C(n,k)` (the binomials are still on their increasing arm,
    `Nat.choose_le_succ_of_lt_half_left`), that window is strictly wider — this is exactly
    where the alteration method's extra factor of `≈ k` over the union bound comes from.
    Pure `ℕ`-division, valid for every `k`; no `decide`. -/
theorem deletionBound_mono_of_pred_subthreshold (hk : 2 ≤ k) (hkn : k ≤ n)
    (hpred : 2 * n.choose (k - 1) < 2 ^ (k.choose 2)) :
    deletionBound n k ≤ deletionBound (n + 1) k := by
  have hq : 0 < 2 ^ (k.choose 2) := pow_pos (by norm_num) _
  -- Pascal's rule in the form we need (the exact binomial-ratio step).
  have hpascal : 2 * (n + 1).choose k = 2 * n.choose k + 2 * n.choose (k - 1) := by
    have h : (n + 1).choose k = n.choose k + n.choose (k - 1) := by
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.choose_succ_succ, Nat.add_sub_cancel]
      ring
    omega
  simp only [deletionBound]
  set q := 2 ^ (k.choose 2) with hq_def
  set a := 2 * n.choose k with ha_def
  set c := 2 * (n + 1).choose k with hc_def
  set b := 2 * n.choose (k - 1) with hb_def
  -- The floor `⌊c/q⌋` sits between `⌊a/q⌋` and `⌊a/q⌋ + 1` (added mass `b < q`).
  have hxy : a / q ≤ c / q := Nat.div_le_div_right (by omega)
  have hyx1 : c / q ≤ a / q + 1 :=
    calc c / q ≤ (a + q) / q := Nat.div_le_div_right (by omega)
      _ = a / q + 1 := Nat.add_div_right a hq
  omega

/-- **Wherever the sharp union bound is still feasible, the deletion bound is still
    improving.**  If the first-moment test `2·C(n,k) < 2^C(k,2)` holds at `n` and the
    binomials are on their increasing arm (`C(n,k−1) ≤ C(n,k)`, automatic in the Ramsey
    regime `k−1 < n/2`), then `deletionBound n k ≤ deletionBound (n+1) k`.  Consequently
    the deletion optimum lies at least as far out as the union optimum — and, because the
    `(k−1)`-window `2·C(n,k−1) < 2^C(k,2)` is strictly wider than the `k`-window, strictly
    beyond it.  A direct corollary of `deletionBound_mono_of_pred_subthreshold`. -/
theorem deletionBound_mono_of_unionFeasible (hk : 2 ≤ k) (hkn : k ≤ n)
    (hunion : 2 * n.choose k < 2 ^ (k.choose 2))
    (hmid : n.choose (k - 1) ≤ n.choose k) :
    deletionBound n k ≤ deletionBound (n + 1) k :=
  deletionBound_mono_of_pred_subthreshold hk hkn (by omega)

/-- **The deletion bound is monotone across the entire `(k−1)` sub-threshold window.**
    `deletionBound_mono_of_pred_subthreshold` shows a *single* step `n → n+1` never
    decreases the deletion bound while `2·C(n,k−1) < 2^C(k,2)`.  Chaining that step by
    induction gives the *global* statement its docstring only asserts: if the `(k−1)`
    first moment stays subthreshold throughout the interval `[n, N)`, i.e.

        `∀ m ∈ [n, N),  2·C(m,k−1) < 2^C(k,2)`,

    then `deletionBound n k ≤ deletionBound N k` for the whole run.  In particular the
    deletion optimum is attained no earlier than the *top* of the `(k−1)`-window
    `2·C(·,k−1) < 2^C(k,2)`, which strictly contains the union window
    `2·C(·,k) < 2^C(k,2)` (since `C(m,k−1) ≤ C(m,k)` on the increasing arm).  This is the
    general, `decide`-free source of the alteration method's advantage over the sharp
    union bound: the union bound stalls at the top of the `k`-window, the deletion bound
    keeps climbing to the top of the wider `(k−1)`-window.  Axiom-free. -/
theorem deletionBound_mono_window (hk : 2 ≤ k) {n : ℕ} (hkn : k ≤ n) :
    ∀ N, n ≤ N → (∀ m, n ≤ m → m < N → 2 * m.choose (k - 1) < 2 ^ (k.choose 2)) →
      deletionBound n k ≤ deletionBound N k := by
  intro N hnN
  induction N, hnN using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ N hnN ih =>
      intro hsub
      exact le_trans (ih (fun m hm hmN => hsub m hm (Nat.lt_succ_of_lt hmN)))
        (deletionBound_mono_of_pred_subthreshold hk (le_trans hkn hnN)
          (hsub N hnN (Nat.lt_succ_self N)))

/-- **Ramsey form: the guaranteed mono-free set never shrinks across the `(k−1)`-window.**
    For any host size `N` reachable from `n` without the `(k−1)` first moment crossing
    threshold, the deletion method on `K_N` certifies a monochromatic-`Kₖ`-free set at
    least as large as the one it certifies at `n`.  Combined with the strict window-width
    gap this is exactly the mechanism behind the concrete `+1/+2/+3/+4` witnesses at
    `k = 6,7,8,9`: each sits at the top of its `(k−1)`-window, strictly past the union
    cap.  Immediate from `deletionBound_mono_window` and `ramsey_deletion_bound`. -/
theorem deletion_noloss_across_window (hk : 2 ≤ k) {n N : ℕ} (hkn : k ≤ n) (hnN : n ≤ N)
    (hsub : ∀ m, n ≤ m → m < N → 2 * m.choose (k - 1) < 2 ^ (k.choose 2)) :
    ∃ (c : Coloring N) (R : Finset (Fin N)),
      deletionBound n k ≤ R.card ∧
      ∀ K : Finset (Fin N), K ⊆ R → K.card = k → ¬ Mono c K := by
  obtain ⟨c, R, hRcard, hR⟩ :=
    ramsey_deletion_bound (n := N) (k := k) hk (le_trans hkn hnN)
  exact ⟨c, R, le_trans (deletionBound_mono_window hk hkn N hnN hsub) hRcard, hR⟩

set_option maxHeartbeats 800000 in
/-- **The sharp union bound caps at `n = 17` for `k = 6`.**  The first-moment test
    `2·C(n,6) < 2^{C(6,2)} = 2^{15}` holds at `n = 17` (`2·12376 = 24752 < 32768`) but
    fails at `n = 18` (`2·18564 = 37128 ≥ 32768`).  So the union bound alone certifies
    a monochromatic-`K₆`-free colouring only up to 17 vertices, i.e. `R(6,6) > 17`. -/
theorem unionBound_caps_at_17_for_K6 :
    2 * (17 : ℕ).choose 6 < 2 ^ ((6 : ℕ).choose 2) ∧
      ¬ (2 * (18 : ℕ).choose 6 < 2 ^ ((6 : ℕ).choose 2)) := by
  decide

set_option maxHeartbeats 800000 in
/-- **Deletion reaches an 18-vertex monochromatic-`K₆`-free set.**  Applying the
    deletion method at `n = 19, k = 6` gives `deletionBound 19 6 = 19 − ⌊2·C(19,6)/2^{15}⌋
    = 19 − ⌊54264/32768⌋ = 19 − 1 = 18`: a 2-colouring of `K₁₉` and a set `R` of at
    least 18 vertices with no monochromatic `K₆`.  This **strictly beats** the sharp
    union bound (`unionBound_caps_at_17_for_K6`, which stops at 17), so the deletion
    method certifies `R(6,6) > 18` — a strict improvement the symmetric LLL of the
    sibling file does not achieve at `k = 6`. -/
theorem deletion_no_mono_K6 :
    ∃ (c : Coloring 19) (R : Finset (Fin 19)),
      18 ≤ R.card ∧ ∀ K : Finset (Fin 19), K ⊆ R → K.card = 6 → ¬ Mono c K := by
  obtain ⟨c, R, hRcard, hR⟩ :=
    ramsey_deletion_bound (n := 19) (k := 6) (by norm_num) (by norm_num)
  have h : deletionBound 19 6 = 18 := by decide
  rw [h] at hRcard
  exact ⟨c, R, hRcard, hR⟩

/-- **The sharp union bound caps at `n = 27` for `k = 7`.**  The first-moment test
    `2·C(n,7) < 2^{C(7,2)} = 2^{21} = 2097152` holds at `n = 27`
    (`2·888030 = 1776060 < 2097152`) but fails at `n = 28`
    (`2·1184040 = 2368080 ≥ 2097152`).  So the union bound alone certifies a
    monochromatic-`K₇`-free colouring only up to 27 vertices, i.e. `R(7,7) > 27`.

    The binomials `C(27,7)` and `C(28,7)` are ≈ `10⁶`, so evaluating `Nat.choose`
    directly by `decide` is impractical (the two-way `choose` recursion has ≈ `C(n,k)`
    leaves with no kernel memoisation).  We instead route through the *single*-recursion
    identity `Nat.choose n k = n.descFactorial k / k !`
    (`Nat.choose_eq_descFactorial_div_factorial`): `descFactorial` needs only `k`
    multiplications on kernel-accelerated `Nat` literals, so the reduction is cheap and
    still axiom-free (`of_decide_eq_true`, no `Lean.ofReduceBool`). -/
theorem unionBound_caps_at_27_for_K7 :
    2 * (27 : ℕ).choose 7 < 2 ^ ((7 : ℕ).choose 2) ∧
      ¬ (2 * (28 : ℕ).choose 7 < 2 ^ ((7 : ℕ).choose 2)) := by
  have h27 : (27 : ℕ).choose 7 = 888030 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  have h28 : (28 : ℕ).choose 7 = 1184040 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  rw [h27, h28]
  decide

/-- **Deletion reaches a 29-vertex monochromatic-`K₇`-free set.**  Applying the deletion
    method at `n = 30, k = 7` gives
    `deletionBound 30 7 = 30 − ⌊2·C(30,7)/2^{21}⌋ = 30 − ⌊4071600/2097152⌋ = 30 − 1 = 29`:
    a 2-colouring of `K₃₀` and a set `R` of at least 29 vertices with no monochromatic
    `K₇`.  This **strictly beats** the sharp union bound (`unionBound_caps_at_27_for_K7`,
    which stops at 27), so the deletion method certifies `R(7,7) > 29` — a `+2` strict
    improvement over the union bound, matching the `+1` improvement it gives at `k = 6`.

    As with the `k = 6` witness, the large binomial `C(30,7) = 2035800` is evaluated via
    the `descFactorial` route rather than by `decide` on `Nat.choose`. -/
theorem deletion_no_mono_K7 :
    ∃ (c : Coloring 30) (R : Finset (Fin 30)),
      29 ≤ R.card ∧ ∀ K : Finset (Fin 30), K ⊆ R → K.card = 7 → ¬ Mono c K := by
  obtain ⟨c, R, hRcard, hR⟩ :=
    ramsey_deletion_bound (n := 30) (k := 7) (by norm_num) (by norm_num)
  have h : deletionBound 30 7 = 29 := by
    have h30 : (30 : ℕ).choose 7 = 2035800 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]; decide
    show 30 - (2 * (30 : ℕ).choose 7) / 2 ^ ((7 : ℕ).choose 2) = 29
    rw [h30]; decide
  rw [h] at hRcard
  exact ⟨c, R, hRcard, hR⟩

/-- **The sharp union bound caps at `n = 42` for `k = 8`.**  The first-moment test
    `2·C(n,8) < 2^{C(8,2)} = 2^{28} = 268435456` holds at `n = 42`
    (`2·118030185 = 236060370 < 268435456`) but fails at `n = 43`
    (`2·145008513 = 290017026 ≥ 268435456`).  So the union bound alone certifies a
    monochromatic-`K₈`-free colouring only up to 42 vertices, i.e. `R(8,8) > 42`.

    As at `k = 7`, the binomials `C(42,8), C(43,8)` are ≈ `10⁸`, far past the naive
    `decide`-on-`Nat.choose` range, so we route through the single-recursion identity
    `Nat.choose n k = n.descFactorial k / k !`
    (`Nat.choose_eq_descFactorial_div_factorial`), which needs only `k` kernel
    multiplications and stays axiom-free (`of_decide_eq_true`, no `Lean.ofReduceBool`). -/
theorem unionBound_caps_at_42_for_K8 :
    2 * (42 : ℕ).choose 8 < 2 ^ ((8 : ℕ).choose 2) ∧
      ¬ (2 * (43 : ℕ).choose 8 < 2 ^ ((8 : ℕ).choose 2)) := by
  have h42 : (42 : ℕ).choose 8 = 118030185 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  have h43 : (43 : ℕ).choose 8 = 145008513 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  rw [h42, h43]
  decide

/-- **Deletion reaches a 45-vertex monochromatic-`K₈`-free set.**  Applying the deletion
    method at `n = 46, k = 8` gives
    `deletionBound 46 8 = 46 − ⌊2·C(46,8)/2^{28}⌋ = 46 − ⌊521865630/268435456⌋ = 46 − 1 = 45`:
    a 2-colouring of `K₄₆` and a set `R` of at least 45 vertices with no monochromatic
    `K₈`.  This **strictly beats** the sharp union bound (`unionBound_caps_at_42_for_K8`,
    which stops at 42), so the deletion method certifies `R(8,8) > 45` — a `+3` strict
    improvement over the union bound, continuing the `+1` (`k = 6`) and `+2` (`k = 7`)
    gains of the two witnesses above.

    `n = 46` is the top of the `M = 1` deletion window for `k = 8`
    (`2^{28} ≤ 2·C(46,8) = 521865630 < 2·2^{28} = 536870912`, and `C(47,8)` already forces
    `M = 2`), so this is the largest bound the `ramsey_deletion_one_past` mechanism yields
    at `k = 8`.  As with the `k = 7` witness, `C(46,8) = 260932815` is evaluated via the
    `descFactorial` route rather than by `decide` on `Nat.choose`. -/
theorem deletion_no_mono_K8 :
    ∃ (c : Coloring 46) (R : Finset (Fin 46)),
      45 ≤ R.card ∧ ∀ K : Finset (Fin 46), K ⊆ R → K.card = 8 → ¬ Mono c K := by
  obtain ⟨c, R, hRcard, hR⟩ :=
    ramsey_deletion_bound (n := 46) (k := 8) (by norm_num) (by norm_num)
  have h : deletionBound 46 8 = 45 := by
    have h46 : (46 : ℕ).choose 8 = 260932815 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]; decide
    show 46 - (2 * (46 : ℕ).choose 8) / 2 ^ ((8 : ℕ).choose 2) = 45
    rw [h46]; decide
  rw [h] at hRcard
  exact ⟨c, R, hRcard, hR⟩

/-- **The sharp union bound caps at `n = 65` for `k = 9`.**  The first-moment test
    `2·C(n,9) < 2^{C(9,2)} = 2^{36} = 68719476736` holds at `n = 65`
    (`2·31966749880 = 63933499760 < 68719476736`) but fails at `n = 66`
    (`2·37014131440 = 74028262880 ≥ 68719476736`).  So the union bound alone certifies a
    monochromatic-`K₉`-free colouring only up to 65 vertices, i.e. `R(9,9) > 65`.

    As at `k = 7, 8`, the binomials `C(65,9), C(66,9)` are ≈ `10¹⁰`, far past the naive
    `decide`-on-`Nat.choose` range, so we route through the single-recursion identity
    `Nat.choose n k = n.descFactorial k / k !`
    (`Nat.choose_eq_descFactorial_div_factorial`), which needs only `k` kernel
    multiplications and stays axiom-free (`of_decide_eq_true`, no `Lean.ofReduceBool`). -/
theorem unionBound_caps_at_65_for_K9 :
    2 * (65 : ℕ).choose 9 < 2 ^ ((9 : ℕ).choose 2) ∧
      ¬ (2 * (66 : ℕ).choose 9 < 2 ^ ((9 : ℕ).choose 2)) := by
  have h65 : (65 : ℕ).choose 9 = 31966749880 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  have h66 : (66 : ℕ).choose 9 = 37014131440 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  rw [h65, h66]
  decide

/-- **Deletion reaches a 69-vertex monochromatic-`K₉`-free set.**  Applying the deletion
    method at `n = 70, k = 9` gives
    `deletionBound 70 9 = 70 − ⌊2·C(70,9)/2^{36}⌋ = 70 − ⌊130067057120/68719476736⌋ = 70 − 1 = 69`:
    a 2-colouring of `K₇₀` and a set `R` of at least 69 vertices with no monochromatic
    `K₉`.  This **strictly beats** the sharp union bound (`unionBound_caps_at_65_for_K9`,
    which stops at 65), so the deletion method certifies `R(9,9) > 69` — a `+4` strict
    improvement over the union bound, continuing the `+1` (`k = 6`), `+2` (`k = 7`) and
    `+3` (`k = 8`) gains of the witnesses above.

    `n = 70` is the top of the `M = 1` deletion window for `k = 9`
    (`2^{36} ≤ 2·C(70,9) = 130067057120 < 2·2^{36} = 137438953472`, and `C(71,9)` already
    forces `M = 2`), so this is the largest bound the `ramsey_deletion_one_past` mechanism
    yields at `k = 9`.  As with the `k = 7, 8` witnesses, `C(70,9) = 65033528560` is
    evaluated via the `descFactorial` route rather than by `decide` on `Nat.choose`. -/
theorem deletion_no_mono_K9 :
    ∃ (c : Coloring 70) (R : Finset (Fin 70)),
      69 ≤ R.card ∧ ∀ K : Finset (Fin 70), K ⊆ R → K.card = 9 → ¬ Mono c K := by
  obtain ⟨c, R, hRcard, hR⟩ :=
    ramsey_deletion_bound (n := 70) (k := 9) (by norm_num) (by norm_num)
  have h : deletionBound 70 9 = 69 := by
    have h70 : (70 : ℕ).choose 9 = 65033528560 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]; decide
    show 70 - (2 * (70 : ℕ).choose 9) / 2 ^ ((9 : ℕ).choose 2) = 69
    rw [h70]; decide
  rw [h] at hRcard
  exact ⟨c, R, hRcard, hR⟩

/-- **The sharp union bound caps at `n = 100` for `k = 10`.**  The first-moment test
    `2·C(n,10) < 2^{C(10,2)} = 2^{45} = 35184372088832` holds at `n = 100`
    (`2·17310309456440 = 34620618912880 < 35184372088832`) but fails at `n = 101`
    (`2·19212541264840 = 38425082529680 ≥ 35184372088832`).  So the union bound alone
    certifies a monochromatic-`K₁₀`-free colouring only up to 100 vertices, i.e.
    `R(10,10) > 100`.

    As at `k = 7, 8, 9`, the binomials `C(100,10), C(101,10)` are ≈ `10¹³`, far past the
    naive `decide`-on-`Nat.choose` range, so we route through the single-recursion identity
    `Nat.choose n k = n.descFactorial k / k !`
    (`Nat.choose_eq_descFactorial_div_factorial`), which needs only `k` kernel
    multiplications and stays axiom-free (`of_decide_eq_true`, no `Lean.ofReduceBool`). -/
theorem unionBound_caps_at_100_for_K10 :
    2 * (100 : ℕ).choose 10 < 2 ^ ((10 : ℕ).choose 2) ∧
      ¬ (2 * (101 : ℕ).choose 10 < 2 ^ ((10 : ℕ).choose 2)) := by
  have h100 : (100 : ℕ).choose 10 = 17310309456440 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  have h101 : (101 : ℕ).choose 10 = 19212541264840 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  rw [h100, h101]
  decide

/-- **Deletion reaches a 106-vertex monochromatic-`K₁₀`-free set.**  Applying the deletion
    method at `n = 107, k = 10` gives
    `deletionBound 107 10 = 107 − ⌊2·C(107,10)/2^{45}⌋ = 107 − ⌊70274746011470/35184372088832⌋
    = 107 − 1 = 106`: a 2-colouring of `K₁₀₇` and a set `R` of at least 106 vertices with no
    monochromatic `K₁₀`.  This **strictly beats** the sharp union bound
    (`unionBound_caps_at_100_for_K10`, which stops at 100), so the deletion method certifies
    `R(10,10) > 106` — a `+6` strict improvement over the union bound, continuing the `+1`
    (`k = 6`), `+2` (`k = 7`), `+3` (`k = 8`) and `+4` (`k = 9`) gains of the witnesses above.

    `n = 107` is the top of the `M = 1` deletion window for `k = 10`
    (`2^{45} ≤ 2·C(107,10) = 70274746011470 < 2·2^{45} = 70368744177664`, and `C(108,10)`
    already forces `M = 2`), so this is the largest bound the `ramsey_deletion_one_past`
    mechanism yields at `k = 10`.  As with the `k = 7, 8, 9` witnesses,
    `C(107,10) = 35137373005735` is evaluated via the `descFactorial` route rather than by
    `decide` on `Nat.choose`. -/
theorem deletion_no_mono_K10 :
    ∃ (c : Coloring 107) (R : Finset (Fin 107)),
      106 ≤ R.card ∧ ∀ K : Finset (Fin 107), K ⊆ R → K.card = 10 → ¬ Mono c K := by
  obtain ⟨c, R, hRcard, hR⟩ :=
    ramsey_deletion_bound (n := 107) (k := 10) (by norm_num) (by norm_num)
  have h : deletionBound 107 10 = 106 := by
    have h107 : (107 : ℕ).choose 10 = 35137373005735 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]; decide
    show 107 - (2 * (107 : ℕ).choose 10) / 2 ^ ((10 : ℕ).choose 2) = 106
    rw [h107]; decide
  rw [h] at hRcard
  exact ⟨c, R, hRcard, hR⟩

#check @ramsey_deletion
#check @ramsey_deletion_window
#check @ramsey_deletion_generalizes_first_moment
#check @ramsey_deletion_bound
#check @ramsey_deletion_one_past
#check @deletionBound_mono_of_pred_subthreshold
#check @deletionBound_mono_of_unionFeasible
#check @deletionBound_mono_window
#check @deletion_noloss_across_window
#check @deletion_no_mono_K6
#check @unionBound_caps_at_27_for_K7
#check @deletion_no_mono_K7
#check @unionBound_caps_at_42_for_K8
#check @deletion_no_mono_K8
#check @unionBound_caps_at_65_for_K9
#check @deletion_no_mono_K9
#check @unionBound_caps_at_100_for_K10
#check @deletion_no_mono_K10

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no `sorryAx`, no `Lean.ofReduceBool`, no `native_decide`.  The concrete `k = 6` and
-- `k = 7` witnesses use kernel `decide` (`of_decide_eq_true`), which is axiom-free — it
-- does NOT introduce `Lean.ofReduceBool` the way `native_decide` would.  The `k = 7`
-- binomials route through `Nat.choose_eq_descFactorial_div_factorial` to keep the kernel
-- reduction cheap (single-recursion `descFactorial`), also axiom-free.
#print axioms ramsey_deletion
#print axioms ramsey_deletion_window
#print axioms ramsey_deletion_generalizes_first_moment
#print axioms ramsey_deletion_one_past
#print axioms deletionBound_mono_of_pred_subthreshold
#print axioms deletionBound_mono_of_unionFeasible
#print axioms deletionBound_mono_window
#print axioms deletion_noloss_across_window
#print axioms deletion_no_mono_K6
#print axioms unionBound_caps_at_27_for_K7
#print axioms deletion_no_mono_K7
#print axioms unionBound_caps_at_42_for_K8
#print axioms deletion_no_mono_K8
#print axioms unionBound_caps_at_65_for_K9
#print axioms deletion_no_mono_K9
#print axioms unionBound_caps_at_100_for_K10
#print axioms deletion_no_mono_K10

end ProbMethod.RamseyDeletion
