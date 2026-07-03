/-
  Ramsey R(k,k) via the Symmetric Lovász Local Lemma  (ramsey-r4k-extensions OQ-03)

  The classical Erdős first-moment bound  R(k,k) > 2^{⌊k/2⌋}  (proved axiom-free
  in `Proofs/ErdosRamseyLowerBound.lean`) is improved by a factor Θ(k) using the
  symmetric Lovász Local Lemma (LLL).  The bad events "the k-clique S is
  monochromatic" are NOT independent, but the event for S depends only on the
  events for cliques sharing an edge with S.  This file supplies the axiom-free
  combinatorial core of that application together with a hypothesis-clean
  reduction:

  * `cliqueMonoProb k = 2 / 2^C(k,2)` — the probability that a fixed k-clique is
    monochromatic under a uniform random 2-colouring of the edges of K_n
    (the value `p` in the symmetric LLL).

  * `cliqueDependencyBound n k = C(k,2)·C(n-2,k-2)` — the LLL dependency degree
    `d`, together with the PROVED count `cliqueNeighbors_card_le`: for any fixed
    k-clique S the number of other k-cliques whose vertex set meets S in ≥ 2
    vertices (equivalently, whose edge set shares an edge with S) is at most
    `cliqueDependencyBound n k`.  This is the fact stated but not proved in the
    `RamseyR4kExtensions` narrative.

  * `RamseyLLLCondition n k` — the symmetric-LLL applicability test
    `e·p·(d+1) ≤ 1`, with the standard surrogate `e ≤ 3` already used by the
    gallery's other LLL files, plus its antitonicity in `n`.

  * `SymmetricLLLForRamsey` / `ramsey_lll_lower_bound` — assuming the symmetric-LLL
    avoidance principle (the single ingredient not yet in Mathlib), the numeric
    condition yields a monochromatic-clique-free 2-colouring of K_n, i.e.
    R(k,k) > n.  No `axiom`, no `sorry`: the LLL principle is an explicit,
    clearly-labelled hypothesis rather than an assumed axiom.

  Erdős–Lovász (1975); Spencer (1977).
-/
import Mathlib
import Proofs.ErdosRamseyLowerBound

namespace RamseyLLL

open Finset

-- ═══════════════════════════════════════════════════════════════════
-- PART I: THE LLL PARAMETERS FOR THE MONOCHROMATIC-CLIQUE EVENTS
-- ═══════════════════════════════════════════════════════════════════

/-- Probability that a *fixed* k-clique is monochromatic under a uniform random
    2-colouring of the edges of `K_n`: there are `C(k,2)` edges, `2` monochromatic
    colourings out of `2^{C(k,2)}`, so `p = 2 / 2^{C(k,2)}`.  This is the value
    `p` fed to the symmetric Lovász Local Lemma. -/
def cliqueMonoProb (k : ℕ) : ℚ := 2 / 2 ^ (k.choose 2)

/-- The LLL dependency degree `d` for the monochromatic-clique events on `K_n`:
    a fixed k-clique `S` has `C(k,2)` edges, and each edge lies in at most
    `C(n-2, k-2)` other k-cliques, so at most `C(k,2)·C(n-2,k-2)` cliques are
    dependent on `S`.  The next section proves this really is an upper bound. -/
def cliqueDependencyBound (n k : ℕ) : ℕ := k.choose 2 * (n - 2).choose (k - 2)

/-- The symmetric-LLL applicability condition `e·p·(d+1) ≤ 1` for the
    diagonal-Ramsey monochromatic-clique events, using the standard rational
    surrogate `e ≤ 3` shared with the gallery's `LovaszLocalLemma` files.  When it
    holds, the symmetric LLL guarantees a monochromatic-clique-free 2-colouring of
    `K_n`, hence `R(k,k) > n`. -/
def RamseyLLLCondition (n k : ℕ) : Prop :=
  3 * cliqueMonoProb k * ((cliqueDependencyBound n k : ℚ) + 1) ≤ 1

lemma cliqueMonoProb_pos (k : ℕ) : 0 < cliqueMonoProb k := by
  unfold cliqueMonoProb; positivity

/-- For `k ≥ 2` the monochromatic-clique probability is at most `1` (a fixed
    clique has at least one edge). -/
lemma cliqueMonoProb_le_one {k : ℕ} (hk : 2 ≤ k) : cliqueMonoProb k ≤ 1 := by
  unfold cliqueMonoProb
  have h1 : 1 ≤ k.choose 2 := by
    calc 1 = (2 : ℕ).choose 2 := by decide
      _ ≤ k.choose 2 := Nat.choose_le_choose 2 hk
  have h2 : (2 : ℚ) ≤ 2 ^ (k.choose 2) := by
    calc (2 : ℚ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (k.choose 2) := by
          apply pow_le_pow_right₀ (by norm_num) h1
  rw [div_le_one (by positivity)]
  linarith

-- ═══════════════════════════════════════════════════════════════════
-- PART II: THE DEPENDENCY-DEGREE BOUND (axiom-free combinatorics)
-- ═══════════════════════════════════════════════════════════════════

/-- The k-cliques (other than `S`) whose vertex set meets `S` in at least two
    vertices — equivalently, whose edge set shares an edge with `S`'s.  These are
    exactly the bad events "dependent" on the bad event for `S` in the LLL
    dependency graph. -/
def cliqueNeighbors {n : ℕ} (S : Finset (Fin n)) (k : ℕ) : Finset (Finset (Fin n)) :=
  (univ.powersetCard k).filter (fun T => T ≠ S ∧ 2 ≤ (S ∩ T).card)

/-- For a fixed pair `e` (`|e| = 2`), the number of k-cliques of `K_n` containing
    `e` is at most `C(n-2, k-2)`:  the map `T ↦ T \ e` injects them into the
    `(k-2)`-subsets of the remaining `n-2` vertices. -/
theorem containing_card_le {n : ℕ} (e : Finset (Fin n)) (k : ℕ) (he : e.card = 2) :
    ((univ.powersetCard k).filter (fun T => e ⊆ T)).card
      ≤ (n - 2).choose (k - 2) := by
  classical
  have hmaps : Set.MapsTo (fun T => T \ e)
      ((univ.powersetCard k).filter (fun T => e ⊆ T) : Set (Finset (Fin n)))
      (powersetCard (k - 2) (univ \ e) : Set (Finset (Fin n))) := by
    intro T hT
    rw [Finset.mem_coe, mem_filter, mem_powersetCard] at hT
    obtain ⟨⟨_hsub, hTcard⟩, heT⟩ := hT
    rw [Finset.mem_coe, mem_powersetCard]
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [mem_sdiff] at hx ⊢
      exact ⟨mem_univ x, hx.2⟩
    · rw [card_sdiff_of_subset heT, hTcard, he]
  have hinj : Set.InjOn (fun T => T \ e)
      ((univ.powersetCard k).filter (fun T => e ⊆ T) : Set (Finset (Fin n))) := by
    intro T hT T' hT' heq
    rw [Finset.mem_coe, mem_filter, mem_powersetCard] at hT hT'
    have hTe : e ⊆ T := hT.2
    have hT'e : e ⊆ T' := hT'.2
    have heq' : T \ e = T' \ e := heq
    calc T = (T \ e) ∪ e := (sdiff_union_of_subset hTe).symm
      _ = (T' \ e) ∪ e := by rw [heq']
      _ = T' := sdiff_union_of_subset hT'e
  calc ((univ.powersetCard k).filter (fun T => e ⊆ T)).card
      ≤ (powersetCard (k - 2) (univ \ e)).card := card_le_card_of_injOn _ hmaps hinj
    _ = ((univ \ e).card).choose (k - 2) := card_powersetCard _ _
    _ = (n - 2).choose (k - 2) := by
        rw [card_sdiff_of_subset (subset_univ e), card_univ, Fintype.card_fin, he]

/-- **Dependency-degree bound.**  For any fixed k-clique `S` of `K_n`, the number
    of *other* k-cliques whose vertex set meets `S` in ≥ 2 vertices — i.e. the LLL
    dependency degree of the bad event "S is monochromatic" — is at most
    `cliqueDependencyBound n k = C(k,2)·C(n-2,k-2)`.

    Proof: every such clique `T` shares a pair `e ⊆ S ∩ T`, so the neighbours are
    covered by the `C(k,2)` pairs of `S`, each carrying ≤ `C(n-2,k-2)` cliques. -/
theorem cliqueNeighbors_card_le {n : ℕ} (S : Finset (Fin n)) (k : ℕ) (hS : S.card = k) :
    (cliqueNeighbors S k).card ≤ cliqueDependencyBound n k := by
  classical
  have hcover : cliqueNeighbors S k
      ⊆ (S.powersetCard 2).biUnion
          (fun e => (univ.powersetCard k).filter (fun T => e ⊆ T)) := by
    intro T hT
    rw [cliqueNeighbors, mem_filter] at hT
    obtain ⟨hTmem, _hTne, hge⟩ := hT
    obtain ⟨e, hesub, hecard⟩ := exists_subset_card_eq hge
    rw [mem_biUnion]
    refine ⟨e, ?_, ?_⟩
    · rw [mem_powersetCard]
      exact ⟨hesub.trans inter_subset_left, hecard⟩
    · rw [mem_filter]
      exact ⟨hTmem, hesub.trans inter_subset_right⟩
  calc (cliqueNeighbors S k).card
      ≤ ((S.powersetCard 2).biUnion
          (fun e => (univ.powersetCard k).filter (fun T => e ⊆ T))).card :=
        card_le_card hcover
    _ ≤ (S.powersetCard 2).card * (n - 2).choose (k - 2) := by
        apply card_biUnion_le_card_mul
        intro e he
        rw [mem_powersetCard] at he
        exact containing_card_le e k he.2
    _ = cliqueDependencyBound n k := by
        unfold cliqueDependencyBound
        rw [card_powersetCard, hS]

-- ═══════════════════════════════════════════════════════════════════
-- PART III: THE SYMMETRIC-LLL → RAMSEY REDUCTION (hypothesis-clean)
-- ═══════════════════════════════════════════════════════════════════

/-- **Symmetric Lovász Local Lemma, Ramsey avoidance form.**  The single
    ingredient not yet in Mathlib: if the monochromatic-clique events on `K_n`
    satisfy the symmetric-LLL numeric test `e·p·(d+1) ≤ 1` (with
    `p = cliqueMonoProb k` and `d = cliqueDependencyBound n k`, whose validity as
    the true dependency degree is `cliqueNeighbors_card_le`), then some symmetric
    irreflexive 2-colouring of `K_n` has no monochromatic k-clique of either
    colour.  Kept as an explicit hypothesis so every downstream result is
    axiom-free. -/
def SymmetricLLLForRamsey : Prop :=
  ∀ n k : ℕ, 3 ≤ k → RamseyLLLCondition n k →
    ∃ color : Fin n → Fin n → Bool,
      (∀ x y, color x y = color y x) ∧
      (∀ x, color x x = false) ∧
      (∀ s : Finset (Fin n), s.card = k →
        ¬ (∀ x y, x ∈ s → y ∈ s → x ≠ y → color x y = true)) ∧
      (∀ s : Finset (Fin n), s.card = k →
        ¬ (∀ x y, x ∈ s → y ∈ s → x ≠ y → color x y = false))

/-- **LLL-improved diagonal Ramsey lower bound (reduction).**  Assuming the
    symmetric-LLL avoidance principle, whenever the LLL numeric condition holds at
    `(n, k)` there is a monochromatic-`K_k`-free 2-colouring of `K_n`; that is,
    `R(k,k) > n`.  Because `RamseyLLLCondition` is antitone in `n`
    (`RamseyLLLCondition_antitone`), this yields the bound at every smaller `n` as
    well. -/
theorem ramsey_lll_lower_bound (hLLL : SymmetricLLLForRamsey)
    {k : ℕ} (hk : 3 ≤ k) {n : ℕ} (hcond : RamseyLLLCondition n k) :
    ∃ color : Fin n → Fin n → Bool,
      (∀ x y, color x y = color y x) ∧
      (∀ x, color x x = false) ∧
      (∀ s : Finset (Fin n), s.card = k →
        ¬ (∀ x y, x ∈ s → y ∈ s → x ≠ y → color x y = true)) ∧
      (∀ s : Finset (Fin n), s.card = k →
        ¬ (∀ x y, x ∈ s → y ∈ s → x ≠ y → color x y = false)) :=
  hLLL n k hk hcond

-- ═══════════════════════════════════════════════════════════════════
-- PART IV: MONOTONICITY OF THE LLL THRESHOLD
-- ═══════════════════════════════════════════════════════════════════

/-- The dependency degree is monotone in the number of vertices. -/
lemma cliqueDependencyBound_mono {n m k : ℕ} (h : n ≤ m) :
    cliqueDependencyBound n k ≤ cliqueDependencyBound m k := by
  unfold cliqueDependencyBound
  exact Nat.mul_le_mul (le_refl _)
    (Nat.choose_le_choose (k - 2) (Nat.sub_le_sub_right h 2))

/-- The LLL condition defines a genuine threshold: if it holds at `m` vertices it
    holds at every `n ≤ m`.  (More vertices ⇒ larger dependency degree ⇒ harder to
    satisfy.) -/
lemma RamseyLLLCondition_antitone {n m k : ℕ} (h : n ≤ m)
    (hm : RamseyLLLCondition m k) : RamseyLLLCondition n k := by
  unfold RamseyLLLCondition at *
  have hd : (cliqueDependencyBound n k : ℚ) ≤ (cliqueDependencyBound m k : ℚ) := by
    exact_mod_cast cliqueDependencyBound_mono h
  have hp : (0 : ℚ) ≤ 3 * cliqueMonoProb k := by
    have := cliqueMonoProb_pos k; linarith
  calc 3 * cliqueMonoProb k * ((cliqueDependencyBound n k : ℚ) + 1)
      ≤ 3 * cliqueMonoProb k * ((cliqueDependencyBound m k : ℚ) + 1) := by
        apply mul_le_mul_of_nonneg_left _ hp
        linarith
    _ ≤ 1 := hm

-- ═══════════════════════════════════════════════════════════════════
-- PART V: WHY LLL BEATS THE UNION BOUND (dependency-vs-total identity)
-- ═══════════════════════════════════════════════════════════════════

/-- **Exact dependency-to-total identity.**  Counting incidences
    `(k-clique, edge inside it)` two ways gives
    `C(n,2)·d = C(k,2)²·C(n,k)`, where `d = cliqueDependencyBound n k` is the LLL
    dependency degree and `C(n,k)` is the total number of bad events (the k-cliques
    of `K_n`).  Equivalently `d / C(n,k) = C(k,2)² / C(n,2)`: the dependency degree
    is only a `Θ(k⁴/n²)` fraction of all events, which is exactly why the *local*
    LLL test controls the process where the *global* union bound cannot.  Pure
    finite counting via the subset-of-a-subset identity `Nat.choose_mul`. -/
theorem cliqueDependency_total_identity {n k : ℕ} (hk : 2 ≤ k) :
    n.choose 2 * cliqueDependencyBound n k = (k.choose 2) ^ 2 * n.choose k := by
  unfold cliqueDependencyBound
  have h : n.choose k * k.choose 2 = n.choose 2 * (n - 2).choose (k - 2) :=
    Nat.choose_mul (n := n) (k := k) (s := 2) hk
  calc n.choose 2 * (k.choose 2 * (n - 2).choose (k - 2))
      = k.choose 2 * (n.choose 2 * (n - 2).choose (k - 2)) := by ring
    _ = k.choose 2 * (n.choose k * k.choose 2) := by rw [← h]
    _ = (k.choose 2) ^ 2 * n.choose k := by ring

/-- **In the Ramsey regime the dependency degree is dominated by the total event
    count.**  Whenever `C(k,2)² ≤ C(n,2)` (i.e. `n` is at least quadratic in `k`,
    which holds with enormous room to spare once `n ≈ 2^{k/2}`), the LLL dependency
    degree `d` is at most the number `C(n,k)` of monochromatic-clique events.  This
    is the precise sense in which the symmetric LLL's *local* condition
    `e·p·(d+1) ≤ 1` is weaker — hence satisfiable for larger `n` — than the
    first-moment/union-bound condition, which must control all `C(n,k)` events at
    once. -/
theorem cliqueDependencyBound_le_total {n k : ℕ} (hk : 2 ≤ k) (hn : 2 ≤ n)
    (hreg : (k.choose 2) ^ 2 ≤ n.choose 2) :
    cliqueDependencyBound n k ≤ n.choose k := by
  have hpos : 0 < n.choose 2 := Nat.choose_pos hn
  have key : n.choose 2 * cliqueDependencyBound n k ≤ n.choose 2 * n.choose k := by
    rw [cliqueDependency_total_identity hk]
    gcongr
  exact le_of_mul_le_mul_left key hpos

end RamseyLLL
