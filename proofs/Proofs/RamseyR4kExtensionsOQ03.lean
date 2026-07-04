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
-- PART V: A CHECKABLE INTEGER CRITERION AND A CONCRETE IMPROVEMENT
-- ═══════════════════════════════════════════════════════════════════

/-- **Integer form of the LLL feasibility test.**  Clearing the denominator
    `2^{C(k,2)}` of `p = cliqueMonoProb k` and the surrogate `e ≤ 3`, the
    symmetric-LLL condition `3 · (2 / 2^{C(k,2)}) · (d + 1) ≤ 1` is *exactly* the
    integer inequality `6 · (d + 1) ≤ 2^{C(k,2)}` with `d = cliqueDependencyBound n k`.
    This turns the rational test into a decidable `ℕ` inequality, so any concrete
    `(n, k)` can be settled by `decide`. -/
theorem ramseyLLLCondition_iff (n k : ℕ) :
    RamseyLLLCondition n k ↔
      6 * (cliqueDependencyBound n k + 1) ≤ 2 ^ (k.choose 2) := by
  unfold RamseyLLLCondition cliqueMonoProb
  rw [show (3 : ℚ) * (2 / 2 ^ (k.choose 2)) * ((cliqueDependencyBound n k : ℚ) + 1)
        = 6 * ((cliqueDependencyBound n k : ℚ) + 1) / 2 ^ (k.choose 2) by ring,
      div_le_one (by positivity)]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

/-- The LLL feasibility condition is decidable — via the integer criterion
    `ramseyLLLCondition_iff` it reduces to a `ℕ` inequality. -/
instance (n k : ℕ) : Decidable (RamseyLLLCondition n k) :=
  decidable_of_iff _ (ramseyLLLCondition_iff n k).symm

/-- **The LLL condition is satisfiable exactly in the regime where it beats the
    first moment.**  At `k = 6` the feasibility test holds all the way up to
    `n = 13`: `6·(C(6,2)·C(11,4)+1) = 29706 ≤ 32768 = 2^{15}`.  Combined with
    `ramsey_lll_lower_bound` (given the symmetric-LLL principle) this yields
    `R(6,6) > 13`, strictly better than the first-moment bound
    `R(6,6) > 2^{⌊6/2⌋} = 8`.  So the extra factor supplied by the LLL is not
    vacuous. -/
theorem ramseyLLLCondition_13_6 : RamseyLLLCondition 13 6 :=
  (ramseyLLLCondition_iff 13 6).mpr (by decide)

/-- Likewise at `k = 5` the test holds up to `n = 7` (`6·(C(5,2)·C(5,3)+1) = 606 ≤
    1024 = 2^{10}`), giving `R(5,5) > 7` under the LLL principle — again beating the
    first-moment bound `R(5,5) > 2^{⌊5/2⌋} = 4`. -/
theorem ramseyLLLCondition_7_5 : RamseyLLLCondition 7 5 :=
  (ramseyLLLCondition_iff 7 5).mpr (by decide)

-- ═══════════════════════════════════════════════════════════════════
-- PART VI: WHY LLL BEATS THE UNION BOUND (dependency-vs-total identity)
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

-- ═══════════════════════════════════════════════════════════════════
-- PART VII: HONEST COMPARISON WITH THE OPTIMIZED UNION BOUND
-- ═══════════════════════════════════════════════════════════════════

/-- **Optimized first-moment (union-bound) feasibility test.**  A uniformly random
    2-colouring of `K_n` has positive probability of avoiding every monochromatic
    k-clique as soon as the *expected* number of monochromatic k-cliques is `< 1`,
    i.e. `C(n,k)·2·2^{-C(k,2)} < 1`, equivalently the integer inequality
    `2·C(n,k) < 2^{C(k,2)}`.  This is the honest first-moment threshold: the sharp
    optimum of the union bound, *not* the deliberately weakened closed form
    `R(k,k) > 2^{⌊k/2⌋}` used elsewhere for its clean shape.  A `ℕ` inequality, so
    decidable. -/
def firstMomentCondition (n k : ℕ) : Prop := 2 * n.choose k < 2 ^ (k.choose 2)

instance (n k : ℕ) : Decidable (firstMomentCondition n k) := by
  unfold firstMomentCondition; infer_instance

/-- **The two tests are governed by proportional core terms.**  Rescaling the exact
    dependency identity `C(n,2)·d = C(k,2)²·C(n,k)` (`cliqueDependency_total_identity`)
    by `6` exhibits the LLL test's core quantity `6·d` and the union-bound test's
    core quantity `2·C(n,k)` as proportional:
    `C(n,2)·(6·d) = 3·C(k,2)²·(2·C(n,k))`.
    Both tests compare their core against the *same* budget `2^{C(k,2)}` (LLL wants
    `6(d+1) ≤ 2^{C(k,2)}` by `ramseyLLLCondition_iff`; the union bound wants
    `2·C(n,k) < 2^{C(k,2)}`), so the ratio `3·C(k,2)² / C(n,2)` decides which test is
    the more permissive.  This is the exact, finite crossover criterion between the
    symmetric LLL and the union bound. -/
theorem lll_core_eq_firstMoment_core {n k : ℕ} (hk : 2 ≤ k) :
    n.choose 2 * (6 * cliqueDependencyBound n k)
      = 3 * (k.choose 2) ^ 2 * (2 * n.choose k) := by
  have h := cliqueDependency_total_identity (n := n) (k := k) hk
  calc n.choose 2 * (6 * cliqueDependencyBound n k)
      = 6 * (n.choose 2 * cliqueDependencyBound n k) := by ring
    _ = 6 * ((k.choose 2) ^ 2 * n.choose k) := by rw [h]
    _ = 3 * (k.choose 2) ^ 2 * (2 * n.choose k) := by ring

/-- **Crossover, large-`n` (asymptotic) side.**  When `3·C(k,2)² ≤ C(n,2)` — i.e.
    `n` is large relative to `k²`, the regime `n ≈ 2^{k/2}` of the actual Ramsey
    application — the LLL core `6·d` is at most the union-bound core `2·C(n,k)`, so
    the symmetric LLL test is the more permissive of the two.  This is the precise,
    axiom-free sense in which the LLL eventually beats the union bound (and, chased
    through the constants, delivers the extra factor `Θ(k)`). -/
theorem lll_core_le_firstMoment_core {n k : ℕ} (hk : 2 ≤ k) (hn : 2 ≤ n)
    (hreg : 3 * (k.choose 2) ^ 2 ≤ n.choose 2) :
    6 * cliqueDependencyBound n k ≤ 2 * n.choose k := by
  have hpos : 0 < n.choose 2 := Nat.choose_pos hn
  have key : n.choose 2 * (6 * cliqueDependencyBound n k)
      ≤ n.choose 2 * (2 * n.choose k) := by
    rw [lll_core_eq_firstMoment_core hk]
    gcongr
  exact le_of_mul_le_mul_left key hpos

/-- **Crossover, small-`k` side — the LLL as set up here does NOT beat the honest
    union bound at `k = 6`.**  The union bound is feasible all the way to `n = 17`
    (`2·C(17,6) = 24752 < 32768 = 2^{15}`), giving `R(6,6) > 17`, whereas the LLL
    test already *fails* at `n = 14` (indeed at `n = 17`).  So the improvement over
    the first moment claimed elsewhere in this entry is only over the *weakened*
    closed form `R(6,6) > 2^{⌊6/2⌋} = 8`; against the sharp union bound the LLL is
    strictly worse here — the LLL's factor-`Θ(k)` gain is asymptotic and has not yet
    kicked in at `k = 6` (consistent with `3·C(6,2)² = 675 > 136 = C(17,2)`, the
    small-`n` side of `lll_core_le_firstMoment_core`). -/
theorem unionBound_beats_lll_at_6 :
    firstMomentCondition 17 6 ∧ ¬ RamseyLLLCondition 17 6 := by
  refine ⟨by decide, ?_⟩
  rw [ramseyLLLCondition_iff]
  decide

/-- The same phenomenon at `k = 7`: the union bound is feasible at `n = 27`
    (`2·C(27,7) = 1776060 < 2097152 = 2^{21}`, giving `R(7,7) > 27`), while the LLL
    test fails there.  So at `k = 7` too the sharp first moment is stronger than the
    symmetric-LLL test of this file. -/
theorem unionBound_beats_lll_at_7 :
    firstMomentCondition 27 7 ∧ ¬ RamseyLLLCondition 27 7 := by
  refine ⟨by decide, ?_⟩
  rw [ramseyLLLCondition_iff]
  decide

/-- **Crossover, small-`n` (strict converse) side.**  The exact dual of
    `lll_core_le_firstMoment_core`.  When `C(n,2) < 3·C(k,2)²` — `n` is *small*
    relative to `k²`, the pre-asymptotic regime of `unionBound_beats_lll_at_6/7` —
    the union-bound core `2·C(n,k)` is *strictly* smaller than the LLL core `6·d`,
    so the honest first moment is the more permissive of the two tests.  Together
    with `lll_core_le_firstMoment_core` this pins the crossover to the single
    scalar comparison `C(n,2) ⋛ 3·C(k,2)²`.

    Proof: cancel the positive common factor `2·C(n,k) > 0` (needs `k ≤ n`) out of
    the exact identity `C(n,2)·(6d) = 3·C(k,2)²·(2·C(n,k))`
    (`lll_core_eq_firstMoment_core`); the strict hypothesis on `C(n,2)` then
    transfers directly. -/
theorem firstMoment_core_lt_lll_core {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    (hreg : n.choose 2 < 3 * (k.choose 2) ^ 2) :
    2 * n.choose k < 6 * cliqueDependencyBound n k := by
  have hpos : 0 < 2 * n.choose k := by
    have := Nat.choose_pos hkn; positivity
  have hid := lll_core_eq_firstMoment_core (n := n) (k := k) hk
  have hlt : n.choose 2 * (2 * n.choose k)
      < n.choose 2 * (6 * cliqueDependencyBound n k) := by
    rw [hid]
    exact mul_lt_mul_of_pos_right hreg hpos
  exact lt_of_mul_lt_mul_left hlt (Nat.zero_le _)

/-- **Sharp crossover characterization.**  Combining the large-`n` bound
    `lll_core_le_firstMoment_core` (contrapositive) with its strict small-`n`
    converse `firstMoment_core_lt_lll_core` shows the crossover between the
    symmetric-LLL feasibility core `6·(d+1)` and the sharp union-bound core
    `2·C(n,k)` is governed *exactly* by the sign of `C(n,2) − 3·C(k,2)²`:

      `2·C(n,k) < 6·d  ↔  C(n,2) < 3·C(k,2)²`.

    Reading `6·d` as the dominant part of the LLL budget requirement `6·(d+1)` and
    `2·C(n,k)` as the union-bound budget requirement (both compared against the same
    `2^{C(k,2)}`, cf. `ramseyLLLCondition_iff` and `firstMomentCondition`), this is
    the finite, axiom-free statement that the two feasibility tests of this file
    trade places precisely at `C(n,2) = 3·C(k,2)²`.  It subsumes the numeric
    witnesses `unionBound_beats_lll_at_6/7` (small-`n` side) and the asymptotic
    `lll_core_le_firstMoment_core` (large-`n` side) as the two halves of one
    equivalence. -/
theorem lll_core_gt_firstMoment_core_iff {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    (hn : 2 ≤ n) :
    2 * n.choose k < 6 * cliqueDependencyBound n k
      ↔ n.choose 2 < 3 * (k.choose 2) ^ 2 := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    exact absurd (lll_core_le_firstMoment_core hk hn hcon) (by omega)
  · exact firstMoment_core_lt_lll_core hk hkn

-- ═══════════════════════════════════════════════════════════════════
-- PART VIII: THE REAL LLL CONSTANT `e < 3` JUSTIFIES THE INTEGER SURROGATE
-- ═══════════════════════════════════════════════════════════════════

/-  `RamseyLLLCondition` uses the rational surrogate `e ≤ 3` in place of the true
    symmetric-LLL constant `e`.  Everything above is finite rational/combinatorial
    arithmetic; the one genuinely analytic ingredient needed to connect that
    surrogate to the *real* symmetric LLL is that the avoidance factor
    `(d/(d+1))^d` never drops below `1/3`.  This part supplies exactly that, and
    then derives the per-event symmetric-LLL hypothesis in the shape consumed by
    the general measure-theoretic LLL (`LovaszLocalLemmaOQ01StrongInduction.avoidance_pos`):
    `p ≤ x · (1-x)^d` with `x = 1/(d+1)`.  It does **not** discharge
    `SymmetricLLLForRamsey` — the probability-space construction and the
    independence hypothesis remain open — but it closes the numeric gap between the
    file's rational test and the real LLL, which is the arithmetic half of that
    reduction. -/

/-- **The symmetric avoidance factor stays above `1/3`.**  For every dependency
    degree `d`, `(d/(d+1))^d ≥ 1/3`.

    This is the quantitative fact behind the surrogate `e ≤ 3` used in
    `RamseyLLLCondition`: the true symmetric-LLL inequality `p ≤ x·(1-x)^d` at the
    optimal `x = 1/(d+1)` needs the factor `(1-x)^d = (d/(d+1))^d`, and this factor
    is `≥ 1/e > 1/3` because `(1 + 1/d)^d ≤ e < 3`.  The proof raises Mathlib's
    `Real.add_one_le_exp` (`1 + 1/d ≤ exp(1/d)`) to the `d`-th power to get
    `(1+1/d)^d ≤ exp 1`, invokes `Real.exp_one_lt_d9` (`exp 1 < 2.7182818286 < 3`),
    and inverts. -/
theorem symmetric_avoidance_factor_ge_third (d : ℕ) :
    (1 : ℝ) / 3 ≤ ((d : ℝ) / (d + 1)) ^ d := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; norm_num
  · have htpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    -- (1 + 1/d) ≤ exp (1/d)
    have hstep : (1 : ℝ) + 1 / d ≤ Real.exp (1 / d) := by
      have h := Real.add_one_le_exp (1 / (d : ℝ)); linarith
    have hbase_nonneg : (0 : ℝ) ≤ 1 + 1 / (d : ℝ) := by positivity
    -- raise to the d-th power
    have hpow : (1 + 1 / (d : ℝ)) ^ d ≤ Real.exp (1 / d) ^ d :=
      pow_le_pow_left₀ hbase_nonneg hstep d
    -- exp(1/d)^d = exp(d · (1/d)) = exp 1
    have hexp : Real.exp (1 / (d : ℝ)) ^ d = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; congr 1; field_simp
    -- combine: (1 + 1/d)^d ≤ exp 1 < 3
    have hlt3 : (1 + 1 / (d : ℝ)) ^ d < 3 := by
      calc (1 + 1 / (d : ℝ)) ^ d ≤ Real.exp 1 := by rw [← hexp]; exact hpow
        _ < 2.7182818286 := Real.exp_one_lt_d9
        _ < 3 := by norm_num
    -- 1 + 1/d = (d+1)/d
    have hid : (1 : ℝ) + 1 / d = ((d : ℝ) + 1) / d := by field_simp
    have hXpos : (0 : ℝ) < (((d : ℝ) + 1) / d) ^ d := by positivity
    have hXle : (((d : ℝ) + 1) / d) ^ d ≤ 3 := by rw [← hid]; exact hlt3.le
    -- invert: 1/3 ≤ 1/X = (d/(d+1))^d
    have hinv := one_div_le_one_div_of_le hXpos hXle
    rw [show ((d : ℝ) / (d + 1)) ^ d = 1 / (((d : ℝ) + 1) / d) ^ d by
          rw [one_div, ← inv_pow, inv_div]]
    exact hinv

/-- **The rational LLL test implies the real symmetric-LLL per-event hypothesis.**
    Writing `D = cliqueDependencyBound n k` and `x = 1/(D+1)`, the numeric condition
    `RamseyLLLCondition n k` (i.e. `3·p·(D+1) ≤ 1`) implies the inequality the
    measure-theoretic LLL actually consumes,
    `p ≤ x · (D/(D+1))^D = x · (1-x)^D`.

    Proof: `RamseyLLLCondition` gives `p ≤ 1/(3(D+1))`; multiply the factor bound
    `(D/(D+1))^D ≥ 1/3` (`symmetric_avoidance_factor_ge_third`) by `x = 1/(D+1) ≥ 0`
    to get `x·(D/(D+1))^D ≥ 1/(3(D+1)) ≥ p`.  Since every factor `1-x = D/(D+1) < 1`,
    for any dependency set `S₁` with `|S₁| ≤ D` we also have
    `∏_{j∈S₁}(1-x) ≥ (D/(D+1))^D`, so this is exactly the `hlll` premise of
    `avoidance_pos` in the symmetric case. -/
theorem cliqueMonoProb_le_symmetric_lll_rhs {n k : ℕ} (hcond : RamseyLLLCondition n k) :
    (cliqueMonoProb k : ℝ)
      ≤ (1 / ((cliqueDependencyBound n k : ℝ) + 1))
          * ((cliqueDependencyBound n k : ℝ) / ((cliqueDependencyBound n k : ℝ) + 1))
              ^ (cliqueDependencyBound n k) := by
  set D := cliqueDependencyBound n k with hDdef
  have hne : ((D : ℝ) + 1) ≠ 0 := by positivity
  -- unfold the rational condition and cast to ℝ
  have hq : 3 * cliqueMonoProb k * ((D : ℚ) + 1) ≤ 1 := hcond
  have hqr : 3 * (cliqueMonoProb k : ℝ) * ((D : ℝ) + 1) ≤ 1 := by exact_mod_cast hq
  -- p ≤ 1/(3(D+1))
  have hpbound : (cliqueMonoProb k : ℝ) ≤ 1 / (3 * ((D : ℝ) + 1)) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith [hqr]
  -- the real avoidance factor is ≥ 1/3
  have hfac := symmetric_avoidance_factor_ge_third D
  calc (cliqueMonoProb k : ℝ)
      ≤ 1 / (3 * ((D : ℝ) + 1)) := hpbound
    _ = (1 / ((D : ℝ) + 1)) * (1 / 3) := by field_simp
    _ ≤ (1 / ((D : ℝ) + 1)) * (((D : ℝ) / ((D : ℝ) + 1)) ^ D) :=
        mul_le_mul_of_nonneg_left hfac (by positivity)

/-- **The symmetric reserved value satisfies the `hx1` premise of `avoidance_pos`.**
    In the symmetric instantiation of the general asymmetric Lovász Local Lemma
    (`LovaszLocalLemmaOQ01StrongInduction.avoidance_pos`) every reserved value is the
    common `x = 1/(D+1)` with `D = cliqueDependencyBound n k`.  The LLL induction
    requires each `xᵢ < 1`; that holds here because the dependency degree is at least
    `1` whenever `2 ≤ k ≤ n` (both `k.choose 2` and `(n-2).choose (k-2)` are positive),
    so `D + 1 ≥ 2 > 1`. -/
theorem symmetric_reserved_lt_one {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) :
    (1 : ℝ) / ((cliqueDependencyBound n k : ℝ) + 1) < 1 := by
  have h1 : 0 < k.choose 2 := Nat.choose_pos hk
  have h2 : 0 < (n - 2).choose (k - 2) := Nat.choose_pos (by omega)
  have hDpos : 0 < cliqueDependencyBound n k := by
    unfold cliqueDependencyBound; exact Nat.mul_pos h1 h2
  have hD1n : 1 ≤ cliqueDependencyBound n k := hDpos
  have hD1 : (1 : ℝ) ≤ (cliqueDependencyBound n k : ℝ) := by exact_mod_cast hD1n
  rw [div_lt_one (by positivity)]
  linarith

/-- **Block form of the symmetric-LLL numeric premise.**  Generalises
    `cliqueMonoProb_le_symmetric_lll_rhs` from the full-neighbourhood exponent `D` to an
    arbitrary dependency sub-block `S₁` with `|S₁| ≤ D`.  This is the exact shape of the
    `hlll` hypothesis consumed by the general asymmetric Lovász Local Lemma
    `LovaszLocalLemmaOQ01StrongInduction.avoidance_pos`, in the symmetric instantiation
    `xⱼ ≡ 1/(D+1)` (so `1 - xⱼ = D/(D+1)`):

      `p ≤ xᵢ · ∏_{j∈S₁} (1 - xⱼ) = (1/(D+1)) · (D/(D+1))^{|S₁|}`.

    Proof: the base `D/(D+1)` lies in `[0,1]`, so shrinking the exponent from `D` to
    `|S₁| ≤ D` only increases the power (`pow_le_pow_of_le_one`); chain with the
    full-neighbourhood bound `cliqueMonoProb_le_symmetric_lll_rhs`.  Together with
    `symmetric_reserved_lt_one` (the `hx1` premise) this discharges *both* numeric inputs
    of `avoidance_pos` for the monochromatic-clique bad events; only the probability-space
    construction and the mutual-independence hypothesis remain open. -/
theorem cliqueMonoProb_le_symmetric_lll_block {n k : ℕ} (hcond : RamseyLLLCondition n k)
    (S₁ : Finset ℕ) (hcard : S₁.card ≤ cliqueDependencyBound n k) :
    (cliqueMonoProb k : ℝ)
      ≤ (1 / ((cliqueDependencyBound n k : ℝ) + 1))
          * ∏ _j ∈ S₁, (1 - 1 / ((cliqueDependencyBound n k : ℝ) + 1)) := by
  set D := cliqueDependencyBound n k with hDdef
  have hne : ((D : ℝ) + 1) ≠ 0 := by positivity
  -- `1 - 1/(D+1) = D/(D+1)`
  have hfactor : (1 : ℝ) - 1 / ((D : ℝ) + 1) = (D : ℝ) / ((D : ℝ) + 1) := by
    rw [one_sub_div hne]; ring
  -- the constant product over `S₁` is a power of the base
  have hprod : (∏ _j ∈ S₁, (1 - 1 / ((D : ℝ) + 1)))
      = ((D : ℝ) / ((D : ℝ) + 1)) ^ S₁.card := by
    rw [hfactor, Finset.prod_const]
  rw [hprod]
  -- the base `D/(D+1)` lies in `[0,1]`
  have hb0 : (0 : ℝ) ≤ (D : ℝ) / ((D : ℝ) + 1) := by positivity
  have hb1 : (D : ℝ) / ((D : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  -- shrinking the exponent from `D` to `|S₁| ≤ D` only increases the (`≤ 1`) power
  have hpow : ((D : ℝ) / ((D : ℝ) + 1)) ^ D
      ≤ ((D : ℝ) / ((D : ℝ) + 1)) ^ S₁.card :=
    pow_le_pow_of_le_one hb0 hb1 hcard
  have hxnn : (0 : ℝ) ≤ 1 / ((D : ℝ) + 1) := by positivity
  calc (cliqueMonoProb k : ℝ)
      ≤ (1 / ((D : ℝ) + 1)) * (((D : ℝ) / ((D : ℝ) + 1)) ^ D) :=
        cliqueMonoProb_le_symmetric_lll_rhs hcond
    _ ≤ (1 / ((D : ℝ) + 1)) * (((D : ℝ) / ((D : ℝ) + 1)) ^ S₁.card) :=
        mul_le_mul_of_nonneg_left hpow hxnn

end RamseyLLL
