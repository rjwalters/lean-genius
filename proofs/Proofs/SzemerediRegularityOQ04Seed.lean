/-
  # Szemerédi Regularity OQ-04 — S22: seed existence for the AFKS outer loop

  The chain construction (S21, `SzemerediRegularityOQ04Chain.lean`) proves the
  two-level AFKS conclusion from TWO inputs: a seed fine partition satisfying
  the loop invariant (covering, pairwise disjoint, refining the coarse
  partition `Vparts`, globally equitable, per-part mass floor `m`) and an
  invariant-MAINTAINING step oracle.  This file discharges the first input:
  the seed always exists once the coarse parts are large enough.

  * `exists_uniform_blocks` / `exists_two_size_blocks` — the chopping engine:
    a finset of cardinality `k·c` (resp. `a·m + b·(m+1)`) splits into pairwise
    disjoint covering blocks of size exactly `c` (resp. of sizes `m`/`m+1`).

  * `exists_two_size_decomposition` — the arithmetic gate: every `n` with
    `m² ≤ n + 1` is `a·m + b·(m+1)`.  Writing `n = qm + r`, the size bound
    forces `r ≤ q` (else `n ≤ r(m+1) - m ≤ m² - 1 - m < n`), so
    `n = (q-r)·m + r·(m+1)`.  The threshold `m² - 1` is sharp: `n = m² - 2`
    with `r = m - 1` has `q = m - 2 < r`.

  * `exists_equitable_refinement` — the global assembly: a pairwise disjoint
    family whose parts all have `m² ≤ card + 1` admits a refinement into
    blocks whose sizes ALL lie in `{m, m+1}` — so the refinement is globally
    equitable (any two block sizes differ by at most 1), not merely equitable
    within each parent.

  * `exists_equitable_seed` — packaging into exactly the five seed
    obligations of the S21 capstone: cover, pairwise disjoint,
    `IsRefinement q₀ Vparts`, `(B₁.card : ℤ) - B₂.card ≤ 1`, and the mass
    floor `(m : ℚ) ≤ B.card`.

  * `exists_afksTwoLevel_of_large_parts` — the S21 capstone with the seed
    hypotheses REPLACED by the size condition `m² ≤ P.card + 1` on the coarse
    parts: an `ε`-regular coarse partition with large parts plus a maintained
    oracle at scale `m` yields the full two-level conclusion.

  * `exists_afksTwoLevel_of_maintained_oracle_unit` — at scale `m = 1` the
    size condition is vacuous (`1 ≤ card + 1`), so EVERY covering disjoint
    coarse partition admits a seed (the singleton refinement, rebuilt here as
    the `m = 1` instance of the engine): the two-level conclusion needs no
    seed hypothesis at all at unit scale.

  With this file the OQ-04 program's remaining gap is exactly ONE statement:
  the re-equitization step (upgrade the bare-split successor of
  `exists_energy_next_of_not_afksFineRegular` to an invariant-maintaining one
  keeping a positive fraction of its energy gain).  Seed existence is closed.

  All proofs are complete and machine-checked (`#print axioms` reports only
  `[propext, Classical.choice, Quot.sound]`) and contain no `sorry`.

  Reference: Alon–Fischer–Krivelevich–Szegedy, "Efficient testing of large
  graphs", Combinatorica 20 (2000).
-/
import Mathlib
import Proofs.SzemerediRegularityOQ04Chain

namespace Szemeredi.RegularityOQ04Seed

open Classical
open Szemeredi.Core Szemeredi.Regularity Szemeredi.EnergyIncrement
  Szemeredi.RegularityOQ04 Szemeredi.RegularityOQ04Energy
  Szemeredi.RegularityOQ04Bridge Szemeredi.RegularityOQ04StepThree
  Szemeredi.RegularityOQ04DefectGain Szemeredi.RegularityOQ04Outer
  Szemeredi.RegularityOQ04TwoLevel Szemeredi.RegularityOQ04ToleranceBridge
  Szemeredi.RegularityOQ04OuterBoth Szemeredi.RegularityOQ04StepRealize
  Szemeredi.RegularityOQ04Chain

variable {V : Type*} [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- PART I: THE CHOPPING ENGINE
-- ═══════════════════════════════════════════════════════════════════

/-- **Uniform chop.**  A finset of cardinality `k * c` splits into pairwise
    disjoint blocks of size exactly `c` covering it.  Induction on `k`:
    extract one block of size `c` (`Finset.exists_subset_card_eq`) and recurse
    on the difference. -/
theorem exists_uniform_blocks (c : ℕ) :
    ∀ (k : ℕ) (S : Finset V), S.card = k * c →
      ∃ F : Finset (Finset V),
        (∀ B ∈ F, B.card = c) ∧
        (∀ B ∈ F, B ⊆ S) ∧
        (∀ B₁ B₂ : Finset V, B₁ ∈ F → B₂ ∈ F → B₁ ≠ B₂ → Disjoint B₁ B₂) ∧
        (∀ x ∈ S, ∃ B ∈ F, x ∈ B) := by
  intro k
  induction k with
  | zero =>
      intro S hS
      have hSempty : S = ∅ := Finset.card_eq_zero.mp (by simpa using hS)
      subst hSempty
      exact ⟨∅, by simp, by simp, by simp, by simp⟩
  | succ k ih =>
      intro S hS
      have hcS : c ≤ S.card := by
        rw [hS, add_one_mul]
        exact Nat.le_add_left c (k * c)
      obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hcS
      have hrest : (S \ T).card = k * c := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hTS, hS, hTcard,
          add_one_mul, Nat.add_sub_cancel]
      obtain ⟨F, hFcard, hFsub, hFdisj, hFcover⟩ := ih (S \ T) hrest
      refine ⟨insert T F, ?_, ?_, ?_, ?_⟩
      · intro B hB
        rcases Finset.mem_insert.mp hB with rfl | hB
        · exact hTcard
        · exact hFcard B hB
      · intro B hB
        rcases Finset.mem_insert.mp hB with rfl | hB
        · exact hTS
        · exact (hFsub B hB).trans Finset.sdiff_subset
      · intro B₁ B₂ hB₁ hB₂ hne
        rcases Finset.mem_insert.mp hB₁ with h₁ | h₁ <;>
          rcases Finset.mem_insert.mp hB₂ with h₂ | h₂
        · exact absurd (h₁.trans h₂.symm) hne
        · rw [h₁]; exact Finset.disjoint_sdiff.mono_right (hFsub _ h₂)
        · rw [h₂]; exact (Finset.disjoint_sdiff.mono_right (hFsub _ h₁)).symm
        · exact hFdisj _ _ h₁ h₂ hne
      · intro x hx
        by_cases hxT : x ∈ T
        · exact ⟨T, Finset.mem_insert_self _ _, hxT⟩
        · obtain ⟨B, hBF, hxB⟩ := hFcover x (Finset.mem_sdiff.mpr ⟨hx, hxT⟩)
          exact ⟨B, Finset.mem_insert_of_mem hBF, hxB⟩

/-- **Two-size chop.**  A finset of cardinality `a * m + b * (m + 1)` splits
    into pairwise disjoint covering blocks of sizes `m` or `m + 1`: carve off
    a subset of cardinality `a * m`, chop it uniformly into `m`-blocks, and
    chop the complement uniformly into `(m + 1)`-blocks. -/
theorem exists_two_size_blocks (m a b : ℕ) (S : Finset V)
    (hS : S.card = a * m + b * (m + 1)) :
    ∃ F : Finset (Finset V),
      (∀ B ∈ F, B.card = m ∨ B.card = m + 1) ∧
      (∀ B ∈ F, B ⊆ S) ∧
      (∀ B₁ B₂ : Finset V, B₁ ∈ F → B₂ ∈ F → B₁ ≠ B₂ → Disjoint B₁ B₂) ∧
      (∀ x ∈ S, ∃ B ∈ F, x ∈ B) := by
  obtain ⟨S₁, hS₁S, hS₁card⟩ := Finset.exists_subset_card_eq
    (n := a * m) (hS ▸ Nat.le_add_right _ _)
  have hS₂card : (S \ S₁).card = b * (m + 1) := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hS₁S, hS, hS₁card,
      Nat.add_sub_cancel_left]
  obtain ⟨F₁, hF₁card, hF₁sub, hF₁disj, hF₁cover⟩ :=
    exists_uniform_blocks m a S₁ hS₁card
  obtain ⟨F₂, hF₂card, hF₂sub, hF₂disj, hF₂cover⟩ :=
    exists_uniform_blocks (m + 1) b (S \ S₁) hS₂card
  refine ⟨F₁ ∪ F₂, ?_, ?_, ?_, ?_⟩
  · intro B hB
    rcases Finset.mem_union.mp hB with hB | hB
    · exact Or.inl (hF₁card B hB)
    · exact Or.inr (hF₂card B hB)
  · intro B hB
    rcases Finset.mem_union.mp hB with hB | hB
    · exact (hF₁sub B hB).trans hS₁S
    · exact (hF₂sub B hB).trans Finset.sdiff_subset
  · intro B₁ B₂ hB₁ hB₂ hne
    rcases Finset.mem_union.mp hB₁ with h₁ | h₁ <;>
      rcases Finset.mem_union.mp hB₂ with h₂ | h₂
    · exact hF₁disj _ _ h₁ h₂ hne
    · exact Finset.disjoint_sdiff.mono (hF₁sub _ h₁) (hF₂sub _ h₂)
    · exact (Finset.disjoint_sdiff.mono (hF₁sub _ h₂) (hF₂sub _ h₁)).symm
    · exact hF₂disj _ _ h₁ h₂ hne
  · intro x hx
    by_cases hx₁ : x ∈ S₁
    · obtain ⟨B, hB, hxB⟩ := hF₁cover x hx₁
      exact ⟨B, Finset.mem_union_left _ hB, hxB⟩
    · obtain ⟨B, hB, hxB⟩ := hF₂cover x (Finset.mem_sdiff.mpr ⟨hx, hx₁⟩)
      exact ⟨B, Finset.mem_union_right _ hB, hxB⟩

/-- **Two-size decomposition.**  Every `n` with `m * m ≤ n + 1` (and `0 < m`)
    is `a * m + b * (m + 1)`: write `n = qm + r` with `r < m`; the size bound
    forces `r ≤ q` (otherwise `n = qm + r ≤ (r-1)m + r = r(m+1) - m ≤
    (m-1)(m+1) - m = m² - 1 - m < n`, absurd), so `n = (q-r)m + r(m+1)`. -/
theorem exists_two_size_decomposition (m n : ℕ) (hm : 0 < m)
    (hn : m * m ≤ n + 1) :
    ∃ a b : ℕ, n = a * m + b * (m + 1) := by
  have hdm : m * (n / m) + n % m = n := Nat.div_add_mod n m
  have hr : n % m < m := Nat.mod_lt _ hm
  have hq : n % m ≤ n / m := by
    by_contra hcon
    have h1 : n / m + 1 ≤ n % m := by omega
    have h2 : m * (n / m) + m ≤ m * (n % m) := by
      calc m * (n / m) + m = m * (n / m + 1) := by ring
        _ ≤ m * (n % m) := Nat.mul_le_mul le_rfl h1
    have h3 : m * (n % m) + m ≤ m * m := by
      have h4 : n % m + 1 ≤ m := hr
      calc m * (n % m) + m = m * (n % m + 1) := by ring
        _ ≤ m * m := Nat.mul_le_mul le_rfl h4
    linarith
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hq
  refine ⟨d, n % m, ?_⟩
  calc n = m * (n / m) + n % m := hdm.symm
    _ = m * (n % m + d) + n % m := by rw [← hd]
    _ = d * m + n % m * (m + 1) := by ring

/-- **Equitable block partition of one large set.**  Any finset with
    `m * m ≤ card + 1` splits into pairwise disjoint covering blocks whose
    sizes all lie in `{m, m + 1}`. -/
theorem exists_equitable_blocks (m : ℕ) (hm : 0 < m) (S : Finset V)
    (hsize : m * m ≤ S.card + 1) :
    ∃ F : Finset (Finset V),
      (∀ B ∈ F, B.card = m ∨ B.card = m + 1) ∧
      (∀ B ∈ F, B ⊆ S) ∧
      (∀ B₁ B₂ : Finset V, B₁ ∈ F → B₂ ∈ F → B₁ ≠ B₂ → Disjoint B₁ B₂) ∧
      (∀ x ∈ S, ∃ B ∈ F, x ∈ B) := by
  obtain ⟨a, b, hab⟩ := exists_two_size_decomposition m S.card hm hsize
  exact exists_two_size_blocks m a b S hab

-- ═══════════════════════════════════════════════════════════════════
-- PART II: THE GLOBAL EQUITABLE REFINEMENT
-- ═══════════════════════════════════════════════════════════════════

/-- **Globally equitable refinement of a disjoint family.**  A pairwise
    disjoint family whose parts all satisfy `m * m ≤ card + 1` admits a
    refinement into blocks of sizes `m`/`m + 1` — pairwise disjoint, each
    block inside a parent, covering every vertex any parent covers.  Because
    ALL block sizes lie in `{m, m + 1}`, equitability holds globally across
    parents, which is exactly what the S21 invariant demands. -/
theorem exists_equitable_refinement (m : ℕ) (hm : 0 < m) :
    ∀ parts : Finset (Finset V),
      (∀ P Q : Finset V, P ∈ parts → Q ∈ parts → P ≠ Q → Disjoint P Q) →
      (∀ P ∈ parts, m * m ≤ P.card + 1) →
      ∃ q : Finset (Finset V),
        (∀ B ∈ q, B.card = m ∨ B.card = m + 1) ∧
        (∀ B ∈ q, ∃ P ∈ parts, B ⊆ P) ∧
        (∀ B₁ B₂ : Finset V, B₁ ∈ q → B₂ ∈ q → B₁ ≠ B₂ → Disjoint B₁ B₂) ∧
        (∀ (v : V) (P : Finset V), P ∈ parts → v ∈ P → ∃ B ∈ q, v ∈ B) := by
  intro parts
  induction parts using Finset.induction_on with
  | empty =>
      intro _ _
      exact ⟨∅, by simp, by simp, by simp, by simp⟩
  | @insert P parts' hP ih =>
      intro hdisj hsize
      obtain ⟨q', hq'card, hq'ref, hq'disj, hq'cover⟩ := ih
        (fun P₁ Q₁ h₁ h₂ hne =>
          hdisj _ _ (Finset.mem_insert_of_mem h₁) (Finset.mem_insert_of_mem h₂) hne)
        (fun P₁ h₁ => hsize _ (Finset.mem_insert_of_mem h₁))
      obtain ⟨F, hFcard, hFsub, hFdisj, hFcover⟩ :=
        exists_equitable_blocks m hm P (hsize P (Finset.mem_insert_self _ _))
      have hFdisjq' : ∀ B₁ B₂ : Finset V, B₁ ∈ F → B₂ ∈ q' → Disjoint B₁ B₂ := by
        intro B₁ B₂ h₁ h₂
        obtain ⟨Q, hQ, hB₂Q⟩ := hq'ref B₂ h₂
        have hPQ : P ≠ Q := by
          rintro rfl; exact hP hQ
        exact (hdisj P Q (Finset.mem_insert_self _ _)
          (Finset.mem_insert_of_mem hQ) hPQ).mono (hFsub _ h₁) hB₂Q
      refine ⟨F ∪ q', ?_, ?_, ?_, ?_⟩
      · intro B hB
        rcases Finset.mem_union.mp hB with hB | hB
        · exact hFcard B hB
        · exact hq'card B hB
      · intro B hB
        rcases Finset.mem_union.mp hB with hB | hB
        · exact ⟨P, Finset.mem_insert_self _ _, hFsub B hB⟩
        · obtain ⟨Q, hQ, hBQ⟩ := hq'ref B hB
          exact ⟨Q, Finset.mem_insert_of_mem hQ, hBQ⟩
      · intro B₁ B₂ hB₁ hB₂ hne
        rcases Finset.mem_union.mp hB₁ with h₁ | h₁ <;>
          rcases Finset.mem_union.mp hB₂ with h₂ | h₂
        · exact hFdisj _ _ h₁ h₂ hne
        · exact hFdisjq' _ _ h₁ h₂
        · exact (hFdisjq' _ _ h₂ h₁).symm
        · exact hq'disj _ _ h₁ h₂ hne
      · intro v P₀ hP₀ hvP₀
        rcases Finset.mem_insert.mp hP₀ with rfl | hP₀
        · obtain ⟨B, hB, hvB⟩ := hFcover v hvP₀
          exact ⟨B, Finset.mem_union_left _ hB, hvB⟩
        · obtain ⟨B, hB, hvB⟩ := hq'cover v P₀ hP₀ hvP₀
          exact ⟨B, Finset.mem_union_right _ hB, hvB⟩

-- ═══════════════════════════════════════════════════════════════════
-- PART III: THE SEED
-- ═══════════════════════════════════════════════════════════════════

/-- **Seed existence.**  A covering, pairwise disjoint coarse partition whose
    parts all satisfy `m * m ≤ card + 1` admits a fine partition satisfying
    ALL FIVE seed obligations of the S21 capstone
    (`exists_afksTwoLevel_of_maintained_oracle`): covering, pairwise
    disjoint, refining `Vparts`, globally equitable
    (`(B₁.card : ℤ) - B₂.card ≤ 1`), and mass floor `(m : ℚ) ≤ B.card`. -/
theorem exists_equitable_seed (m : ℕ) (hm : 0 < m)
    (Vparts : Finset (Finset V))
    (hVcover : ∀ v : V, ∃ P ∈ Vparts, v ∈ P)
    (hVdisj : ∀ P Q : Finset V, P ∈ Vparts → Q ∈ Vparts → P ≠ Q → Disjoint P Q)
    (hVsize : ∀ P ∈ Vparts, m * m ≤ P.card + 1) :
    ∃ q₀ : Finset (Finset V),
      (∀ v : V, ∃ B ∈ q₀, v ∈ B) ∧
      (∀ B₁ B₂ : Finset V, B₁ ∈ q₀ → B₂ ∈ q₀ → B₁ ≠ B₂ → Disjoint B₁ B₂) ∧
      IsRefinement q₀ Vparts ∧
      (∀ B₁ B₂ : Finset V, B₁ ∈ q₀ → B₂ ∈ q₀ → (B₁.card : ℤ) - B₂.card ≤ 1) ∧
      (∀ B ∈ q₀, (m : ℚ) ≤ B.card) := by
  obtain ⟨q, hqcard, hqref, hqdisj, hqcover⟩ :=
    exists_equitable_refinement m hm Vparts hVdisj hVsize
  refine ⟨q, ?_, hqdisj, ?_, ?_, ?_⟩
  · intro v
    obtain ⟨P, hP, hvP⟩ := hVcover v
    exact hqcover v P hP hvP
  · intro B hB
    exact hqref B hB
  · intro B₁ B₂ h₁ h₂
    rcases hqcard B₁ h₁ with h | h <;> rcases hqcard B₂ h₂ with h' | h' <;>
      (rw [h, h']; push_cast; omega)
  · intro B hB
    rcases hqcard B hB with h | h <;> (rw [h]; push_cast; linarith)

-- ═══════════════════════════════════════════════════════════════════
-- PART IV: THE CAPSTONE WITHOUT SEED HYPOTHESES
-- ═══════════════════════════════════════════════════════════════════

/-- **The two-level AFKS conclusion from large coarse parts.**  The S21
    capstone with its five seed hypotheses replaced by the size condition
    `m * m ≤ P.card + 1` on the coarse parts: an `ε`-regular, covering,
    pairwise disjoint coarse partition with large parts, plus the maintained
    step oracle at integer scale `m`, yield the full two-level conclusion.
    The seed is manufactured by `exists_equitable_seed`. -/
theorem exists_afksTwoLevel_of_large_parts [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℚ) (E : ℕ → ℚ) (m : ℕ) (hm : 0 < m) (δ : ℚ) (hδ : 0 < δ)
    (Vparts : Finset (Finset V))
    (hcoarse : IsRegularPartition G ε Vparts)
    (hVcover : ∀ v : V, ∃ P ∈ Vparts, v ∈ P)
    (hVdisj : ∀ P Q : Finset V, P ∈ Vparts → Q ∈ Vparts → P ≠ Q → Disjoint P Q)
    (hVsize : ∀ P ∈ Vparts, m * m ≤ P.card + 1)
    (horacle : ∀ q : Finset (Finset V),
      (∀ v : V, ∃ P ∈ q, v ∈ P) →
      (∀ P Q : Finset V, P ∈ q → Q ∈ q → P ≠ Q → Disjoint P Q) →
      IsRefinement q Vparts →
      (∀ P Q : Finset V, P ∈ q → Q ∈ q → (P.card : ℤ) - Q.card ≤ 1) →
      (∀ P ∈ q, (m : ℚ) ≤ (P.card : ℚ)) →
      ¬ IsAFKSFineRegular G ε (E Vparts.card) q →
      ∃ q' : Finset (Finset V),
        (∀ v : V, ∃ P ∈ q', v ∈ P) ∧
        (∀ P Q : Finset V, P ∈ q' → Q ∈ q' → P ≠ Q → Disjoint P Q) ∧
        IsRefinement q' Vparts ∧
        (∀ P Q : Finset V, P ∈ q' → Q ∈ q' → (P.card : ℤ) - Q.card ≤ 1) ∧
        (∀ P ∈ q', (m : ℚ) ≤ (P.card : ℚ)) ∧
        partitionEnergy G q + δ ≤ partitionEnergy G q') :
    ∃ Wparts : Finset (Finset V), IsAFKSTwoLevel G ε E Vparts Wparts := by
  obtain ⟨q₀, hcover₀, hdisj₀, href₀, hequit₀, hmass₀⟩ :=
    exists_equitable_seed m hm Vparts hVcover hVdisj hVsize
  exact exists_afksTwoLevel_of_maintained_oracle G ε E (m : ℚ) δ hδ Vparts q₀
    hcoarse hcover₀ hdisj₀ href₀ hequit₀ hmass₀ horacle

/-- **The two-level AFKS conclusion at unit scale — no seed hypothesis at
    all.**  At `m = 1` the size condition `1 ≤ P.card + 1` is vacuous, so any
    `ε`-regular covering disjoint coarse partition plus a maintained oracle
    at mass scale `1` already yields the two-level conclusion.  This makes
    explicit that seed existence was never an obstruction at unit scale: the
    singleton refinement is a valid seed for every coarse partition. -/
theorem exists_afksTwoLevel_of_maintained_oracle_unit [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℚ) (E : ℕ → ℚ) (δ : ℚ) (hδ : 0 < δ)
    (Vparts : Finset (Finset V))
    (hcoarse : IsRegularPartition G ε Vparts)
    (hVcover : ∀ v : V, ∃ P ∈ Vparts, v ∈ P)
    (hVdisj : ∀ P Q : Finset V, P ∈ Vparts → Q ∈ Vparts → P ≠ Q → Disjoint P Q)
    (horacle : ∀ q : Finset (Finset V),
      (∀ v : V, ∃ P ∈ q, v ∈ P) →
      (∀ P Q : Finset V, P ∈ q → Q ∈ q → P ≠ Q → Disjoint P Q) →
      IsRefinement q Vparts →
      (∀ P Q : Finset V, P ∈ q → Q ∈ q → (P.card : ℤ) - Q.card ≤ 1) →
      (∀ P ∈ q, (1 : ℚ) ≤ (P.card : ℚ)) →
      ¬ IsAFKSFineRegular G ε (E Vparts.card) q →
      ∃ q' : Finset (Finset V),
        (∀ v : V, ∃ P ∈ q', v ∈ P) ∧
        (∀ P Q : Finset V, P ∈ q' → Q ∈ q' → P ≠ Q → Disjoint P Q) ∧
        IsRefinement q' Vparts ∧
        (∀ P Q : Finset V, P ∈ q' → Q ∈ q' → (P.card : ℤ) - Q.card ≤ 1) ∧
        (∀ P ∈ q', (1 : ℚ) ≤ (P.card : ℚ)) ∧
        partitionEnergy G q + δ ≤ partitionEnergy G q') :
    ∃ Wparts : Finset (Finset V), IsAFKSTwoLevel G ε E Vparts Wparts := by
  refine exists_afksTwoLevel_of_large_parts G ε E 1 one_pos δ hδ Vparts
    hcoarse hVcover hVdisj (fun P _ => by omega) ?_
  simpa only [Nat.cast_one] using horacle

end Szemeredi.RegularityOQ04Seed
