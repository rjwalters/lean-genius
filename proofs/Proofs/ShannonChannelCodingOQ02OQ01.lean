/-
  Fano's Inequality from Conditional Entropy Machinery

  Open Question 02-OQ-01: Prove Fano's inequality using the conditional entropy
  definitions from the Shannon information theory framework.

  This file bridges:
    - `FanoInequality.fano_theorem` (OQ-03): H(X|Y) ≤ h(P_e) + P_e·log(|X|-1)
      using a self-contained definition of conditionalEntropy
    - `InformationTheory.conditionalEntropy` (ShannonEntropy.lean): the project's
      standard conditional entropy definition

  Key result: the two definitions of conditionalEntropy agree (definitional equality),
  so `fano_theorem` implies the `fano_inequality` axiom in ShannonChannelCoding.lean.

  Status:
  - [PROVED] Definition compatibility: FanoInequality.conditionalEntropy =
    InformationTheory.conditionalEntropy (definitionally equal)
  - [PROVED] Standalone: OQ-03 proves Fano completely without ShannonEntropy.lean
  - [PROVED] fano_trivial_singleton (1-element edge case, Unit α)
  - [PROVED] fano_from_oq03_std: bridge using InformationTheory.conditionalEntropy
    (unblocked by PR #16334 which proved strong_subadditivity).
  - [PROVED] fano_singleton_card_one: |α| = 1 case in standard form
  - [PROVED] fano_inequality_proved: full dispatcher discharging the
    `fano_inequality` axiom signature in ShannonChannelCoding.lean
    (no cardinality hypothesis).

  Axioms: 0
  Sorries: 0
-/
import Mathlib
import Proofs.ShannonChannelCodingOQ03
import Proofs.ShannonChannelCodingOQ04
import Proofs.ShannonEntropy

open Real Finset InformationTheory InformationTheory.BinaryEntropy
open FanoInequality

namespace FanoFromConditionalEntropy

-- ============================================================
-- Section 1: Definition Compatibility
-- ============================================================

/-- The conditional entropy definitions in OQ-03 and ShannonEntropy.lean are
    definitionally equal. Both use:
      H(X|Y) = -∑_{x,y} pXY(x,y) · log(pXY(x,y) / P(Y=y))
    with the convention 0 · log 0 = 0 (via Real.log 0 = 0). -/
theorem conditional_entropy_defs_agree
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (pXY : α × β → ℝ) :
    FanoInequality.conditionalEntropy pXY =
    -(∑ x : α, ∑ y : β,
      if pXY (x, y) = 0 then 0
      else pXY (x, y) * Real.log (pXY (x, y) / (∑ x' : α, pXY (x', y)))) := by
  rfl

-- ============================================================
-- Section 2: Fano's Inequality — Standalone Version (from OQ-03)
-- ============================================================

/-- **Fano's Inequality** (via OQ-03 architecture):
    For |α| ≥ 2, any joint distribution pXY on α × β satisfies:
      H(X|Y) ≤ h(P_e) + P_e · log(|X| - 1)

    This is a consequence of `fano_theorem` from OQ-03, instantiated directly.
    The definition of conditionalEntropy used here matches the project standard. -/
theorem fano_from_oq03 {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [Nonempty α]
    (hn : 1 < Fintype.card α)
    (pXY : α × β → ℝ) (hp : ∀ x, 0 ≤ pXY x) (hsum : ∑ x, pXY x = 1) :
    let P_e := 1 - ∑ y : β, ∑ x : α, pXY (x, y) ^ 2 / (∑ x' : α, pXY (x', y))
    FanoInequality.conditionalEntropy pXY ≤
      h P_e + P_e * Real.log ((Fintype.card α : ℝ) - 1) :=
  fano_theorem hn pXY hp hsum

-- ============================================================
-- Section 3: Axiom Reduction (Blocked by ShannonEntropy.lean)
-- ============================================================

/-
### Connection to ShannonChannelCoding.lean

The main goal is to replace the axiom `fano_inequality` in ShannonChannelCoding.lean:

```lean
axiom fano_inequality ... :
    conditionalEntropy pXY ≤ h P_e + P_e * log (|X| - 1)
```

where `conditionalEntropy` is `InformationTheory.conditionalEntropy` from ShannonEntropy.lean.

**Compatibility**: Since `FanoInequality.conditionalEntropy` and
`InformationTheory.conditionalEntropy` are definitionally equal (same formula),
`fano_from_oq03` above directly implies `fano_inequality`.

**Blocker**: ShannonEntropy.lean has a pre-existing compilation error in
`strong_subadditivity` (line 811: `linarith [h_cmi]` fails). This prevents importing
the file and accessing `InformationTheory.conditionalEntropy`.

**Root cause of line 811 failure**: After the `simp_rw [hXY]`, `simp_rw [hYZ]`,
`simp_rw [hY]`, `simp_rw [hterm]` rewrites, the YZ marginal sum (from hYZ) has
summation order `∑ y ∑ z ∑ x`, while the corresponding term from hterm has order
`∑ x ∑ y ∑ z`. Lean's `linarith` cannot see these as equal (they're definitionally
but not syntactically equal), preventing cancellation.

**Fix needed**: Before `linarith [h_cmi]`, add a sum commutativity rewrite:
```lean
rw [show ∑ y : β, ∑ z : γ, ∑ x : α, f x y z = ∑ x : α, ∑ y : β, ∑ z : γ, f x y z from
  by rw [Finset.sum_comm]; simp_rw [Finset.sum_comm (s := Finset.univ)]]
```
This normalizes the YZ sum order to match, allowing `linarith` to see the cancellation.
-/

/-
**Axiom reduction (BLOCKED — documentation only)**:

The `fano_inequality` axiom in ShannonChannelCoding.lean would follow from
`fano_from_oq03` above by definitional equality of the two conditionalEntropy
definitions. The actual replacement in ShannonChannelCoding.lean would be:

```
have := fano_from_oq03 hn pXY hp hsum
exact this  -- or with a definitional equality coercion
```

This integration is currently blocked because ShannonEntropy.lean's
`strong_subadditivity` (line 811) fails to build. Until that's fixed, the
`fano_inequality` axiom in ShannonChannelCoding.lean stands.

**No `axiom : False` placeholder is declared here** — `axiom blocker : False`
is logically unsound (anything follows from False), so even an unused
declaration is a footgun for future authors who might invoke it. We leave
this as a comment instead.
-/

-- ============================================================
-- Section 4: Key Properties Used
-- ============================================================

/-- Fano's inequality holds for the 1-element case trivially:
    H(X|Y) = 0 = h(0) + 0 · log(0) (since |X| = 1 means X is deterministic). -/
theorem fano_trivial_singleton {β : Type*} [Fintype β] [DecidableEq β]
    {pXY : Unit × β → ℝ} (hp : ∀ x, 0 ≤ pXY x) (hsum : ∑ x, pXY x = 1) :
    FanoInequality.conditionalEntropy pXY ≤
      h (1 - ∑ y : β, ∑ x : Unit, pXY (x, y) ^ 2 / (∑ x' : Unit, pXY (x', y))) +
      (1 - ∑ y : β, ∑ x : Unit, pXY (x, y) ^ 2 / (∑ x' : Unit, pXY (x', y))) *
      Real.log ((Fintype.card Unit : ℝ) - 1) := by
  -- For |X| = 1: H(X|Y) = 0 and (|X|-1) = 0 so both sides equal 0.
  -- RHS: card Unit = 1, so log(1-1) = log 0 = 0, and the whole expression is h(p) for
  -- some p, but the coefficient is (|X|-1)=0, giving h(p)+0=h(p)≥0.
  -- LHS: conditionalEntropy pXY = 0 since the only x is () and pXY((),y)/pXY((),y)=1,
  -- so each term pXY((),y)*log(1) = 0.
  -- The simp-level proof requires careful handling of Fintype.sum_unique for Unit sums.
  -- Step 1: (Fintype.card Unit : ℝ) - 1 = 0, so log(0) = 0, second term vanishes
  have hcard : (Fintype.card Unit : ℝ) - 1 = 0 := by simp [Fintype.card_unit]
  rw [hcard, Real.log_zero, mul_zero, add_zero]
  -- Step 2: Simplify Unit sums: ∑ x : Unit, f x = f ()
  simp only [Finset.univ_unique, Finset.sum_singleton]
  -- Step 3: pXY((),y)^2 / pXY((),y) = pXY((),y) (when nonzero, 0 when zero)
  -- So P_e = 1 - ∑ y, pXY((),y) = 1 - 1 = 0 (from hsum)
  have hpe_zero : 1 - ∑ y : β, pXY ((), y) ^ 2 / pXY ((), y) = 0 := by
    have : ∀ y, pXY ((), y) ^ 2 / pXY ((), y) = pXY ((), y) := fun y => by
      by_cases h : pXY ((), y) = 0
      · simp [h]
      · rw [sq, mul_div_cancel_left₀ _ h]
    simp_rw [this]
    have hsum' : ∑ y : β, pXY ((), y) = 1 := by
      have h := hsum
      rw [Fintype.sum_prod_type] at h
      simpa using h
    linarith
  rw [hpe_zero]
  -- Step 4: h(0) ≥ 0 and conditionalEntropy = 0 (Unit X), so 0 ≤ h(0) = 0
  -- h(0) = -0·log 0 - 1·log 1 = 0 (binary entropy)
  -- conditionalEntropy: for each y, pXY((),y)/pXY((),y) = 1, log 1 = 0
  unfold FanoInequality.conditionalEntropy
  simp only [Finset.univ_unique, Finset.sum_singleton]
  have hterm : ∀ y, (if pXY ((), y) = 0 then (0:ℝ)
      else pXY ((), y) * Real.log (pXY ((), y) / pXY ((), y))) = 0 := fun y => by
    by_cases h0 : pXY ((), y) = 0
    · simp [h0]
    · simp only [h0, ↓reduceIte]
      rw [div_self h0, Real.log_one, mul_zero]
  simp_rw [hterm]
  simp only [Finset.sum_const_zero, neg_zero]
  exact h_nonneg (le_refl 0) zero_le_one

-- ============================================================
-- Section 5: Discharge of the `fano_inequality` axiom
-- ============================================================
--
-- The blocker cited in Sections 3-4 (ShannonEntropy.lean strong_subadditivity)
-- was resolved by PR #16334. With `Proofs.ShannonEntropy` now imported, we
-- can produce a theorem whose statement uses `InformationTheory.conditionalEntropy`
-- — i.e., a literal match for the `fano_inequality` axiom in the parent
-- `ShannonChannelCoding.lean`. The actual replacement of the axiom is a
-- follow-up change in that file (small ~5-line edit, deferred to avoid
-- ballooning this PR).

/-- **Bridge**: Fano's inequality stated using `InformationTheory.conditionalEntropy`
    (the project-standard definition from `ShannonEntropy.lean`).

    By `conditional_entropy_defs_agree` the two definitions are definitionally
    equal (both unfold to the same expression), so `fano_from_oq03` produces
    a proof of this signature directly via `:=`. -/
theorem fano_from_oq03_std {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [Nonempty α]
    (hn : 1 < Fintype.card α)
    (pXY : α × β → ℝ) (hp : ∀ x, 0 ≤ pXY x) (hsum : ∑ x, pXY x = 1) :
    let P_e := 1 - ∑ y : β, ∑ x : α, pXY (x, y) ^ 2 / (∑ x' : α, pXY (x', y))
    InformationTheory.conditionalEntropy pXY ≤
      h P_e + P_e * Real.log ((Fintype.card α : ℝ) - 1) :=
  fano_from_oq03 hn pXY hp hsum

/-- Fano's inequality for any 1-element domain (`Fintype.card α = 1`).
    Both sides simplify to 0:
    * `H(X|Y) = 0` (X is deterministic, so each ratio inside the log is 1)
    * `P_e = 0` (singleton α means the squared-marginal sum equals the total mass = 1)
    * `log((card α : ℝ) - 1) = log 0 = 0` annihilates the second RHS term
    * `h 0 = 0`. -/
theorem fano_singleton_card_one {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [Nonempty α]
    (hcard : Fintype.card α = 1)
    (pXY : α × β → ℝ) (hp : ∀ x, 0 ≤ pXY x) (hsum : ∑ x, pXY x = 1) :
    let P_e := 1 - ∑ y : β, ∑ x : α, pXY (x, y) ^ 2 / (∑ x' : α, pXY (x', y))
    InformationTheory.conditionalEntropy pXY ≤
      h P_e + P_e * Real.log ((Fintype.card α : ℝ) - 1) := by
  intro P_e
  -- Subsingleton α from card = 1
  haveI hsub : Subsingleton α :=
    Fintype.card_le_one_iff_subsingleton.mp hcard.le
  obtain ⟨x₀⟩ := ‹Nonempty α›
  -- Singleton collapse: ∑ x : α, f x = f x₀
  have hcollapse : ∀ (f : α → ℝ), ∑ x : α, f x = f x₀ := fun f => by
    refine Finset.sum_eq_single x₀ ?_ ?_
    · intros b _ hb; exact absurd (Subsingleton.elim b x₀) hb
    · intro hmem; exact absurd (Finset.mem_univ x₀) hmem
  -- log((card α : ℝ) - 1) = log 0 = 0
  have hRHS2 : ((Fintype.card α : ℝ) - 1) = 0 := by rw [hcard]; norm_num
  rw [hRHS2, Real.log_zero, mul_zero, add_zero]
  -- ∑ x' pXY (x', y) = pXY (x₀, y)
  have hcol_y : ∀ y : β, ∑ x' : α, pXY (x', y) = pXY (x₀, y) :=
    fun y => hcollapse (fun x' => pXY (x', y))
  -- LHS: InformationTheory.conditionalEntropy pXY = 0
  have hLHS : InformationTheory.conditionalEntropy pXY = 0 := by
    unfold InformationTheory.conditionalEntropy
    have hterm : ∀ x y, (if pXY (x, y) = 0 then (0 : ℝ)
        else pXY (x, y) * Real.log (pXY (x, y) / (∑ x' : α, pXY (x', y)))) = 0 := by
      intro x y
      by_cases h0 : pXY (x, y) = 0
      · simp [h0]
      · -- Subsingleton: x = x₀, so the ratio is 1
        have hxx₀ : x = x₀ := Subsingleton.elim x x₀
        simp only [h0, ↓reduceIte, hcol_y]
        rw [hxx₀] at h0 ⊢
        rw [div_self h0, Real.log_one, mul_zero]
    simp_rw [hterm]
    simp
  rw [hLHS]
  -- P_e = 0
  have hPe : P_e = 0 := by
    show 1 - ∑ y : β, ∑ x : α, pXY (x, y) ^ 2 / (∑ x' : α, pXY (x', y)) = 0
    have hinner : ∀ y, ∑ x : α, pXY (x, y) ^ 2 / (∑ x' : α, pXY (x', y))
        = pXY (x₀, y) := by
      intro y
      rw [hcollapse (fun x => pXY (x, y) ^ 2 / (∑ x' : α, pXY (x', y))), hcol_y]
      by_cases h0 : pXY (x₀, y) = 0
      · rw [h0]; simp
      · rw [sq, mul_div_cancel_left₀ _ h0]
    simp_rw [hinner]
    -- ∑ y pXY (x₀, y) = 1 from hsum
    have hsum1 : ∑ y : β, pXY (x₀, y) = 1 := by
      have hexpand : ∑ p : α × β, pXY p = ∑ x : α, ∑ y : β, pXY (x, y) :=
        Fintype.sum_prod_type _
      rw [hexpand, hcollapse (fun x => ∑ y : β, pXY (x, y))] at hsum
      exact hsum
    linarith
  rw [hPe]
  -- final: 0 ≤ h 0, by h_nonneg on the unit interval
  exact h_nonneg (le_refl 0) zero_le_one

/-- **Fano's inequality, fully discharged**: matches the signature of the
    `fano_inequality` axiom in `ShannonChannelCoding.lean` exactly (no
    cardinality hypothesis). Case-splits on `Fintype.card α`:
    * `card = 0` → contradiction with `hsum = 1` (empty sum is 0)
    * `card = 1` → `fano_singleton_card_one`
    * `card ≥ 2` → `fano_from_oq03_std`

    Replacing the axiom in `ShannonChannelCoding.lean` is a follow-up
    `theorem fano_inequality := fano_inequality_proved` (deferred to keep
    this PR self-contained and reduce conflict risk). -/
theorem fano_inequality_proved {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (pXY : α × β → ℝ) (hp : ∀ x, 0 ≤ pXY x) (hsum : ∑ x, pXY x = 1) :
    let P_e := 1 - ∑ y : β, ∑ x : α, pXY (x, y) ^ 2 / (∑ x' : α, pXY (x', y))
    InformationTheory.conditionalEntropy pXY ≤
      h P_e + P_e * Real.log ((Fintype.card α : ℝ) - 1) := by
  -- Nonempty α: otherwise the sum is 0, contradicting hsum = 1
  haveI : Nonempty α := by
    rcases (Fintype.card α).eq_zero_or_pos with h0 | hpos
    · exfalso
      haveI : IsEmpty α := Fintype.card_eq_zero_iff.mp h0
      haveI : IsEmpty (α × β) := ⟨fun ⟨a, _⟩ => ‹IsEmpty α›.elim a⟩
      have hsum0 : ∑ x : α × β, pXY x = 0 := by
        rw [Finset.univ_eq_empty]; exact Finset.sum_empty
      linarith
    · exact Fintype.card_pos_iff.mp hpos
  -- Case on Fintype.card α
  rcases Nat.lt_or_ge (Fintype.card α) 2 with hlt | hge
  · -- card < 2 means card = 1 (card ≥ 1 from Nonempty)
    have hpos : 0 < Fintype.card α := Fintype.card_pos
    have hcard : Fintype.card α = 1 := by omega
    exact fano_singleton_card_one hcard pXY hp hsum
  · -- card ≥ 2
    exact fano_from_oq03_std hge pXY hp hsum

end FanoFromConditionalEntropy
