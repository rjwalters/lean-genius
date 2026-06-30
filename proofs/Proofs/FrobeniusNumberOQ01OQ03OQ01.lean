/-
  OQ-01-OQ-03-OQ-01: Type One ⟹ Symmetric — the converse, generator-agnostic
  (frobenius-number-oq-01-oq-03-oq-01)

  The parent `frobenius-number-oq-01-oq-03` proves, for the *specific* two-generator
  semigroup `⟨a, b⟩`, that it is **symmetric** and has **type one**
  (`pseudoFrobenius_setOf_eq : PF = {g}`).  Its docstring leaves open the converse:

  > *"Prove the converse: a numerical semigroup of type 1 (`|PF(S)| = 1`) is
  >  symmetric, completing the 'symmetric ⟺ type one' equivalence in a
  >  generator-agnostic setting."*

  This file supplies exactly that — and both directions — for an **arbitrary**
  numerical semigroup `S ⊆ ℕ` (closed under addition, containing `0`, with finite
  complement), with no reference to generators.  The headline is the classical
  Kunz / Gorenstein equivalence

  > `S` is symmetric  ⟺  `S` has type one  (`|PF(S)| = 1`).

  ## Statements (all generator-agnostic, `S : Set ℕ`)

  * `IsFrobeniusNumber S g` — `g` is the largest gap: `g ∉ S` and everything above
    `g` lies in `S`.  Proved **unique** (`isFrobeniusNumber_unique`) and **existent**
    for any proper numerical semigroup (`exists_isFrobeniusNumber`).
  * `IsSymmetric S g` — the gap/element duality `k ∈ S ↔ g - k ∉ S` on `0 ≤ k ≤ g`.
  * `IsPF S x` — `x` is pseudo-Frobenius: a gap all of whose translates by nonzero
    semigroup elements re-enter `S`.  `{x | IsPF S x}.ncard` is the **type**.

  ## Main results

  * `gap_dominated` — every gap is `⪯`-dominated by a pseudo-Frobenius number
    (the structural engine of the converse): the finite set of gaps `y ≥ x` with
    `y - x ∈ S` has a maximum, and that maximum is pseudo-Frobenius.
  * `isPF_setOf_eq_of_isSymmetric` — **symmetric ⟹ type one**: `{x | IsPF S x} = {g}`.
  * `isSymmetric_of_isPF_ncard_one` — **type one ⟹ symmetric** (the open converse):
    if `g` is the unique pseudo-Frobenius number then `S` is symmetric.
  * `isSymmetric_iff_isPF_ncard_one` — the full equivalence `IsSymmetric ↔ type = 1`.

  ## Subsumes the parent

  The two-generator semigroup `{n | Representable a b n}` is shown to be a numerical
  semigroup with Frobenius number `frobeniusNumber a b` (`representable_*`), so the
  general equivalence recovers the parent's symmetric/type-one results
  (`representable_type_one`) from a single source.

  ## Status: 0 sorries, 0 axioms (built on the verified parent chain).
-/
import Mathlib
import Proofs.FrobeniusNumber
import Proofs.FrobeniusNumberOQ01OQ03

namespace FrobeniusNumberOQ01OQ03OQ01

open scoped Classical

/-! ## Generator-agnostic numerical semigroups -/

/-- A **numerical semigroup**: a set of naturals containing `0`, closed under
addition, with finite (and nonempty) complement.  The last two conditions say the
gap set `ℕ \ S` is a nonempty finite set — exactly when a Frobenius number exists. -/
def IsNumericalSemigroup (S : Set ℕ) : Prop :=
  0 ∈ S ∧ (∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) ∧ {n | n ∉ S}.Finite ∧ (∃ n, n ∉ S)

/-- `g` is the **Frobenius number** of `S`: the largest gap.  Equivalently `g ∉ S`
and every `n > g` is in `S`. -/
def IsFrobeniusNumber (S : Set ℕ) (g : ℕ) : Prop :=
  g ∉ S ∧ ∀ n, g < n → n ∈ S

/-- `S` is **symmetric** with respect to its Frobenius number `g`: for every
`k ≤ g`, exactly one of `k`, `g - k` is representable. -/
def IsSymmetric (S : Set ℕ) (g : ℕ) : Prop :=
  ∀ k ≤ g, k ∈ S ↔ g - k ∉ S

/-- `x` is a **pseudo-Frobenius number** of `S`: a gap such that `x + s ∈ S` for
every nonzero `s ∈ S`.  The cardinality of `{x | IsPF S x}` is the **type** of `S`. -/
def IsPF (S : Set ℕ) (x : ℕ) : Prop :=
  x ∉ S ∧ ∀ s ∈ S, 0 < s → x + s ∈ S

/-! ## The Frobenius number: existence and uniqueness -/

/-- The Frobenius number, when it exists, is **unique**. -/
theorem isFrobeniusNumber_unique {S : Set ℕ} {g₁ g₂ : ℕ}
    (h₁ : IsFrobeniusNumber S g₁) (h₂ : IsFrobeniusNumber S g₂) : g₁ = g₂ := by
  rcases lt_trichotomy g₁ g₂ with h | h | h
  · exact absurd (h₁.2 g₂ h) h₂.1
  · exact h
  · exact absurd (h₂.2 g₁ h) h₁.1

/-- Every proper numerical semigroup **has** a Frobenius number: the maximum of the
nonempty finite gap set. -/
theorem exists_isFrobeniusNumber {S : Set ℕ} (hfin : {n | n ∉ S}.Finite)
    (hproper : ∃ n, n ∉ S) : ∃ g, IsFrobeniusNumber S g := by
  classical
  obtain ⟨n₀, hn₀⟩ := hproper
  have hne : hfin.toFinset.Nonempty := ⟨n₀, by rw [Set.Finite.mem_toFinset]; exact hn₀⟩
  refine ⟨hfin.toFinset.max' hne, ?_, ?_⟩
  · have := hfin.toFinset.max'_mem hne
    rwa [Set.Finite.mem_toFinset] at this
  · intro n hn
    by_contra hnS
    have hmem : n ∈ hfin.toFinset := by rw [Set.Finite.mem_toFinset]; exact hnS
    have := hfin.toFinset.le_max' n hmem
    omega

/-! ## Pseudo-Frobenius basics -/

/-- The Frobenius number is itself pseudo-Frobenius: it is a gap, and adding any
positive semigroup element lands strictly above `g`, hence back inside `S`. -/
theorem frobeniusNumber_isPF {S : Set ℕ} {g : ℕ} (hg : IsFrobeniusNumber S g) :
    IsPF S g :=
  ⟨hg.1, fun s _ hspos => hg.2 (g + s) (by omega)⟩

/-- Every pseudo-Frobenius number is `≤ g`: it is a gap, and nothing above `g` is a
gap. -/
theorem isPF_le_frobeniusNumber {S : Set ℕ} {g x : ℕ} (hg : IsFrobeniusNumber S g)
    (hx : IsPF S x) : x ≤ g := by
  by_contra h
  exact hx.1 (hg.2 x (by omega))

/-! ## The structural engine: every gap is dominated by a pseudo-Frobenius number -/

/-- **Domination lemma.**  For any gap `x`, the finite set of gaps `y ≥ x` with
`y - x ∈ S` has a maximum `m`, and `m` is pseudo-Frobenius.  Thus every gap sits
below some pseudo-Frobenius number in the order `u ⪯ v ⟺ v - u ∈ S`.  This is the
heart of the converse `type one ⟹ symmetric`. -/
theorem gap_dominated {S : Set ℕ} (h0 : 0 ∈ S)
    (hadd : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) (hfin : {n | n ∉ S}.Finite)
    {x : ℕ} (hx : x ∉ S) : ∃ m, IsPF S m ∧ x ≤ m ∧ m - x ∈ S := by
  classical
  -- `T` : gaps `y ≥ x` whose distance to `x` is in `S`.
  set T : Set ℕ := {y | y ∉ S ∧ x ≤ y ∧ y - x ∈ S} with hT
  have hTsub : T ⊆ {n | n ∉ S} := fun y hy => hy.1
  have hTfin : T.Finite := hfin.subset hTsub
  have hxT : x ∈ T := ⟨hx, le_rfl, by rw [Nat.sub_self]; exact h0⟩
  have hFne : hTfin.toFinset.Nonempty := ⟨x, by rw [Set.Finite.mem_toFinset]; exact hxT⟩
  -- Take the maximum `m` of `T`.
  set m : ℕ := hTfin.toFinset.max' hFne with hm
  have hmT : m ∈ T := by
    have := hTfin.toFinset.max'_mem hFne
    rwa [Set.Finite.mem_toFinset] at this
  obtain ⟨hm_notS, hxm, hmx_S⟩ := hmT
  have hmax : ∀ y ∈ T, y ≤ m := by
    intro y hy
    apply Finset.le_max'
    rw [Set.Finite.mem_toFinset]; exact hy
  refine ⟨m, ⟨hm_notS, ?_⟩, hxm, hmx_S⟩
  -- `m` is pseudo-Frobenius: any `m + s` (`s ∈ S`, `s > 0`) is in `S`, else it would
  -- be a strictly larger member of `T`.
  intro s hs hspos
  by_contra hms
  have hmsT : m + s ∈ T := by
    refine ⟨hms, by omega, ?_⟩
    have hsub : (m + s) - x = (m - x) + s := by omega
    rw [hsub]; exact hadd _ hmx_S _ hs
  have := hmax _ hmsT
  omega

/-! ## Direction 1: symmetric ⟹ type one -/

/-- **Symmetric ⟹ type one.**  If `S` is symmetric then its set of pseudo-Frobenius
numbers is the singleton `{g}`: any pseudo-Frobenius `x < g` would, by symmetry, have
`g - x ∈ S` positive, forcing `x + (g - x) = g ∈ S` — impossible. -/
theorem isPF_setOf_eq_of_isSymmetric {S : Set ℕ} {g : ℕ} (hg : IsFrobeniusNumber S g)
    (hsym : IsSymmetric S g) : {x | IsPF S x} = {g} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro hx
    rcases eq_or_lt_of_le (isPF_le_frobeniusNumber hg hx) with heq | hlt
    · exact heq
    · exfalso
      -- `x` is a gap, `x < g`, so by symmetry `g - x ∈ S`.
      have hgx : g - x ∈ S := by
        by_contra hgxnot
        exact hx.1 ((hsym x (le_of_lt hlt)).mpr hgxnot)
      have hpos : 0 < g - x := by omega
      have hmem : x + (g - x) ∈ S := hx.2 (g - x) hgx hpos
      rw [show x + (g - x) = g by omega] at hmem
      exact hg.1 hmem
  · rintro rfl; exact frobeniusNumber_isPF hg

/-! ## Direction 2: type one ⟹ symmetric (the open converse) -/

/-- **Type one ⟹ symmetric** (the converse left open by the parent).  If the only
pseudo-Frobenius number is `g`, then `S` is symmetric.  The reverse inclusion uses
`gap_dominated`: a gap `k` is dominated by a pseudo-Frobenius number, which must be
`g`, so `g - k ∈ S`. -/
theorem isSymmetric_of_isPF_ncard_one {S : Set ℕ} {g : ℕ} (h0 : 0 ∈ S)
    (hadd : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) (hfin : {n | n ∉ S}.Finite)
    (hg : IsFrobeniusNumber S g) (htype : {x | IsPF S x}.ncard = 1) :
    IsSymmetric S g := by
  classical
  -- From `ncard = 1` and `g ∈ PF`, the set of pseudo-Frobenius numbers is `{g}`.
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp htype
  have hg_pf : g ∈ {x | IsPF S x} := frobeniusNumber_isPF hg
  have hga : a = g := by rw [ha, Set.mem_singleton_iff] at hg_pf; exact hg_pf.symm
  subst hga
  intro k hk
  constructor
  · -- `k ∈ S → g - k ∉ S`: else `k + (g - k) = g ∈ S`, contradicting `g ∉ S`.
    intro hkS hgkS
    have hmem : k + (a - k) ∈ S := hadd k hkS (a - k) hgkS
    rw [show k + (a - k) = a by omega] at hmem
    exact hg.1 hmem
  · -- `g - k ∉ S → k ∈ S`, contrapositive: a gap `k` has `g - k ∈ S`.
    intro hgk
    by_contra hkS
    obtain ⟨m, hm_pf, _, hmk⟩ := gap_dominated h0 hadd hfin hkS
    have hmS : m ∈ {x | IsPF S x} := hm_pf
    rw [ha, Set.mem_singleton_iff] at hmS
    subst hmS
    exact hgk hmk

/-! ## The equivalence -/

/-- **Symmetric ⟺ type one** for any numerical semigroup with Frobenius number `g`. -/
theorem isSymmetric_iff_isPF_ncard_one {S : Set ℕ} {g : ℕ} (h0 : 0 ∈ S)
    (hadd : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) (hfin : {n | n ∉ S}.Finite)
    (hg : IsFrobeniusNumber S g) :
    IsSymmetric S g ↔ {x | IsPF S x}.ncard = 1 :=
  ⟨fun hsym => by
      rw [isPF_setOf_eq_of_isSymmetric hg hsym, Set.ncard_singleton],
    isSymmetric_of_isPF_ncard_one h0 hadd hfin hg⟩

/-- Packaged for a bundled `IsNumericalSemigroup`. -/
theorem isSymmetric_iff_type_one {S : Set ℕ} (hS : IsNumericalSemigroup S) {g : ℕ}
    (hg : IsFrobeniusNumber S g) :
    IsSymmetric S g ↔ {x | IsPF S x}.ncard = 1 :=
  isSymmetric_iff_isPF_ncard_one hS.1 hS.2.1 hS.2.2.1 hg

/-! ## Subsuming the parent: the two-generator semigroup `⟨a, b⟩` -/

section TwoGenerator

open FrobeniusNumber

variable {a b : ℕ}

/-- The set of representable numbers `{n | Representable a b n}` is a numerical
semigroup: it contains `0`, is closed under addition, and (by Sylvester) has all of
`{n | n > g}` inside it, so only finitely many gaps. -/
theorem representable_isNumericalSemigroup (hab : Nat.Coprime a b) (ha : 2 ≤ a)
    (hb : 2 ≤ b) : IsNumericalSemigroup {n | Representable a b n} := by
  obtain ⟨_, hgnot, hmax⟩ := sylvester_frobenius hab ha hb
  refine ⟨representable_zero a b, ?_, ?_, ?_⟩
  · -- closure under addition
    rintro x ⟨px, qx, rfl⟩ y ⟨py, qy, rfl⟩
    exact ⟨px + py, qx + qy, by ring⟩
  · -- finitely many gaps: all gaps are `≤ g`
    apply Set.Finite.subset (Set.finite_Iic (frobeniusNumber a b))
    intro n hn
    simp only [Set.mem_Iic]
    by_contra h
    exact hn (hmax n (by omega))
  · exact ⟨frobeniusNumber a b, hgnot⟩

/-- `frobeniusNumber a b` is the Frobenius number of `⟨a, b⟩` in the general sense. -/
theorem representable_isFrobeniusNumber (hab : Nat.Coprime a b) (ha : 2 ≤ a)
    (hb : 2 ≤ b) :
    IsFrobeniusNumber {n | Representable a b n} (frobeniusNumber a b) := by
  obtain ⟨_, hgnot, hmax⟩ := sylvester_frobenius hab ha hb
  exact ⟨hgnot, fun n hn => hmax n hn⟩

/-- `⟨a, b⟩` is symmetric in the general sense (re-export of the parent's
`symmetric_le_frobenius`). -/
theorem representable_isSymmetric (hab : Nat.Coprime a b) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IsSymmetric {n | Representable a b n} (frobeniusNumber a b) := by
  intro k hk
  exact FrobeniusNumberOQ01OQ03.symmetric_le_frobenius ha hb hab hk

/-- **The general equivalence recovers the parent's type-one theorem.**  Feeding the
two-generator symmetry into `isSymmetric_iff_type_one` yields `|PF(⟨a,b⟩)| = 1`
without re-running the parent's pseudo-Frobenius computation. -/
theorem representable_type_one (hab : Nat.Coprime a b) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    {x | IsPF {n | Representable a b n} x}.ncard = 1 :=
  (isSymmetric_iff_type_one (representable_isNumericalSemigroup hab ha hb)
    (representable_isFrobeniusNumber hab ha hb)).mp
    (representable_isSymmetric hab ha hb)

/-- Concrete sanity check: `⟨3, 5⟩` has Frobenius number `7`. -/
example : frobeniusNumber 3 5 = 7 := by decide

end TwoGenerator

end FrobeniusNumberOQ01OQ03OQ01
