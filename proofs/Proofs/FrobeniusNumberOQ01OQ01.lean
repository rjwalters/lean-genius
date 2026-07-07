import Mathlib.NumberTheory.FrobeniusNumber
import Mathlib.Tactic

/-!
# The Frobenius Number for Three or More Generators — Monotonicity and an Upper Bound

## What This Proves

For two coprime generators `m, n > 1`, Sylvester's theorem gives the exact Frobenius
number `g(m, n) = m*n - m - n` (Mathlib's `frobeniusNumber_pair`).  For **three or more**
generators there is *no* closed-form formula (the problem is NP-hard in general), so the
honest and useful target is a **bound**.

This file supplies the structural fact that Mathlib's Frobenius development is missing:
the Frobenius number is **monotone (antitone) in the generating set**.  Adding generators
can only make more numbers representable, hence can only *lower* the largest
non-representable number.  From this we obtain, for any generating set that *contains* a
coprime pair `m, n`, the computable upper bound

  g(s) ≤ m*n - m - n.

In particular, for three generators `{m, n, k}` with `gcd(m,n) = 1`:

  g(m, n, k) ≤ m*n - m - n,

directly answering the open question "generalize to three or more generators".  We also
show the bound is often **strict**: whenever the old Frobenius value `m*n - m - n` becomes
representable in the larger set, the new Frobenius number is strictly smaller.

## Definition (Mathlib)

`FrobeniusNumber g s` means `g = IsGreatest { k | k ∉ AddSubmonoid.closure s }`, i.e. `g`
is the largest natural number NOT expressible as a nonnegative integer combination of
elements of `s`.

## Status
- [x] Monotonicity of the Frobenius number in the generating set (antitone)
- [x] Strict decrease when the old boundary value becomes representable
- [x] Existence + upper bound for any set containing a coprime pair
- [x] Explicit three-generator corollary
- [x] Fully verified, 0 sorries, 0 axioms

## Mathlib Dependencies
- `FrobeniusNumber`, `frobeniusNumber_pair`, `exists_frobeniusNumber_iff`
  (`Mathlib.NumberTheory.FrobeniusNumber`)
- `AddSubmonoid.closure_mono` : monotonicity of additive-submonoid closure
- `Nat.setGcd_dvd_of_mem`, `Nat.dvd_gcd` : gcd of a set divides its members

## Historical Note
Sylvester (1884) solved the two-generator case.  For `n ≥ 3` generators the Frobenius
number has no closed form; only bounds and algorithms are known (Erdős–Graham, Brauer,
Selmer, …).  The monotonicity bound below is the most elementary of these: it says the
two-generator formula, applied to any coprime pair inside the generating set, is an upper
bound for the whole set.
-/

set_option linter.unusedVariables false

namespace FrobeniusMultiGenerator

open scoped Classical

/-!
## Part 1 — Monotonicity of the Frobenius number

The key structural lemma, absent from Mathlib: enlarging the generating set cannot
increase the Frobenius number.
-/

/-- **Monotonicity (antitone).**  If `s ⊆ t` and both sets have Frobenius numbers `f` and
`g`, then `g ≤ f`.  Adding generators can only make more numbers representable, so the
largest non-representable number can only decrease. -/
theorem frobeniusNumber_antitone {s t : Set ℕ} {f g : ℕ}
    (hst : s ⊆ t) (hf : FrobeniusNumber f s) (hg : FrobeniusNumber g t) : g ≤ f := by
  -- `closure s ≤ closure t`, so `g ∉ closure t` gives `g ∉ closure s`.
  have hmono : AddSubmonoid.closure s ≤ AddSubmonoid.closure t :=
    AddSubmonoid.closure_mono hst
  have hg_not_s : g ∉ AddSubmonoid.closure s := fun h => hg.1 (hmono h)
  -- `f` is the greatest element of `{k | k ∉ closure s}`, and `g` lies in that set.
  exact hf.2 hg_not_s

/-- **Strict decrease.**  If in addition the old Frobenius value `f` of `s` becomes
representable in the larger set `t` (i.e. `f ∈ closure t`), then the new Frobenius number
is *strictly* smaller: `g < f`.  This is why the bound of Part 2 is typically not tight
for three or more generators. -/
theorem frobeniusNumber_lt_of_mem_closure {s t : Set ℕ} {f g : ℕ}
    (hst : s ⊆ t) (hf : FrobeniusNumber f s) (hg : FrobeniusNumber g t)
    (hfmem : f ∈ AddSubmonoid.closure t) : g < f := by
  have hle : g ≤ f := frobeniusNumber_antitone hst hf hg
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · -- `g = f` would make `f` non-representable in `t`, contradicting `hfmem`.
    subst h
    exact absurd hfmem hg.1

/-!
## Part 2 — Existence and an upper bound from a coprime pair
-/

/-- If a set `s` contains two coprime elements, its set-gcd is `1`. -/
theorem setGcd_eq_one_of_coprime {s : Set ℕ} {m n : ℕ}
    (hm : m ∈ s) (hn : n ∈ s) (cop : Nat.Coprime m n) : Nat.setGcd s = 1 := by
  have d1 : Nat.setGcd s ∣ m := Nat.setGcd_dvd_of_mem hm
  have d2 : Nat.setGcd s ∣ n := Nat.setGcd_dvd_of_mem hn
  have hdvd : Nat.setGcd s ∣ Nat.gcd m n := Nat.dvd_gcd d1 d2
  have hg1 : Nat.gcd m n = 1 := cop
  rw [hg1] at hdvd
  exact Nat.dvd_one.mp hdvd

/-- **Main bound.**  Let `s` be any set of generators containing a coprime pair `m, n`
with `m, n > 1`, and not containing `1`.  Then `s` has a Frobenius number `g`, and it is
bounded above by the two-generator (Sylvester) value:

  `g ≤ m*n - m - n`.

This is the elementary upper bound for the Frobenius number of three or more generators. -/
theorem frobeniusNumber_le_pair {s : Set ℕ} {m n : ℕ}
    (hm : m ∈ s) (hn : n ∈ s) (cop : Nat.Coprime m n)
    (hm1 : 1 < m) (hn1 : 1 < n) (h1 : (1 : ℕ) ∉ s) :
    ∃ g, FrobeniusNumber g s ∧ g ≤ m * n - m - n := by
  -- Existence: `setGcd s = 1` and `1 ∉ s`.
  have hgcd : Nat.setGcd s = 1 := setGcd_eq_one_of_coprime hm hn cop
  obtain ⟨g, hg⟩ := exists_frobeniusNumber_iff.mpr ⟨hgcd, h1⟩
  refine ⟨g, hg, ?_⟩
  -- Sylvester's two-generator value on `{m, n} ⊆ s`.
  have hpair : FrobeniusNumber (m * n - m - n) {m, n} := frobeniusNumber_pair cop hm1 hn1
  have hsub : ({m, n} : Set ℕ) ⊆ s := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hm
    · exact hn
  exact frobeniusNumber_antitone hsub hpair hg

/-!
## Part 3 — The explicit three-generator corollary
-/

/-- **Three generators.**  For coprime `m, n > 1` and any third generator `k > 1`, the set
`{m, n, k}` has a Frobenius number bounded by Sylvester's two-generator value:

  `g(m, n, k) ≤ m*n - m - n`.

The coprimality of just *one* pair suffices; the third generator only lowers the value. -/
theorem frobeniusNumber_triple_le {m n k : ℕ}
    (cop : Nat.Coprime m n) (hm : 1 < m) (hn : 1 < n) (hk : 1 < k) :
    ∃ g, FrobeniusNumber g ({m, n, k} : Set ℕ) ∧ g ≤ m * n - m - n := by
  refine frobeniusNumber_le_pair (m := m) (n := n) ?_ ?_ cop hm hn ?_
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  · intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    omega

/-- **Strict three-generator bound.**  If the third generator `k` equals Sylvester's value
`m*n - m - n` (which is `> 1` once `m, n ≥ 3` are coprime, e.g. `{3, 5}` gives `7`), then it
was previously the *largest* non-representable number for `{m, n}`, so adding it strictly
lowers the Frobenius number:

  `g(m, n, k) < m*n - m - n`. -/
theorem frobeniusNumber_triple_strict {m n : ℕ}
    (cop : Nat.Coprime m n) (hm : 1 < m) (hn : 1 < n)
    (hk : 1 < m * n - m - n) :
    ∃ g, FrobeniusNumber g ({m, n, m * n - m - n} : Set ℕ) ∧ g < m * n - m - n := by
  -- Frobenius number of the enlarged set exists (from the triple bound below).
  have hsub : ({m, n} : Set ℕ) ⊆ ({m, n, m * n - m - n} : Set ℕ) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  have hpair : FrobeniusNumber (m * n - m - n) ({m, n} : Set ℕ) :=
    frobeniusNumber_pair cop hm hn
  obtain ⟨g, hg, _⟩ := frobeniusNumber_triple_le cop hm hn hk
  refine ⟨g, hg, ?_⟩
  -- The value `m*n - m - n` is itself a generator of the enlarged set, hence representable.
  have hkmem : (m * n - m - n) ∈ AddSubmonoid.closure ({m, n, m * n - m - n} : Set ℕ) :=
    AddSubmonoid.subset_closure (by simp)
  exact frobeniusNumber_lt_of_mem_closure hsub hpair hg hkmem

end FrobeniusMultiGenerator


open Nat

namespace FrobeniusNumberOQ01OQ01

/-! ## Explicit representability by `{6, 9, 20}` -/

/-- `n` is representable by `6, 9, 20` if `n = 6x + 9y + 20z` for some naturals `x, y, z`. -/
def Representable3 (n : ℕ) : Prop := ∃ x y z : ℕ, n = 6 * x + 9 * y + 20 * z

/-- `43` is not representable: no non-negative combination of `6, 9, 20` equals `43`.
    (`omega` decides this linear Diophantine (non-)existence directly.) -/
theorem not_representable3_43 : ¬ Representable3 43 := by
  rintro ⟨x, y, z, h⟩
  omega

/-- Every integer `≥ 44` is representable by `6, 9, 20`.
    Base residues `44, 45, 46, 47, 48, 49` are given explicit witnesses; larger values
    reduce by `6` to a smaller representable value (strong induction). -/
theorem representable3_ge : ∀ n, 44 ≤ n → Representable3 n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases h : n ≤ 49
    · interval_cases n
      · exact ⟨4, 0, 1, by norm_num⟩   -- 44 = 6·4 + 20
      · exact ⟨0, 5, 0, by norm_num⟩   -- 45 = 9·5
      · exact ⟨1, 0, 2, by norm_num⟩   -- 46 = 6 + 20·2
      · exact ⟨0, 3, 1, by norm_num⟩   -- 47 = 9·3 + 20
      · exact ⟨8, 0, 0, by norm_num⟩   -- 48 = 6·8
      · exact ⟨0, 1, 2, by norm_num⟩   -- 49 = 9 + 20·2
    · obtain ⟨x, y, z, hxyz⟩ := ih (n - 6) (by omega) (by omega)
      exact ⟨x + 1, y, z, by omega⟩

/-! ## Bridge to Mathlib's `AddSubmonoid.closure` -/

/-- The representable numbers, packaged as the additive submonoid they form. -/
def R3 : AddSubmonoid ℕ where
  carrier := {n | Representable3 n}
  zero_mem' := ⟨0, 0, 0, by norm_num⟩
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    obtain ⟨x₁, y₁, z₁, rfl⟩ := ha
    obtain ⟨x₂, y₂, z₂, rfl⟩ := hb
    exact ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂, by ring⟩

/-- A submonoid absorbs natural-number multiples of its members. -/
private theorem nat_mul_mem {S : AddSubmonoid ℕ} {m : ℕ} (hm : m ∈ S) (k : ℕ) : m * k ∈ S := by
  induction k with
  | zero => simpa using S.zero_mem
  | succ k ih => rw [Nat.mul_succ]; exact S.add_mem ih hm

/-- Membership in the closure of `{6, 9, 20}` is exactly representability by `6, 9, 20`. -/
theorem mem_closure_iff (n : ℕ) :
    n ∈ AddSubmonoid.closure ({6, 9, 20} : Set ℕ) ↔ Representable3 n := by
  constructor
  · intro hn
    have hle : AddSubmonoid.closure ({6, 9, 20} : Set ℕ) ≤ R3 := by
      rw [AddSubmonoid.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨1, 0, 0, by norm_num⟩
      · exact ⟨0, 1, 0, by norm_num⟩
      · exact ⟨0, 0, 1, by norm_num⟩
    exact hle hn
  · rintro ⟨x, y, z, rfl⟩
    have h6 : (6 : ℕ) ∈ AddSubmonoid.closure ({6, 9, 20} : Set ℕ) :=
      AddSubmonoid.subset_closure (by simp)
    have h9 : (9 : ℕ) ∈ AddSubmonoid.closure ({6, 9, 20} : Set ℕ) :=
      AddSubmonoid.subset_closure (by simp)
    have h20 : (20 : ℕ) ∈ AddSubmonoid.closure ({6, 9, 20} : Set ℕ) :=
      AddSubmonoid.subset_closure (by simp)
    exact add_mem (add_mem (nat_mul_mem h6 x) (nat_mul_mem h9 y)) (nat_mul_mem h20 z)

/-! ## The Chicken McNugget number: `g(6, 9, 20) = 43` -/

/-- **The Chicken McNugget theorem.** The Frobenius number of `{6, 9, 20}` is `43`:
    `43` cannot be written as a non-negative combination of `6, 9, 20`, but every
    larger integer can. This is the canonical three-generator instance; no closed-form
    formula produces it (the pair formula `frobeniusNumber_pair` does not apply). -/
theorem chickenMcNugget : FrobeniusNumber 43 ({6, 9, 20} : Set ℕ) := by
  rw [frobeniusNumber_iff]
  refine ⟨?_, ?_⟩
  · rw [mem_closure_iff]
    exact not_representable3_43
  · intro k hk
    rw [mem_closure_iff]
    exact representable3_ge k (by omega)

/-! ## Well-definedness for any number of generators (Schur's theorem) -/

/-- **n-generator well-definedness.** For any set of generators `s`, if `gcd s = 1`
    and `1 ∉ s` then a Frobenius number exists. This is the structural generalization
    to `n ≥ 3` generators of the fact that the Frobenius number is well-defined; the
    (impossible) part of the open question is a *closed form*, not existence. -/
theorem exists_frobeniusNumber_of_setGcd_one {s : Set ℕ} (hgcd : Nat.setGcd s = 1)
    (h1 : (1 : ℕ) ∉ s) : ∃ n, FrobeniusNumber n s :=
  exists_frobeniusNumber_iff.mpr ⟨hgcd, h1⟩

/-- The Chicken McNugget set does have a Frobenius number, and (by `chickenMcNugget`
    together with the uniqueness built into `IsGreatest`) it is `43`. -/
theorem exists_frobeniusNumber_mcnugget : ∃ n, FrobeniusNumber n ({6, 9, 20} : Set ℕ) :=
  ⟨43, chickenMcNugget⟩

end FrobeniusNumberOQ01OQ01
