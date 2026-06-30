/-
  Erdős Problem #2 — Open Question OQ-03:
  "Can the Balister et al. bound of 616,000 be further improved?"

  Source problem: https://erdosproblems.com/2
  Related formalization: Proofs/Erdos2Problem.lean

  ---------------------------------------------------------------------------
  Scope and honesty
  ---------------------------------------------------------------------------
  The open question OQ-03 asks for a *quantitative* improvement to the upper
  bound 616,000 (Balister–Bollobás–Morris–Sahasrabudhe–Tiba, 2022) on the
  minimum modulus of a covering system.  That is a wide-open research-level
  quantitative problem and is NOT resolved here.

  What this file contributes is the elementary *structural arithmetic* that
  every such bound must respect — the counting constraints that any covering
  system with a large minimum modulus is forced to obey.  These are the "soft"
  consequences of the classical density inequality

        Σ 1/nᵢ ≥ 1                                       (reciprocal-sum bound)

  which the parent file `Erdos2Problem.lean` axiomatizes as
  `Erdos2.reciprocal_sum_ge_one`.  Here we do NOT use that axiom: every theorem
  takes the reciprocal-sum bound as an explicit hypothesis
  `cs.reciprocalSum ≥ 1`, so the whole file is axiom-free (0 `axiom`
  declarations, 0 `sorry`, no `native_decide`).

  This file is deliberately SELF-CONTAINED: the parent `Erdos2Problem.lean`
  currently fails to compile under Lean 4.26.0 / Mathlib (its theorem
  `hough_bound` forward-references the `balister_bound` axiom declared later in
  the file).  We therefore re-introduce the minimal definitions we need rather
  than importing it, so this contribution is independently verifiable.

  Main results (all conditional on the classical reciprocal-sum bound):

  * `reciprocalSum_le`    — Σ 1/nᵢ ≤ k/m  when every modulus is ≥ m
                            (k = number of congruence classes).
  * `card_classes_ge`     — a covering system with minimum modulus ≥ m has at
                            least m congruence classes (k ≥ m).
  * `maxModulus_ge`       — with distinct moduli all in [m, M], necessarily
                            2m ≤ M + 1, i.e. the moduli must span a factor-2
                            range; a maximal modulus ≥ 2m − 1 is forced.
  * `improvement_cost`    — the combined structural price of a min modulus ≥ m.
  * `card_bound_tight`    — the count bound k ≥ m is tight (the trivial
                            {0, 1 mod 2} system realises k = m = 2).

  Interpretation w.r.t. OQ-03: any covering system witnessing a minimum
  modulus m needs ≥ m classes and a modulus ≥ 2m − 1.  Pushing the *lower*
  bound (currently Owens' 42) therefore has an unavoidable combinatorial cost,
  and any improved *upper* bound M must be consistent with `maxModulus_ge`.
-/

import Mathlib

open Set Finset

namespace Erdos2OQ03

/- ## Minimal covering-system definitions (self-contained) -/

/-- An arithmetic progression represented as a pair (residue, modulus). -/
structure CongruenceClass where
  residue : ℕ
  modulus : ℕ
  modulus_pos : modulus ≥ 2

/-- The set of integers in a congruence class. -/
def CongruenceClass.toSet (c : CongruenceClass) : Set ℤ :=
  { x | x ≡ c.residue [ZMOD c.modulus] }

/-- A covering system is a finite list of congruence classes that cover all
    integers. -/
structure CoveringSystem where
  classes : List CongruenceClass
  nonempty : classes.length ≥ 1
  covers : ∀ x : ℤ, ∃ c ∈ classes, x ∈ c.toSet

/-- The list of moduli in a covering system. -/
def CoveringSystem.moduli (cs : CoveringSystem) : List ℕ :=
  cs.classes.map CongruenceClass.modulus

/-- A covering system has distinct moduli. -/
def CoveringSystem.hasDistinctModuli (cs : CoveringSystem) : Prop :=
  cs.moduli.Nodup

/-- A covering system has minimum modulus at least `m`. -/
def CoveringSystem.hasMinModulusAtLeast (cs : CoveringSystem) (m : ℕ) : Prop :=
  ∀ c ∈ cs.classes, m ≤ c.modulus

/-- The reciprocal sum of the moduli, `Σ 1/nᵢ`. -/
def CoveringSystem.reciprocalSum (cs : CoveringSystem) : ℚ :=
  (cs.moduli.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum

/- ## The reciprocal-sum upper bound -/

/--
If every modulus of `cs` is at least `m ≥ 1`, then the reciprocal sum is at
most `k / m`, where `k = cs.classes.length` is the number of congruence
classes.  This is the trivial half of the density picture: each summand
`1/nᵢ` is at most `1/m`.
-/
theorem reciprocalSum_le (cs : CoveringSystem) {m : ℕ} (hm : 1 ≤ m)
    (hmin : cs.hasMinModulusAtLeast m) :
    cs.reciprocalSum ≤ (cs.classes.length : ℚ) / m := by
  rw [CoveringSystem.reciprocalSum, CoveringSystem.moduli, List.map_map]
  -- goal: (cs.classes.map ((fun n => 1/↑n) ∘ modulus)).sum ≤ k/m
  have hbound : ∀ x ∈ cs.classes.map ((fun n : ℕ => (1 : ℚ) / (n : ℚ)) ∘ CongruenceClass.modulus),
      x ≤ (1 : ℚ) / m := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    simp only [Function.comp_apply]
    exact one_div_le_one_div_of_le (by exact_mod_cast hm) (by exact_mod_cast hmin c hc)
  have h := List.sum_le_card_nsmul _ _ hbound
  rwa [List.length_map, nsmul_eq_mul, mul_one_div] at h

/- ## Lower bound on the number of congruence classes -/

/--
**Class-count bound.**  A covering system whose minimum modulus is at least
`m` must contain at least `m` congruence classes.

This is the elementary engine behind every quantitative attack on Erdős #2:
to have a large minimum modulus you are forced to use many classes.  It is
conditional on the classical reciprocal-sum bound `cs.reciprocalSum ≥ 1`
(parent axiom `Erdos2.reciprocal_sum_ge_one`), supplied here as a hypothesis.
-/
theorem card_classes_ge (cs : CoveringSystem) {m : ℕ} (hm : 1 ≤ m)
    (hmin : cs.hasMinModulusAtLeast m) (hrec : cs.reciprocalSum ≥ 1) :
    m ≤ cs.classes.length := by
  have hmpos : (0 : ℚ) < m := by exact_mod_cast (show 0 < m by omega)
  have hle : (1 : ℚ) ≤ (cs.classes.length : ℚ) / m :=
    le_trans hrec (reciprocalSum_le cs hm hmin)
  have : (m : ℚ) ≤ (cs.classes.length : ℚ) := (one_le_div hmpos).1 hle
  exact_mod_cast this

/- ## The moduli must span a wide range -/

/--
**Spread bound.**  If a covering system has *distinct* moduli, all lying in
the interval `[m, M]`, then `2m ≤ M + 1`.  Equivalently the largest modulus
is at least `2m − 1`: the moduli cannot all be confined to a narrow window
above the minimum.

Proof: `card_classes_ge` forces at least `m` classes, while distinctness
confines the moduli to `Icc m M`, which has only `M + 1 − m` elements.
-/
theorem maxModulus_ge (cs : CoveringSystem) {m M : ℕ} (hm : 1 ≤ m)
    (hdist : cs.hasDistinctModuli)
    (hmin : cs.hasMinModulusAtLeast m)
    (hmax : ∀ c ∈ cs.classes, c.modulus ≤ M)
    (hrec : cs.reciprocalSum ≥ 1) :
    2 * m ≤ M + 1 := by
  have hcard : m ≤ cs.classes.length := card_classes_ge cs hm hmin hrec
  have hnd : cs.moduli.Nodup := hdist
  have hsub : cs.moduli.toFinset ⊆ Finset.Icc m M := by
    intro n hn
    rw [List.mem_toFinset, CoveringSystem.moduli, List.mem_map] at hn
    obtain ⟨c, hc, rfl⟩ := hn
    exact Finset.mem_Icc.2 ⟨hmin c hc, hmax c hc⟩
  have hk : cs.classes.length ≤ M + 1 - m :=
    calc cs.classes.length
        = cs.moduli.length := by simp [CoveringSystem.moduli]
      _ = cs.moduli.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
      _ ≤ (Finset.Icc m M).card := Finset.card_le_card hsub
      _ = M + 1 - m := Nat.card_Icc m M
  omega

/--
**Structural cost of a large minimum modulus.**  Packaging the two bounds:
a covering system with distinct moduli, minimum modulus ≥ `m`, and all moduli
≤ `M` must use at least `m` classes and reach a modulus ≥ `2m − 1`.

This is the structural content behind OQ-03: any hypothetical covering system
that improves the known bounds is constrained by these inequalities.
-/
theorem improvement_cost (cs : CoveringSystem) {m M : ℕ} (hm : 1 ≤ m)
    (hdist : cs.hasDistinctModuli)
    (hmin : cs.hasMinModulusAtLeast m)
    (hmax : ∀ c ∈ cs.classes, c.modulus ≤ M)
    (hrec : cs.reciprocalSum ≥ 1) :
    m ≤ cs.classes.length ∧ 2 * m ≤ M + 1 :=
  ⟨card_classes_ge cs hm hmin hrec, maxModulus_ge cs hm hdist hmin hmax hrec⟩

/- ## Tightness of the class-count bound -/

/-- A modulus-2 congruence class: even integers. -/
def mod2_even : CongruenceClass := ⟨0, 2, by norm_num⟩
/-- A modulus-2 congruence class: odd integers. -/
def mod2_odd : CongruenceClass := ⟨1, 2, by norm_num⟩

/-- The integers are covered by the even and odd classes. -/
theorem even_odd_cover : ∀ x : ℤ, x ∈ mod2_even.toSet ∨ x ∈ mod2_odd.toSet := by
  intro x
  unfold mod2_even mod2_odd CongruenceClass.toSet
  simp only [mem_setOf_eq, Int.ModEq]
  rcases Int.emod_two_eq_zero_or_one x with h | h
  · left; omega
  · right; omega

/-- The trivial covering system `{0 mod 2, 1 mod 2}`. -/
def trivialCover : CoveringSystem where
  classes := [mod2_even, mod2_odd]
  nonempty := by simp
  covers := fun x => by
    rcases even_odd_cover x with h | h
    · exact ⟨mod2_even, by simp, h⟩
    · exact ⟨mod2_odd, by simp, h⟩

/-- Its reciprocal sum is exactly `1/2 + 1/2 = 1`. -/
theorem trivialCover_reciprocalSum : trivialCover.reciprocalSum = 1 := by
  simp [CoveringSystem.reciprocalSum, CoveringSystem.moduli, trivialCover,
    mod2_even, mod2_odd]
  norm_num

/--
**The class-count bound is tight.**  There is a covering system attaining
`k = m` exactly: the trivial mod-2 cover has minimum modulus `m = 2` and
exactly `k = 2` classes, with reciprocal sum `1`.  So `card_classes_ge`
cannot be improved to `m < k` in general.
-/
theorem card_bound_tight :
    ∃ (cs : CoveringSystem) (m : ℕ),
      1 ≤ m ∧ cs.hasMinModulusAtLeast m ∧ cs.reciprocalSum ≥ 1 ∧
        cs.classes.length = m := by
  refine ⟨trivialCover, 2, by norm_num, ?_, ?_, ?_⟩
  · intro c hc
    simp only [trivialCover, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp [mod2_even, mod2_odd]
  · rw [trivialCover_reciprocalSum]
  · simp [trivialCover]

end Erdos2OQ03
