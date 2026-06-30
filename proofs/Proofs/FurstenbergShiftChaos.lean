/-
# Furstenberg Correspondence OQ-01 (incomplete-01): Topological Dynamics of the Shift

## What This File Contains

The parent files (`FurstenbergCorrespondence`, `FurstenbergCorrespondenceOQ01`) develop
the **measure-theoretic** side of the Furstenberg correspondence: Cesàro averages of Dirac
measures on the orbit of an indicator, weak-* limits, and the reduction to a Prokhorov
compactness statement.

This file develops the complementary **topological-dynamics** side of the very same shift
system `T : {0,1}^ℕ → {0,1}^ℕ`, `T(x)(n) = x(n+1)`.  The headline result is that the shift
is **chaotic in the sense of Devaney**:

1. **Topological transitivity / mixing** — for any two finite words `v, w` and any delay
   `t ≥ |v|` there is a point that starts with `v` and reads off `w` after `t` shifts.
   Hence every nonempty open set is eventually carried across every other nonempty open set.
2. **Dense periodic points** — the periodic points `w w w …` are dense: every nonempty
   open set contains a `T`-periodic point.
3. **Sensitive dependence on initial conditions** — there is a sensitivity constant
   (separation at coordinate `0`, i.e. distance `1` in the standard metric) such that
   every point has, arbitrarily close to it, a point whose orbit eventually separates.

This is the symbolic-dynamics foundation underlying *Furstenberg's topological multiple
recurrence theorem* (the topological route to Szemerédi).  Whereas the measure-theoretic
correspondence translates positive density into an invariant measure, the topological
structure here records the recurrence and instability built into the raw shift.

Everything is proved with **0 axioms and 0 sorries**, by explicit symbolic constructions.

## References

- R. L. Devaney, *An Introduction to Chaotic Dynamical Systems* (1989).
- J. Banks et al., "On Devaney's definition of chaos", Amer. Math. Monthly 99 (1992).
- H. Furstenberg, *Recurrence in Ergodic Theory and Combinatorial Number Theory* (1981).
-/
import Mathlib

namespace FurstenbergShiftChaos

open Set Topology Function

/-! ═══════════════════════════════════════════════════════════════════════════════
PART I: CANTOR SPACE AND THE SHIFT
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Cantor space: binary sequences `ℕ → Bool`, with the product topology. -/
abbrev Cantor := ℕ → Bool

/-- The left shift `T(x)(n) = x(n+1)`. -/
def shift : Cantor → Cantor := fun x n => x (n + 1)

theorem shift_continuous : Continuous shift :=
  continuous_pi (fun n => continuous_apply (n + 1))

theorem shift_measurable : Measurable shift := shift_continuous.measurable

/-- Iterating the shift: `T^[n](x)(k) = x(k + n)`. -/
theorem shift_iterate (x : Cantor) (n k : ℕ) : shift^[n] x k = x (k + n) := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp_apply, shift, ih]
    congr 1; omega

/-! ═══════════════════════════════════════════════════════════════════════════════
PART II: WORD CYLINDERS — A CLOPEN NEIGHBOURHOOD BASIS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The cylinder of a finite word `w`: all sequences whose first `|w|` symbols are `w`. -/
def Cyl (w : List Bool) : Set Cantor :=
  ⋂ (i : Fin w.length), {x : Cantor | x i = w.getD i false}

/-- Membership in a word cylinder is agreement with `w` on the first `|w|` coordinates. -/
theorem mem_Cyl_iff (w : List Bool) (x : Cantor) :
    x ∈ Cyl w ↔ ∀ i, i < w.length → x i = w.getD i false := by
  simp only [Cyl, Set.mem_iInter, Set.mem_setOf_eq]
  exact ⟨fun h i hi => h ⟨i, hi⟩, fun h i => h i.1 i.2⟩

/-- Word cylinders are clopen. -/
theorem Cyl_isClopen (w : List Bool) : IsClopen (Cyl w) := by
  apply isClopen_iInter_of_finite
  intro i
  have : {x : Cantor | x (i : ℕ) = w.getD (i : ℕ) false}
      = (fun x : Cantor => x (i : ℕ)) ⁻¹' {w.getD (i : ℕ) false} := rfl
  rw [this]
  exact (isClopen_discrete {w.getD (i : ℕ) false}).preimage (continuous_apply (i : ℕ))

theorem Cyl_isOpen (w : List Bool) : IsOpen (Cyl w) := (Cyl_isClopen w).2

/-- The canonical length-`m` prefix word of a point `x`. -/
def prefixWord (x : Cantor) (m : ℕ) : List Bool := List.ofFn (fun i : Fin m => x i)

@[simp] theorem prefixWord_length (x : Cantor) (m : ℕ) : (prefixWord x m).length = m := by
  simp [prefixWord]

theorem prefixWord_getD (x : Cantor) (m i : ℕ) (hi : i < m) :
    (prefixWord x m).getD i false = x i := by
  have hlen : i < (prefixWord x m).length := by simpa using hi
  rw [List.getD_eq_getElem (prefixWord x m) false hlen]
  simp [prefixWord, List.getElem_ofFn]

/-- Membership in a prefix cylinder is agreement on the first `m` coordinates. -/
theorem mem_Cyl_prefixWord_iff (x y : Cantor) (m : ℕ) :
    x ∈ Cyl (prefixWord y m) ↔ ∀ i, i < m → x i = y i := by
  rw [mem_Cyl_iff]
  constructor
  · intro h i hi
    have := h i (by simpa using hi)
    rwa [prefixWord_getD y m i hi] at this
  · intro h i hi
    rw [prefixWord_length] at hi
    rw [prefixWord_getD y m i hi]; exact h i hi

/-- A point lies in the cylinder of its own length-`m` prefix. -/
theorem self_mem_Cyl_prefixWord (x : Cantor) (m : ℕ) : x ∈ Cyl (prefixWord x m) :=
  (mem_Cyl_prefixWord_iff x x m).mpr (fun _ _ => rfl)

/-- **Cylinder basis.** Every neighbourhood of a point contains a prefix cylinder of that
    point.  Thus the clopen word cylinders form a neighbourhood basis for Cantor space. -/
theorem exists_cyl_subset {U : Set Cantor} (hU : IsOpen U) {y : Cantor} (hy : y ∈ U) :
    ∃ m : ℕ, Cyl (prefixWord y m) ⊆ U := by
  rw [isOpen_pi_iff] at hU
  obtain ⟨I, u, hu, hsub⟩ := hU y hy
  refine ⟨(I.sup id) + 1, fun x hx => hsub ?_⟩
  intro i hi
  have hi_lt : i < (I.sup id) + 1 := Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  have hxi : x i = y i := (mem_Cyl_prefixWord_iff x y _).mp hx i hi_lt
  rw [hxi]
  exact (hu i hi).2

/-! ═══════════════════════════════════════════════════════════════════════════════
PART III: DENSE PERIODIC POINTS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The periodic point `w w w …` obtained by repeating a nonempty word `w`. -/
def periodicPoint (w : List Bool) : Cantor := fun n => w.getD (n % w.length) false

/-- `periodicPoint w` has period `|w|` under the shift. -/
theorem periodicPoint_isPeriodicPt (w : List Bool) :
    Function.IsPeriodicPt shift w.length (periodicPoint w) := by
  unfold Function.IsPeriodicPt Function.IsFixedPt
  funext n
  rw [shift_iterate]
  simp only [periodicPoint]
  rw [Nat.add_mod_right]

/-- For a nonempty word `w`, the repetition `w w w …` starts with `w`. -/
theorem periodicPoint_mem_Cyl (w : List Bool) :
    periodicPoint w ∈ Cyl w := by
  rw [mem_Cyl_iff]
  intro i hi
  simp only [periodicPoint]
  rw [Nat.mod_eq_of_lt hi]

/-- The set of `T`-periodic points. -/
def PeriodicPts : Set Cantor := {x | ∃ p, 0 < p ∧ shift^[p] x = x}

/-- **Dense periodic points (Devaney condition 2).** The `T`-periodic points are dense
    in Cantor space: every nonempty open set contains a point that is exactly periodic
    under the shift. -/
theorem dense_periodicPts : Dense PeriodicPts := by
  rw [dense_iff_inter_open]
  intro U hU hne
  obtain ⟨y, hy⟩ := hne
  obtain ⟨m, hsub⟩ := exists_cyl_subset hU hy
  -- Use a length-(m+1) prefix word, guaranteed nonempty so its repetition is periodic.
  set w := prefixWord y (m + 1) with hw
  have hwlen : 0 < w.length := by rw [hw, prefixWord_length]; omega
  have hmem : periodicPoint w ∈ Cyl w := periodicPoint_mem_Cyl w
  -- A length-(m+1) prefix agrees with `y` on all of `[0, m+1)`, hence on `[0, m)`.
  have hagree : ∀ i, i < m + 1 → periodicPoint w i = y i := by
    have := (mem_Cyl_prefixWord_iff (periodicPoint w) y (m + 1)).mp (by rwa [← hw])
    exact this
  have hInU : periodicPoint w ∈ U :=
    hsub ((mem_Cyl_prefixWord_iff (periodicPoint w) y m).mpr
      (fun i hi => hagree i (by omega)))
  exact ⟨periodicPoint w, hInU, ⟨w.length, hwlen, periodicPoint_isPeriodicPt w⟩⟩

/-! ═══════════════════════════════════════════════════════════════════════════════
PART IV: TOPOLOGICAL TRANSITIVITY AND MIXING
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The explicit "bridging" point for two words `v, w` and delay `t ≥ |v|`:
    it starts with `v`, and after `t` shifts it reads off `w`. -/
def bridge (v w : List Bool) (t : ℕ) : Cantor :=
  fun n => if n < v.length then v.getD n false else w.getD (n - t) false

theorem bridge_mem_Cyl_left (v w : List Bool) (t : ℕ) : bridge v w t ∈ Cyl v := by
  rw [mem_Cyl_iff]
  intro i hi
  simp only [bridge, if_pos hi]

theorem bridge_shift_mem_Cyl_right (v w : List Bool) {t : ℕ} (ht : v.length ≤ t) :
    shift^[t] (bridge v w t) ∈ Cyl w := by
  rw [mem_Cyl_iff]
  intro i hi
  rw [shift_iterate]
  have hge : ¬ (i + t < v.length) := by omega
  simp only [bridge, if_neg hge]
  congr 1
  omega

/-- **Topological transitivity (Devaney condition 1).** For any two nonempty open sets
    `U, V`, some shift carries a point of `U` into `V`: there is a point of `U` whose
    `t`-th iterate lands in `V`. -/
theorem transitive (U V : Set Cantor) (hU : IsOpen U) (hV : IsOpen V)
    (hUne : U.Nonempty) (hVne : V.Nonempty) :
    ∃ (x : Cantor) (t : ℕ), x ∈ U ∧ shift^[t] x ∈ V := by
  obtain ⟨u, hu⟩ := hUne
  obtain ⟨v, hv⟩ := hVne
  obtain ⟨m, hmU⟩ := exists_cyl_subset hU hu
  obtain ⟨k, hkV⟩ := exists_cyl_subset hV hv
  set vw := prefixWord u m with hvw
  set ww := prefixWord v k with hww
  exact ⟨bridge vw ww vw.length, vw.length, hmU (bridge_mem_Cyl_left vw ww vw.length),
    hkV (bridge_shift_mem_Cyl_right vw ww (le_refl vw.length))⟩

/-- **Mixing strengthening.** At the level of word cylinders, every delay `t ≥ |v|`
    bridges the cylinder of `v` into the cylinder of `w`. -/
theorem mixing_cyl (v w : List Bool) {t : ℕ} (ht : v.length ≤ t) :
    ∃ x, x ∈ Cyl v ∧ shift^[t] x ∈ Cyl w :=
  ⟨bridge v w t, bridge_mem_Cyl_left v w t, bridge_shift_mem_Cyl_right v w ht⟩

/-! ═══════════════════════════════════════════════════════════════════════════════
PART V: SENSITIVE DEPENDENCE ON INITIAL CONDITIONS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Sensitive dependence (Devaney condition 3).** With sensitivity constant `1`
    (separation at coordinate `0`, i.e. distance `1` in the standard metric
    `d(x,y) = 2^{-min{n : x n ≠ y n}}`): for every point `x` and every precision `m`,
    there is a point `y` agreeing with `x` on the first `m` coordinates whose orbit
    eventually separates from that of `x`. -/
theorem sensitive (x : Cantor) (m : ℕ) :
    ∃ y : Cantor, (∀ i, i < m → y i = x i) ∧ ∃ n, shift^[n] y 0 ≠ shift^[n] x 0 := by
  refine ⟨Function.update x m (!x m), ?_, m, ?_⟩
  · intro i hi
    rw [Function.update_of_ne (by omega : i ≠ m)]
  · have h1 : shift^[m] (Function.update x m (!x m)) 0 = !x m := by
      rw [shift_iterate, zero_add, Function.update_self]
    have h2 : shift^[m] x 0 = x m := by rw [shift_iterate, zero_add]
    rw [h1, h2]
    cases x m <;> decide

/-! ═══════════════════════════════════════════════════════════════════════════════
PART VI: DEVANEY CHAOS — ASSEMBLY
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **The shift on Cantor space is chaotic in the sense of Devaney.**
    It is topologically transitive, has dense periodic points, and depends sensitively
    on initial conditions. -/
theorem shift_devaney_chaos :
    (∀ U V : Set Cantor, IsOpen U → IsOpen V → U.Nonempty → V.Nonempty →
      ∃ (x : Cantor) (t : ℕ), x ∈ U ∧ shift^[t] x ∈ V) ∧
    Dense PeriodicPts ∧
    (∀ (x : Cantor) (m : ℕ), ∃ y : Cantor,
      (∀ i, i < m → y i = x i) ∧ ∃ n, shift^[n] y 0 ≠ shift^[n] x 0) :=
  ⟨transitive, dense_periodicPts, sensitive⟩

-- Axiom audit: should report only `propext`, `Classical.choice`, `Quot.sound`.
#print axioms shift_devaney_chaos

end FurstenbergShiftChaos
