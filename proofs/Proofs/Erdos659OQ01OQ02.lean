/-
# Erdős Problem #659 OQ-01-OQ-02 — d ≥ 3 extension: axis-vs-plane scaffold

This file is the S3 ACT **scaffold** for the open question

> Can the O(n/√(log n)) sharp-distance-bound theorem for ℝ² (parent
> `erdos-659-oq-01`) be extended to ℝ^d for `d ≥ 3`?

The plan (per S1c OBSERVE PR #18431 + S2a OBSERVE PR #18494 + S2b PREP
PR #18554) is to ship a Pell-equation-safe sub-lattice family
`L_{p, q} := { (δ₁, δ₂√p, δ₃√q) : δᵢ ∈ ℤ }` for selected squarefree
prime pairs `(p, q)`, then derive the Θ(n^{2/3}) rate.

S2b PREP §4–§6 isolated the **axis-vs-plane** half of the safety
predicate into three equations in three unknowns:

```
(A)   5 c² = a² + 2 b²
(B)   2 b² = a² + 5 c²
(C)   a²    = 2 b² + 5 c²
```

A solution `(a, b, c) ≠ (0, 0, 0)` to any of A/B/C corresponds to an
axis-vs-plane equidistant 4-tuple in `L_{2, 5}`. The S2b §4–§5 QR-descent
template proves all three have only the trivial integer solution by
reducing mod 5 and applying the quadratic-non-residue status of `2` and
`−2` mod 5.

This file ships the **complete** axis-vs-plane safety theorem — the
three predicates, their composite, and the named theorems — with all
three QR-descent bodies **proved** (S4 ACT, 2026-05-29) by infinite descent
on the natAbs of the isolated variable. The descent recipe is in
`research/problems/erdos-659-oq-01-oq-02/sessions/2026-05-13-s2b-prep-qr-descent-mathlib-audit-for-2-5-pair.md`
§5 (the Lean template) and §7 (generalisation pointer for the other
six safe pairs identified by S2a).

**Scope.** Axis-vs-plane only. Full-rank safety (per S2c PREP §6.1) is
deferred to a separate axiomatisation pending Mathlib Hasse-Minkowski
infrastructure that does not yet exist at v4.26.0.

**Sorries / axioms.** 0 sorries; 0 axioms. The three axis-vs-plane
equations A/B/C for `(p, q) = (2, 5)` are fully proved (Docker-verified
GREEN, S4 ACT, 2026-05-29). The S7 ACT (2026-06-04) extension adds the
analogous axis-vs-plane safety for the second safe prime pair
`(p, q) = (3, 5)` (`safe_3_5_axis_vs_plane`), using the same QR-descent
template with two new mod-5 helpers
(`zmod_5_a_sq_plus_3_b_sq_eq_zero_iff`, `zmod_5_a_sq_eq_three_b_sq_iff`).
Full-rank safety (per S2c PREP §6.1) remains a separate future
axiomatisation, pending Mathlib ternary Hasse-Minkowski infrastructure.
-/

import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

namespace Erdos659OQ01OQ02

/-! ## S4 PREP — ZMod 5 QR helpers (mod-5 step for QR descent)

The S4 ACT proofs of `safe_A_holds`, `safe_B_holds`, `safe_C_holds` each
need a mod-5 step ahead of the integer descent. The two `decide`-checked
lemmas below encapsulate that mod-5 analysis once and for all, replacing
the longer `ZMod.exists_sq_eq_{two,neg_two}_iff` + case-on-residue path
sketched in
`sessions/2026-05-13-s2b-prep-qr-descent-mathlib-audit-for-2-5-pair.md`
§4 with a 25-case `decide` check.

Both are pure ZMod-5 facts, independent of the integer descent
infrastructure; they reduce the S4 ACT body to substitution arithmetic
plus `Nat.strongRecOn`. -/

/-- **(S4 PREP, mod-5 step for equation A)** `a² + 2b² ≡ 0 (mod 5)` iff
    both `a ≡ 0` and `b ≡ 0` in `ZMod 5`. Equivalent (via §3.2 of S2b
    PREP) to the assertion that `−2` is not a square in `ZMod 5`. -/
lemma zmod_5_a_sq_plus_2_b_sq_eq_zero_iff (a b : ZMod 5) :
    a ^ 2 + 2 * b ^ 2 = 0 ↔ a = 0 ∧ b = 0 := by
  revert a b
  decide

/-- **(S4 PREP, mod-5 step for equations B and C)** `a² ≡ 2 b² (mod 5)`
    iff both `a ≡ 0` and `b ≡ 0` in `ZMod 5`. Equivalent (via §3.1 of S2b
    PREP) to the assertion that `2` is not a square in `ZMod 5`. -/
lemma zmod_5_a_sq_eq_two_b_sq_iff (a b : ZMod 5) :
    a ^ 2 = 2 * b ^ 2 ↔ a = 0 ∧ b = 0 := by
  revert a b
  decide

/-- **(S7 ACT, mod-5 step for equation A' on the prime pair `(3, 5)`)**
    `a² + 3 b² ≡ 0 (mod 5)` iff both `a ≡ 0` and `b ≡ 0` in `ZMod 5`.
    Equivalent to the assertion that `−3` is not a square in `ZMod 5`. -/
lemma zmod_5_a_sq_plus_3_b_sq_eq_zero_iff (a b : ZMod 5) :
    a ^ 2 + 3 * b ^ 2 = 0 ↔ a = 0 ∧ b = 0 := by
  revert a b
  decide

/-- **(S7 ACT, mod-5 step for equations B' and C' on the prime pair `(3, 5)`)**
    `a² ≡ 3 b² (mod 5)` iff both `a ≡ 0` and `b ≡ 0` in `ZMod 5`.
    Equivalent to the assertion that `3` is not a square in `ZMod 5`. -/
lemma zmod_5_a_sq_eq_three_b_sq_iff (a b : ZMod 5) :
    a ^ 2 = 3 * b ^ 2 ↔ a = 0 ∧ b = 0 := by
  revert a b
  decide

/-- **(S8 ACT, mod-13 step for equation A on the prime pair `(2, 13)`)**
    `a² + 2 b² ≡ 0 (mod 13)` iff both `a ≡ 0` and `b ≡ 0` in `ZMod 13`.
    Equivalent to the assertion that `−2` is not a square in `ZMod 13`
    (squares mod 13 are `{0, 1, 3, 4, 9, 10, 12}`; `11 = −2 mod 13` is
    not among them). 169-case `decide` check. -/
lemma zmod_13_a_sq_plus_2_b_sq_eq_zero_iff (a b : ZMod 13) :
    a ^ 2 + 2 * b ^ 2 = 0 ↔ a = 0 ∧ b = 0 := by
  revert a b
  decide

/-- **(S8 ACT, mod-13 step for equations B and C on the prime pair `(2, 13)`)**
    `a² ≡ 2 b² (mod 13)` iff both `a ≡ 0` and `b ≡ 0` in `ZMod 13`.
    Equivalent to the assertion that `2` is not a square in `ZMod 13`
    (squares mod 13 are `{0, 1, 3, 4, 9, 10, 12}`; `2` is not among them).
    169-case `decide` check. -/
lemma zmod_13_a_sq_eq_two_b_sq_iff (a b : ZMod 13) :
    a ^ 2 = 2 * b ^ 2 ↔ a = 0 ∧ b = 0 := by
  revert a b
  decide

/-- Equation A predicate for the prime pair `(p, q) = (2, 5)`:
    `5 c² = a² + 2 b²` has only the trivial integer solution.

    Geometric meaning: an axis-vs-plane equidistant 4-tuple in
    `L_{2, 5}` projecting onto coordinate axis 1 and the (axis 2,
    axis 3) plane would give a non-trivial solution.

    Discharge plan (S4 ACT, ~30 LOC): reduce mod 5 to deduce
    `5 ∣ a.natAbs` and `5 ∣ b.natAbs` (using `−2` not a square mod 5);
    substitute and rearrange to deduce `5 ∣ c.natAbs`; descend by
    `Nat.strongRecOn` on `c.natAbs`. See S2b PREP §4.1 + §5. -/
def safe_A : Prop :=
  ∀ a b c : ℤ, (5 : ℤ) * c ^ 2 = a ^ 2 + 2 * b ^ 2 → a = 0 ∧ b = 0 ∧ c = 0

/-- Equation B predicate for the prime pair `(p, q) = (2, 5)`:
    `2 b² = a² + 5 c²` has only the trivial integer solution.

    Discharge plan (S4 ACT, ~30 LOC): analogous to `safe_A` with
    `b` ↔ `c` (mod-5 reduction via `2` not a square mod 5). See
    S2b PREP §4.2. -/
def safe_B : Prop :=
  ∀ a b c : ℤ, (2 : ℤ) * b ^ 2 = a ^ 2 + 5 * c ^ 2 → a = 0 ∧ b = 0 ∧ c = 0

/-- Equation C predicate for the prime pair `(p, q) = (2, 5)`:
    `a² = 2 b² + 5 c²` has only the trivial integer solution.

    Discharge plan (S4 ACT, ~30 LOC): analogous to `safe_A` with
    `a` ↔ `c`. See S2b PREP §4.3. -/
def safe_C : Prop :=
  ∀ a b c : ℤ, a ^ 2 = (2 : ℤ) * b ^ 2 + 5 * c ^ 2 → a = 0 ∧ b = 0 ∧ c = 0

/-- **(S4 ACT — axis-vs-plane equation A, PROVED).**
    `5 c² = a² + 2 b²` has only `(0, 0, 0)`.

    Infinite descent on `c.natAbs`: mod 5 (via
    `zmod_5_a_sq_plus_2_b_sq_eq_zero_iff`, i.e. `−2` is not a QR mod 5)
    forces `5 ∣ a`, `5 ∣ b`, then `5 ∣ c`; the reduced triple satisfies
    the same equation with strictly smaller `c.natAbs`. -/
theorem safe_A_holds : safe_A := by
  have key : ∀ n : ℕ, ∀ a b c : ℤ, c.natAbs = n →
      (5 : ℤ) * c ^ 2 = a ^ 2 + 2 * b ^ 2 → a = 0 ∧ b = 0 ∧ c = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a b c hc heq
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · have hc0 : c = 0 := Int.natAbs_eq_zero.mp (by omega)
        subst hc0
        refine ⟨?_, ?_, rfl⟩
        · exact sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg b]) (sq_nonneg a))
        · exact sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg a]) (sq_nonneg b))
      · have hz : (a : ZMod 5) ^ 2 + 2 * (b : ZMod 5) ^ 2 = 0 := by
          have h : ((a ^ 2 + 2 * b ^ 2 : ℤ) : ZMod 5) = ((5 * c ^ 2 : ℤ) : ZMod 5) := by
            rw [heq]
          push_cast at h
          rw [show (5 : ZMod 5) = 0 from by decide, zero_mul] at h
          exact h
        rw [zmod_5_a_sq_plus_2_b_sq_eq_zero_iff] at hz
        have hda : (5 : ℤ) ∣ a := (ZMod.intCast_zmod_eq_zero_iff_dvd a 5).mp hz.1
        have hdb : (5 : ℤ) ∣ b := (ZMod.intCast_zmod_eq_zero_iff_dvd b 5).mp hz.2
        obtain ⟨a', rfl⟩ := hda
        obtain ⟨b', rfl⟩ := hdb
        have h5 : (5 : ℤ) * c ^ 2 = 5 * (5 * (a' ^ 2 + 2 * b' ^ 2)) := by
          linear_combination heq
        have hc2 : c ^ 2 = 5 * (a' ^ 2 + 2 * b' ^ 2) :=
          mul_left_cancel₀ (by norm_num : (5 : ℤ) ≠ 0) h5
        have hdc : (5 : ℤ) ∣ c := by
          have hp : Prime (5 : ℤ) := by norm_num
          exact hp.dvd_of_dvd_pow (⟨a' ^ 2 + 2 * b' ^ 2, hc2⟩ : (5 : ℤ) ∣ c ^ 2)
        obtain ⟨c', rfl⟩ := hdc
        have heq' : (5 : ℤ) * c' ^ 2 = a' ^ 2 + 2 * b' ^ 2 := by
          have h25 : (5 : ℤ) * (5 * c' ^ 2) = 5 * (a' ^ 2 + 2 * b' ^ 2) := by
            linear_combination hc2
          exact mul_left_cancel₀ (by norm_num : (5 : ℤ) ≠ 0) h25
        have hmeas : c'.natAbs < n := by
          have h5nat : (5 : ℤ).natAbs = 5 := by decide
          rw [Int.natAbs_mul, h5nat] at hc
          omega
        obtain ⟨ha0, hb0, hc0⟩ := ih c'.natAbs hmeas a' b' c' rfl heq'
        subst ha0; subst hb0; subst hc0
        refine ⟨by ring, by ring, by ring⟩
  intro a b c heq
  exact key c.natAbs a b c rfl heq

/-- **(S4 ACT — axis-vs-plane equation B, PROVED).**
    `2 b² = a² + 5 c²` has only `(0, 0, 0)`.

    Infinite descent on `b.natAbs`: mod 5 (via `zmod_5_a_sq_eq_two_b_sq_iff`,
    i.e. `2` is not a QR mod 5) forces `5 ∣ a`, `5 ∣ b`, then `5 ∣ c`. -/
theorem safe_B_holds : safe_B := by
  have key : ∀ n : ℕ, ∀ a b c : ℤ, b.natAbs = n →
      (2 : ℤ) * b ^ 2 = a ^ 2 + 5 * c ^ 2 → a = 0 ∧ b = 0 ∧ c = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a b c hb heq
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · have hb0 : b = 0 := Int.natAbs_eq_zero.mp (by omega)
        subst hb0
        refine ⟨?_, rfl, ?_⟩
        · exact sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg c]) (sq_nonneg a))
        · exact sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg a]) (sq_nonneg c))
      · have hz : (a : ZMod 5) ^ 2 = 2 * (b : ZMod 5) ^ 2 := by
          have h : ((2 * b ^ 2 : ℤ) : ZMod 5) = ((a ^ 2 + 5 * c ^ 2 : ℤ) : ZMod 5) := by
            rw [heq]
          push_cast at h
          rw [show (5 : ZMod 5) = 0 from by decide, zero_mul, add_zero] at h
          exact h.symm
        rw [zmod_5_a_sq_eq_two_b_sq_iff] at hz
        have hda : (5 : ℤ) ∣ a := (ZMod.intCast_zmod_eq_zero_iff_dvd a 5).mp hz.1
        have hdb : (5 : ℤ) ∣ b := (ZMod.intCast_zmod_eq_zero_iff_dvd b 5).mp hz.2
        obtain ⟨a', rfl⟩ := hda
        obtain ⟨b', rfl⟩ := hdb
        have h5 : (5 : ℤ) * c ^ 2 = 5 * (5 * (2 * b' ^ 2 - a' ^ 2)) := by
          linear_combination -heq
        have hc2 : c ^ 2 = 5 * (2 * b' ^ 2 - a' ^ 2) :=
          mul_left_cancel₀ (by norm_num : (5 : ℤ) ≠ 0) h5
        have hdc : (5 : ℤ) ∣ c := by
          have hp : Prime (5 : ℤ) := by norm_num
          exact hp.dvd_of_dvd_pow (⟨2 * b' ^ 2 - a' ^ 2, hc2⟩ : (5 : ℤ) ∣ c ^ 2)
        obtain ⟨c', rfl⟩ := hdc
        have heq' : (2 : ℤ) * b' ^ 2 = a' ^ 2 + 5 * c' ^ 2 := by
          have h25 : (5 : ℤ) * (2 * b' ^ 2) = 5 * (a' ^ 2 + 5 * c' ^ 2) := by
            linear_combination -hc2
          exact mul_left_cancel₀ (by norm_num : (5 : ℤ) ≠ 0) h25
        have hmeas : b'.natAbs < n := by
          have h5nat : (5 : ℤ).natAbs = 5 := by decide
          rw [Int.natAbs_mul, h5nat] at hb
          omega
        obtain ⟨ha0, hb0, hc0⟩ := ih b'.natAbs hmeas a' b' c' rfl heq'
        subst ha0; subst hb0; subst hc0
        refine ⟨by ring, by ring, by ring⟩
  intro a b c heq
  exact key b.natAbs a b c rfl heq

/-- **(S4 ACT — axis-vs-plane equation C, PROVED).**
    `a² = 2 b² + 5 c²` has only `(0, 0, 0)`.

    Infinite descent on `a.natAbs`: mod 5 (via `zmod_5_a_sq_eq_two_b_sq_iff`)
    forces `5 ∣ a`, `5 ∣ b`, then `5 ∣ c`. -/
theorem safe_C_holds : safe_C := by
  have key : ∀ n : ℕ, ∀ a b c : ℤ, a.natAbs = n →
      a ^ 2 = (2 : ℤ) * b ^ 2 + 5 * c ^ 2 → a = 0 ∧ b = 0 ∧ c = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a b c ha heq
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · have ha0 : a = 0 := Int.natAbs_eq_zero.mp (by omega)
        subst ha0
        refine ⟨rfl, ?_, ?_⟩
        · exact sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg c]) (sq_nonneg b))
        · exact sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg b]) (sq_nonneg c))
      · have hz : (a : ZMod 5) ^ 2 = 2 * (b : ZMod 5) ^ 2 := by
          have h : ((a ^ 2 : ℤ) : ZMod 5) = ((2 * b ^ 2 + 5 * c ^ 2 : ℤ) : ZMod 5) := by
            rw [heq]
          push_cast at h
          rw [show (5 : ZMod 5) = 0 from by decide, zero_mul, add_zero] at h
          exact h
        rw [zmod_5_a_sq_eq_two_b_sq_iff] at hz
        have hda : (5 : ℤ) ∣ a := (ZMod.intCast_zmod_eq_zero_iff_dvd a 5).mp hz.1
        have hdb : (5 : ℤ) ∣ b := (ZMod.intCast_zmod_eq_zero_iff_dvd b 5).mp hz.2
        obtain ⟨a', rfl⟩ := hda
        obtain ⟨b', rfl⟩ := hdb
        have h5 : (5 : ℤ) * c ^ 2 = 5 * (5 * (a' ^ 2 - 2 * b' ^ 2)) := by
          linear_combination -heq
        have hc2 : c ^ 2 = 5 * (a' ^ 2 - 2 * b' ^ 2) :=
          mul_left_cancel₀ (by norm_num : (5 : ℤ) ≠ 0) h5
        have hdc : (5 : ℤ) ∣ c := by
          have hp : Prime (5 : ℤ) := by norm_num
          exact hp.dvd_of_dvd_pow (⟨a' ^ 2 - 2 * b' ^ 2, hc2⟩ : (5 : ℤ) ∣ c ^ 2)
        obtain ⟨c', rfl⟩ := hdc
        have heq' : a' ^ 2 = (2 : ℤ) * b' ^ 2 + 5 * c' ^ 2 := by
          have h25 : (5 : ℤ) * a' ^ 2 = 5 * (2 * b' ^ 2 + 5 * c' ^ 2) := by
            linear_combination -hc2
          exact mul_left_cancel₀ (by norm_num : (5 : ℤ) ≠ 0) h25
        have hmeas : a'.natAbs < n := by
          have h5nat : (5 : ℤ).natAbs = 5 := by decide
          rw [Int.natAbs_mul, h5nat] at ha
          omega
        obtain ⟨ha0, hb0, hc0⟩ := ih a'.natAbs hmeas a' b' c' rfl heq'
        subst ha0; subst hb0; subst hc0
        refine ⟨by ring, by ring, by ring⟩
  intro a b c heq
  exact key a.natAbs a b c rfl heq

/-- The axis-vs-plane safety predicate for a prime pair `(p, q)`.
    Asserts that none of the three QR equations A/B/C admits a
    non-trivial integer solution. This is the **necessary** condition
    on `(p, q)` for the lattice `L_{p, q}` to satisfy the
    `fourPointProperty` along axis-vs-plane equidistant 4-tuples.

    Per S2c PREP §6.1, the corresponding full-rank safety statement is
    separately axiomatized (Mathlib v4.26.0 lacks the ternary
    Hasse-Minkowski infrastructure to discharge it as a theorem). -/
def SafePrimePair_AxisVsPlane (p q : ℕ) : Prop :=
  (∀ a b c : ℤ, (q : ℤ) * c ^ 2 = a ^ 2 + (p : ℤ) * b ^ 2 → a = 0 ∧ b = 0 ∧ c = 0) ∧
  (∀ a b c : ℤ, (p : ℤ) * b ^ 2 = a ^ 2 + (q : ℤ) * c ^ 2 → a = 0 ∧ b = 0 ∧ c = 0) ∧
  (∀ a b c : ℤ, a ^ 2 = (p : ℤ) * b ^ 2 + (q : ℤ) * c ^ 2 → a = 0 ∧ b = 0 ∧ c = 0)

/-- **The main axis-vs-plane safety theorem for the prime pair
    `(p, q) = (2, 5)`.**

    Derived as the conjunction of `safe_A_holds`, `safe_B_holds`, and
    `safe_C_holds`, each now **proved** by infinite descent (S4 ACT). This
    completes the axis-vs-plane half of the `L_{2, 5}` safety story. The
    full-rank half is a separate future axiomatisation per S2c PREP §6.1. -/
theorem safe_2_5_axis_vs_plane : SafePrimePair_AxisVsPlane 2 5 :=
  ⟨safe_A_holds, safe_B_holds, safe_C_holds⟩

/-! ## S7 ACT — axis-vs-plane safety for the prime pair `(3, 5)`

The three theorems below mirror `safe_{A,B,C}_holds` 1:1, with the coefficient
`2` swapped for `3` in the QR analysis and the mod-5 helpers
(`zmod_5_a_sq_plus_3_b_sq_eq_zero_iff`, `zmod_5_a_sq_eq_three_b_sq_iff`)
replacing their `(2, 5)` counterparts. The descent skeleton is identical;
correctness was checked via the QR reduction tables in
`research/problems/erdos-659-oq-01-oq-02/sessions/2026-06-04-s7-prep-2-3-5-axis-vs-plane-recipe.md`. -/

/-- **(S7 ACT — axis-vs-plane equation A' for `(p, q) = (3, 5)`).**
    `5 c² = a² + 3 b²` has only `(0, 0, 0)`.

    Infinite descent on `c.natAbs`: mod 5 (via
    `zmod_5_a_sq_plus_3_b_sq_eq_zero_iff`, i.e. `−3` is not a QR mod 5)
    forces `5 ∣ a`, `5 ∣ b`, then `5 ∣ c`. -/
theorem safe_A_3_5_holds :
    ∀ a b c : ℤ, (5 : ℤ) * c ^ 2 = a ^ 2 + 3 * b ^ 2 → a = 0 ∧ b = 0 ∧ c = 0 := by
  have key : ∀ n : ℕ, ∀ a b c : ℤ, c.natAbs = n →
      (5 : ℤ) * c ^ 2 = a ^ 2 + 3 * b ^ 2 → a = 0 ∧ b = 0 ∧ c = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a b c hc heq
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · have hc0 : c = 0 := Int.natAbs_eq_zero.mp (by omega)
        subst hc0
        refine ⟨?_, ?_, rfl⟩
        · exact sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg b]) (sq_nonneg a))
        · exact sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg a]) (sq_nonneg b))
      · have hz : (a : ZMod 5) ^ 2 + 3 * (b : ZMod 5) ^ 2 = 0 := by
          have h : ((a ^ 2 + 3 * b ^ 2 : ℤ) : ZMod 5) = ((5 * c ^ 2 : ℤ) : ZMod 5) := by
            rw [heq]
          push_cast at h
          rw [show (5 : ZMod 5) = 0 from by decide, zero_mul] at h
          exact h
        rw [zmod_5_a_sq_plus_3_b_sq_eq_zero_iff] at hz
        have hda : (5 : ℤ) ∣ a := (ZMod.intCast_zmod_eq_zero_iff_dvd a 5).mp hz.1
        have hdb : (5 : ℤ) ∣ b := (ZMod.intCast_zmod_eq_zero_iff_dvd b 5).mp hz.2
        obtain ⟨a', rfl⟩ := hda
        obtain ⟨b', rfl⟩ := hdb
        have h5 : (5 : ℤ) * c ^ 2 = 5 * (5 * (a' ^ 2 + 3 * b' ^ 2)) := by
          linear_combination heq
        have hc2 : c ^ 2 = 5 * (a' ^ 2 + 3 * b' ^ 2) :=
          mul_left_cancel₀ (by norm_num : (5 : ℤ) ≠ 0) h5
        have hdc : (5 : ℤ) ∣ c := by
          have hp : Prime (5 : ℤ) := by norm_num
          exact hp.dvd_of_dvd_pow (⟨a' ^ 2 + 3 * b' ^ 2, hc2⟩ : (5 : ℤ) ∣ c ^ 2)
        obtain ⟨c', rfl⟩ := hdc
        have heq' : (5 : ℤ) * c' ^ 2 = a' ^ 2 + 3 * b' ^ 2 := by
          have h25 : (5 : ℤ) * (5 * c' ^ 2) = 5 * (a' ^ 2 + 3 * b' ^ 2) := by
            linear_combination hc2
          exact mul_left_cancel₀ (by norm_num : (5 : ℤ) ≠ 0) h25
        have hmeas : c'.natAbs < n := by
          have h5nat : (5 : ℤ).natAbs = 5 := by decide
          rw [Int.natAbs_mul, h5nat] at hc
          omega
        obtain ⟨ha0, hb0, hc0⟩ := ih c'.natAbs hmeas a' b' c' rfl heq'
        subst ha0; subst hb0; subst hc0
        refine ⟨by ring, by ring, by ring⟩
  intro a b c heq
  exact key c.natAbs a b c rfl heq

/-- **(S7 ACT — axis-vs-plane equation B' for `(p, q) = (3, 5)`).**
    `3 b² = a² + 5 c²` has only `(0, 0, 0)`.

    Infinite descent on `b.natAbs`: mod 5 (via `zmod_5_a_sq_eq_three_b_sq_iff`,
    i.e. `3` is not a QR mod 5) forces `5 ∣ a`, `5 ∣ b`, then `5 ∣ c`. -/
theorem safe_B_3_5_holds :
    ∀ a b c : ℤ, (3 : ℤ) * b ^ 2 = a ^ 2 + 5 * c ^ 2 → a = 0 ∧ b = 0 ∧ c = 0 := by
  have key : ∀ n : ℕ, ∀ a b c : ℤ, b.natAbs = n →
      (3 : ℤ) * b ^ 2 = a ^ 2 + 5 * c ^ 2 → a = 0 ∧ b = 0 ∧ c = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a b c hb heq
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · have hb0 : b = 0 := Int.natAbs_eq_zero.mp (by omega)
        subst hb0
        refine ⟨?_, rfl, ?_⟩
        · exact sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg c]) (sq_nonneg a))
        · exact sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg a]) (sq_nonneg c))
      · have hz : (a : ZMod 5) ^ 2 = 3 * (b : ZMod 5) ^ 2 := by
          have h : ((3 * b ^ 2 : ℤ) : ZMod 5) = ((a ^ 2 + 5 * c ^ 2 : ℤ) : ZMod 5) := by
            rw [heq]
          push_cast at h
          rw [show (5 : ZMod 5) = 0 from by decide, zero_mul, add_zero] at h
          exact h.symm
        rw [zmod_5_a_sq_eq_three_b_sq_iff] at hz
        have hda : (5 : ℤ) ∣ a := (ZMod.intCast_zmod_eq_zero_iff_dvd a 5).mp hz.1
        have hdb : (5 : ℤ) ∣ b := (ZMod.intCast_zmod_eq_zero_iff_dvd b 5).mp hz.2
        obtain ⟨a', rfl⟩ := hda
        obtain ⟨b', rfl⟩ := hdb
        have h5 : (5 : ℤ) * c ^ 2 = 5 * (5 * (3 * b' ^ 2 - a' ^ 2)) := by
          linear_combination -heq
        have hc2 : c ^ 2 = 5 * (3 * b' ^ 2 - a' ^ 2) :=
          mul_left_cancel₀ (by norm_num : (5 : ℤ) ≠ 0) h5
        have hdc : (5 : ℤ) ∣ c := by
          have hp : Prime (5 : ℤ) := by norm_num
          exact hp.dvd_of_dvd_pow (⟨3 * b' ^ 2 - a' ^ 2, hc2⟩ : (5 : ℤ) ∣ c ^ 2)
        obtain ⟨c', rfl⟩ := hdc
        have heq' : (3 : ℤ) * b' ^ 2 = a' ^ 2 + 5 * c' ^ 2 := by
          have h25 : (5 : ℤ) * (3 * b' ^ 2) = 5 * (a' ^ 2 + 5 * c' ^ 2) := by
            linear_combination -hc2
          exact mul_left_cancel₀ (by norm_num : (5 : ℤ) ≠ 0) h25
        have hmeas : b'.natAbs < n := by
          have h5nat : (5 : ℤ).natAbs = 5 := by decide
          rw [Int.natAbs_mul, h5nat] at hb
          omega
        obtain ⟨ha0, hb0, hc0⟩ := ih b'.natAbs hmeas a' b' c' rfl heq'
        subst ha0; subst hb0; subst hc0
        refine ⟨by ring, by ring, by ring⟩
  intro a b c heq
  exact key b.natAbs a b c rfl heq

/-- **(S7 ACT — axis-vs-plane equation C' for `(p, q) = (3, 5)`).**
    `a² = 3 b² + 5 c²` has only `(0, 0, 0)`.

    Infinite descent on `a.natAbs`: mod 5 (via `zmod_5_a_sq_eq_three_b_sq_iff`)
    forces `5 ∣ a`, `5 ∣ b`, then `5 ∣ c`. -/
theorem safe_C_3_5_holds :
    ∀ a b c : ℤ, a ^ 2 = (3 : ℤ) * b ^ 2 + 5 * c ^ 2 → a = 0 ∧ b = 0 ∧ c = 0 := by
  have key : ∀ n : ℕ, ∀ a b c : ℤ, a.natAbs = n →
      a ^ 2 = (3 : ℤ) * b ^ 2 + 5 * c ^ 2 → a = 0 ∧ b = 0 ∧ c = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a b c ha heq
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · have ha0 : a = 0 := Int.natAbs_eq_zero.mp (by omega)
        subst ha0
        refine ⟨rfl, ?_, ?_⟩
        · exact sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg c]) (sq_nonneg b))
        · exact sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg b]) (sq_nonneg c))
      · have hz : (a : ZMod 5) ^ 2 = 3 * (b : ZMod 5) ^ 2 := by
          have h : ((a ^ 2 : ℤ) : ZMod 5) = ((3 * b ^ 2 + 5 * c ^ 2 : ℤ) : ZMod 5) := by
            rw [heq]
          push_cast at h
          rw [show (5 : ZMod 5) = 0 from by decide, zero_mul, add_zero] at h
          exact h
        rw [zmod_5_a_sq_eq_three_b_sq_iff] at hz
        have hda : (5 : ℤ) ∣ a := (ZMod.intCast_zmod_eq_zero_iff_dvd a 5).mp hz.1
        have hdb : (5 : ℤ) ∣ b := (ZMod.intCast_zmod_eq_zero_iff_dvd b 5).mp hz.2
        obtain ⟨a', rfl⟩ := hda
        obtain ⟨b', rfl⟩ := hdb
        have h5 : (5 : ℤ) * c ^ 2 = 5 * (5 * (a' ^ 2 - 3 * b' ^ 2)) := by
          linear_combination -heq
        have hc2 : c ^ 2 = 5 * (a' ^ 2 - 3 * b' ^ 2) :=
          mul_left_cancel₀ (by norm_num : (5 : ℤ) ≠ 0) h5
        have hdc : (5 : ℤ) ∣ c := by
          have hp : Prime (5 : ℤ) := by norm_num
          exact hp.dvd_of_dvd_pow (⟨a' ^ 2 - 3 * b' ^ 2, hc2⟩ : (5 : ℤ) ∣ c ^ 2)
        obtain ⟨c', rfl⟩ := hdc
        have heq' : a' ^ 2 = (3 : ℤ) * b' ^ 2 + 5 * c' ^ 2 := by
          have h25 : (5 : ℤ) * a' ^ 2 = 5 * (3 * b' ^ 2 + 5 * c' ^ 2) := by
            linear_combination -hc2
          exact mul_left_cancel₀ (by norm_num : (5 : ℤ) ≠ 0) h25
        have hmeas : a'.natAbs < n := by
          have h5nat : (5 : ℤ).natAbs = 5 := by decide
          rw [Int.natAbs_mul, h5nat] at ha
          omega
        obtain ⟨ha0, hb0, hc0⟩ := ih a'.natAbs hmeas a' b' c' rfl heq'
        subst ha0; subst hb0; subst hc0
        refine ⟨by ring, by ring, by ring⟩
  intro a b c heq
  exact key a.natAbs a b c rfl heq

/-- **The main axis-vs-plane safety theorem for the prime pair `(p, q) = (3, 5)`.**

    Derived as the conjunction of `safe_A_3_5_holds`, `safe_B_3_5_holds`, and
    `safe_C_3_5_holds`, each proved by the same QR-descent template as the
    proved `(2, 5)` version. The full-rank half is a separate future
    axiomatisation per S2c PREP §6.1. -/
theorem safe_3_5_axis_vs_plane : SafePrimePair_AxisVsPlane 3 5 :=
  ⟨safe_A_3_5_holds, safe_B_3_5_holds, safe_C_3_5_holds⟩

/-! ## S8 ACT — axis-vs-plane safety for the prime pair `(2, 13)`

The three theorems below mirror `safe_{A,B,C}_holds` 1:1 with the mod-5
helpers swapped for the new mod-13 helpers
(`zmod_13_a_sq_plus_2_b_sq_eq_zero_iff`, `zmod_13_a_sq_eq_two_b_sq_iff`) and
the descent prime `5` swapped for `13`. The coefficient on `b²` stays at `2`,
so the descent skeleton is *closer* to the (2, 5) case than the (3, 5) case
was — the only changes are the modulus and the descent prime. -/

/-- **(S8 ACT — axis-vs-plane equation A for `(p, q) = (2, 13)`).**
    `13 c² = a² + 2 b²` has only `(0, 0, 0)`.

    Infinite descent on `c.natAbs`: mod 13 (via
    `zmod_13_a_sq_plus_2_b_sq_eq_zero_iff`, i.e. `−2` is not a QR mod 13)
    forces `13 ∣ a`, `13 ∣ b`, then `13 ∣ c`. -/
theorem safe_A_2_13_holds :
    ∀ a b c : ℤ, (13 : ℤ) * c ^ 2 = a ^ 2 + 2 * b ^ 2 → a = 0 ∧ b = 0 ∧ c = 0 := by
  have key : ∀ n : ℕ, ∀ a b c : ℤ, c.natAbs = n →
      (13 : ℤ) * c ^ 2 = a ^ 2 + 2 * b ^ 2 → a = 0 ∧ b = 0 ∧ c = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a b c hc heq
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · have hc0 : c = 0 := Int.natAbs_eq_zero.mp (by omega)
        subst hc0
        refine ⟨?_, ?_, rfl⟩
        · exact sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg b]) (sq_nonneg a))
        · exact sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg a]) (sq_nonneg b))
      · have hz : (a : ZMod 13) ^ 2 + 2 * (b : ZMod 13) ^ 2 = 0 := by
          have h : ((a ^ 2 + 2 * b ^ 2 : ℤ) : ZMod 13) = ((13 * c ^ 2 : ℤ) : ZMod 13) := by
            rw [heq]
          push_cast at h
          rw [show (13 : ZMod 13) = 0 from by decide, zero_mul] at h
          exact h
        rw [zmod_13_a_sq_plus_2_b_sq_eq_zero_iff] at hz
        have hda : (13 : ℤ) ∣ a := (ZMod.intCast_zmod_eq_zero_iff_dvd a 13).mp hz.1
        have hdb : (13 : ℤ) ∣ b := (ZMod.intCast_zmod_eq_zero_iff_dvd b 13).mp hz.2
        obtain ⟨a', rfl⟩ := hda
        obtain ⟨b', rfl⟩ := hdb
        have h13 : (13 : ℤ) * c ^ 2 = 13 * (13 * (a' ^ 2 + 2 * b' ^ 2)) := by
          linear_combination heq
        have hc2 : c ^ 2 = 13 * (a' ^ 2 + 2 * b' ^ 2) :=
          mul_left_cancel₀ (by norm_num : (13 : ℤ) ≠ 0) h13
        have hdc : (13 : ℤ) ∣ c := by
          have hp : Prime (13 : ℤ) := by norm_num
          exact hp.dvd_of_dvd_pow (⟨a' ^ 2 + 2 * b' ^ 2, hc2⟩ : (13 : ℤ) ∣ c ^ 2)
        obtain ⟨c', rfl⟩ := hdc
        have heq' : (13 : ℤ) * c' ^ 2 = a' ^ 2 + 2 * b' ^ 2 := by
          have h169 : (13 : ℤ) * (13 * c' ^ 2) = 13 * (a' ^ 2 + 2 * b' ^ 2) := by
            linear_combination hc2
          exact mul_left_cancel₀ (by norm_num : (13 : ℤ) ≠ 0) h169
        have hmeas : c'.natAbs < n := by
          have h13nat : (13 : ℤ).natAbs = 13 := by decide
          rw [Int.natAbs_mul, h13nat] at hc
          omega
        obtain ⟨ha0, hb0, hc0⟩ := ih c'.natAbs hmeas a' b' c' rfl heq'
        subst ha0; subst hb0; subst hc0
        refine ⟨by ring, by ring, by ring⟩
  intro a b c heq
  exact key c.natAbs a b c rfl heq

/-- **(S8 ACT — axis-vs-plane equation B for `(p, q) = (2, 13)`).**
    `2 b² = a² + 13 c²` has only `(0, 0, 0)`.

    Infinite descent on `b.natAbs`: mod 13 (via `zmod_13_a_sq_eq_two_b_sq_iff`,
    i.e. `2` is not a QR mod 13) forces `13 ∣ a`, `13 ∣ b`, then `13 ∣ c`. -/
theorem safe_B_2_13_holds :
    ∀ a b c : ℤ, (2 : ℤ) * b ^ 2 = a ^ 2 + 13 * c ^ 2 → a = 0 ∧ b = 0 ∧ c = 0 := by
  have key : ∀ n : ℕ, ∀ a b c : ℤ, b.natAbs = n →
      (2 : ℤ) * b ^ 2 = a ^ 2 + 13 * c ^ 2 → a = 0 ∧ b = 0 ∧ c = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a b c hb heq
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · have hb0 : b = 0 := Int.natAbs_eq_zero.mp (by omega)
        subst hb0
        refine ⟨?_, rfl, ?_⟩
        · exact sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg c]) (sq_nonneg a))
        · exact sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg a]) (sq_nonneg c))
      · have hz : (a : ZMod 13) ^ 2 = 2 * (b : ZMod 13) ^ 2 := by
          have h : ((2 * b ^ 2 : ℤ) : ZMod 13) = ((a ^ 2 + 13 * c ^ 2 : ℤ) : ZMod 13) := by
            rw [heq]
          push_cast at h
          rw [show (13 : ZMod 13) = 0 from by decide, zero_mul, add_zero] at h
          exact h.symm
        rw [zmod_13_a_sq_eq_two_b_sq_iff] at hz
        have hda : (13 : ℤ) ∣ a := (ZMod.intCast_zmod_eq_zero_iff_dvd a 13).mp hz.1
        have hdb : (13 : ℤ) ∣ b := (ZMod.intCast_zmod_eq_zero_iff_dvd b 13).mp hz.2
        obtain ⟨a', rfl⟩ := hda
        obtain ⟨b', rfl⟩ := hdb
        have h13 : (13 : ℤ) * c ^ 2 = 13 * (13 * (2 * b' ^ 2 - a' ^ 2)) := by
          linear_combination -heq
        have hc2 : c ^ 2 = 13 * (2 * b' ^ 2 - a' ^ 2) :=
          mul_left_cancel₀ (by norm_num : (13 : ℤ) ≠ 0) h13
        have hdc : (13 : ℤ) ∣ c := by
          have hp : Prime (13 : ℤ) := by norm_num
          exact hp.dvd_of_dvd_pow (⟨2 * b' ^ 2 - a' ^ 2, hc2⟩ : (13 : ℤ) ∣ c ^ 2)
        obtain ⟨c', rfl⟩ := hdc
        have heq' : (2 : ℤ) * b' ^ 2 = a' ^ 2 + 13 * c' ^ 2 := by
          have h169 : (13 : ℤ) * (2 * b' ^ 2) = 13 * (a' ^ 2 + 13 * c' ^ 2) := by
            linear_combination -hc2
          exact mul_left_cancel₀ (by norm_num : (13 : ℤ) ≠ 0) h169
        have hmeas : b'.natAbs < n := by
          have h13nat : (13 : ℤ).natAbs = 13 := by decide
          rw [Int.natAbs_mul, h13nat] at hb
          omega
        obtain ⟨ha0, hb0, hc0⟩ := ih b'.natAbs hmeas a' b' c' rfl heq'
        subst ha0; subst hb0; subst hc0
        refine ⟨by ring, by ring, by ring⟩
  intro a b c heq
  exact key b.natAbs a b c rfl heq

/-- **(S8 ACT — axis-vs-plane equation C for `(p, q) = (2, 13)`).**
    `a² = 2 b² + 13 c²` has only `(0, 0, 0)`.

    Infinite descent on `a.natAbs`: mod 13 (via `zmod_13_a_sq_eq_two_b_sq_iff`)
    forces `13 ∣ a`, `13 ∣ b`, then `13 ∣ c`. -/
theorem safe_C_2_13_holds :
    ∀ a b c : ℤ, a ^ 2 = (2 : ℤ) * b ^ 2 + 13 * c ^ 2 → a = 0 ∧ b = 0 ∧ c = 0 := by
  have key : ∀ n : ℕ, ∀ a b c : ℤ, a.natAbs = n →
      a ^ 2 = (2 : ℤ) * b ^ 2 + 13 * c ^ 2 → a = 0 ∧ b = 0 ∧ c = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a b c ha heq
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · have ha0 : a = 0 := Int.natAbs_eq_zero.mp (by omega)
        subst ha0
        refine ⟨rfl, ?_, ?_⟩
        · exact sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg c]) (sq_nonneg b))
        · exact sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg b]) (sq_nonneg c))
      · have hz : (a : ZMod 13) ^ 2 = 2 * (b : ZMod 13) ^ 2 := by
          have h : ((a ^ 2 : ℤ) : ZMod 13) = ((2 * b ^ 2 + 13 * c ^ 2 : ℤ) : ZMod 13) := by
            rw [heq]
          push_cast at h
          rw [show (13 : ZMod 13) = 0 from by decide, zero_mul, add_zero] at h
          exact h
        rw [zmod_13_a_sq_eq_two_b_sq_iff] at hz
        have hda : (13 : ℤ) ∣ a := (ZMod.intCast_zmod_eq_zero_iff_dvd a 13).mp hz.1
        have hdb : (13 : ℤ) ∣ b := (ZMod.intCast_zmod_eq_zero_iff_dvd b 13).mp hz.2
        obtain ⟨a', rfl⟩ := hda
        obtain ⟨b', rfl⟩ := hdb
        have h13 : (13 : ℤ) * c ^ 2 = 13 * (13 * (a' ^ 2 - 2 * b' ^ 2)) := by
          linear_combination -heq
        have hc2 : c ^ 2 = 13 * (a' ^ 2 - 2 * b' ^ 2) :=
          mul_left_cancel₀ (by norm_num : (13 : ℤ) ≠ 0) h13
        have hdc : (13 : ℤ) ∣ c := by
          have hp : Prime (13 : ℤ) := by norm_num
          exact hp.dvd_of_dvd_pow (⟨a' ^ 2 - 2 * b' ^ 2, hc2⟩ : (13 : ℤ) ∣ c ^ 2)
        obtain ⟨c', rfl⟩ := hdc
        have heq' : a' ^ 2 = (2 : ℤ) * b' ^ 2 + 13 * c' ^ 2 := by
          have h169 : (13 : ℤ) * a' ^ 2 = 13 * (2 * b' ^ 2 + 13 * c' ^ 2) := by
            linear_combination -hc2
          exact mul_left_cancel₀ (by norm_num : (13 : ℤ) ≠ 0) h169
        have hmeas : a'.natAbs < n := by
          have h13nat : (13 : ℤ).natAbs = 13 := by decide
          rw [Int.natAbs_mul, h13nat] at ha
          omega
        obtain ⟨ha0, hb0, hc0⟩ := ih a'.natAbs hmeas a' b' c' rfl heq'
        subst ha0; subst hb0; subst hc0
        refine ⟨by ring, by ring, by ring⟩
  intro a b c heq
  exact key a.natAbs a b c rfl heq

/-- **The main axis-vs-plane safety theorem for the prime pair `(p, q) = (2, 13)`.**

    Derived as the conjunction of `safe_A_2_13_holds`, `safe_B_2_13_holds`, and
    `safe_C_2_13_holds`, each proved by the same QR-descent template as the
    proved `(2, 5)` and `(3, 5)` versions. The full-rank half is a separate
    future axiomatisation per S2c PREP §6.1. -/
theorem safe_2_13_axis_vs_plane : SafePrimePair_AxisVsPlane 2 13 :=
  ⟨safe_A_2_13_holds, safe_B_2_13_holds, safe_C_2_13_holds⟩

/-!
### S10 ACT — `(5, 7)` axis-vs-plane safety (mixed-modulus discharge)

Fourth member of the S2a safe-pair family
`{(2,5), (2,13), (3,5), (5,7), (5,13), (7,13), (11,13)}`.  Unlike the three
earlier discharges, which reduce every equation modulo the larger prime, the
`(5, 7)` pair is **mixed-modulus** (S9 PREP, 2026-06-13): `−5 ≡ 2 (mod 7)` is a
quadratic *residue* mod 7, so equation A cannot be killed mod 7.  Instead
equations A and C reduce **mod 5** — where `7 ≡ 2` lets them reuse the existing
`zmod_5_a_sq_eq_two_b_sq_iff` — and only equation B reduces mod 7, needing the
single new helper `zmod_7_a_sq_eq_five_b_sq_iff`.
-/

/-- **(S10 ACT, mod-7 step for equation B on the prime pair `(5, 7)`)**
    `a² ≡ 5 b² (mod 7)` iff both `a ≡ 0` and `b ≡ 0` in `ZMod 7`.
    Equivalent to the assertion that `5` is not a square in `ZMod 7`
    (squares mod 7 are `{0, 1, 2, 4}`; `5` is not among them).
    49-case `decide` check. -/
lemma zmod_7_a_sq_eq_five_b_sq_iff (a b : ZMod 7) :
    a ^ 2 = 5 * b ^ 2 ↔ a = 0 ∧ b = 0 := by
  revert a b
  decide

/-- **(S10 ACT — axis-vs-plane equation A for `(p, q) = (5, 7)`).**
    `7 c² = a² + 5 b²` has only `(0, 0, 0)`.

    Infinite descent on `c.natAbs`, reducing **mod 5** (not mod 7 — `−5 ≡ 2` is
    a QR mod 7): since `7 ≡ 2 (mod 5)`, the equation collapses to
    `a² ≡ 2 c² (mod 5)` and `zmod_5_a_sq_eq_two_b_sq_iff` forces `5 ∣ a`,
    `5 ∣ c`, then `5 ∣ b`. -/
theorem safe_A_5_7_holds :
    ∀ a b c : ℤ, (7 : ℤ) * c ^ 2 = a ^ 2 + 5 * b ^ 2 → a = 0 ∧ b = 0 ∧ c = 0 := by
  have key : ∀ n : ℕ, ∀ a b c : ℤ, c.natAbs = n →
      (7 : ℤ) * c ^ 2 = a ^ 2 + 5 * b ^ 2 → a = 0 ∧ b = 0 ∧ c = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a b c hc heq
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · have hc0 : c = 0 := Int.natAbs_eq_zero.mp (by omega)
        subst hc0
        refine ⟨?_, ?_, rfl⟩
        · exact sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg b]) (sq_nonneg a))
        · exact sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg a]) (sq_nonneg b))
      · have hz : (a : ZMod 5) ^ 2 = 2 * (c : ZMod 5) ^ 2 := by
          have h : ((7 * c ^ 2 : ℤ) : ZMod 5) = ((a ^ 2 + 5 * b ^ 2 : ℤ) : ZMod 5) := by
            rw [heq]
          push_cast at h
          rw [show (5 : ZMod 5) = 0 from by decide,
              show (7 : ZMod 5) = 2 from by decide, zero_mul, add_zero] at h
          exact h.symm
        rw [zmod_5_a_sq_eq_two_b_sq_iff] at hz
        have hda : (5 : ℤ) ∣ a := (ZMod.intCast_zmod_eq_zero_iff_dvd a 5).mp hz.1
        have hdc : (5 : ℤ) ∣ c := (ZMod.intCast_zmod_eq_zero_iff_dvd c 5).mp hz.2
        obtain ⟨a', rfl⟩ := hda
        obtain ⟨c', rfl⟩ := hdc
        have h5b : (5 : ℤ) * b ^ 2 = 5 * (5 * (7 * c' ^ 2 - a' ^ 2)) := by
          linear_combination -heq
        have hb2 : b ^ 2 = 5 * (7 * c' ^ 2 - a' ^ 2) :=
          mul_left_cancel₀ (by norm_num : (5 : ℤ) ≠ 0) h5b
        have hdb : (5 : ℤ) ∣ b := by
          have hp : Prime (5 : ℤ) := by norm_num
          exact hp.dvd_of_dvd_pow (⟨7 * c' ^ 2 - a' ^ 2, hb2⟩ : (5 : ℤ) ∣ b ^ 2)
        obtain ⟨b', rfl⟩ := hdb
        have heq' : (7 : ℤ) * c' ^ 2 = a' ^ 2 + 5 * b' ^ 2 := by
          have h25 : (5 : ℤ) * (7 * c' ^ 2) = 5 * (a' ^ 2 + 5 * b' ^ 2) := by
            linear_combination -hb2
          exact mul_left_cancel₀ (by norm_num : (5 : ℤ) ≠ 0) h25
        have hmeas : c'.natAbs < n := by
          have h5nat : (5 : ℤ).natAbs = 5 := by decide
          rw [Int.natAbs_mul, h5nat] at hc
          omega
        obtain ⟨ha0, hb0, hc0⟩ := ih c'.natAbs hmeas a' b' c' rfl heq'
        subst ha0; subst hb0; subst hc0
        refine ⟨by ring, by ring, by ring⟩
  intro a b c heq
  exact key c.natAbs a b c rfl heq

/-- **(S10 ACT — axis-vs-plane equation B for `(p, q) = (5, 7)`).**
    `5 b² = a² + 7 c²` has only `(0, 0, 0)`.

    Infinite descent on `b.natAbs`: mod 7 (via the new
    `zmod_7_a_sq_eq_five_b_sq_iff`) forces `7 ∣ a`, `7 ∣ b`, then `7 ∣ c`. -/
theorem safe_B_5_7_holds :
    ∀ a b c : ℤ, (5 : ℤ) * b ^ 2 = a ^ 2 + 7 * c ^ 2 → a = 0 ∧ b = 0 ∧ c = 0 := by
  have key : ∀ n : ℕ, ∀ a b c : ℤ, b.natAbs = n →
      (5 : ℤ) * b ^ 2 = a ^ 2 + 7 * c ^ 2 → a = 0 ∧ b = 0 ∧ c = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a b c hb heq
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · have hb0 : b = 0 := Int.natAbs_eq_zero.mp (by omega)
        subst hb0
        refine ⟨?_, rfl, ?_⟩
        · exact sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg c]) (sq_nonneg a))
        · exact sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg a]) (sq_nonneg c))
      · have hz : (a : ZMod 7) ^ 2 = 5 * (b : ZMod 7) ^ 2 := by
          have h : ((5 * b ^ 2 : ℤ) : ZMod 7) = ((a ^ 2 + 7 * c ^ 2 : ℤ) : ZMod 7) := by
            rw [heq]
          push_cast at h
          rw [show (7 : ZMod 7) = 0 from by decide, zero_mul, add_zero] at h
          exact h.symm
        rw [zmod_7_a_sq_eq_five_b_sq_iff] at hz
        have hda : (7 : ℤ) ∣ a := (ZMod.intCast_zmod_eq_zero_iff_dvd a 7).mp hz.1
        have hdb : (7 : ℤ) ∣ b := (ZMod.intCast_zmod_eq_zero_iff_dvd b 7).mp hz.2
        obtain ⟨a', rfl⟩ := hda
        obtain ⟨b', rfl⟩ := hdb
        have h7c : (7 : ℤ) * c ^ 2 = 7 * (7 * (5 * b' ^ 2 - a' ^ 2)) := by
          linear_combination -heq
        have hc2 : c ^ 2 = 7 * (5 * b' ^ 2 - a' ^ 2) :=
          mul_left_cancel₀ (by norm_num : (7 : ℤ) ≠ 0) h7c
        have hdc : (7 : ℤ) ∣ c := by
          have hp : Prime (7 : ℤ) := by norm_num
          exact hp.dvd_of_dvd_pow (⟨5 * b' ^ 2 - a' ^ 2, hc2⟩ : (7 : ℤ) ∣ c ^ 2)
        obtain ⟨c', rfl⟩ := hdc
        have heq' : (5 : ℤ) * b' ^ 2 = a' ^ 2 + 7 * c' ^ 2 := by
          have h49 : (7 : ℤ) * (5 * b' ^ 2) = 7 * (a' ^ 2 + 7 * c' ^ 2) := by
            linear_combination -hc2
          exact mul_left_cancel₀ (by norm_num : (7 : ℤ) ≠ 0) h49
        have hmeas : b'.natAbs < n := by
          have h7nat : (7 : ℤ).natAbs = 7 := by decide
          rw [Int.natAbs_mul, h7nat] at hb
          omega
        obtain ⟨ha0, hb0, hc0⟩ := ih b'.natAbs hmeas a' b' c' rfl heq'
        subst ha0; subst hb0; subst hc0
        refine ⟨by ring, by ring, by ring⟩
  intro a b c heq
  exact key b.natAbs a b c rfl heq

/-- **(S10 ACT — axis-vs-plane equation C for `(p, q) = (5, 7)`).**
    `a² = 5 b² + 7 c²` has only `(0, 0, 0)`.

    Infinite descent on `a.natAbs`, reducing **mod 5** (as for equation A):
    `7 ≡ 2 (mod 5)` collapses the equation to `a² ≡ 2 c² (mod 5)`, and
    `zmod_5_a_sq_eq_two_b_sq_iff` forces `5 ∣ a`, `5 ∣ c`, then `5 ∣ b`. -/
theorem safe_C_5_7_holds :
    ∀ a b c : ℤ, a ^ 2 = (5 : ℤ) * b ^ 2 + 7 * c ^ 2 → a = 0 ∧ b = 0 ∧ c = 0 := by
  have key : ∀ n : ℕ, ∀ a b c : ℤ, a.natAbs = n →
      a ^ 2 = (5 : ℤ) * b ^ 2 + 7 * c ^ 2 → a = 0 ∧ b = 0 ∧ c = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a b c ha heq
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · have ha0 : a = 0 := Int.natAbs_eq_zero.mp (by omega)
        subst ha0
        refine ⟨rfl, ?_, ?_⟩
        · exact sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg c]) (sq_nonneg b))
        · exact sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg b]) (sq_nonneg c))
      · have hz : (a : ZMod 5) ^ 2 = 2 * (c : ZMod 5) ^ 2 := by
          have h : ((a ^ 2 : ℤ) : ZMod 5) = ((5 * b ^ 2 + 7 * c ^ 2 : ℤ) : ZMod 5) := by
            rw [heq]
          push_cast at h
          rw [show (5 : ZMod 5) = 0 from by decide,
              show (7 : ZMod 5) = 2 from by decide, zero_mul, zero_add] at h
          exact h
        rw [zmod_5_a_sq_eq_two_b_sq_iff] at hz
        have hda : (5 : ℤ) ∣ a := (ZMod.intCast_zmod_eq_zero_iff_dvd a 5).mp hz.1
        have hdc : (5 : ℤ) ∣ c := (ZMod.intCast_zmod_eq_zero_iff_dvd c 5).mp hz.2
        obtain ⟨a', rfl⟩ := hda
        obtain ⟨c', rfl⟩ := hdc
        have h5b : (5 : ℤ) * b ^ 2 = 5 * (5 * (a' ^ 2 - 7 * c' ^ 2)) := by
          linear_combination -heq
        have hb2 : b ^ 2 = 5 * (a' ^ 2 - 7 * c' ^ 2) :=
          mul_left_cancel₀ (by norm_num : (5 : ℤ) ≠ 0) h5b
        have hdb : (5 : ℤ) ∣ b := by
          have hp : Prime (5 : ℤ) := by norm_num
          exact hp.dvd_of_dvd_pow (⟨a' ^ 2 - 7 * c' ^ 2, hb2⟩ : (5 : ℤ) ∣ b ^ 2)
        obtain ⟨b', rfl⟩ := hdb
        have heq' : a' ^ 2 = (5 : ℤ) * b' ^ 2 + 7 * c' ^ 2 := by
          have h25 : (5 : ℤ) * a' ^ 2 = 5 * (5 * b' ^ 2 + 7 * c' ^ 2) := by
            linear_combination -hb2
          exact mul_left_cancel₀ (by norm_num : (5 : ℤ) ≠ 0) h25
        have hmeas : a'.natAbs < n := by
          have h5nat : (5 : ℤ).natAbs = 5 := by decide
          rw [Int.natAbs_mul, h5nat] at ha
          omega
        obtain ⟨ha0, hb0, hc0⟩ := ih a'.natAbs hmeas a' b' c' rfl heq'
        subst ha0; subst hb0; subst hc0
        refine ⟨by ring, by ring, by ring⟩
  intro a b c heq
  exact key a.natAbs a b c rfl heq

/-- **The main axis-vs-plane safety theorem for the prime pair `(p, q) = (5, 7)`.**

    Fourth discharged member of the S2a safe-pair family, and the first
    requiring the mixed-modulus route (equations A and C mod 5 reusing
    `zmod_5_a_sq_eq_two_b_sq_iff`, equation B mod 7 via the new
    `zmod_7_a_sq_eq_five_b_sq_iff`).  The full-rank half is a separate future
    axiomatisation per S2c PREP §6.1. -/
theorem safe_5_7_axis_vs_plane : SafePrimePair_AxisVsPlane 5 7 :=
  ⟨safe_A_5_7_holds, safe_B_5_7_holds, safe_C_5_7_holds⟩

/-!
### S11 ACT — `(5, 13)` axis-vs-plane safety (mixed-modulus discharge)

Fifth member of the S2a safe-pair family
`{(2,5), (2,13), (3,5), (5,7), (5,13), (7,13), (11,13)}`, following the
mixed-modulus route pre-audited at the S10 close: equations A and C reduce
**mod 5** — where `13 ≡ 3` lets them reuse the existing
`zmod_5_a_sq_eq_three_b_sq_iff` (`3` is not a QR mod 5) — and only equation B
reduces mod 13, needing the single new helper `zmod_13_a_sq_eq_five_b_sq_iff`
(`5` is not a QR mod 13).
-/

/-- **(S11 ACT, mod-13 step for equation B on the prime pair `(5, 13)`)**
    `a² ≡ 5 b² (mod 13)` iff both `a ≡ 0` and `b ≡ 0` in `ZMod 13`.
    Equivalent to the assertion that `5` is not a square in `ZMod 13`
    (squares mod 13 are `{0, 1, 3, 4, 9, 10, 12}`; `5` is not among them).
    169-case `decide` check. -/
lemma zmod_13_a_sq_eq_five_b_sq_iff (a b : ZMod 13) :
    a ^ 2 = 5 * b ^ 2 ↔ a = 0 ∧ b = 0 := by
  revert a b
  decide

/-- **(S11 ACT — axis-vs-plane equation A for `(p, q) = (5, 13)`).**
    `13 c² = a² + 5 b²` has only `(0, 0, 0)`.

    Infinite descent on `c.natAbs`, reducing **mod 5**: since `13 ≡ 3 (mod 5)`,
    the equation collapses to `a² ≡ 3 c² (mod 5)` and
    `zmod_5_a_sq_eq_three_b_sq_iff` forces `5 ∣ a`, `5 ∣ c`, then `5 ∣ b`. -/
theorem safe_A_5_13_holds :
    ∀ a b c : ℤ, (13 : ℤ) * c ^ 2 = a ^ 2 + 5 * b ^ 2 → a = 0 ∧ b = 0 ∧ c = 0 := by
  have key : ∀ n : ℕ, ∀ a b c : ℤ, c.natAbs = n →
      (13 : ℤ) * c ^ 2 = a ^ 2 + 5 * b ^ 2 → a = 0 ∧ b = 0 ∧ c = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a b c hc heq
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · have hc0 : c = 0 := Int.natAbs_eq_zero.mp (by omega)
        subst hc0
        refine ⟨?_, ?_, rfl⟩
        · exact sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg b]) (sq_nonneg a))
        · exact sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg a]) (sq_nonneg b))
      · have hz : (a : ZMod 5) ^ 2 = 3 * (c : ZMod 5) ^ 2 := by
          have h : ((13 * c ^ 2 : ℤ) : ZMod 5) = ((a ^ 2 + 5 * b ^ 2 : ℤ) : ZMod 5) := by
            rw [heq]
          push_cast at h
          rw [show (5 : ZMod 5) = 0 from by decide,
              show (13 : ZMod 5) = 3 from by decide, zero_mul, add_zero] at h
          exact h.symm
        rw [zmod_5_a_sq_eq_three_b_sq_iff] at hz
        have hda : (5 : ℤ) ∣ a := (ZMod.intCast_zmod_eq_zero_iff_dvd a 5).mp hz.1
        have hdc : (5 : ℤ) ∣ c := (ZMod.intCast_zmod_eq_zero_iff_dvd c 5).mp hz.2
        obtain ⟨a', rfl⟩ := hda
        obtain ⟨c', rfl⟩ := hdc
        have h5b : (5 : ℤ) * b ^ 2 = 5 * (5 * (13 * c' ^ 2 - a' ^ 2)) := by
          linear_combination -heq
        have hb2 : b ^ 2 = 5 * (13 * c' ^ 2 - a' ^ 2) :=
          mul_left_cancel₀ (by norm_num : (5 : ℤ) ≠ 0) h5b
        have hdb : (5 : ℤ) ∣ b := by
          have hp : Prime (5 : ℤ) := by norm_num
          exact hp.dvd_of_dvd_pow (⟨13 * c' ^ 2 - a' ^ 2, hb2⟩ : (5 : ℤ) ∣ b ^ 2)
        obtain ⟨b', rfl⟩ := hdb
        have heq' : (13 : ℤ) * c' ^ 2 = a' ^ 2 + 5 * b' ^ 2 := by
          have h25 : (5 : ℤ) * (13 * c' ^ 2) = 5 * (a' ^ 2 + 5 * b' ^ 2) := by
            linear_combination -hb2
          exact mul_left_cancel₀ (by norm_num : (5 : ℤ) ≠ 0) h25
        have hmeas : c'.natAbs < n := by
          have h5nat : (5 : ℤ).natAbs = 5 := by decide
          rw [Int.natAbs_mul, h5nat] at hc
          omega
        obtain ⟨ha0, hb0, hc0⟩ := ih c'.natAbs hmeas a' b' c' rfl heq'
        subst ha0; subst hb0; subst hc0
        refine ⟨by ring, by ring, by ring⟩
  intro a b c heq
  exact key c.natAbs a b c rfl heq

/-- **(S11 ACT — axis-vs-plane equation B for `(p, q) = (5, 13)`).**
    `5 b² = a² + 13 c²` has only `(0, 0, 0)`.

    Infinite descent on `b.natAbs`: mod 13 (via the new
    `zmod_13_a_sq_eq_five_b_sq_iff`) forces `13 ∣ a`, `13 ∣ b`, then `13 ∣ c`. -/
theorem safe_B_5_13_holds :
    ∀ a b c : ℤ, (5 : ℤ) * b ^ 2 = a ^ 2 + 13 * c ^ 2 → a = 0 ∧ b = 0 ∧ c = 0 := by
  have key : ∀ n : ℕ, ∀ a b c : ℤ, b.natAbs = n →
      (5 : ℤ) * b ^ 2 = a ^ 2 + 13 * c ^ 2 → a = 0 ∧ b = 0 ∧ c = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a b c hb heq
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · have hb0 : b = 0 := Int.natAbs_eq_zero.mp (by omega)
        subst hb0
        refine ⟨?_, rfl, ?_⟩
        · exact sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg c]) (sq_nonneg a))
        · exact sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg a]) (sq_nonneg c))
      · have hz : (a : ZMod 13) ^ 2 = 5 * (b : ZMod 13) ^ 2 := by
          have h : ((5 * b ^ 2 : ℤ) : ZMod 13) = ((a ^ 2 + 13 * c ^ 2 : ℤ) : ZMod 13) := by
            rw [heq]
          push_cast at h
          rw [show (13 : ZMod 13) = 0 from by decide, zero_mul, add_zero] at h
          exact h.symm
        rw [zmod_13_a_sq_eq_five_b_sq_iff] at hz
        have hda : (13 : ℤ) ∣ a := (ZMod.intCast_zmod_eq_zero_iff_dvd a 13).mp hz.1
        have hdb : (13 : ℤ) ∣ b := (ZMod.intCast_zmod_eq_zero_iff_dvd b 13).mp hz.2
        obtain ⟨a', rfl⟩ := hda
        obtain ⟨b', rfl⟩ := hdb
        have h13c : (13 : ℤ) * c ^ 2 = 13 * (13 * (5 * b' ^ 2 - a' ^ 2)) := by
          linear_combination -heq
        have hc2 : c ^ 2 = 13 * (5 * b' ^ 2 - a' ^ 2) :=
          mul_left_cancel₀ (by norm_num : (13 : ℤ) ≠ 0) h13c
        have hdc : (13 : ℤ) ∣ c := by
          have hp : Prime (13 : ℤ) := by norm_num
          exact hp.dvd_of_dvd_pow (⟨5 * b' ^ 2 - a' ^ 2, hc2⟩ : (13 : ℤ) ∣ c ^ 2)
        obtain ⟨c', rfl⟩ := hdc
        have heq' : (5 : ℤ) * b' ^ 2 = a' ^ 2 + 13 * c' ^ 2 := by
          have h169 : (13 : ℤ) * (5 * b' ^ 2) = 13 * (a' ^ 2 + 13 * c' ^ 2) := by
            linear_combination -hc2
          exact mul_left_cancel₀ (by norm_num : (13 : ℤ) ≠ 0) h169
        have hmeas : b'.natAbs < n := by
          have h13nat : (13 : ℤ).natAbs = 13 := by decide
          rw [Int.natAbs_mul, h13nat] at hb
          omega
        obtain ⟨ha0, hb0, hc0⟩ := ih b'.natAbs hmeas a' b' c' rfl heq'
        subst ha0; subst hb0; subst hc0
        refine ⟨by ring, by ring, by ring⟩
  intro a b c heq
  exact key b.natAbs a b c rfl heq

/-- **(S11 ACT — axis-vs-plane equation C for `(p, q) = (5, 13)`).**
    `a² = 5 b² + 13 c²` has only `(0, 0, 0)`.

    Infinite descent on `a.natAbs`, reducing **mod 5** (as for equation A):
    `13 ≡ 3 (mod 5)` collapses the equation to `a² ≡ 3 c² (mod 5)`, and
    `zmod_5_a_sq_eq_three_b_sq_iff` forces `5 ∣ a`, `5 ∣ c`, then `5 ∣ b`. -/
theorem safe_C_5_13_holds :
    ∀ a b c : ℤ, a ^ 2 = (5 : ℤ) * b ^ 2 + 13 * c ^ 2 → a = 0 ∧ b = 0 ∧ c = 0 := by
  have key : ∀ n : ℕ, ∀ a b c : ℤ, a.natAbs = n →
      a ^ 2 = (5 : ℤ) * b ^ 2 + 13 * c ^ 2 → a = 0 ∧ b = 0 ∧ c = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a b c ha heq
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · have ha0 : a = 0 := Int.natAbs_eq_zero.mp (by omega)
        subst ha0
        refine ⟨rfl, ?_, ?_⟩
        · exact sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg c]) (sq_nonneg b))
        · exact sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg b]) (sq_nonneg c))
      · have hz : (a : ZMod 5) ^ 2 = 3 * (c : ZMod 5) ^ 2 := by
          have h : ((a ^ 2 : ℤ) : ZMod 5) = ((5 * b ^ 2 + 13 * c ^ 2 : ℤ) : ZMod 5) := by
            rw [heq]
          push_cast at h
          rw [show (5 : ZMod 5) = 0 from by decide,
              show (13 : ZMod 5) = 3 from by decide, zero_mul, zero_add] at h
          exact h
        rw [zmod_5_a_sq_eq_three_b_sq_iff] at hz
        have hda : (5 : ℤ) ∣ a := (ZMod.intCast_zmod_eq_zero_iff_dvd a 5).mp hz.1
        have hdc : (5 : ℤ) ∣ c := (ZMod.intCast_zmod_eq_zero_iff_dvd c 5).mp hz.2
        obtain ⟨a', rfl⟩ := hda
        obtain ⟨c', rfl⟩ := hdc
        have h5b : (5 : ℤ) * b ^ 2 = 5 * (5 * (a' ^ 2 - 13 * c' ^ 2)) := by
          linear_combination -heq
        have hb2 : b ^ 2 = 5 * (a' ^ 2 - 13 * c' ^ 2) :=
          mul_left_cancel₀ (by norm_num : (5 : ℤ) ≠ 0) h5b
        have hdb : (5 : ℤ) ∣ b := by
          have hp : Prime (5 : ℤ) := by norm_num
          exact hp.dvd_of_dvd_pow (⟨a' ^ 2 - 13 * c' ^ 2, hb2⟩ : (5 : ℤ) ∣ b ^ 2)
        obtain ⟨b', rfl⟩ := hdb
        have heq' : a' ^ 2 = (5 : ℤ) * b' ^ 2 + 13 * c' ^ 2 := by
          have h25 : (5 : ℤ) * a' ^ 2 = 5 * (5 * b' ^ 2 + 13 * c' ^ 2) := by
            linear_combination -hb2
          exact mul_left_cancel₀ (by norm_num : (5 : ℤ) ≠ 0) h25
        have hmeas : a'.natAbs < n := by
          have h5nat : (5 : ℤ).natAbs = 5 := by decide
          rw [Int.natAbs_mul, h5nat] at ha
          omega
        obtain ⟨ha0, hb0, hc0⟩ := ih a'.natAbs hmeas a' b' c' rfl heq'
        subst ha0; subst hb0; subst hc0
        refine ⟨by ring, by ring, by ring⟩
  intro a b c heq
  exact key a.natAbs a b c rfl heq

/-- **The main axis-vs-plane safety theorem for the prime pair `(p, q) = (5, 13)`.**

    Fifth discharged member of the S2a safe-pair family, via the same
    mixed-modulus route as `(5, 7)` (equations A and C mod 5 reusing
    `zmod_5_a_sq_eq_three_b_sq_iff`, equation B mod 13 via the new
    `zmod_13_a_sq_eq_five_b_sq_iff`).  The full-rank half is a separate future
    axiomatisation per S2c PREP §6.1. -/
theorem safe_5_13_axis_vs_plane : SafePrimePair_AxisVsPlane 5 13 :=
  ⟨safe_A_5_13_holds, safe_B_5_13_holds, safe_C_5_13_holds⟩

end Erdos659OQ01OQ02
