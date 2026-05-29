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

This file ships the **outer scaffold** — the three predicates,
their composite, and the named theorem statements — with the descent
**bodies deferred to S4 ACT** as three strategic sorries. The
descent recipe is fully written out in
`research/problems/erdos-659-oq-01-oq-02/sessions/2026-05-13-s2b-prep-qr-descent-mathlib-audit-for-2-5-pair.md`
§5 (the Lean template) and §7 (generalisation pointer for the other
six safe pairs identified by S2a).

**Scope.** Axis-vs-plane only. Full-rank safety (per S2c PREP §6.1) is
deferred to a separate axiomatisation pending Mathlib Hasse-Minkowski
infrastructure that does not yet exist at v4.26.0.

**Sorries / axioms.** 3 strategic sorries (one per equation); 0 axioms
in this file. Build pending convention applies (recursive `.lake`
symlink in the researcher worktree precludes local `lake build`; the
auditor / next ACT session is expected to verify via the Docker
wrapper).
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

/-- **(STRATEGIC SORRY — S4 ACT, axis-vs-plane equation A).**
    `5 c² = a² + 2 b²` has only `(0, 0, 0)`.

    Proof (deferred): see this file's docstring + S2b PREP §5 template. -/
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

/-- **(STRATEGIC SORRY — S4 ACT, axis-vs-plane equation B).**
    `2 b² = a² + 5 c²` has only `(0, 0, 0)`.

    Proof (deferred): analogous to `safe_A_holds`; see S2b PREP §4.2. -/
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

/-- **(STRATEGIC SORRY — S4 ACT, axis-vs-plane equation C).**
    `a² = 2 b² + 5 c²` has only `(0, 0, 0)`.

    Proof (deferred): analogous to `safe_A_holds`; see S2b PREP §4.3. -/
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
    `safe_C_holds`. Each conjunct is currently a strategic sorry;
    closing all three via the S2b §5 QR-descent template completes the
    axis-vs-plane half of the `L_{2, 5}` safety story. The full-rank
    half is axiomatised separately per S2c PREP §6.1. -/
theorem safe_2_5_axis_vs_plane : SafePrimePair_AxisVsPlane 2 5 :=
  ⟨safe_A_holds, safe_B_holds, safe_C_holds⟩

end Erdos659OQ01OQ02
