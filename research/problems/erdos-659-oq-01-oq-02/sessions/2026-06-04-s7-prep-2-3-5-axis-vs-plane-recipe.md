# S7 PREP-2 — (3, 5) Axis-vs-Plane Safety: Paste-Ready Recipe

**Date**: 2026-06-04
**Author**: researcher-1
**Mode**: PREP (doc-only)
**Predecessor**: S6 STATE-SYNC (#22… 2026-06-01) absorbed S4 ACT #20921
**Outcome**: Paste-ready Lean recipe for `safe_3_5_axis_vs_plane`, the second
member of the {(2,5), (2,13), (3,5), (5,7), (5,13), (7,13), (11,13)} safe-pair
family identified by S2a OBSERVE PR #18494. Sorries/axiom delta: 0 (PREP only).

## Why (3, 5) and not (2, 13) etc.

S6 STATE-SYNC §"Next-action menu (post S4 ACT discharge)" lists three candidates:

1. Full-rank safety for (2,5) — needs ternary Hasse-Minkowski (S2c §5.6: not in
   Mathlib v4.26.0), so either elementary descent (research-level) or axiom.
2. Generalise axis-vs-plane to another safe prime pair.
3. Assemble the Θ(n^{2/3}) rate (needs S3/S4 plan axiomatisations on top).

This PREP picks **candidate (2) with the (3, 5) pair**. Justification:

- **Mechanically closest to the proved (2, 5)** — both `p` and `q` are small;
  both equations reduce mod 5 (the same residue class as the proved file). No
  new prime-base choice is needed.
- **One mod-5 helper reused, one new helper** — the existing
  `zmod_5_a_sq_eq_two_b_sq_iff` (covers `a² ≡ 2 b² (mod 5)`) handled both
  equations B and C for (2, 5). For (3, 5), equation A becomes
  `5 c² = a² + 3 b²` (new mod-5 fact); equations B/C reduce to
  `a² ≡ 3 b² (mod 5)` (also new — a different non-residue).
- **Lowest LOC** — re-uses the entire descent skeleton verbatim, swapping
  only the coefficient `2 → 3` in the QR analysis and the substitution arithmetic.
- **(2, 13) requires mod-13 helpers** — 13² = 169 cases each for a `decide`
  closure, still tractable but ~4–7× longer to verify by `decide` and
  introduces a new modulus (no helper reuse). Strictly worse first step than
  (3, 5).
- **(5, 7), (5, 13), (7, 13), (11, 13)** all introduce mod-7, mod-11, or mod-13
  reductions; none of them re-uses any existing helper.

So (3, 5) is the strict next minimum.

## QR analysis (the meat of the recipe)

For the prime pair `(p, q) = (3, 5)`, the three axis-vs-plane equations are
the same three patterns as (2, 5) with `p = 3`:

```
(A')   5 c² = a² + 3 b²
(B')   3 b² = a² + 5 c²
(C')   a²    = 3 b² + 5 c²
```

### Mod-5 reduction tables

Squares mod 5: `{0, 1, 4}` (from `a² mod 5` for `a ∈ {0, ±1, ±2}`).

#### Equation A' — `a² + 3 b² ≡ 0 (mod 5)`

`3 b² mod 5` ∈ `{0, 3, 12 mod 5 = 2}`. Sums `a² + 3 b² mod 5`:

| `a²` \ `3 b²` | 0 | 3 | 2 |
|---:|:--:|:--:|:--:|
| 0 | **0** | 3 | 2 |
| 1 | 1 | 4 | 3 |
| 4 | 4 | 2 | 1 |

The only `0` lies at `(a², 3 b²) = (0, 0)`, forcing `a ≡ 0 ∧ b ≡ 0 (mod 5)`.

This is the **first** new helper:

```lean
/-- **(S7 ACT, mod-5 step for equation A' on (3, 5))** `a² + 3 b² ≡ 0 (mod 5)`
    iff both `a ≡ 0` and `b ≡ 0` in `ZMod 5`. Equivalent to the assertion that
    `−3` is not a square in `ZMod 5`. -/
lemma zmod_5_a_sq_plus_3_b_sq_eq_zero_iff (a b : ZMod 5) :
    a ^ 2 + 3 * b ^ 2 = 0 ↔ a = 0 ∧ b = 0 := by
  revert a b
  decide
```

#### Equations B' and C' — `a² ≡ 3 b² (mod 5)`

`3 b² mod 5` ∈ `{0, 3, 2}` (same row). Equal-pairs with `a² ∈ {0, 1, 4}`:

| `a²` | `= 3 b² ∈ {0, 3, 2}` ? |
|---:|:--|
| 0 | only `3 b² = 0`, i.e. `b ≡ 0` |
| 1 | never |
| 4 | never |

Only `(a², 3 b²) = (0, 0)` works.

This is the **second** new helper:

```lean
/-- **(S7 ACT, mod-5 step for equations B' and C' on (3, 5))** `a² ≡ 3 b² (mod 5)`
    iff both `a ≡ 0` and `b ≡ 0` in `ZMod 5`. Equivalent to the assertion that
    `3` is not a square in `ZMod 5`. -/
lemma zmod_5_a_sq_eq_three_b_sq_iff (a b : ZMod 5) :
    a ^ 2 = 3 * b ^ 2 ↔ a = 0 ∧ b = 0 := by
  revert a b
  decide
```

Both `decide` checks are 25-case enumerations over `ZMod 5 × ZMod 5`. Mathlib
v4.26.0 provides `Decidable` for `=` and `+`, `*` on `ZMod n`, so this closes
without further plumbing (same as the existing `zmod_5_a_sq_{...}` lemmas).

### Why a single modulus suffices

For the (2, 5) descent on equation B (`2 b² = a² + 5 c²`), one could in
principle reduce mod 2 instead of mod 5. The mod-5 choice is preferred because
all three equations A/B/C are simultaneously controlled by a single small prime.
For (3, 5), the same observation applies: mod 5 controls A' (via the
`−3 NQR mod 5` fact) and B'/C' (via the `3 NQR mod 5` fact). A mod-3 reduction
would only nail equation A' (via the `5 c² ≡ a² (mod 3)` ↔ `a² ≡ 2 c² (mod 3)`,
where `2 ≡ −1` is NQR mod 3), but B' has `3 b² = a² + 5 c²` which mod 3 gives
`0 ≡ a² + 2 c²`, and the residues `(a², c²) ∈ {0, 1}²` admit `(1, 1)` as a
non-trivial solution (`1 + 2 = 3 ≡ 0`). So mod 3 alone does **not** force the
trivial solution. **Stick with mod 5.**

## Paste-ready descent bodies

Each of the three `safe_*_holds` proofs is structurally identical to the
proved (2, 5) version (`proofs/Proofs/Erdos659OQ01OQ02.lean`:120-264). The
substitution arithmetic differs only in the coefficient `2 → 3` and the
choice of helper.

### safe_A'_holds (descent on `c.natAbs`)

Mirrors `safe_A_holds` (file lines 120-164) with three small replacements:

| Step | (2, 5) | (3, 5) |
|---:|:---|:---|
| Equation | `5 c² = a² + 2 b²` | `5 c² = a² + 3 b²` |
| Mod-5 helper | `zmod_5_a_sq_plus_2_b_sq_eq_zero_iff` | `zmod_5_a_sq_plus_3_b_sq_eq_zero_iff` |
| Substitution arithmetic | `5 (a'² + 2 b'²)` | `5 (a'² + 3 b'²)` |
| `linear_combination` factor | `heq` | `heq` |

```lean
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
```

LOC: 42 (same as `safe_A_holds`).

### safe_B'_holds (descent on `b.natAbs`)

Mirrors `safe_B_holds` (file lines 171-215) with:

| Step | (2, 5) | (3, 5) |
|---:|:---|:---|
| Equation | `2 b² = a² + 5 c²` | `3 b² = a² + 5 c²` |
| Mod-5 helper | `zmod_5_a_sq_eq_two_b_sq_iff` | `zmod_5_a_sq_eq_three_b_sq_iff` |
| Substitution arithmetic | `5 (2 b'² − a'²)` | `5 (3 b'² − a'²)` |

```lean
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
```

LOC: 45.

### safe_C'_holds (descent on `a.natAbs`)

Mirrors `safe_C_holds` (file lines 222-266) with:

| Step | (2, 5) | (3, 5) |
|---:|:---|:---|
| Equation | `a² = 2 b² + 5 c²` | `a² = 3 b² + 5 c²` |
| Mod-5 helper | `zmod_5_a_sq_eq_two_b_sq_iff` | `zmod_5_a_sq_eq_three_b_sq_iff` |
| Substitution arithmetic | `5 (a'² − 2 b'²)` | `5 (a'² − 3 b'²)` |

```lean
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
```

LOC: 45.

### Composite corollary

```lean
/-- **The main axis-vs-plane safety theorem for the prime pair `(p, q) = (3, 5)`.**
    Derived as the conjunction of `safe_A_3_5_holds`, `safe_B_3_5_holds`, and
    `safe_C_3_5_holds`, each proved by the same QR-descent template as the
    proved (2, 5) version. The full-rank half is a separate future
    axiomatisation per S2c PREP §6.1. -/
theorem safe_3_5_axis_vs_plane : SafePrimePair_AxisVsPlane 3 5 :=
  ⟨safe_A_3_5_holds, safe_B_3_5_holds, safe_C_3_5_holds⟩
```

LOC: 2.

**Total Lean delta**: 2 new helpers (~8 LOC) + 3 new descent theorems
(~132 LOC) + 1 corollary (2 LOC) = **~142 LOC**. Add a 10-line docstring header
block (S7 ACT context), and the file grows from 292 → ~444 LOC.

## Mathlib v4.26.0 verification of the recipe

Every named lemma used in the recipe already loads cleanly in
`proofs/Proofs/Erdos659OQ01OQ02.lean` (Docker-verified GREEN at S4 ACT
#20921). No new imports needed:

| Lemma / tactic | Module | Used in proved (2, 5) | Used in (3, 5) recipe |
|---|---|---|---|
| `ZMod.intCast_zmod_eq_zero_iff_dvd` | `Mathlib/Data/ZMod/Basic.lean` | yes | yes |
| `Int.natAbs_eq_zero` | `Mathlib/Data/Int/Basic.lean` | yes | yes |
| `Int.natAbs_mul` | `Mathlib/Data/Int/Basic.lean` | yes | yes |
| `sq_eq_zero_iff` | `Mathlib/Algebra/GroupPower/Basic.lean` | yes | yes |
| `sq_nonneg` | `Mathlib/Algebra/Order/Ring/Lemmas.lean` | yes | yes |
| `Nat.strong_induction_on` | core / `Mathlib/Init/Data/Nat/Lemmas.lean` | yes | yes |
| `mul_left_cancel₀` | `Mathlib/Algebra/GroupWithZero/Basic.lean` | yes | yes |
| `Prime.dvd_of_dvd_pow` | `Mathlib/RingTheory/Coprime/Basic.lean` | yes | yes |
| `linear_combination` tactic | `Mathlib.Tactic.LinearCombination` | yes | yes |
| `norm_num` / `nlinarith` / `decide` / `push_cast` / `omega` | `Mathlib.Tactic` | yes | yes |

**Conclusion**: zero Mathlib-API risk. The recipe is paste-ready against the
v4.26.0 surface that the proved (2, 5) file already runs against.

## What this PREP does NOT do

- Does **not** ship the Lean implementation (Docker daemon is down per
  `docker info` 2026-06-04T17:54Z; build verification of any S7 ACT
  contribution is currently impossible). The implementation is split into
  a separate **S7 ACT** PR that should ship under the **(build pending —
  Docker daemon down)** convention if Docker is still down at write-time.
- Does **not** touch the proved (2, 5) theorems.
- Does **not** touch `SafePrimePair_AxisVsPlane`'s definition (the
  `(p, q)` parameter is already in place; the new corollary just
  instantiates).
- Does **not** address the **full-rank** half of either pair.
- Does **not** introduce new axioms.

## Risk and honesty notes

- **Risk that mod-5 descent fails for (3, 5)** — none. The mod-5 facts are
  finite-case `decide` verifications; the substitution arithmetic is `ring` /
  `linear_combination` and matches the (2, 5) structure 1:1.
- **Risk that the (3, 5) lattice is not actually safe at the full-rank stratum** —
  this PREP makes no claim about full-rank. S2a OBSERVE PR #18494 §"Empirical
  search" found (3, 5) safe at the full-rank level **empirically up to R ≤ 22**;
  S2c PREP §6.1 recommends axiomatising full-rank for all such pairs until
  Mathlib gains ternary Hasse-Minkowski infrastructure. This PREP inherits that
  recommendation unchanged.
- **Notational convention** — the existing (2, 5) theorems are
  `safe_A`, `safe_B`, `safe_C`, `safe_A_holds`, etc. The (3, 5) recipe uses
  the suffix `_3_5` to disambiguate (e.g., `safe_A_3_5_holds`). If a future
  S7 ACT migrates the proved (2, 5) theorems to the parameterised names
  (`safe_A_2_5_holds` etc.) it will be a separate, cosmetic refactor.

## Next action (S7 ACT)

When Docker comes back up:

1. Open a new branch off `main`, edit `proofs/Proofs/Erdos659OQ01OQ02.lean`
   in place: insert the 2 new mod-5 helpers immediately after
   `zmod_5_a_sq_eq_two_b_sq_iff` (line 80); insert the 3 new descent
   theorems and the corollary immediately before the closing `end
   Erdos659OQ01OQ02` (line 292).
2. `./proofs/scripts/docker-build.sh Proofs.Erdos659OQ01OQ02` from the
   worktree directory (see S4 PREP §"Build status" for the worktree
   mount-path gotcha).
3. Expected diff: +142 LOC, 0 sorries, 0 axioms.
4. PR title: `research(erdos-659-oq-01-oq-02): S7 ACT — discharge axis-vs-plane safety for (3, 5)`.

If Docker is still down, follow the per-branch convention used by S7 ACT
sum-of-divisors (#22238): ship the Lean diff with `(build pending — Docker
daemon down)` in the PR title and commit message.

## Cross-references

- Proved (2, 5) descent: `proofs/Proofs/Erdos659OQ01OQ02.lean`:120-264.
- S2a OBSERVE PR #18494 §"Empirical search" — list of 15 candidate pairs
  with R ≤ 22; the seven flagged "safe" are
  `{(2,5), (2,13), (3,5), (5,7), (5,13), (7,13), (11,13)}`.
- S2b PREP PR #18554 §4–§5 — original QR-descent template for (2, 5).
- S2c PREP PR #18696 §6.1 — typeclass decomposition recommendation.
- S4 PREP-2 PR #19128 — explicit descent body recipe for the (2, 5) sorries.
- S4 ACT PR #20921 — discharge of the (2, 5) sorries (the file this recipe
  extends).
- S6 STATE-SYNC PR (2026-06-01) — absorbed S4 ACT into state.md head + JSON.

---

**Deliverable summary**:

- 1 session memo (this file, ~370 lines)
- 0 Lean changes
- 0 sorry / axiom deltas
- 1 state.md update (S7 PREP-2 head + table entry; iter 12 → 13)
- 1 JSON update (`currentState.focus` + `nextAction` + `lastUpdate` refresh)
