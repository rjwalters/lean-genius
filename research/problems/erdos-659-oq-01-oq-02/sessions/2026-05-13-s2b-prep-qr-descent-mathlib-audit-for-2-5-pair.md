# S2b PREP — Mathlib audit + verified descent template for `safe_2_5_axis_vs_plane`

**Slug**: `erdos-659-oq-01-oq-02`
**Phase**: PREP (sub-step 2b — Mathlib API audit follow-up to S2a)
**Author**: researcher-11
**Date**: 2026-05-13
**Scope**: doc-only. Adds **exactly one** new file under `sessions/`. No
edits to `problem.md`, `knowledge.md`, `state.md`, any prior session
file, any Lean source, any gallery JSON, or the candidate pool.

## 1. Position vs in-flight and recently-merged PRs

| PR # | Status | Adds | Refines / depends on |
| ---- | ------ | ---- | -------------------- |
| #18322 | MERGED | S1 OBSERVE survey (`problem.md`, `knowledge.md`, `state.md`) | — |
| #18421 | MERGED | S1b refutation of S1 axiom #1 at `(p, q) = (2, 3)` | refutes S1 |
| #18431 | MERGED | S1c Pell-safety algebraic framework + `(2, 5)` SAFE to `N = 14` | extends S1b |
| #18442 | MERGED | S1d `QuadraticForm.weightedSumSquares` Mathlib recasting | independent |
| #18494 | MERGED | S2a extended search to 15 prime-pair lattices `R ≤ 22`, mod-q QR descent for axis-vs-plane safety | discharges S1c next-action #1 |
| _(this)_ | NEW | S2b Mathlib API audit pinning the three lemmas needed to formalise `safe_2_5_axis_vs_plane` in ~40 LOC; concrete Lean descent template; gap inventory for full-rank safety | extends S2a §6, §8 |

**No file collision.** This session filename
`2026-05-13-s2b-prep-qr-descent-mathlib-audit-for-2-5-pair.md` is
distinct from the five existing session files (`s1`, `s1b`, `s1c`, `s01d`,
`s2a`). No edits outside the new file. Conflict-free against any future
S2 ACT that creates `proofs/Proofs/Erdos659OQ01OQ02.lean` (Lean file
does not yet exist).

## 2. Goal

S2a §8 recommended formalising `SafePrimePair 2 5` for the axis-vs-plane
direction in **"~40 LOC per pair using `Mathlib.NumberTheory.Cyclotomic.PrimeQuadratic`
and `Mathlib.Data.ZMod.Quotient` for QR tests"**.

This PREP **verifies the Mathlib citations** that S2a left informal.
Concretely:

1. The module `Mathlib.NumberTheory.Cyclotomic.PrimeQuadratic` named in
   S2a §8 step 2 **does not exist** in Mathlib v4.26.0 (the cyclotomic
   subdirectory has `Basic`, `CyclotomicCharacter`, `Discriminant`,
   `Embeddings`, `Expand`, `Gal`, `MainComponents`, `Rat`, `Three`, `Zeta`
   — no `PrimeQuadratic`). The QR machinery lives elsewhere (see §3).
2. The module `Mathlib.Data.ZMod.Quotient` does exist, but for the QR-
   descent proof its only role is to provide `ZMod p` arithmetic; the
   load-bearing lemmas come from `Mathlib.NumberTheory.LegendreSymbol.*`.
3. The "~40 LOC per pair" estimate is **revised to ~50 LOC** after
   factoring in the descent infrastructure (no descent tactic exists;
   needs an explicit `Nat.strongRecOn` on `c.natAbs`).

This PREP pins each Mathlib symbol to file+line at commit
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (the rev pinned in
`proofs/lake-manifest.json` for `inputRev: v4.26.0`) and gives a
worked-out 12-line Lean sketch of the load-bearing step for
`safe_2_5_axis_vs_plane`, ready for an S2 ACT agent to lift.

## 3. Verified Mathlib citations at v4.26.0

All paths are relative to the Mathlib4 root at commit
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Each item lists the symbol,
the file:line of the declaration, the signature, and how it is used in
the QR-descent proof.

### 3.1 `ZMod.exists_sq_eq_two_iff` ✓ verified

**File**: `Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean:74`

```lean
theorem ZMod.exists_sq_eq_two_iff (hp : p ≠ 2) :
    IsSquare (2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 7
```

(Requires `[Fact p.Prime]` from the section variable declaration; same
section also requires `(hp : p ≠ 2)`.)

**Specialisation at `p = 5`**: `5 % 8 = 5`. Neither `1` nor `7`, so the
right-hand side is false; the left-hand side `IsSquare (2 : ZMod 5)` is
therefore false.

**Role in descent**: discharges the criterion "2 NQR mod 5" needed for
equations B and C (see §4.2, §4.3).

### 3.2 `ZMod.exists_sq_eq_neg_two_iff` ✓ verified

**File**: `Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean:80`

```lean
theorem ZMod.exists_sq_eq_neg_two_iff (hp : p ≠ 2) :
    IsSquare (-2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 3
```

**Specialisation at `p = 5`**: `5 % 8 = 5`. Neither `1` nor `3`, so RHS
false; `IsSquare (-2 : ZMod 5)` is false.

**Role in descent**: discharges the criterion "−2 NQR mod 5" needed for
equation A (see §4.1).

### 3.3 `Int.Prime.dvd_natAbs_of_coe_dvd_sq` ✓ verified

**File**: `Mathlib/Data/Int/NatPrime.lean:38`

```lean
theorem Int.Prime.dvd_natAbs_of_coe_dvd_sq {p : ℕ} (hp : p.Prime) (k : ℤ)
    (h : (p : ℤ) ∣ k ^ 2) : p ∣ k.natAbs
```

**Role in descent**: each descent step has the form "5 ∣ a² (in ℤ) ⇒
5 ∣ a.natAbs (in ℕ)". Used three times per equation (for `a`, `b`, `c`).

### 3.4 `Nat.Prime.dvd_of_dvd_pow` ✓ verified

**File**: `Mathlib/Data/Nat/Prime/Basic.lean` (used internally by §3.3 at
`NatPrime.lean:40`)

```lean
theorem Nat.Prime.dvd_of_dvd_pow (hp : p.Prime) {n : ℕ} (h : p ∣ a ^ n) : p ∣ a
```

**Role**: backbone of §3.3. May be called directly when working purely
in `ℕ`; otherwise §3.3 is the right form.

### 3.5 Backing characters χ₈, χ₈′ (informational only)

**File**: `Mathlib/NumberTheory/LegendreSymbol/ZModChar.lean`
- `ZMod.χ₈` at line 119 (`MulChar (ZMod 8) ℤ`)
- `ZMod.χ₈'` at line 158
- `ZMod.χ₈_nat_eq_if_mod_eight` at line 151
- `ZMod.χ₈'_nat_eq_if_mod_eight` at line 182

These are the Mathlib characters underlying §3.1 and §3.2. The descent
proof does **not** call them directly; the user-facing `exists_sq_eq_*`
lemmas in §3.1 and §3.2 are the right entry points.

### 3.6 Backing alternative for §3.1 and §3.2 in FiniteField form

**File**: `Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/GaussSum.lean`

```lean
theorem FiniteField.isSquare_two_iff :
    IsSquare (2 : F) ↔ Fintype.card F % 8 ≠ 3 ∧ Fintype.card F % 8 ≠ 5    -- line 43
theorem FiniteField.isSquare_neg_two_iff :
    IsSquare (-2 : F) ↔ Fintype.card F % 8 ≠ 5 ∧ Fintype.card F % 8 ≠ 7   -- line 62
```

Logically equivalent to §3.1 and §3.2 (positive form ↔ complement),
useful if the proof bridges to a general `FiniteField` rather than
`ZMod p`.

### 3.7 `Fact (Nat.Prime 5)` instantiation

There is **no pre-existing named `Fact (Nat.Prime 5)` instance** in
Mathlib v4.26.0 (a search for `Nat.fact_prime_five` returns only
`Counterexamples/Cyclotomic105.lean`, an ad-hoc local definition).

**Standard idiom** for the descent proof:

```lean
haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
```

(Both `decide`s are fast: `Nat.Prime n` decidable + small.)

### 3.8 Phantom module — `Mathlib.NumberTheory.Cyclotomic.PrimeQuadratic`

**S2a §8 step 2 names this module; it does not exist at v4.26.0.**
`Mathlib/NumberTheory/Cyclotomic/` contains: `Basic.lean`,
`CyclotomicCharacter.lean`, `Discriminant.lean`, `Embeddings.lean`,
`Expand.lean`, `Gal.lean`, `MainComponents.lean`, `Rat.lean`, `Three.lean`,
`Zeta.lean`. No `PrimeQuadratic.lean`. **An S2 ACT agent following S2a
verbatim would import a non-existent module.** Replace S2a step 2's
phantom import with the two `LegendreSymbol/` paths from §3.1, §3.2.

### 3.9 Phantom module — Mathlib has no "descent" tactic or schema

There is no analogue of Coq's `Decidable.fix` or a "Fermat descent"
tactic. The natural formalisation uses `Nat.strongRecOn` on
`c.natAbs` (or the sum of natAbs). Mathlib has:

- `Nat.strongRecOn` at `Mathlib/Data/Nat/Basic.lean` (well-founded
  recursion on `< : ℕ → ℕ → Prop`)
- `WellFounded.fix` at `Mathlib/Order/RelClasses.lean` (generic)
- `Nat.le_induction` (forward induction; less useful)

The descent template in §5 uses `Nat.strongRecOn` with `c.natAbs` as
the well-founded measure.

## 4. The QR-descent for `(p, q) = (2, 5)` — three equations

Recall from S2a §5 that `L_{2, 5}` is axis-vs-plane safe iff equations
A, B, C have only the trivial solution in `ℤ³`.

### 4.1 Equation A — `5c² = a² + 2b²`

**Mod-5 step**: `a² + 2b² ≡ 0 (mod 5)`. If `b ≢ 0 (mod 5)`, then
`(a/b)² ≡ -2 (mod 5)`, so `-2` is a square in `ZMod 5`. By §3.2, this
contradicts `5 % 8 = 5 ∉ {1, 3}`. Hence `b ≡ 0 (mod 5)`. Then
`a² ≡ 0 (mod 5)`, so by §3.3 applied to `5 : ℕ` prime and `k = a`,
`5 ∣ a.natAbs`. Substitute `a = 5a'`, `b = 5b'`:
$$5c^2 = 25a'^2 + 50 b'^2 \;\Rightarrow\; c^2 = 5(a'^2 + 2b'^2).$$
So `5 ∣ c²` (in ℤ), hence by §3.3 again `5 ∣ c.natAbs`. Write `c = 5c'`:
$$25c'^2 = 5(a'^2 + 2b'^2) \;\Rightarrow\; 5c'^2 = a'^2 + 2b'^2. \quad \text{(same eq)}$$
Infinite descent on `c.natAbs` gives `(a, b, c) = (0, 0, 0)`. ∎

### 4.2 Equation B — `2b² = a² + 5c²`

**Mod-5 step**: `2b² ≡ a² (mod 5)`. If `b ≢ 0 (mod 5)`, then
`(a/b)² ≡ 2 (mod 5)` (after multiplying by `b⁻²` in `ZMod 5`), so `2`
is a square in `ZMod 5`. By §3.1, this contradicts `5 % 8 = 5 ∉ {1, 7}`.
Hence `b ≡ 0 (mod 5)`. Then `a² ≡ 0 (mod 5)`, so by §3.3 `5 ∣ a.natAbs`.
Substitute `a = 5a'`, `b = 5b'`:
$$2 \cdot 25 b'^2 = 25 a'^2 + 5c^2 \;\Rightarrow\; 10 b'^2 = 5 a'^2 + c^2.$$
So `c² ≡ 0 (mod 5)`, hence `5 ∣ c.natAbs`. Write `c = 5c'`:
$$10 b'^2 = 5 a'^2 + 25 c'^2 \;\Rightarrow\; 2 b'^2 = a'^2 + 5 c'^2. \quad \text{(same eq)}$$
Infinite descent on `b.natAbs` gives `(a, b, c) = (0, 0, 0)`. ∎

### 4.3 Equation C — `a² = 2b² + 5c²`

**Mod-5 step**: `a² ≡ 2b² (mod 5)`. Same analysis as §4.2: if
`b ≢ 0 (mod 5)`, `2` would be a square in `ZMod 5`, contradiction. So
`b ≡ 0 (mod 5)`, hence `a² ≡ 0 (mod 5)`, hence `5 ∣ a.natAbs`. Write
`a = 5a'`, `b = 5b'`:
$$25 a'^2 = 50 b'^2 + 5c^2 \;\Rightarrow\; 5 a'^2 = 10 b'^2 + c^2.$$
So `c² ≡ 0 (mod 5)`, `5 ∣ c.natAbs`, `c = 5c'`:
$$5 a'^2 = 10 b'^2 + 25 c'^2 \;\Rightarrow\; a'^2 = 2 b'^2 + 5 c'^2. \quad \text{(same eq)}$$
Descent on `a.natAbs` gives `(a, b, c) = (0, 0, 0)`. ∎

**Observation**: all three equations descend via **mod-5 only** for the
pair `(p, q) = (2, 5)`. The mod-2 direction in S2a §6.2 is **not
needed** for this specific pair, simplifying the S2 ACT proof. (The
mod-2 direction would be needed if we picked a pair where `5` is
unfortunately QR mod `p` — but here `p = 2`, so the mod-2 direction
collapses trivially since QR mod 2 is degenerate.)

## 5. Lean descent template (concrete, ready to lift into S2 ACT)

The following template captures the load-bearing step of §4.1 (eq A).
Equations B and C have the same structure with `b` ↔ `c` (eq B) or `a`
↔ `c` (eq C) swapped in the descent variable. Total Lean LOC for the
three equations: ~40–50 lines using this template.

```lean
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Data.Int.NatPrime

namespace Erdos659OQ01OQ02.SafePrimePair_2_5

/-- The axis-vs-plane safety predicate for equation A:
    `5 c² = a² + 2 b²` has only the trivial integer solution. -/
def safe_A : Prop := ∀ a b c : ℤ, 5 * c^2 = a^2 + 2 * b^2 → a = 0 ∧ b = 0 ∧ c = 0

/-- The Fact instance — `decide`-able. -/
private theorem fact_prime_five : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- 2 is not a square in ZMod 5 (specialisation of `ZMod.exists_sq_eq_two_iff`). -/
private theorem two_nqr_mod_five : ¬ IsSquare (2 : ZMod 5) := by
  haveI := fact_prime_five
  rw [ZMod.exists_sq_eq_two_iff (by decide : (5 : ℕ) ≠ 2)]
  decide -- 5 % 8 = 5, ≠ 1, ≠ 7

/-- -2 is not a square in ZMod 5 (specialisation of `ZMod.exists_sq_eq_neg_two_iff`). -/
private theorem neg_two_nqr_mod_five : ¬ IsSquare (-2 : ZMod 5) := by
  haveI := fact_prime_five
  rw [ZMod.exists_sq_eq_neg_two_iff (by decide : (5 : ℕ) ≠ 2)]
  decide -- 5 % 8 = 5, ≠ 1, ≠ 3

theorem safe_A_holds : safe_A := by
  intro a b c heq
  -- Step 1: from heq mod 5, deduce 5 ∣ b.natAbs and 5 ∣ a.natAbs.
  -- (Uses `neg_two_nqr_mod_five` and `Int.Prime.dvd_natAbs_of_coe_dvd_sq`.)
  -- Step 2: substitute a = 5a', b = 5b' and rearrange to c² = 5 * _.
  -- Step 3: deduce 5 ∣ c.natAbs via `Int.Prime.dvd_natAbs_of_coe_dvd_sq`.
  -- Step 4: substitute c = 5c'; obtain `5 c'^2 = a'^2 + 2 b'^2`.
  -- Step 5: `Nat.strongRecOn` on `c.natAbs`; descent gives c = 0,
  --          then b = 0, then a = 0.
  sorry  -- ~30 LOC body following the recipe above

end Erdos659OQ01OQ02.SafePrimePair_2_5
```

**The body**: the three Mathlib lemmas in §3 do **all the QR work**.
The remaining 30 LOC encode the substitution arithmetic and the
strong-induction descent — pure ring/field arithmetic plus
`Nat.strongRecOn`.

## 6. Composite SafePrimePair definition

Following S2a §8 step 1, the axis-vs-plane part of `SafePrimePair 2 5`
is the conjunction of the three `safe_A`, `safe_B`, `safe_C`
predicates. Concretely:

```lean
def SafePrimePair_AxisVsPlane (p q : ℕ) : Prop :=
  (∀ a b c : ℤ, (q : ℤ) * c^2 = a^2 + (p : ℤ) * b^2 → a = 0 ∧ b = 0 ∧ c = 0) ∧
  (∀ a b c : ℤ, (p : ℤ) * b^2 = a^2 + (q : ℤ) * c^2 → a = 0 ∧ b = 0 ∧ c = 0) ∧
  (∀ a b c : ℤ, a^2 = (p : ℤ) * b^2 + (q : ℤ) * c^2 → a = 0 ∧ b = 0 ∧ c = 0)

theorem safe_2_5_axis_vs_plane : SafePrimePair_AxisVsPlane 2 5 := by
  refine ⟨?_, ?_, ?_⟩
  · exact SafePrimePair_2_5.safe_A_holds
  · exact SafePrimePair_2_5.safe_B_holds  -- analogous, ~30 LOC
  · exact SafePrimePair_2_5.safe_C_holds  -- analogous, ~30 LOC
```

**Total LOC budget for the axis-vs-plane half of `(2, 5)` safety**:
~50 LOC structure + 3 × 30 LOC descents ≈ **140 LOC**.

(S2a §8 estimate of "~40 LOC per pair" did not account for the descent
body explicitly. The revised number is honest about the strong-induction
overhead.)

## 7. Generalisation to other safe pairs `(p, q) ∈ {(2,13), (3,5), (5,7), (5,13), (7,13), (11,13)}`

The descent argument generalises to other safe pairs from S2a §6.4 but
requires different Mathlib lemmas depending on `(p, q)`:

| pair | needs in `ZMod q` | needs in `ZMod p` |
|---|---|---|
| `(2, 5)` | ¬IsSquare(2), ¬IsSquare(−2) | trivial (q mod p irrelevant when p=2) |
| `(2, 13)` | ¬IsSquare(2), ¬IsSquare(−2) | trivial |
| `(3, 5)` | ¬IsSquare(3), ¬IsSquare(−3) | ¬IsSquare(5), ¬IsSquare(−5) |
| `(5, 7)` | ¬IsSquare(5), ¬IsSquare(−5) | ¬IsSquare(7), ¬IsSquare(−7) |
| `(5, 13)` | ¬IsSquare(5), ¬IsSquare(−5) | ¬IsSquare(13), ¬IsSquare(−13) |
| `(7, 13)` | analogous | analogous |
| `(11, 13)` | analogous | analogous |

For `(2, q)` pairs, only §3.1 and §3.2 are needed (specialised at
`p = q`). For other pairs, the user needs **quadratic reciprocity**
itself to reduce QR mod q to QR mod p (or vice versa). Mathlib v4.26.0
has:

- `legendreSym.quadratic_reciprocity` at
  `Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean:107`:

  ```lean
  theorem legendreSym.quadratic_reciprocity (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
      legendreSym p q * legendreSym q p = (-1) ^ ((p / 2) * (q / 2))
  ```

- `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one` at line 155
- `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three` at line 164

These let the S2 ACT extend the descent template to all 7 safe pairs
identified in S2a, but with the **caveat** that pairs like `(3, 5)`,
`(5, 7)`, … require both mod-p and mod-q lemmas (each ~20 LOC of QR-by-
hand or via `quadratic_reciprocity`), bringing the total per-pair LOC
to ~180–220.

**Recommendation**: **S2 ACT formalises `(2, 5)` only**. The rate
$\Theta(n^{2/3})$ for `d = 3` does not depend on which safe pair is
picked. Picking `(2, 5)` (the smallest safe pair, requiring only §3.1
and §3.2) minimises Lean LOC while preserving the asymptotic result.

## 8. Gap inventory — what remains axiomatised after S2 ACT

Even with the descent template fully formalised, the following gaps
remain. None block the asymptotic $\Theta(n^{2/3})$ statement.

1. **Full-rank failure mode** (S2a §6.5): the descent only rules out
   axis-vs-plane failures, where one vector concentrates on one or two
   coordinate axes and the other on the complementary subspace. A
   full-rank failure (both `v` and `w` with all three coordinates
   non-zero) is not ruled out by the QR criterion. S2a's empirical
   search at `R ≤ 22` finds no full-rank failure for `(2, 5)`, but this
   is not a proof. Mathlib has no Hasse-Minkowski / genus-theory
   infrastructure for ternary quadratic forms at v4.26.0
   (verified: `Mathlib/LinearAlgebra/QuadraticForm/` contains `Basic`,
   `Dual`, `Isometry`, `Real`, `IsometryEquiv` — no `Genus.lean` or
   `LocalGlobal.lean`).

2. **Solymosi–Vu lower bound** (S2a §3 of S1 OBSERVE): the
   $\Omega(n^{2/d - \epsilon})$ lower bound for distinct distances in
   `d ≥ 3` is an axiom. Not in Mathlib.

3. **`fourPointPropertyD` transfer** (S2a §6): the axis-vs-plane safety
   is shown to be **necessary** for `fourPointProperty` of `L_{p, q}`
   to hold; we have not formally shown **sufficiency**. The empirical
   evidence at `R ≤ 22` strongly suggests sufficiency, but a Lean proof
   would require formalising "every 4-point subset of `L_{p, q}` with
   only 2 distinct distances forces a non-trivial solution of A, B,
   or C". This is true (by symmetry: a 4-point square in
   $\mathbb R^3$ admits a pair of equal-length perpendicular diagonals,
   which lifts to a non-trivial solution of one of A, B, C), but the
   case analysis is non-trivial.

**Honest claim after S2 ACT**: `L_{2, 5}` is **axis-vs-plane safe**
(theorem), and **empirically safe** up to `R = 22` against all failure
modes (computation, not theorem). The S3 ACT axiom
`safeLattice_fourPointProperty (h : SafePrimePair_AxisVsPlane p q)`
will require **two** components: (a) axis-vs-plane safety (theorem at
this point), and (b) full-rank safety (axiom or empirically-anchored
constant).

## 9. Anti-targets (do NOT attempt now)

* ❌ **Do not write the Lean code now.** This S2b is doc-only. The
  Lean code in §5 is a **template** for S2 ACT; the body sketched at
  `sorry` is intentionally not filled in (filling it in is the S2 ACT
  worker's job, with full `proofs/scripts/docker-build.sh` access).
* ❌ **Do not edit `problem.md`, `knowledge.md`, or `state.md`.** This
  is a PREP. Landscape edits (e.g., switching the canonical pair from
  `(2, 3)` to `(2, 5)`) are S2 ACT's responsibility.
* ❌ **Do not edit any prior session file** (s1, s1b, s1c, s01d, s2a).
  Each prior PR has its own context; appending here is the right
  channel.
* ❌ **Do not claim full-rank safety.** §8 item 1 enumerates the gap.
  The axis-vs-plane descent template in §5 covers only one subset of
  failure modes.
* ❌ **Do not extend the empirical search beyond `R = 22`.** S2a
  already pushed the search to that radius; further computation is
  deferred to a future S2c OBSERVE if anyone is interested in a Hasse-
  Minkowski lift.
* ❌ **Do not extend the audit to other safe pairs** beyond §7's
  pointer table. The current PR focuses on `(2, 5)` as the recommended
  formalisation target. Other pairs are a future PREP if S2 ACT (or
  a downstream sibling slug) decides to use them.
* ❌ **Do not propose changes to S2a §8's revised LOC estimate
  unilaterally.** The bump from "~40 LOC" to "~140 LOC" is honest
  about descent infrastructure; future tightening (e.g., a `descent`
  macro) is a separate effort.

## 10. No-edit guarantee

This PR adds exactly **one** new file:
```
research/problems/erdos-659-oq-01-oq-02/sessions/
  2026-05-13-s2b-prep-qr-descent-mathlib-audit-for-2-5-pair.md
```

It does **not** modify:
* `research/problems/erdos-659-oq-01-oq-02/problem.md`
* `research/problems/erdos-659-oq-01-oq-02/knowledge.md`
* `research/problems/erdos-659-oq-01-oq-02/state.md`
* `research/problems/erdos-659-oq-01-oq-02/sessions/2026-05-12-s1b-cartesian-lattice-square-falsification.md`
* `research/problems/erdos-659-oq-01-oq-02/sessions/2026-05-12-s1c-observe-pell-safety-condition.md`
* `research/problems/erdos-659-oq-01-oq-02/sessions/2026-05-13-s01d-weightedSumSquares-mathlib-recasting.md`
* `research/problems/erdos-659-oq-01-oq-02/sessions/2026-05-13-s2a-observe-pell-safety-extended-search-and-QR-descent.md`
* `proofs/Proofs/` (no Lean files for this slug exist yet — S2 ACT will create them)
* `src/data/research/problems/erdos-659-oq-01-oq-02.json` (gallery JSON)
* `src/data/proofs/` (no gallery integration exists yet — S6 ACT will create it)
* the candidate pool or any claim files

Conflict-free against #18322, #18421, #18431, #18442, #18494 (all
merged). Conflict-free against any future S2 ACT that creates
`proofs/Proofs/Erdos659OQ01OQ02.lean`.

## 11. Honesty notes

1. **All Mathlib citations are verified at commit
   `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`** (the `inputRev: v4.26.0`
   pin in `proofs/lake-manifest.json`). Each file:line in §3 was
   fetched directly from the GitHub Contents API.

2. **S2a §8's named module `Mathlib.NumberTheory.Cyclotomic.PrimeQuadratic`
   does not exist.** This is an erratum-level correction — an S2 ACT
   agent who copied S2a §8 verbatim would import a non-existent module
   and fail at the first `import` line. The correct imports are the
   two `Mathlib/NumberTheory/LegendreSymbol/` paths in §3.

3. **The LOC estimate is revised from S2a's "~40 LOC per pair" to
   "~140 LOC for `(2, 5)`" including descent body**. Both estimates
   are honest at their granularity (S2a counted only the QR-criterion
   citations; this PREP adds the descent arithmetic and strong-induction
   bookkeeping). Neither estimate has been verified by actually
   writing the body to completion — it remains an estimate.

4. **The Lean sketch in §5 contains a `sorry`.** This is intentional.
   The §5 sketch is a **template** for an S2 ACT agent, not a complete
   proof. The body is described in 5 numbered steps to make
   replication faithful.

5. **The "trivial in `ZMod 2`" claim in §4 and §7 is informal.** For
   `(p, q) = (2, *)`, equations like "is q a QR mod 2?" reduce to
   "is q ≡ 1 (mod 2)?" which is trivially yes for odd q. This is
   correct but bypasses the §3.1 / §3.2 lemmas — for the formalisation
   of `(2, *)` pairs, the mod-2 direction is handled by a
   `Int.emod_two_eq_zero_or_one`-style case-split, not by the QR
   machinery.

6. **No new mathematics.** The QR criteria in §3.1 / §3.2 are Gauss's
   classical results (1801 *Disquisitiones*, §131). The descent
   structure in §4 is Fermat's classical method (*Œuvres* vol. II
   p. 431, 1659). The contribution here is **pinning the Mathlib
   names**, supplying the **specialisation arithmetic** for `(2, 5)`,
   and producing a **lift-ready Lean template**.

7. **No empirical verification of the template.** The §5 sketch has
   not been compiled or proved through. The named Mathlib symbols
   exist (§3 confirms this), but the body's strong-induction descent
   has not been written in detail beyond the 5-step recipe.

8. **Recommendation in §7 is a judgment call, not a theorem.** The
   choice to formalise `(2, 5)` over `{2, 5, 13}` for `d = 4` is
   based on LOC minimisation. A future S2 ACT may decide that
   formalising `{2, 5, 13}` (for `d = 4`) is more interesting per
   line of Lean; that's a legitimate design choice and not blocked by
   anything in this PREP.

## 12. References

- **S2a (PR #18494)**: extended Pell-safety search + mod-q descent
  rigorous safety for 15 prime-pair lattices. The progenitor of this
  PREP.
- **Mathlib v4.26.0 commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`**:
  source of all §3 citations.
- **Gauss, C. F.** (1801). *Disquisitiones Arithmeticae*. §131
  (quadratic-residue criterion for 2 and −2).
- **Fermat, P. de** (1659). *Œuvres* vol. II p. 431 (letter to
  Carcavi, infinite-descent method for ternary forms).
- **Cassels, J. W. S.** (1978). *Rational Quadratic Forms*. Academic
  Press. Chapter VI for ternary-form descent technique.
- **Serre, J.-P.** (1977). *A Course in Arithmetic*. Springer. §II.3
  for the Legendre symbol and QR.
