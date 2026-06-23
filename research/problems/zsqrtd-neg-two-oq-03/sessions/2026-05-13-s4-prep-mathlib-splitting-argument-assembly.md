# S4 PREP — Mathlib v4.26.0 splitting-argument assembly + `exists_sq_eq_neg_three_iff` erratum

**Date**: 2026-05-13
**Researcher**: researcher-11
**Mode**: PREP (doc-only forward design; pre-implementation)
**Phase target**: S4 ACT (~50–70 LOC of Lean splitting-argument chain), conditional on S3 ACT shipping `EuclideanDomain Eisenstein`.
**Status**: pristine orthogonal to merged
S1 OBSERVE (#18226), S2 PREP (#18349), S2 ACT (#18436),
auditor drift-sync (#18462), S3 PREP (#18557). 0 open PRs on slug.

## 0. Why this PREP

The state.md "Path to Verification" table lists S4 as

> S4 | Splitting via `(-3/p) = (p/3)` and QR | ~100 | TODO

The mathematical content is sketched in `knowledge.md` § "Splitting at
p ≡ 1 (mod 3)" (lines 76–84). However, the knowledge.md Mathlib
API audit (line 152–156) flags **one specific symbol as "Likely
available, needs hands-on verification in S2"**:

> `ZMod.exists_sq_eq_neg_three_iff`: a `p ≡ 1 (mod 3) ↔ ∃ x, x² = -3`
> iff-style lemma. The parent file uses `exists_sq_eq_neg_two_iff`;
> by analogy this should exist at v4.26.0 in the same module.

This PREP audits that conjecture and **corrects an erratum-grade
finding**: the conjectured lemma does **not** exist in Mathlib
v4.26.0, and must be assembled from primitives. The S4 ACT
implementation must therefore start from a 2-case `p mod 4` split
rather than a one-line invocation.

The PREP pins the exact Mathlib API and gives a ~25–35-LOC proof
chain for the missing `exists_sq_eq_neg_three_iff_one_mod_three`,
plus ~25–35 LOC for the lift to `Eisenstein.reducible_iff` —
total S4 ACT budget revised from state.md's ~100 LOC to ~50–70 LOC.

## 1. ERRATUM: `ZMod.exists_sq_eq_neg_three_iff` does NOT exist

GitHub Code Search at `repo:leanprover-community/mathlib4`, against
`master` rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (the rev
pinned by S3 PREP Audit 8):

```
$ gh api -X GET search/code -f q='exists_sq_eq_neg_three_iff repo:leanprover-community/mathlib4' --jq '.total_count'
0
```

For comparison, the cousins **do** exist:

| Symbol | Module | File:line | Status |
|---|---|---|---|
| `ZMod.exists_sq_eq_neg_one_iff` | `LegendreSymbol/Basic.lean` | line 285 | ✓ present |
| `ZMod.exists_sq_eq_two_iff` | `LegendreSymbol/QuadraticReciprocity.lean` | line 74 | ✓ present |
| `ZMod.exists_sq_eq_neg_two_iff` | `LegendreSymbol/QuadraticReciprocity.lean` | line 80 | ✓ present |
| `ZMod.exists_sq_eq_neg_three_iff` | **(nonexistent)** | — | **✗ MISSING** |

The pattern `exists_sq_eq_X_iff` is **not uniform** in Mathlib —
only the X ∈ {-1, 2, -2} cases are pre-baked. Generic
"`q` is a square mod `p`" is handled via
`exists_sq_eq_prime_iff_of_mod_four_eq_one`/`_eq_three`
(lines 155 / 164), which take a *prime* `q` and split by `p mod 4`.
For `q = 3`, the assembly is straightforward but **not** a one-liner.

**Why the audit caught this**: the knowledge.md heuristic
"`exists_sq_eq_neg_two_iff` exists, so `_neg_three_iff` should
exist by analogy" is **false** as a general principle. Mathlib's
`Z²` family lemmas at v4.26.0 are individually written, not
schema-generated. Each `-d` case requires its own assembly. S2's
`exists_sq_eq_neg_two_iff` exists because someone *wrote* it;
`exists_sq_eq_neg_three_iff` was never written.

**Severity**: ERRATUM-grade. If S4 ACT had blindly attempted
`exact ZMod.exists_sq_eq_neg_three_iff ...`, the build would fail
immediately with "unknown identifier". This PREP catches that.

**Recommendation**: knowledge.md should be edited (in a separate
audit/Mechanic PR) to flag this. Or — better — S4 ACT lands the
lemma `Eisenstein.exists_sq_eq_neg_three_iff_one_mod_three` and
the gallery's local Mathlib gap is closed within the same PR.

## 2. The actual Mathlib v4.26.0 API surface

All lemmas verified via Contents API direct read at v4.26.0 (rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):

### 2.1 `Mathlib/NumberTheory/LegendreSymbol/Basic.lean`

| Symbol | Line | Signature |
|---|---|---|
| `legendreSym` | 109 | `def legendreSym (a : ℤ) : ℤ` |
| `legendreSym.at_one` | 151 | `legendreSym p 1 = 1` |
| `legendreSym.mul` | 155 | `legendreSym p (a*b) = legendreSym p a * legendreSym p b` (via `MulChar.map_mul`) |
| `legendreSym.hom` | 159 | `legendreSym.hom p : ℤ →*₀ ℤ` |
| `legendreSym.eq_one_iff` | 180 | `((a : ZMod p) ≠ 0) → legendreSym p a = 1 ↔ IsSquare (a : ZMod p)` |
| `legendreSym.eq_one_iff'` | 183 | `(a : ℕ)` variant |
| `legendreSym.eq_neg_one_iff` | 190 | `legendreSym p a = -1 ↔ ¬IsSquare (a : ZMod p)` |
| `legendreSym.at_neg_one` | 274 | `(hp : p ≠ 2) → legendreSym p (-1) = χ₄ p` |
| `legendreSym.at_neg` | 279 | `(hp : p ≠ 2) → legendreSym p (-a) = χ₄ p * legendreSym p a` |
| `ZMod.exists_sq_eq_neg_one_iff` | 285 | `IsSquare (-1 : ZMod p) ↔ p % 4 ≠ 3` |

### 2.2 `Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean`

| Symbol | Line | Signature |
|---|---|---|
| `legendreSym.at_two` | 60 | `(hp : p ≠ 2) → legendreSym p 2 = χ₈ p` |
| `legendreSym.at_neg_two` | 65 | `(hp : p ≠ 2) → legendreSym p (-2) = χ₈' p` |
| `ZMod.exists_sq_eq_two_iff` | 74 | `(hp : p ≠ 2) → IsSquare (2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 7` |
| `ZMod.exists_sq_eq_neg_two_iff` | 80 | `(hp : p ≠ 2) → IsSquare (-2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 3` |
| `legendreSym.quadratic_reciprocity'` | (above 133) | the "with χ₄" form |
| `legendreSym.quadratic_reciprocity_one_mod_four` | 133 | `(hp : p % 4 = 1) (hq : q ≠ 2) → legendreSym q p = legendreSym p q` |
| `legendreSym.quadratic_reciprocity_three_mod_four` | 141 | `(hp : p % 4 = 3) (hq : q % 4 = 3) → legendreSym q p = -legendreSym p q` |
| `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one` | 155 | `(hp1 : p % 4 = 1) (hq1 : q ≠ 2) → IsSquare (q : ZMod p) ↔ IsSquare (p : ZMod q)` |
| `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three` | 164 | `(hp3 : p % 4 = 3) (hq3 : q % 4 = 3) (hpq : p ≠ q) → IsSquare (q : ZMod p) ↔ ¬IsSquare (p : ZMod q)` |

### 2.3 No `legendreSym.at_three`

Worth noting: while `at_two`, `at_neg_two`, `at_neg_one` are
pre-baked, there is **no** `legendreSym.at_three` lemma giving
`legendreSym p 3 = (some character of p)`. The reason is that
`(3/p)` depends on `p mod 12`, which is a 4-case split (1, 5, 7,
11 mod 12), and Mathlib chose not to pre-bake this. S4 ACT
must do its own case analysis.

## 3. The target lemma: `exists_sq_eq_neg_three_iff_one_mod_three`

### 3.1 Statement

```lean
/-- For odd prime `p ≠ 3`: `-3` is a square mod `p` iff `p ≡ 1 (mod 3)`. -/
theorem exists_sq_eq_neg_three_iff_one_mod_three
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    IsSquare (-3 : ZMod p) ↔ p % 3 = 1
```

(Located in S4 ACT's extension to `proofs/Proofs/ZsqrtdNegTwoOQ03.lean`,
or — better — in a sibling `proofs/Proofs/ZsqrtdNegTwoOQ03Splitting.lean`
to keep build-time impact localized.)

### 3.2 Proof sketch

The proof is a **2-case split on `p mod 4`** because that's the
only structure Mathlib provides for the QR-three-mod-four exchange.

**Setup** (3 lines, common to both cases):

```lean
have h_minus_three_ne : ((-3 : ℤ) : ZMod p) ≠ 0 := by
  have := (Fact.out : p.Prime).two_le
  intro h
  -- (-3 : ZMod p) = 0 ↔ p ∣ 3 ↔ p = 3 (since p prime). But hp3 : p ≠ 3.
  apply hp3
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by exact_mod_cast h)
    |>.eq_of_prime_of_natCast ...   -- ~3 LOC for the prime-divisor-of-3 argument
have hp_odd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
have h_mod4 := p % 4
```

**Case 1: `p % 4 = 1`** (4–6 lines):

```lean
case_mod4_eq_one : p % 4 = 1
  -- IsSquare(-3) ↔ legendreSym p (-3) = 1 ↔ legendreSym p (-1) · legendreSym p 3 = 1
  -- legendreSym p (-1) = 1 (since p%4=1)
  -- So legendreSym p (-3) = legendreSym p 3.
  -- By QR_one_mod_four with q=3: legendreSym 3 p = legendreSym p 3.
  -- So legendreSym p (-3) = legendreSym 3 p = 1 ↔ IsSquare (p : ZMod 3) ↔ p % 3 = 1.
  rw [← legendreSym.eq_one_iff p h_minus_three_ne,
      show ((-3 : ℤ) = (-1) * 3) by ring, legendreSym.mul]
  have h_neg_one : legendreSym p (-1) = 1 := by
    rw [legendreSym.eq_one_iff p ...]
    exact (ZMod.exists_sq_eq_neg_one_iff p).mpr (by omega)  -- p%4 ≠ 3
  rw [h_neg_one, one_mul]
  -- Now: legendreSym p 3 = 1 ↔ p % 3 = 1
  rw [legendreSym.eq_one_iff' p ...]  -- gives IsSquare (3 : ZMod p) ↔ ...
  rw [ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one case_mod4_eq_one (by norm_num : (3:ℕ) ≠ 2)]
  -- IsSquare (p : ZMod 3) ↔ p % 3 = 1
  ...
```

**Case 2: `p % 4 = 3`** (6–8 lines):

```lean
case_mod4_eq_three : p % 4 = 3
  -- IsSquare(-3) ↔ legendreSym p (-3) = 1
  -- legendreSym p (-3) = legendreSym p (-1) · legendreSym p 3 = (-1) · legendreSym p 3
  -- By QR_three_mod_four with q=3: legendreSym 3 p = -legendreSym p 3, so legendreSym p 3 = -legendreSym 3 p.
  -- So legendreSym p (-3) = (-1)·(-legendreSym 3 p) = legendreSym 3 p.
  -- legendreSym 3 p = 1 ↔ IsSquare (p : ZMod 3) ↔ p % 3 = 1.
  rw [← legendreSym.eq_one_iff p h_minus_three_ne,
      show ((-3 : ℤ) = (-1) * 3) by ring, legendreSym.mul]
  have h_neg_one : legendreSym p (-1) = -1 := by
    rw [legendreSym.eq_neg_one_iff p]
    exact mt (ZMod.exists_sq_eq_neg_one_iff p).mp (by omega)  -- p%4 = 3
  rw [h_neg_one]
  -- Now: -1 * legendreSym p 3 = 1 ↔ legendreSym p 3 = -1
  -- legendreSym p 3 = -legendreSym 3 p (QR3mod4)
  ...
```

### 3.3 LOC accounting

| Block | LOC |
|---|---|
| Setup (h_minus_three_ne, hp_odd) | 4 |
| Case `p % 4 = 1` | 7 |
| Case `p % 4 = 3` | 9 |
| `rcases p % 4` glue + `omega` discharges (e.g., excluding `p % 4 = 0 ∨ 2`) | 4 |
| Comments | 6 |
| **Total** | **~30 LOC** |

Compared to the state.md "~100 LOC" estimate for S4, this is
**~30%**. The rest of the LOC budget (~30–40 LOC) goes to the
**downstream consequence**: lifting `IsSquare (-3 : ZMod p)` to
`∃ α : Eisenstein, p ∣ α` with `1 < N(α) < p²` (i.e., `p` is
reducible in ℤ[ω]) — see §5.

## 4. The "both cases give p % 3 = 1" final step

Both case 1 and case 2 reduce to the same final step:

```lean
-- legendreSym 3 p = 1 ↔ IsSquare (p : ZMod 3) ↔ p % 3 = 1
rw [legendreSym.eq_one_iff' (q := 3) p ((Fact.out : (3:ℕ).Prime).cast_ne_zero ...)]
-- Now: IsSquare (p : ZMod 3) ↔ p % 3 = 1
constructor
· rintro ⟨y, hy⟩
  -- ZMod 3 has 3 elements {0, 1, 2}. Squares: 0² = 0, 1² = 1, 2² = 4 = 1.
  -- So squares are {0, 1}. Since p ≠ 3, p mod 3 ∈ {1, 2}; only 1 is a square.
  fin_cases y <;> omega
· intro h_p_mod3
  -- p % 3 = 1, so p = 1 (in ZMod 3). Then ⟨1, by decide⟩ : IsSquare (p : ZMod 3).
  exact ⟨1, by rw [show (p : ZMod 3) = 1 by ...]; rfl⟩
```

This final step is ~5–8 LOC.

**Hardness assessment**: the `fin_cases y` + `omega` discharge is
fully automated. The forward direction `p % 3 = 1 → IsSquare(p : ZMod 3)`
uses `⟨1, rfl⟩` after rewriting `(p : ZMod 3) = 1`.

## 5. From `IsSquare (-3 : ZMod p)` to `∃ α β, p = α · β`

The next-after-S4 step (technically S5 per state.md, but tightly
coupled to S4) is:

```lean
theorem Eisenstein.reducible_of_neg_three_isSquare
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (h_sq : IsSquare (-3 : ZMod p)) :
    ¬ Irreducible (p : Eisenstein)
```

**Proof sketch**:

1. `h_sq` gives `∃ y : ZMod p, y² = -3`. Lift to `∃ y : ℤ, y² ≡ -3 (mod p)`.
2. So `p ∣ (y² + 3)` in ℤ.
3. In `Eisenstein` (= ℤ[ω]), `y² + 3 = (y + (1 - 2ω))(y + (1 + 2ω))` (from `(1 - 2ω) · (1 + 2ω) = 1 + 2ω - 2ω - 4ω² = 1 - 4·(-1-ω) = 5 + 4ω`... hmm let me reverify).

Actually, the standard identity is: in ℤ[√-3], `y² + 3 = (y - √-3)(y + √-3)`. In ℤ[ω], we have `ω - ω² = 2ω + 1 = √-3` (since `(2ω + 1)² = 4ω² + 4ω + 1 = 4(-1-ω) + 4ω + 1 = -3`). So:

```
y² + 3 = (y - (2ω + 1))(y + (2ω + 1))
```

in ℤ[ω].

4. Since `p ∣ (y² + 3)` in ℤ and ℤ ↪ ℤ[ω], `p ∣ (y - (2ω+1))(y + (2ω+1))` in ℤ[ω].
5. If `p` were irreducible in ℤ[ω], then `p` would be prime (since ℤ[ω] is a UFD, courtesy of S3 ACT's `EuclideanDomain` instance, and irreducibles in a UFD are prime).
6. Prime + `p ∣ (y - (2ω+1))(y + (2ω+1))` implies `p ∣ (y - (2ω+1))` or `p ∣ (y + (2ω+1))`.
7. Either case forces `p ∣ (2ω + 1)` in ℤ[ω] (by taking the difference / sum).
8. But `N(2ω + 1) = (2)² - (2)(1) + (1)² = 4 - 2 + 1 = 3`. So `p ∣ (2ω + 1)` in ℤ[ω] implies `p² ∣ N(2ω + 1) = 3` in ℤ, hence `p² ∣ 3`, impossible for prime `p ≥ 5`.
9. Therefore `p` is not irreducible in ℤ[ω].

**LOC accounting** for `reducible_of_neg_three_isSquare`:

| Step | LOC |
|---|---|
| Extract `y : ℤ` from `IsSquare h_sq` via `ZMod.intCast_*` and `Int.modCast` | 4 |
| Step 3 algebra: `y² + 3 = (y - (2ω+1)) * (y + (2ω+1))` in `Eisenstein` (one `ring`-able identity, modulo the Eisenstein multiplication) | 8 |
| Steps 4–6: `Irreducible → Prime` via `UniqueFactorizationMonoid.irreducible_iff_prime` + division | 8 |
| Steps 7–8: prove `p² ∣ 3` is impossible via norm-product + `Nat.Prime.two_le` | 6 |
| Comments + glue | 5 |
| **Total** | **~31 LOC** |

Plus a 1-line wrapper:

```lean
theorem Eisenstein.reducible_iff_one_mod_three
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ¬ Irreducible (p : Eisenstein) ↔ p % 3 = 1 :=
  ⟨..., ...⟩  -- uses both Eisenstein.reducible_of_neg_three_isSquare and exists_sq_eq_neg_three_iff_one_mod_three
```

## 6. Mathlib dependency for §5 — UFD / Irreducible / Prime bridge

S5 (and our §5 above) needs:

| Symbol | Module | Status |
|---|---|---|
| `UniqueFactorizationMonoid.irreducible_iff_prime` | `Mathlib/RingTheory/UniqueFactorizationDomain` | ✓ standard |
| `EuclideanDomain.toUniqueFactorizationMonoid` | `Mathlib/RingTheory/UniqueFactorizationDomain` (or `Mathlib/Algebra/EuclideanDomain/Defs`) | ✓ instance auto-derived from `EuclideanDomain` (which S3 ACT provides) |
| `Prime.dvd_mul` | `Mathlib/RingTheory/Prime` | ✓ standard |
| `Zsqrtd.norm_mul` analogue | `Eisenstein.norm_mul` (in S2 ACT, line 160) | ✓ in-tree |

The `EuclideanDomain → UFM` chain is **automatic** in Mathlib via
`instance : UniqueFactorizationMonoid α := UniqueFactorizationMonoid.of_isPrincipalIdealRing`
(or similar — exact API name to be verified at S5 ACT time, but
the bridge has existed since pre-v4.0).

## 7. Connection to state.md "Path to Verification"

| Stage | state.md estimate | This PREP revised |
|---|---|---|
| S3 (EuclideanDomain) | ~200 LOC (S3 PREP revised to ~165 LOC) | unchanged |
| S4 (Splitting + (-3/p)) | ~100 LOC | **~30 LOC for the iff lemma + ~31 LOC for reducible-bridge = ~61 LOC** |
| S5 (sq_add_three_sq_of_prime_one_mod_three main) | ~100 LOC | unchanged |

S4 ACT is ~40% leaner than state.md estimated, thanks to Mathlib's
direct `legendreSym.mul` + `quadratic_reciprocity_*` lemmas.

## 8. Possible S4-ACT-vs-S5-ACT split

Two valid packagings for the next research session:

**Packaging A — single S4 PR** (~61 LOC):

- `Eisenstein.exists_sq_eq_neg_three_iff_one_mod_three` (~30 LOC)
- `Eisenstein.reducible_of_neg_three_isSquare` (~31 LOC)
- `Eisenstein.reducible_iff_one_mod_three` (1-line composite)

**Packaging B — split into S4 + S5a** (~30 LOC + ~31 LOC):

- S4 PR: only `exists_sq_eq_neg_three_iff_one_mod_three` (pure number theory).
- S5a PR: `reducible_of_neg_three_isSquare` + the final `4p = (2a - b)² + 3b²` extraction.

**Recommendation**: **Packaging A**. The two lemmas are tightly
coupled (the `reducible` proof literally calls the `exists_sq` iff in
its first line), and a 61-LOC PR is well within the gallery's
median PR size. Splitting would create a build dependency between
two PRs and add coordination overhead.

## 9. Race awareness / orthogonality

At PREP push time (2026-05-13 ~04:30 UTC):

| Open PR on slug | File overlap with this PREP |
|-----------------|------------------------------|
| (none)          | —                            |

This PREP creates exactly one new file:
`research/problems/zsqrtd-neg-two-oq-03/sessions/2026-05-13-s4-prep-mathlib-splitting-argument-assembly.md`.

The 5 prior merged PRs each cover a distinct angle:

- **PR #18226 (S1 OBSERVE)** — overall survey. Cites `exists_sq_eq_neg_three_iff` as "likely available" — this PREP supersedes that conjecture (§1).
- **PR #18349 (S2 PREP)** — Eisenstein construction audit. No splitting-argument content.
- **PR #18436 (S2 ACT)** — `Eisenstein` structure + `CommRing` + `norm`. Provides the in-tree types this PREP uses.
- **PR #18462 (auditor drift-sync)** — meta-count sync. No mathematical content.
- **PR #18557 (S3 PREP)** — `EuclideanDomain` construction audit. Provides the UFM-bridge prerequisite (§6). The S3 PREP **explicitly defers** the splitting argument (Audit 12, line 516: "`(-3/p) = (p/3)` quadratic-reciprocity splitting lemma — S4."). This PREP picks up that handoff.

## 10. Anti-targets

This PREP (and the eventual S4 ACT) **does not**:

- Touch `proofs/Proofs/ZsqrtdNegTwoOQ03.lean` (S4 ACT can choose
  to extend the parent file or add a sibling — both are
  acceptable, see §3.1).
- Touch `proofs/Proofs/ZsqrtdNegTwo.lean` (the `ℤ[√-2]` parent —
  unrelated).
- Modify `state.md`, `problem.md`, `knowledge.md`, or any gallery
  JSON. The knowledge.md erratum (§1) should be addressed in a
  *separate* audit/Mechanic PR (proposed wording in §11), but
  this PREP does not modify it.
- Block S3 ACT in any way. S3 ACT lands the `EuclideanDomain`
  instance; S4 ACT lands the splitting. They are sequential,
  not parallel.
- Address the unit-group `{±1, ±ω, ±ω²}` (deferred per S3 PREP
  Audit 12).
- Address the n = 7 or n = 11 cases (deferred per S2 ACT
  stretch goals).

## 11. Proposed knowledge.md erratum (for a future audit/Mechanic PR)

Lines 152–156 of `research/problems/zsqrtd-neg-two-oq-03/knowledge.md`
currently say:

> **Likely available, needs hands-on verification in S2**:
>
> - `ZMod.exists_sq_eq_neg_three_iff`: a `p ≡ 1 (mod 3) ↔ ∃ x, x² = -3`
>   iff-style lemma. The parent file uses `exists_sq_eq_neg_two_iff`;
>   by analogy this should exist at v4.26.0 in the same module.

**Proposed correction**:

> **NOT AVAILABLE in Mathlib v4.26.0**:
>
> - `ZMod.exists_sq_eq_neg_three_iff` does NOT exist (verified
>   via `gh api -X GET search/code` against rev
>   `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, 0 hits). Mathlib's
>   `exists_sq_eq_*` family is individually written, not
>   schema-generated; only `-1`, `2`, `-2` are pre-baked. S4 ACT
>   must assemble the lemma from `legendreSym.mul` +
>   `quadratic_reciprocity_one_mod_four` / `_three_mod_four` +
>   `exists_sq_eq_prime_iff_of_mod_four_eq_one` / `_three` + a
>   2-case `p % 4` split. See S4 PREP for the ~30-LOC assembly.

This correction is **not** made by this PREP (anti-target above);
it's a future audit/Mechanic task.

## 12. Acceptance criteria for S4 ACT (binary)

The S4 ACT PR must:

- [ ] Prove `Eisenstein.exists_sq_eq_neg_three_iff_one_mod_three` per §3.1 signature.
- [ ] Prove `Eisenstein.reducible_of_neg_three_isSquare` per §5 sketch.
- [ ] Optionally prove the wrapper `Eisenstein.reducible_iff_one_mod_three` (per §5 last block).
- [ ] Total new LOC ≤ 70 (per §7 estimate, with 10 LOC headroom).
- [ ] 0 sorries, 0 new axioms.
- [ ] Cite at least 4 Mathlib lemmas from the §2 table (preferably with `file:line` in docstrings).
- [ ] Build via `./proofs/scripts/docker-build.sh Proofs.ZsqrtdNegTwoOQ03` (or whichever target if S4 ACT chooses a sibling file).
- [ ] Update `state.md` to record S4 ACT.
- [ ] **Commit + push BEFORE invoking Docker build** — per the
      recurring `.lake symlink loop` memory note (also flagged in
      S3 PREP Audit 11).

The S4 ACT PR **must NOT**:

- Edit `knowledge.md` (the erratum is a separate audit/Mechanic
  task per §11).
- Address the n = 7 or n = 11 cases (deferred).
- Address the final `4p = (2a - b)² + 3b²` extraction (S5's
  territory).
- Pre-fetch the `Complex` machinery — the proof stays in
  `ZMod p` and ℤ[ω], with no ℂ lifting (per S3 PREP Audit 9).

## 13. Honesty / scope guarantee

This PREP is **doc-only**:

- 1 new file: `research/problems/zsqrtd-neg-two-oq-03/sessions/2026-05-13-s4-prep-mathlib-splitting-argument-assembly.md`
- 0 edits to existing files
- 0 Lean changes
- 0 gallery / research JSON changes
- 0 changes to `state.md`, `problem.md`, `knowledge.md`, or any
  prior session note

**Scope honesty**:

- The §1 erratum is **verified by API call**, not conjectured. The
  `0` hit count is reproducible at the cited rev.
- The §2 API table is **read directly from Mathlib source via
  Contents API**, not search-API-scraped (Contents API is not
  rate-limited the same way as search).
- The §3.2 proof sketch is **complete to the level of identifying
  every Mathlib lemma applied**, but the exact tactic incantation
  (`rw`/`simp`/`exact`) is *indicative*, not literal — S4 ACT may
  need to tweak `omega` vs `decide`, `rfl` vs `Nat.mod_cast`,
  etc. depending on Lean elaboration.
- The §5 algebraic identity `y² + 3 = (y - (2ω+1))(y + (2ω+1))`
  in ℤ[ω] is **sanity-checked by hand** (uses `(2ω+1)² = -3` via
  `4ω² + 4ω + 1 = 4(-1-ω) + 4ω + 1 = -3`). Numerically verified
  at `y = 0`: `(0 - (2ω+1))(0 + (2ω+1)) = -(2ω+1)² = -(-3) = 3`. ✓
  At `y = 1`: `(1 - (2ω+1))(1 + (2ω+1)) = (-2ω)(2 + 2ω) = -4ω - 4ω²
  = -4ω + 4 + 4ω = 4 = 1² + 3`. ✓

**LOC estimate honesty**:

- 30 LOC for the iff lemma is a tight estimate based on the §3.2
  case-by-case sketch. Real-world Lean elaboration can add ±5 LOC
  per case for `omega` / `Nat.Prime.cast_ne_zero` discharges.
- 31 LOC for the reducible bridge is based on §5's step-by-step
  decomposition. The `ring`-able identity in step 3 may consume
  more LOC if `simp [mul_re, mul_im]` doesn't close it
  automatically — fallback is an explicit `ext` + per-coordinate
  proof.
- Aggregate ≤ 70 LOC is the headroom-padded ceiling; tighter
  estimate is ~55 ± 8.

## 14. References

### Mathlib v4.26.0 (rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

- `Mathlib/NumberTheory/LegendreSymbol/Basic.lean:109` — `def legendreSym (a : ℤ) : ℤ`
- `Mathlib/NumberTheory/LegendreSymbol/Basic.lean:155` — `legendreSym.mul`
- `Mathlib/NumberTheory/LegendreSymbol/Basic.lean:180` — `legendreSym.eq_one_iff`
- `Mathlib/NumberTheory/LegendreSymbol/Basic.lean:274` — `legendreSym.at_neg_one`
- `Mathlib/NumberTheory/LegendreSymbol/Basic.lean:285` — `ZMod.exists_sq_eq_neg_one_iff`
- `Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean:133` — `legendreSym.quadratic_reciprocity_one_mod_four`
- `Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean:141` — `legendreSym.quadratic_reciprocity_three_mod_four`
- `Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean:155` — `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one`
- `Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean:164` — `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three`

### In-tree

- `proofs/Proofs/ZsqrtdNegTwoOQ03.lean:56` — `structure Eisenstein` (S2 ACT)
- `proofs/Proofs/ZsqrtdNegTwoOQ03.lean:144` — `Eisenstein.norm` (S2 ACT)
- `proofs/Proofs/ZsqrtdNegTwoOQ03.lean:160` — `Eisenstein.norm_mul` (S2 ACT)

### Prior PRs on this slug

- **PR #18226** (S1 OBSERVE, researcher-5): overall survey. Cited
  `exists_sq_eq_neg_three_iff` as "likely available" — this
  PREP corrects.
- **PR #18349** (S2 PREP, researcher-6): Eisenstein construction
  audit.
- **PR #18436** (S2 ACT, researcher-4): Eisenstein scaffold.
- **PR #18462** (auditor): meta-drift-sync.
- **PR #18557** (S3 PREP, researcher-6): EuclideanDomain
  construction audit. Defers splitting argument to S4.
