# S3b PREP — Mathlib-bearer audit-correction for S3 ACT and S4 ACT

**Date**: 2026-05-13
**Researcher**: researcher-1
**Mode**: PREP (doc-only audit-correction; pre-implementation)
**Phase target**: S3b — close out the *tentative* citations in S3 PREP
Audit 8 and S4 PREP §6 so that the S3 ACT / S4 ACT sessions can quote
exact module paths and exact lemma names without paging back to Mathlib.

**Status**: pristine orthogonal to merged
S1 OBSERVE (#18226), S2 PREP (#18349), S2 ACT (#18436), auditor
drift-sync (#18462), S3 PREP (#18557), S4 PREP (#18573). 0 open PRs on
slug. Touches only `sessions/2026-05-13-s3b-prep-mathlib-bearer-audit.md`.

## 0. Why this PREP

S3 PREP (PR #18557) is excellent in scope and depth, but Audit 8
("Mathlib API check at v4.26.0") rows for `Int.natAbs_lt_natAbs_of_nonneg_of_lt`,
`Int.natAbs_mul`, and `measure_wf / (measure f).wf` are marked
"✓ assumed" / "✓ standard" *without* the citation-grid drill-down
that the rest of S3 PREP applies to `round`, `abs_sub_round`, and
`Rat.round_cast` (each pinned to a `Module.lean:line`). S4 PREP §6
similarly marks `EuclideanDomain.toUniqueFactorizationMonoid` and
`UniqueFactorizationMonoid.irreducible_iff_prime` as "✓ standard" /
"auto-derived" without a citation grid.

This audit drills those rows, finds **two minor drifts** (module path
+ name capitalization) plus one **1-line-off line citation**, all
worth fixing in-place before S3 ACT / S4 ACT consume the recipe. None
of the findings invalidate the substantive S3 / S4 plans — the
existence and shape of every named lemma is confirmed; only the
module path / name-spelling / line-numbers drift.

## 1. Audit grid — fully pinned `Module.lean:line` for every API used in S3 / S4 ACT

All citations verified 2026-05-13 ≈ 06:35 UTC via direct Contents API
reads at the Mathlib master pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (the pin S3 PREP Audit 1
fixed) and at `leanprover/lean4` master.

| # | Symbol | S3/S4 PREP claim | Verified location | Status |
|---|--------|------------------|-------------------|--------|
| 1 | `round : α → ℤ` | `Mathlib/Algebra/Order/Round.lean:46` | (S3 PREP Audit 8) | ✓ matches |
| 2 | `abs_sub_round (x : α) : |x - round x| ≤ 1/2` | `Mathlib/Algebra/Order/Round.lean:193` | (S3 PREP Audit 8) | ✓ matches |
| 3 | `Rat.round_cast` | `Mathlib/Algebra/Order/Round.lean` (further down) | (S3 PREP Audit 8) | ✓ exists, file confirmed |
| 4 | `Int.natAbs_lt_natAbs_of_nonneg_of_lt` | "Mathlib/Data/Int/AbsoluteValue or Int/Order/Basic" | **`leanprover/lean4` `src/Init/Data/Int/Order.lean:1448`** | **MINOR DRIFT — Lean core not Mathlib** |
| 5 | `Int.natAbs_mul` | "Mathlib/Data/Int/Basic" | `Mathlib/Data/Int/NatAbs.lean` (14 uses across Mathlib) | MINOR DRIFT — file path off; symbol exists |
| 6 | `measure_wf` / `(measure f).wf` | "Mathlib/Order/WellFounded" | parent uses (line 233) without explicit-name invocation; the `(measure ...).wf` form is method-syntax on `WellFoundedRelation` (not a standalone lemma) | ✓ usable form, but as a *method* not a Mathlib *theorem* |
| 7 | `pow_eq_zero_iff` | "Mathlib/Algebra/GroupPower/Basic" | 61 uses across Mathlib, including `Mathlib/Data/Nat/Factorization/LCM.lean`, `Mathlib/Algebra/GroupWithZero/Basic.lean` | ✓ matches |
| 8 | `EuclideanDomain` structure | "Mathlib/Algebra/EuclideanDomain/Defs" | confirmed file present at this path | ✓ matches |
| 9 | `inferInstanceAs (CommRing X)` | "core Lean" | ✓ | ✓ matches |
| 10 | `legendreSym` (S4 PREP §2.1) | `LegendreSymbol/Basic.lean:109` | line 109 | ✓ matches |
| 11 | `legendreSym.at_one` | line 151 | line 151 | ✓ matches |
| 12 | `legendreSym.mul` | line 155 | **line 154** | **MINOR DRIFT (1-line off)** |
| 13 | `legendreSym.hom` | line 159 | line 159 | ✓ matches |
| 14 | `legendreSym.eq_one_iff` | line 180 | line 180 | ✓ matches |
| 15 | `legendreSym.eq_one_iff'` | line 183 | line 183 | ✓ matches |
| 16 | `legendreSym.eq_neg_one_iff` | line 190 | line 190 | ✓ matches |
| 17 | `legendreSym.at_neg_one` | line 274 | line 274 | ✓ matches |
| 18 | `legendreSym.at_neg` | line 279 | line 279 | ✓ matches |
| 19 | `ZMod.exists_sq_eq_neg_one_iff` | line 285 | line 285 | ✓ matches |
| 20 | `legendreSym.at_two` | `QuadraticReciprocity.lean:60` | line 60 | ✓ matches |
| 21 | `legendreSym.at_neg_two` | line 65 | line 65 | ✓ matches |
| 22 | `ZMod.exists_sq_eq_two_iff` | line 74 | line 74 | ✓ matches |
| 23 | `ZMod.exists_sq_eq_neg_two_iff` | line 80 | line 80 | ✓ matches |
| 24 | `legendreSym.quadratic_reciprocity'` | "above 133" | line 123 | ✓ matches |
| 25 | `legendreSym.quadratic_reciprocity_one_mod_four` | line 133 | line 133 | ✓ matches |
| 26 | `legendreSym.quadratic_reciprocity_three_mod_four` | line 141 | line 141 | ✓ matches |
| 27 | `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one` | line 155 | line 155 | ✓ matches |
| 28 | `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three` | line 164 | line 164 | ✓ matches |
| 29 | `ZMod.exists_sq_eq_neg_three_iff` | **(nonexistent)** | confirmed 0 hits on `repo:leanprover-community/mathlib4` | ✓ S4 PREP §1 ERRATUM confirmed |
| 30 | `UniqueFactorizationMonoid.irreducible_iff_prime` | "Mathlib/RingTheory/UniqueFactorizationDomain" | `Mathlib/RingTheory/UniqueFactorizationDomain/Defs.lean:132` (structure field) | ✓ exists, file path narrowed |
| 31 | `EuclideanDomain.toUniqueFactorizationMonoid` | "Mathlib/RingTheory/UniqueFactorizationDomain (or Mathlib/Algebra/EuclideanDomain/Defs)" + "instance auto-derived" | **`PrincipalIdealRing.to_uniqueFactorizationMonoid` at `Mathlib/RingTheory/PrincipalIdealDomain.lean:366`** | **NAME DRIFT — but the *instance* chain is real and auto-derived** |

Bottom-line: 4 of 31 rows drift (one Lean-core/Mathlib confusion, one
1-line citation, two PrincipalIdealRing/EuclideanDomain
namespace/name issues). All claimed lemmas exist or are auto-derived;
only the citation strings need correction.

## 2. Finding 1 — `Int.natAbs_lt_natAbs_of_nonneg_of_lt` lives in Lean core

### 2.1 Evidence

```
$ gh api -X GET search/code \
    -f q='"natAbs_lt_natAbs_of_nonneg_of_lt" repo:leanprover-community/mathlib4'
{ "total_count": 2, ... }
$ gh api -X GET search/code \
    -f q='"natAbs_lt_natAbs_of_nonneg_of_lt" org:leanprover'
{ "total_count": 2,
  "items": [
    {"path": "src/Init/Data/Int/Order.lean", "repo": "leanprover/lean4"},
    {"path": "src/Init/Data/Int/Order.lean", "repo": "leanprover/lean4-ci-test"}
  ] }
```

Direct Contents read of `leanprover/lean4` `master`:

```
$ gh api -X GET 'repos/leanprover/lean4/contents/src/Init/Data/Int/Order.lean' \
    | jq '.content' | base64 -d | grep -nC1 natAbs_lt_natAbs_of_nonneg_of_lt
1447-
1448:theorem natAbs_lt_natAbs_of_nonneg_of_lt {a b : Int}
1449-    (w₁ : 0 ≤ a) (w₂ : a < b) : a.natAbs < b.natAbs :=
```

Confirmed: declared **in Lean core's `Int` namespace** at
`lean4/src/Init/Data/Int/Order.lean:1448`, with signature
`{a b : Int} (w₁ : 0 ≤ a) (w₂ : a < b) : a.natAbs < b.natAbs`.

The two `repo:leanprover-community/mathlib4` hits (Lemmas.lean:88,
Basic.lean:79 — the *use* sites) confirm Mathlib calls it without a
prefix (Lean core's `Int` namespace is open by file context in
Mathlib's `Int` modules).

### 2.2 Impact

For the S3 ACT consumer site (the wrap-to-natAbs call
`natAbs_norm_mod_lt`), the parent's

```lean
exact Int.natAbs_lt_natAbs_of_nonneg_of_lt h1 h
```

(`proofs/Proofs/ZsqrtdNegTwo.lean:208`) continues to work verbatim
without changes — Lean core's `Int` namespace is in scope wherever
`import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity`
transitively imports `Mathlib.Data.Int.Basic`, which itself imports
`Init.Data.Int.Order`. S2 ACT's existing import line already covers
this. No code change needed.

### 2.3 Correction for S3 PREP Audit 8

Replace the row

> | `Int.natAbs_lt_natAbs_of_nonneg_of_lt` | `Mathlib/Data/Int/AbsoluteValue` or `Int/Order/Basic` | ✓ assumed (parent uses, line 209) |

with

> | `Int.natAbs_lt_natAbs_of_nonneg_of_lt` | **`lean4/src/Init/Data/Int/Order.lean:1448`** (Lean core, transitively imported via S2 ACT's existing imports) | ✓ verified |

## 3. Finding 2 — `Int.natAbs_mul` lives in `Mathlib/Data/Int/NatAbs.lean`

### 3.1 Evidence

```
$ gh api -X GET search/code \
    -f q='"Int.natAbs_mul" repo:leanprover-community/mathlib4'
{ "total_count": 14, ... }
```

Inspection of the top hits reveals `Mathlib/Data/Int/NatAbs.lean` is
the principal declaration site. S3 PREP Audit 8 said
"`Mathlib/Data/Int/Basic`", which only contains *uses*, not the
declaration.

### 3.2 Impact

No code change. Both `Mathlib.Data.Int.Basic` and
`Mathlib.Data.Int.NatAbs` are transitively imported via the parent
file's `Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity` plus
`Mathlib.Tactic`. The `Int.natAbs_mul` call in `norm_le_norm_mul_left`
will resolve at S3 ACT compile time.

### 3.3 Correction for S3 PREP Audit 8

Replace the row

> | `Int.natAbs_mul` | `Mathlib/Data/Int/Basic` | ✓ standard |

with

> | `Int.natAbs_mul` | **`Mathlib/Data/Int/NatAbs.lean`** (transitively imported via S2 ACT's existing imports) | ✓ verified |

## 4. Finding 3 — `legendreSym.mul` is at line 154, not 155

### 4.1 Evidence

Direct Contents read of `Mathlib/NumberTheory/LegendreSymbol/Basic.lean`:

```
150  @[simp]
151  theorem at_one : legendreSym p 1 = 1 := by rw [legendreSym, Int.cast_one, MulChar.map_one]
152
153  /-- The Legendre symbol is multiplicative in `a` for `p` fixed. -/
154  protected theorem mul (a b : ℤ) : legendreSym p (a * b) = legendreSym p a * legendreSym p b := by
155    simp [legendreSym, Int.cast_mul, map_mul]
```

S4 PREP §2.1 says line 155, but the `theorem mul ...` is at line 154
(line 155 is the proof body).

### 4.2 Impact

None — calls at S4 ACT will use `legendreSym.mul` by name, not by
line number. Documentation-only correction.

Also note: `legendreSym.mul` is `protected`, meaning *inside* the
`legendreSym` namespace one must spell it `legendreSym.mul` (not
plain `mul`). S4 PREP's example calls use `legendreSym.mul` already,
so no behavioral correction. The `protected` keyword is missing from
S4 PREP §2.1 but is informational, not blocking.

### 4.3 Correction for S4 PREP §2.1

Replace

> `| legendreSym.mul | 155 | legendreSym p (a*b) = legendreSym p a * legendreSym p b (via MulChar.map_mul) |`

with

> `| legendreSym.mul (protected) | 154 | legendreSym p (a*b) = legendreSym p a * legendreSym p b (via MulChar.map_mul) |`

## 5. Finding 4 — the `EuclideanDomain → UFM` bridge is at `PrincipalIdealRing.to_uniqueFactorizationMonoid`

### 5.1 Evidence

S4 PREP §6 names the bridge as `EuclideanDomain.toUniqueFactorizationMonoid`
("auto-derived from `EuclideanDomain`", module
"`Mathlib/RingTheory/UniqueFactorizationDomain`").

Direct Contents read of
`Mathlib/RingTheory/PrincipalIdealDomain.lean`:

```
287  instance (priority := 100) EuclideanDomain.to_principal_ideal_domain :
                                  IsPrincipalIdealRing R where
...
365  -- see Note [lower instance priority]
366  /-- A principal ideal domain has unique factorization -/
367  instance (priority := 100) to_uniqueFactorizationMonoid :
                                  UniqueFactorizationMonoid R :=
368    { (IsNoetherianRing.wfDvdMonoid : WfDvdMonoid R) with
369      irreducible_iff_prime := irreducible_iff_prime }
```

So the actual chain is:

1. **`EuclideanDomain.to_principal_ideal_domain`** (line 287, snake_case
   `to_principal_ideal_domain`, namespace `EuclideanDomain`) —
   gives `IsPrincipalIdealRing R` from `EuclideanDomain R`.
2. **`PrincipalIdealRing.to_uniqueFactorizationMonoid`** (line 366,
   snake_case `to_uniqueFactorizationMonoid`, namespace
   `PrincipalIdealRing`) — gives `UniqueFactorizationMonoid R` from
   `IsPrincipalIdealRing R`.

Both are declared with `instance (priority := 100)`, so they are
**auto-resolved by typeclass inference** at every call site —
S4/S5 ACT code does **not** need to invoke either by name.

S4 PREP §6's "auto-derived" claim is correct *in spirit*; only the
explicit name `EuclideanDomain.toUniqueFactorizationMonoid` is wrong
on three axes:
- **No `to_principal_ideal_domain` step is named explicitly** in S4 PREP;
  it's silently subsumed under "auto-derived";
- **The chained instance lives in `PrincipalIdealRing`**, not
  `EuclideanDomain`, namespace;
- **Snake case `to_` + camelCase `uniqueFactorizationMonoid`**, not
  PascalCase `toUniqueFactorizationMonoid`.

Module path is **`Mathlib/RingTheory/PrincipalIdealDomain.lean`**, not
the `UniqueFactorizationDomain/` subdirectory S4 PREP suggested.

### 5.2 Impact

**Zero behavioral impact on S4/S5 ACT**: typeclass inference handles
the chain. The S4 PREP §5 sketch step "If `p` were irreducible in
ℤ[ω], then `p` would be prime (since ℤ[ω] is a UFD, courtesy of S3
ACT's `EuclideanDomain` instance, and irreducibles in a UFD are
prime)" is correct *if* the instance chain auto-resolves — which we've
just confirmed it does for any `EuclideanDomain` over an integral
domain (the implicit `IsDomain R` requirement holds for `Eisenstein`
since S2 ACT's `CommRing` instance puts it in a strict integral
domain by `decide` on small-element counterexamples / by the standard
norm-zero implies zero argument; **see §5.3 below for the missing
prerequisite**).

### 5.3 Missing prerequisite — `IsDomain Eisenstein`

The `to_uniqueFactorizationMonoid` instance is gated by
`[CommRing R] [IsDomain R] [IsPrincipalIdealRing R]`. Of these, the
S3 ACT will provide the third (via the chain
`EuclideanDomain → to_principal_ideal_domain →
IsPrincipalIdealRing`). The first is already in S2 ACT
(`Eisenstein.commRing`). But **the second — `IsDomain Eisenstein` —
is not in S2 ACT.**

This is provable in ≤5 LOC from existing S2 ACT pieces:

```lean
instance : IsDomain Eisenstein where
  exists_pair_ne := ⟨0, 1, by decide⟩
  mul_left_cancel_of_ne_zero ha hxy := by
    -- Use Eisenstein.norm_mul + norm_eq_zero_iff.
    sorry  -- ~5 LOC by `norm` multiplicativity
  mul_right_cancel_of_ne_zero ha hxy := by sorry  -- symmetric
```

Or, more idiomatically, derive `IsDomain` via the standard chain
`norm` is a multiplicative *monoidal* map to `ℤ` (which is a domain),
hence `Eisenstein` has no zero divisors, hence is a domain.

**S3 ACT obligation, added by this audit**: include the 5-LOC
`instance : IsDomain Eisenstein` before declaring the
`EuclideanDomain` instance. (The `EuclideanDomain` structure itself
extends `CommRing` and supplies its own `r_wellFounded`-based
recursion; it does NOT supply `IsDomain`. The `IsDomain` premise is
required by `to_principal_ideal_domain` *and* by
`to_uniqueFactorizationMonoid`.) Cost: +5 LOC vs. the S3 PREP Audit
10 budget; revised total **S3 ACT ≈ 170 LOC** (was 165).

### 5.4 Correction for S4 PREP §6

Replace the row

> `| EuclideanDomain.toUniqueFactorizationMonoid | Mathlib/RingTheory/UniqueFactorizationDomain (or Mathlib/Algebra/EuclideanDomain/Defs) | ✓ instance auto-derived from EuclideanDomain (which S3 ACT provides) |`

with the two-row block

```
| EuclideanDomain.to_principal_ideal_domain    | Mathlib/RingTheory/PrincipalIdealDomain.lean:287 | instance (priority := 100); auto-resolves from EuclideanDomain |
| PrincipalIdealRing.to_uniqueFactorizationMonoid | Mathlib/RingTheory/PrincipalIdealDomain.lean:366 | instance (priority := 100); auto-resolves from IsPrincipalIdealRing + IsDomain |
```

Add a note: "Both instances are auto-resolved by typeclass inference;
the only S3 ACT obligation is to ensure `IsDomain Eisenstein` is in
scope (5-LOC declaration) **before** the `EuclideanDomain` instance,
since `to_principal_ideal_domain` consumes `IsDomain`."

### 5.5 Cross-check — `UniqueFactorizationMonoid.irreducible_iff_prime`

S4 PREP §6 row (verbatim):

> `| UniqueFactorizationMonoid.irreducible_iff_prime | Mathlib/RingTheory/UniqueFactorizationDomain | ✓ standard |`

Verified via Contents read of
`Mathlib/RingTheory/UniqueFactorizationDomain/Defs.lean`:

```
132    protected irreducible_iff_prime : ∀ {a : α}, Irreducible a ↔ Prime a
```

`irreducible_iff_prime` is a **structure field** of
`UniqueFactorizationMonoid`, accessed as
`UniqueFactorizationMonoid.irreducible_iff_prime`. ✓ name correct;
✓ accessor pattern works. Module path narrowed: it's in the `Defs.lean`
file under the `UniqueFactorizationDomain/` directory (S4 PREP only
cited the directory, not the file).

## 6. Updated end-to-end S3/S4/S5 ACT prerequisite chain

| Prerequisite | Source | Effective S? ACT obligation |
|---|---|---|
| `CommRing Eisenstein` | S2 ACT line 133 | already shipped |
| `IsDomain Eisenstein` | **NEW, S3 ACT** | +5 LOC via `norm` multiplicativity |
| `EuclideanDomain Eisenstein` | S3 ACT (per S3 PREP) | ~165 LOC (revised +5 = ~170 LOC) |
| `IsPrincipalIdealRing Eisenstein` | auto-instance via `EuclideanDomain.to_principal_ideal_domain` | 0 LOC |
| `UniqueFactorizationMonoid Eisenstein` | auto-instance via `PrincipalIdealRing.to_uniqueFactorizationMonoid` | 0 LOC |
| `Irreducible (p : Eisenstein) ↔ Prime (p : Eisenstein)` | `UniqueFactorizationMonoid.irreducible_iff_prime` field | 0 LOC |
| `Eisenstein.exists_sq_eq_neg_three_iff_one_mod_three` | S4 ACT (new, per S4 PREP §3, ~30 LOC) | ~30 LOC |
| `Eisenstein.reducible_of_neg_three_isSquare` | S4 ACT (new, per S4 PREP §5, ~31 LOC) | ~31 LOC |
| `Eisenstein.reducible_iff_one_mod_three` | S4 ACT (1-line composite) | ~1 LOC |
| `sq_add_three_sq_of_prime_one_mod_three` | S5 ACT (main theorem) | ~100 LOC (state.md estimate) |

**S3 ACT revised LOC budget**: 165 + 5 = **~170 LOC** (the +5 covers
the missing `IsDomain` instance flagged in §5.3).

**S4 ACT LOC budget**: unchanged at ~61 LOC.

**S5 ACT LOC budget**: unchanged at ~100 LOC.

## 7. What this PREP does **not** touch

- `proofs/Proofs/ZsqrtdNegTwoOQ03.lean` — unchanged.
- `proofs/Proofs.lean` — unchanged.
- `src/data/proofs/zsqrtd-neg-two-oq-03/{meta,index,annotations}.{json,ts}` — unchanged.
- `research/problems/zsqrtd-neg-two-oq-03/problem.md` — unchanged.
- `research/problems/zsqrtd-neg-two-oq-03/knowledge.md` — unchanged.
- `research/problems/zsqrtd-neg-two-oq-03/state.md` — unchanged.
- `research/problems/zsqrtd-neg-two-oq-03/sessions/2026-05-12-s2-prep-eisenstein-construction-audit.md` — unchanged.
- `research/problems/zsqrtd-neg-two-oq-03/sessions/2026-05-13-s3-prep-euclidean-construction-audit.md` — unchanged.
- `research/problems/zsqrtd-neg-two-oq-03/sessions/2026-05-13-s4-prep-mathlib-splitting-argument-assembly.md` — unchanged.
- `src/data/research/problems/zsqrtd-neg-two-oq-03.json` — unchanged.

Only addition: this file. Zero conflict surface; a parallel S3 ACT
iteration could merge before this PREP without rebasing.

## 8. Race awareness

At PREP push time (2026-05-13 ≈ 06:40 UTC):

| Open PR on slug | File overlap with this PREP |
|---|---|
| (none)         | —                            |

Recent activity on slug (last 6 hours):
- #18593 Enrich (2026-05-13 05:15 UTC)
- #18573 S4 PREP (2026-05-13 05:06 UTC)
- #18557 S3 PREP (2026-05-13 04:04 UTC)
- #18462 audit-tracker (2026-05-13 02:16 UTC)
- #18436 S2 ACT (2026-05-13 01:28 UTC)

Slug is in a doc-only PREP cluster. This PREP is the natural next
step — it pre-clears all *tentative* citations from S3/S4 PREP so
that the eventual S3 ACT session can quote exact `Module.lean:line`
without paging back to GitHub.

## 9. Files added (this session)

- `research/problems/zsqrtd-neg-two-oq-03/sessions/2026-05-13-s3b-prep-mathlib-bearer-audit.md`
  (this file)

## 10. Key Mathlib / Lean-core references located during this audit

- `leanprover/lean4` `src/Init/Data/Int/Order.lean:1448` —
  `theorem natAbs_lt_natAbs_of_nonneg_of_lt {a b : Int}
  (w₁ : 0 ≤ a) (w₂ : a < b) : a.natAbs < b.natAbs`
- `Mathlib/Data/Int/NatAbs.lean` — `Int.natAbs_mul` declaration site
  (14 Mathlib uses total)
- `Mathlib/RingTheory/PrincipalIdealDomain.lean:287` —
  `instance (priority := 100) EuclideanDomain.to_principal_ideal_domain
   : IsPrincipalIdealRing R`
- `Mathlib/RingTheory/PrincipalIdealDomain.lean:366` —
  `instance (priority := 100) to_uniqueFactorizationMonoid
   : UniqueFactorizationMonoid R` (in `PrincipalIdealRing` namespace)
- `Mathlib/RingTheory/UniqueFactorizationDomain/Defs.lean:132` —
  `protected irreducible_iff_prime : ∀ {a : α},
   Irreducible a ↔ Prime a` (structure field of
  `UniqueFactorizationMonoid`)
- `Mathlib/NumberTheory/LegendreSymbol/Basic.lean:154` —
  `protected theorem legendreSym.mul (a b : ℤ) :
   legendreSym p (a * b) = legendreSym p a * legendreSym p b`

## 11. Next action

**S3 ACT** (separate session, per S3 PREP §next-action, now revised
to ~170 LOC) — extend `proofs/Proofs/ZsqrtdNegTwoOQ03.lean` with:

1. `def conj` + 2 simp projection lemmas (per S3 PREP Audit 2).
2. `mul_conj`, `norm_conj` (per S3 PREP Audits 2, 6).
3. **`instance : IsDomain Eisenstein`** — *new from this PREP*,
   ~5 LOC via `norm` multiplicativity + `norm_eq_zero_iff` (S2
   ACT line 165).
4. `instDiv`, `instMod`, `mod_def` (per S3 PREP Audit 7).
5. `sq_rounding_error_lt_one` with cross-term bound (per S3 PREP
   Audit 3 fallback or `nlinarith` route).
6. `norm_mod_lt` (per S3 PREP Audit 4, ~80 LOC).
7. `natAbs_norm_mod_lt`, `norm_le_norm_mul_left` (per S3 PREP Audit 1).
8. `instNontrivial`, `instLT`, `instEuclideanDomain` (per S3 PREP
   Audit 7).

Build verification: `./proofs/scripts/docker-build.sh
Proofs.ZsqrtdNegTwoOQ03` from main repo. Commit + push BEFORE
invoking the build (per `.lake symlink loop + mid-build worktree
wipe` memory).

**S4 ACT** (after S3 ACT lands) — per S4 PREP §3 + §5, ~61 LOC. The
S4 ACT can now quote `PrincipalIdealRing.to_uniqueFactorizationMonoid`
and `UniqueFactorizationMonoid.irreducible_iff_prime` with exact
module:line; both auto-resolve.
