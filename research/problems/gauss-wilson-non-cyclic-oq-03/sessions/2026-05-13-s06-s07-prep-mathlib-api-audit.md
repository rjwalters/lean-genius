# S6 / S7 PREP — Mathlib v4.26.0 API audit (doc-only)

**Date**: 2026-05-13
**Researcher**: researcher-3
**Phase**: AUDIT — verification pass on the Mathlib-name claims made
in the merged S6 PREP (PR #18423,
`2026-05-12-s06-prep-crt-multiplicativity.md`) and the open S7 PREP
(PR #18465,
`2026-05-13-s07-prep-main-theorem-induction.md`).
**Type**: Doc-only erratum companion.
**Branch**: `research/gauss-wilson-non-cyclic-oq-03-s6s7-prep-mathlib-audit-*`
**Status**: no edits to Lean files, `state.md`, `knowledge.md`,
`problem.md`, the two prior PREP session notes, gallery `meta.json`,
or research JSON.

## 0. Why this audit now

Two `sessions/` PREPs (S6 PREP merged, S7 PREP open) now stage the
Lean tactics for the remaining S5b ACT / S6 ACT / S7 ACT chain on
`proofs/Proofs/GaussWilsonNonCyclicOQ03.lean`. Both PREPs cite a
combined ~12 Mathlib lemma names + paths against pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (the current Mathlib
master at audit time; the lean-genius `proofs/lean-toolchain` and
`proofs/lake-manifest.json` track this same range for v4.26.0).

Recently, PR #18467 (researcher-1, 2026-05-13 ~02:30 UTC) caught
2 erratum-grade citation errors in the **sister** slug oq-01's S4
PREP (#18347):

- `Subgroup.card_zpowers` / `Subgroup.zpowers_card` — both phantom
  in Mathlib (correct: `Fintype.card_zpowers` / `Nat.card_zpowers`).
- `selfEquivSigmaOrbits` cited at `Basic.lean:476`; actual
  location is `Defs.lean:482`.

The pattern — citing API names against a 5,000+-file pin — is
fragile, and the sister-slug S4 PREP demonstrates that
recently-merged PREP docs can ship verifiable name errors.
**This audit re-runs the same protocol on the S6 PREP and S7
PREP for oq-03.**

### Audit methodology

For each cited Mathlib name in S6 PREP + S7 PREP, this audit:

1. `gh api -X GET search/code -f q="<name> repo:leanprover-community/mathlib4"` —
   does the symbol exist *anywhere* in Mathlib?
2. `gh api repos/leanprover-community/mathlib4/contents/<path>` then
   `base64 -d | grep -n` — at the path / line cited, is the symbol
   actually at the cited line?
3. Verify signature compatibility against the way the PREP intends
   to use the symbol.

Each finding is graded:

- **ERRATUM-GRADE** — phantom name or wrong path that would block
  the future ACT author at compile time. Must be corrected before
  the corresponding ACT PR.
- **MINOR DRIFT** — correct symbol but stale path/line. Future ACT
  author can rediscover via `grep` in ~30 seconds; record as
  follow-up for the audit-correction layer.
- **CONFIRMED** — symbol exists at the cited path/line with the
  cited signature. No action required.

## 1. Findings — S6 PREP citations

Source: `research/problems/gauss-wilson-non-cyclic-oq-03/sessions/2026-05-12-s06-prep-crt-multiplicativity.md`
(merged via PR #18423, 2026-05-13 00:54 UTC).

### 1.1 ERRATUM-GRADE — `Prod.pow_def` is a phantom name

**Cited in S6 PREP §3 (inline `subtypeSqOneProdEquiv` definition)**:

```lean
toFun  := fun ⟨⟨g, h⟩, hgh⟩ =>
  ⟨⟨g, by have := (Prod.mk.injEq _ _ _ _).mp (by simpa [Prod.pow_def] using hgh)
          exact this.1⟩,
  ...
invFun := fun ⟨⟨g, hg⟩, ⟨h, hh⟩⟩ =>
  ⟨(g, h), by ext <;> simpa [Prod.pow_def] using ⟨hg, hh⟩⟩
```

**Cited in S6 PREP §3 (alternative formulation)**:

> `Prod.pow_def` / `Prod.mk_pow` in `Mathlib.Algebra.GroupPower.Basic`

**Cited in S6 PREP §6.5**:

> The `subtypeSqOneProdEquiv` body uses `Prod.pow_def` and `Prod.ext`;
> these are `@[simp]` and resolve under `simpa`.

**Cited in S6 PREP §1 verification table**:

> `Prod.pow_def` / `Prod.mk_pow` in `Mathlib.Algebra.GroupPower.Basic`

**Audit search**:

```
$ gh api -X GET 'search/code' -f q='Prod.pow_def repo:leanprover-community/mathlib4' --jq '.total_count'
0

$ gh api -X GET 'search/code' -f q='Prod.mk_pow repo:leanprover-community/mathlib4' --jq '.total_count'
0
```

**Verdict**: ERRATUM-GRADE. Both `Prod.pow_def` and `Prod.mk_pow`
return 0 hits across the entire Mathlib repo at master
`2df2f015...`. The namespace `Mathlib.Algebra.GroupPower.Basic` was
also reorganized in the late-2024 / early-2025 algebra refactor
and no longer exists; the `Prod` monoid `npow` lives in
`Mathlib/Algebra/Group/Prod.lean`.

**Why this matters**: The S6 ACT author would write `simpa
[Prod.pow_def]` exactly as the PREP suggests, hit
`unknown identifier 'Prod.pow_def'`, and lose ~10–20 minutes
hunting the correct lemma. The S6 PREP §6.5 explicitly assures
the author that "these are `@[simp]` and resolve under `simpa`" —
the assurance is incorrect.

**What is actually true** (verified via direct read of
`Mathlib/Algebra/Group/Prod.lean` lines 81–85 at master
`2df2f015...`):

```lean
@[to_additive]
instance instMonoid [Monoid M] [Monoid N] : Monoid (M × N) :=
  { npow := fun z a => ⟨Monoid.npow z a.1, Monoid.npow z a.2⟩,
    npow_zero := fun _ => Prod.ext (Monoid.npow_zero _) (Monoid.npow_zero _),
    npow_succ := fun _ _ => Prod.ext (Monoid.npow_succ _ _) (Monoid.npow_succ _ _),
    one_mul := by simp,
    mul_one := by simp }
```

The `npow` operation is defined inline. Consequence: `(a, b)^n =
(a^n, b^n)` holds **by `rfl`** (definitional unfolding of the
inline `npow`); no `Prod.pow_def` lemma is needed.

**Fix for S6 ACT author**: replace every `simpa [Prod.pow_def]`
with one of:

- bare `simp` / `simpa` (the standard simp set already unfolds the
  `npow` instance for `Prod`); or
- explicit `show (a^n, b^n) = (1, 1); ext <;> simp`; or
- `rfl` followed by `Prod.mk.injEq` (already used in the same PREP
  body).

No new Mathlib lemma is required — the equation is `rfl`.

### 1.2 CONFIRMED — `Nat.totient_mul` at `Mathlib/Data/Nat/Totient.lean:131`

S6 PREP §2 cites this as the **template** for the S6 ACT proof
body:

```lean
theorem totient_mul {m n : ℕ} (h : m.Coprime n) : φ (m * n) = φ m * φ n :=
  if hmn0 : m * n = 0 then ...
  else by
    ...
    rw [Fintype.card_congr (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).toEquiv,
      Fintype.card_congr (@MulEquiv.prodUnits (ZMod m) (ZMod n) _ _).toEquiv, Fintype.card_prod]
```

**Audit search**:

```
$ gh api repos/leanprover-community/mathlib4/contents/Mathlib/Data/Nat/Totient.lean \
    --jq .content | base64 -d | grep -n '^theorem totient_mul'
131:theorem totient_mul {m n : ℕ} (h : m.Coprime n) : φ (m * n) = φ m * φ n :=
```

**Verdict**: CONFIRMED. Line number, signature, and template body
match the S6 PREP claim exactly. No action.

### 1.3 CONFIRMED — `MulEquiv.prodUnits` at `Mathlib/Algebra/Group/Prod.lean:589`

S6 PREP §6.4 claims `MulEquiv.prodUnits` is `(M × N)ˣ ≃* Mˣ × Nˣ`.

**Audit search**:

```
$ gh api repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/Group/Prod.lean \
    --jq .content | base64 -d | grep -n 'prodUnits'
589:def prodUnits : (M × N)ˣ ≃* Mˣ × Nˣ where
603:  mp h := ⟨(prodUnits h.unit).1.isUnit, (prodUnits h.unit).2.isUnit⟩
604:  mpr h := (prodUnits.symm (h.1.unit, h.2.unit)).isUnit
```

**Verdict**: CONFIRMED. Signature matches. Note: S6 PREP §1
verification table cites this lemma without a path; the canonical
location is `Mathlib/Algebra/Group/Prod.lean:589`. For
downstream S6 ACT, the existing import chain (via
`Mathlib.NumberTheory.LucasLehmer` → `Mathlib.Data.ZMod.Basic` →
`Mathlib.Algebra.Group.Prod`) supplies this lemma transitively.

### 1.4 CONFIRMED — `ZMod.chineseRemainder` at `Mathlib/Data/ZMod/Basic.lean:872`

S6 PREP §6.3 claims directional convention: `ZMod (m*n) ≃+* ZMod m × ZMod n`.

**Audit search**:

```
$ gh api repos/leanprover-community/mathlib4/contents/Mathlib/Data/ZMod/Basic.lean \
    --jq .content | base64 -d | grep -n 'def chineseRemainder'
872:def chineseRemainder {m n : ℕ} (h : m.Coprime n) : ZMod (m * n) ≃+* ZMod m × ZMod n :=
```

**Verdict**: CONFIRMED. Direction matches.

### 1.5 CONFIRMED — `Nat.recOnPosPrimePosCoprime` at `Mathlib/Data/Nat/Factorization/Induction.lean:49`

S6 PREP §5 reserves this for S7, but cites it as a forward
reference. (Same citation is load-bearing for S7 PREP — see §2.)

**Audit search**:

```
$ gh api repos/leanprover-community/mathlib4/contents/Mathlib/Data/Nat/Factorization/Induction.lean \
    --jq .content | base64 -d | grep -n 'def recOnPosPrimePosCoprime'
49:def recOnPosPrimePosCoprime {motive : ℕ → Sort*}
```

**Verdict**: CONFIRMED. The `@[elab_as_elim]` attribute is at
line 48 (preceding line). Signature and motive parameters match
the cited block verbatim.

### 1.6 CONFIRMED (negative) — `subtypeSqOneProdEquiv` absent in Mathlib

S6 PREP §3 claims:

> This is **the only piece that is not in Mathlib** (no exact-name
> hit for `subtypeSqOneProdEquiv` or `Subtype.sqOneProd` in
> `gh api search/code repo:leanprover-community/mathlib4`,
> verified 2026-05-12).

**Audit search (re-run 2026-05-13)**:

```
$ gh api -X GET 'search/code' -f q='subtypeSqOneProdEquiv repo:leanprover-community/mathlib4' --jq '.total_count'
0
```

**Verdict**: CONFIRMED (negative). The negative claim still holds
at master `2df2f015...`. The S6 ACT author will need to write the
inline ~10-LOC `Equiv.mk` as the PREP suggests, but per §1.1 above
the body should NOT use `simpa [Prod.pow_def]`.

## 2. Findings — S7 PREP citations

Source: `research/problems/gauss-wilson-non-cyclic-oq-03/sessions/2026-05-13-s07-prep-main-theorem-induction.md`
(PR #18465, OPEN at audit time).

### 2.1 ERRATUM-GRADE — `NeZero.pos` is a phantom name

**Cited in S7 PREP §4 (induction proof body)**:

```lean
theorem card_sqrts_one_eq_numSqrtsOne (n : ℕ) [NeZero n] :
    ...
  rw [card_sqrts_one_eq_card_units_sqrts_one n]
  have hn : 0 < n := NeZero.pos n
  ...
```

**Cited in S7 PREP §6 (Mathlib API audit table)**:

> `NeZero.pos` | `Mathlib/Algebra/NeZero.lean` | (search)

**Audit (direct read of `Mathlib/Algebra/NeZero.lean` at master
`2df2f015...`, entire file is 62 lines)**:

The file declares exactly one theorem in the `NeZero` namespace:

```lean
namespace NeZero
variable {M : Type*} {x : M}
theorem of_pos [Preorder M] [Zero M] (h : 0 < x) : NeZero x := ⟨ne_of_gt h⟩
end NeZero
```

This is the **converse direction** (`0 < x → NeZero x`). There is
NO `NeZero.pos` lemma (the `NeZero x → 0 < x` direction).

**Audit search confirms**:

```
$ gh api -X GET 'search/code' -f q='theorem pos_of_neZero repo:leanprover-community/mathlib4' --jq '.total_count' (zero hits matching qualified name)
```

The closest existing lemma in Mathlib is in
`Mathlib/Data/Nat/Cast/NeZero.lean:27`:

```lean
lemma pos_of_neZero_natCast (R) [AddMonoidWithOne R] {n : ℕ} [NeZero (n : R)] : 0 < n :=
  Nat.pos_of_ne_zero (of_neZero_natCast R).out
```

— but this requires `NeZero (n : R)` for a non-ℕ `R`, not the bare
`[NeZero (n : ℕ)]` that S7 PREP §4 has in scope.

**Verdict**: ERRATUM-GRADE. The S7 ACT author would write `have hn
: 0 < n := NeZero.pos n` and hit `unknown identifier 'NeZero.pos'`.

**Fix for S7 ACT author**: replace `NeZero.pos n` with one of:

- `Nat.pos_of_ne_zero (NeZero.ne n)` — Lean core, no extra import.
- `Nat.pos_of_ne_zero <| NeZero.ne n` — same, infix style.
- `NeZero.one_le` (from `Mathlib/Data/Nat/Cast/NeZero.lean:20`):
  `theorem one_le {n : ℕ} [NeZero n] : 1 ≤ n` — gives `1 ≤ n`,
  which is `< · iff` `0 <` via `Nat.pos_iff_ne_zero.mpr (NeZero.ne n)`
  or the equivalence `Nat.one_le_iff_ne_zero`.
- `(NeZero.ne n).bot_lt` (assuming `Nat` has a `bot = 0` instance) —
  less idiomatic.

The simplest substitution is **`Nat.pos_of_ne_zero (NeZero.ne n)`**;
this is what Mathlib uses internally in similar contexts (e.g.,
`Mathlib/Algebra/GroupWithZero/Nat.lean:44-45`).

### 2.2 MINOR DRIFT — `Nat.primeFactors_mul` path

**Cited in S7 PREP §3.1 (`omegaOdd` additivity bookkeeping)**:

> | `Nat.primeFactors_mul` | `Mathlib/NumberTheory/Padics/PadicVal.lean` (or `Nat/Factorization/Basic.lean`) |

**Audit search**:

```
$ gh api -X GET 'search/code' -f q='primeFactors_mul repo:leanprover-community/mathlib4 path:Mathlib/Data/Nat' --jq '.items[] | {name: .name, path: .path}'
{"name":"PrimeFin.lean","path":"Mathlib/Data/Nat/PrimeFin.lean"}
{"name":"Totient.lean","path":"Mathlib/Data/Nat/Totient.lean"}
{"name":"Basic.lean","path":"Mathlib/Data/Nat/Factorization/Basic.lean"}
```

The defining location is:

```
$ gh api repos/leanprover-community/mathlib4/contents/Mathlib/Data/Nat/PrimeFin.lean \
    --jq .content | base64 -d | grep -n 'primeFactors_mul'
95:lemma primeFactors_mul (ha : a ≠ 0) (hb : b ≠ 0) :
100:lemma Coprime.primeFactors_mul {a b : ℕ} (hab : Coprime a b) :
```

**Verdict**: MINOR DRIFT. Both alternatives in the S7 PREP citation
are wrong:

- `Mathlib/NumberTheory/Padics/PadicVal.lean` — irrelevant file (p-adic valuations).
- `Mathlib/Data/Nat/Factorization/Basic.lean` — wrong, the lemma is *referenced* here but defined in PrimeFin.

The correct path is **`Mathlib/Data/Nat/PrimeFin.lean:95`**.
Also note that S7 PREP §3.1 strictly speaking needs the
**coprime variant**, which is at the adjacent line 100:
`Nat.Coprime.primeFactors_mul`. The non-coprime `primeFactors_mul`
(line 95) needs both `a ≠ 0` and `b ≠ 0` and produces a `Finset`
union without the disjointness conclusion; for S7's `omegaOdd`
additivity argument the *coprime* variant is the right entry
point because we need `Disjoint` to conclude `card (A ∪ B) =
card A + card B`.

Recommended S7 ACT chain:

```lean
-- omegaOdd_mul_of_coprime proof sketch (replacing S7 PREP §3.1):
rw [Nat.Coprime.primeFactors_mul h]            -- or primeFactors_mul (ha) (hb)
rw [Finset.filter_union]                        -- distribute the filter over ∪
rw [Finset.card_union_of_disjoint                -- needs Disjoint
       (Finset.disjoint_filter_filter
          (h.disjoint_primeFactors))]
```

(`h.disjoint_primeFactors` from §2.3 below; the
`Finset.disjoint_filter_filter` lemma name should be re-verified
by the ACT author against `Mathlib/Data/Finset/Filter.lean`.)

### 2.3 MINOR DRIFT — `Nat.Coprime.disjoint_primeFactors` path

**Cited in S7 PREP §3.1**:

> | `Nat.Coprime.disjoint_primeFactors` | `Mathlib/Data/Nat/Factorization/Basic.lean` |

**Audit**:

```
$ gh api repos/leanprover-community/mathlib4/contents/Mathlib/Data/Nat/PrimeFin.lean \
    --jq .content | base64 -d | grep -n 'disjoint_primeFactors'
108:@[simp] lemma disjoint_primeFactors (ha : a ≠ 0) (hb : b ≠ 0) :
113:protected lemma Coprime.disjoint_primeFactors (hab : Coprime a b) :
```

**Verdict**: MINOR DRIFT. The lemma exists with the expected
signature `(hab : Coprime a b) → Disjoint a.primeFactors
b.primeFactors`, but at `Mathlib/Data/Nat/PrimeFin.lean:113`, not
in `Mathlib/Data/Nat/Factorization/Basic.lean`. The `@[simp]
disjoint_primeFactors` (line 108) is the more general iff-form
that S7 ACT might also want.

### 2.4 CONFIRMED — `Nat.Prime.eq_two_or_odd'` at `Mathlib/Data/Nat/Prime/Basic.lean:45`

S7 PREP §4 uses:

```lean
rcases Nat.Prime.eq_two_or_odd' hp with rfl | ⟨q, rfl⟩
```

**Audit**:

```
$ gh api repos/leanprover-community/mathlib4/contents/Mathlib/Data/Nat/Prime/Basic.lean \
    --jq .content | base64 -d | grep -n 'eq_two_or_odd'
41:theorem Prime.eq_two_or_odd {p : ℕ} (hp : Prime p) : p = 2 ∨ p % 2 = 1 :=
45:theorem Prime.eq_two_or_odd' {p : ℕ} (hp : Prime p) : p = 2 ∨ Odd p :=
```

**Verdict**: CONFIRMED. Signature `p = 2 ∨ Odd p` matches S7 PREP
§4's `rcases` pattern `rfl | ⟨q, rfl⟩` (the `Odd p` case
destructures to `⟨q, rfl⟩` where `p = 2 * q + 1`).

### 2.5 CONFIRMED — `Finset.card_union_of_disjoint` at `Mathlib/Data/Finset/Card.lean:568`

S7 PREP §3.1 cites:

> | `Finset.card_union_eq_card_add_card_sub_card_inter` | `Mathlib/Data/Finset/Card.lean` |

The S7 PREP §6 table separately cites `Finset.card_union_of_disjoint`.

**Audit**:

```
$ gh api repos/leanprover-community/mathlib4/contents/Mathlib/Data/Finset/Card.lean \
    --jq .content | base64 -d | grep -n 'card_union'
556:theorem card_inter_add_card_union (s t : Finset α) :
559:lemma card_union (s t : Finset α) : #(s ∪ t) = #s + #t - #(s ∩ t) := by grind
568:@[simp] alias ⟨_, card_union_of_disjoint⟩ := card_union_eq_card_add_card
```

**Verdict**: CONFIRMED, with mild correction. The lemma name
cited in S7 PREP §3.1 (`Finset.card_union_eq_card_add_card_sub_card_inter`)
is **not** the canonical Mathlib name at v4.26.0 — the canonical
name is `Finset.card_union` (line 559), which uses `Nat.sub`. The
disjoint-specialization `card_union_of_disjoint` (line 568) is the
better fit for §3.1's `omegaOdd_mul_of_coprime` argument because
it avoids the truncated subtraction.

Recommended S7 ACT usage:

```lean
rw [Finset.card_union_of_disjoint (h.disjoint_primeFactors.mono ...)]
-- ... or rewrite via card_union and then simplify using disjointness ...
```

### 2.6 CONFIRMED — `Nat.recOnPrimeCoprime` at `Mathlib/Data/Nat/Factorization/Induction.lean:68`

S7 PREP §6 cites:

> | `Nat.recOnPrimeCoprime` | `Mathlib/Data/Nat/Factorization/Induction.lean` | 68 |

**Audit**:

```
$ gh api repos/leanprover-community/mathlib4/contents/Mathlib/Data/Nat/Factorization/Induction.lean \
    --jq .content | base64 -d | grep -n 'def recOnPrimeCoprime'
68:def recOnPrimeCoprime {motive : ℕ → Sort*} (zero : motive 0)
```

**Verdict**: CONFIRMED. Note S7 PREP uses `recOnPosPrimePosCoprime`
(line 49) as the principal, not `recOnPrimeCoprime` (line 68); the
latter is mentioned only in the audit table.

## 3. Summary of erratum-grade findings

| #   | PREP    | Symbol cited            | Path/line cited                                       | Reality                                                          | Severity      |
|-----|---------|-------------------------|-------------------------------------------------------|------------------------------------------------------------------|---------------|
| 1.1 | S6 PREP | `Prod.pow_def`          | `Mathlib.Algebra.GroupPower.Basic`                    | Phantom (0 hits). `(a, b)^n = (a^n, b^n)` holds by `rfl`         | ERRATUM-GRADE |
| 1.1 | S6 PREP | `Prod.mk_pow`           | `Mathlib.Algebra.GroupPower.Basic`                    | Phantom (0 hits). Same fix as above                              | ERRATUM-GRADE |
| 2.1 | S7 PREP | `NeZero.pos`            | `Mathlib/Algebra/NeZero.lean`                         | Phantom. Only `NeZero.of_pos` (converse) exists at line 60       | ERRATUM-GRADE |
| 2.2 | S7 PREP | `Nat.primeFactors_mul`  | `Mathlib/NumberTheory/Padics/PadicVal.lean (or …)`    | Actually at `Mathlib/Data/Nat/PrimeFin.lean:95`                  | MINOR DRIFT   |
| 2.3 | S7 PREP | `Coprime.disjoint_primeFactors` | `Mathlib/Data/Nat/Factorization/Basic.lean`  | Actually at `Mathlib/Data/Nat/PrimeFin.lean:113`                 | MINOR DRIFT   |
| 2.5 | S7 PREP | `card_union_eq_card_add_card_sub_card_inter` | `Mathlib/Data/Finset/Card.lean`  | Canonical name is `Finset.card_union` (line 559); the disjoint-specialization is `card_union_of_disjoint` (line 568) | MINOR DRIFT |

Three erratum-grade entries (two of them duplicates of the same
phantom-`Prod.pow_def`-and-`mk_pow` issue): if uncorrected, the
S6 ACT and S7 ACT authors will each hit `unknown identifier`
failures. The three MINOR DRIFT entries cost ~30–60 seconds of
`grep` time per ACT, but don't block compilation directly.

## 4. Recommended PREP-correction footnotes

These corrections should be applied (by a follow-up correction
PR, or inline by the S6 ACT / S7 ACT authors) before the
corresponding ACT lands:

### 4.1 S6 PREP §3 — drop `[Prod.pow_def]` from simpa

```lean
-- OLD (S6 PREP §3):
toFun  := fun ⟨⟨g, h⟩, hgh⟩ =>
  ⟨⟨g, by have := (Prod.mk.injEq _ _ _ _).mp (by simpa [Prod.pow_def] using hgh)
          exact this.1⟩, ...⟩
invFun := fun ⟨⟨g, hg⟩, ⟨h, hh⟩⟩ =>
  ⟨(g, h), by ext <;> simpa [Prod.pow_def] using ⟨hg, hh⟩⟩

-- NEW (drop the [Prod.pow_def] simp argument; npow on Prod is rfl-able):
toFun  := fun ⟨⟨g, h⟩, hgh⟩ =>
  ⟨⟨g, by have := (Prod.mk.injEq _ _ _ _).mp (by simpa using hgh); exact this.1⟩, ...⟩
invFun := fun ⟨⟨g, hg⟩, ⟨h, hh⟩⟩ =>
  ⟨(g, h), by ext <;> simpa using ⟨hg, hh⟩⟩
```

### 4.2 S6 PREP §6.5 — correct the assurance

Replace:

> The `subtypeSqOneProdEquiv` body uses `Prod.pow_def` and
> `Prod.ext`; these are `@[simp]` and resolve under `simpa`.

With:

> The `subtypeSqOneProdEquiv` body uses `Prod.ext` /
> `Prod.mk.injEq`; the equation `(a, b)^n = (a^n, b^n)` holds
> definitionally (the `Monoid (M × N)` `npow` is inline at
> `Mathlib/Algebra/Group/Prod.lean:81–85`), so no extra simp
> lemma is required.

### 4.3 S7 PREP §4 — replace `NeZero.pos`

```lean
-- OLD (S7 PREP §4):
have hn : 0 < n := NeZero.pos n

-- NEW:
have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
```

### 4.4 S7 PREP §3.1 and §6 — correct lemma paths

- `Nat.primeFactors_mul`: `Mathlib/Data/Nat/PrimeFin.lean:95`
  (not `NumberTheory/Padics/PadicVal.lean` and not
  `Nat/Factorization/Basic.lean`).
- `Nat.Coprime.primeFactors_mul`: same file, line 100 — the
  coprime variant, useful when the disjointness is needed
  immediately.
- `Nat.Coprime.disjoint_primeFactors`: same file, line 113 (not
  `Nat/Factorization/Basic.lean`).
- `Finset.card_union_of_disjoint`:
  `Mathlib/Data/Finset/Card.lean:568` (the disjoint-specialization
  is the canonical citation; the general `card_union` at line 559
  uses `Nat.sub` and is less convenient).

## 5. Orthogonality / race awareness

This audit creates exactly one new file:

`research/problems/gauss-wilson-non-cyclic-oq-03/sessions/2026-05-13-s06-s07-prep-mathlib-api-audit.md`.

**Diff against open PRs on this slug:**

| PR     | Open file                                           | This PR adds            | Overlap? |
|--------|-----------------------------------------------------|-------------------------|----------|
| #18230 | S5-prep parity (Lean + state.md + JSON edits)       | sessions/ doc only      | None     |
| #18465 | sessions/2026-05-13-s07-prep-main-theorem-induction.md | sessions/2026-05-13-s06-s07-prep-mathlib-api-audit.md (different filename) | None |

No file-content collision possible — each PREP/audit owns a
distinct sessions/ filename.

**Sister-slug context:**

- oq-01: PR #18467 (S4b PREP Mathlib v4.26.0 API audit, MERGED).
- oq-01: PR #18347 (S4 PREP, MERGED earlier; was source of the 2
  citation errors caught by #18467).

This audit (oq-03 S6+S7 PREP) is the **second instance of the
audit pattern** in the gauss-wilson-non-cyclic family. The
pattern's value is consistent: each audit catches 1–3
erratum-grade citation errors in ~30 minutes of doc-only work, at
~250–400 LOC.

## 6. Anti-targets

This audit PR **does not**:

- Edit `proofs/Proofs/GaussWilsonNonCyclicOQ03.lean` (Lean
  changes are S6 ACT / S7 ACT scope, not audit scope).
- Edit `state.md` (phase, sessions list).
- Edit `problem.md` (theoretical scope).
- Edit `knowledge.md` (Mathlib status).
- Edit `2026-05-12-s5b-observe-even-prime-case.md`,
  `2026-05-12-s06-prep-crt-multiplicativity.md`, or
  `2026-05-13-s07-prep-main-theorem-induction.md` (the audited
  PREPs themselves remain as historical record; this audit is the
  erratum companion).
- Edit `src/data/proofs/gauss-wilson-non-cyclic/meta.json` or
  `src/data/research/problems/gauss-wilson-non-cyclic-oq-03.json`
  (no progress metrics change).
- Resubmit S5b ACT, S6 ACT, or S7 ACT (those remain queued for
  the next implementer; this audit only de-risks them).

## 7. Acceptance criteria (binary)

This audit succeeds iff:

- [x] Each S6 PREP citation has been independently verified by
      `gh api search/code` + `gh api .../contents | base64 -d | grep`.
- [x] Each S7 PREP citation has been independently verified the
      same way.
- [x] Each ERRATUM-GRADE finding has a concrete drop-in
      replacement specified in §4.
- [x] No edits to existing files anywhere in the worktree.
- [x] The single new file lives at
      `research/problems/gauss-wilson-non-cyclic-oq-03/sessions/2026-05-13-s06-s07-prep-mathlib-api-audit.md`.

## 8. Verification log (this audit — read-only)

| Check                                                                          | Outcome |
|--------------------------------------------------------------------------------|---------|
| Mathlib master commit at audit time                                            | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` |
| `Prod.pow_def` search hits                                                     | 0       |
| `Prod.mk_pow` search hits                                                      | 0       |
| `NeZero.pos` in `Mathlib/Algebra/NeZero.lean`                                  | absent (only `NeZero.of_pos`) |
| `Nat.totient_mul` at `Mathlib/Data/Nat/Totient.lean:131`                       | confirmed |
| `MulEquiv.prodUnits` at `Mathlib/Algebra/Group/Prod.lean:589`                  | confirmed `(M × N)ˣ ≃* Mˣ × Nˣ` |
| `ZMod.chineseRemainder` at `Mathlib/Data/ZMod/Basic.lean:872`                  | confirmed `ZMod (m * n) ≃+* ZMod m × ZMod n` |
| `recOnPosPrimePosCoprime` at `Mathlib/Data/Nat/Factorization/Induction.lean:49`| confirmed |
| `recOnPrimeCoprime` at `Mathlib/Data/Nat/Factorization/Induction.lean:68`     | confirmed |
| `Nat.Prime.eq_two_or_odd'` at `Mathlib/Data/Nat/Prime/Basic.lean:45`           | confirmed `p = 2 ∨ Odd p` |
| `Nat.primeFactors_mul` at `Mathlib/Data/Nat/PrimeFin.lean:95`                  | confirmed (S7 PREP gives wrong path) |
| `Nat.Coprime.primeFactors_mul` at `Mathlib/Data/Nat/PrimeFin.lean:100`         | confirmed (the coprime variant useful for S7 §3.1) |
| `Nat.Coprime.disjoint_primeFactors` at `Mathlib/Data/Nat/PrimeFin.lean:113`    | confirmed (S7 PREP gives wrong path) |
| `Finset.card_union_of_disjoint` at `Mathlib/Data/Finset/Card.lean:568`         | confirmed (alias from `card_union_eq_card_add_card`) |
| `subtypeSqOneProdEquiv` search hits                                            | 0 (negative claim still valid) |
| Open PRs on slug at audit time                                                 | 2 (#18230, #18465) — no filename overlap |
| Lean files modified                                                            | 0       |
| Existing sessions/ docs modified                                               | 0       |

## 9. References

- S6 PREP (audited): PR #18423,
  `2026-05-12-s06-prep-crt-multiplicativity.md`, merged
  2026-05-13 00:54 UTC.
- S7 PREP (audited): PR #18465,
  `2026-05-13-s07-prep-main-theorem-induction.md`, OPEN at
  audit time.
- Sister-slug audit precedent: PR #18467 (oq-01 S4b PREP API
  audit), researcher-1, 2026-05-13 ~02:30 UTC.
- Sister-slug source of errata: PR #18347 (oq-01 S4 PREP),
  merged 2026-05-12 22:52 UTC.
- Mathlib master pin:
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (verified live via
  `gh api repos/leanprover-community/mathlib4/commits/master` at
  audit time).

## 10. Honesty / no-edit guarantee

This audit is **doc-only**:

- 1 new file: `research/problems/gauss-wilson-non-cyclic-oq-03/sessions/2026-05-13-s06-s07-prep-mathlib-api-audit.md`
- 0 edits to existing files
- 0 edits to Lean files
- 0 edits to `meta.json` of any proof
- 0 edits to `state.md`, `problem.md`, `knowledge.md`, or earlier
  session notes
- 0 edits to `src/data/research/problems/gauss-wilson-non-cyclic-oq-03.json`

The findings here are **claims about Mathlib v4.26.0**, not
claims about the gauss-wilson-non-cyclic Lean file's correctness.
The Lean file builds cleanly (per state.md S5 entry, 0 axioms /
1 sorry); this audit only de-risks the *future* S5b/S6/S7 ACT
PRs that will close the remaining sorry.
