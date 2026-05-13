# S6 PREP — CRT Multiplicativity of the 2-Torsion Count

**Date**: 2026-05-12
**Researcher**: researcher-6
**Phase**: PREP (orientation for S6 ACT — downstream of S5b ACT)
**Type**: Doc-only design analysis.
**Branch**: `research/gauss-wilson-non-cyclic-oq-03-s6-prep-crt-multiplicativity-*`
**Status**: no edits to Lean files, `state.md`, `knowledge.md`,
`problem.md`, the prior `2026-05-12-s5b-observe-even-prime-case.md`
session note, gallery `meta.json`, or research JSON.

## 0. Why S6 PREP now

`state.md` "Next Action" enumerates the path forward:

> **S5b / S6 next**: even-prime case (k = 1, 2, ≥ 3 give 1, 2, 4) …
>
> **S6 (CRT multiplicativity)**: pulled back to a `Finset.prod` over
> `n.primeFactors`, applying `ZMod.chineseRemainder` and
> `Finset.prod_filter`.

The S5b OBSERVE doc (PR #18356, merged 2026-05-12 23:02 UTC) closed
the even-prime per-prime-power input. The next concrete deliverable
chain is:

1. **S5b ACT** (Lean): instantiate the `card = 1 / 2 / 4` counts for
   `(ZMod 2^k)ˣ` with `k = 1`, `k = 2`, `k ≥ 3`. The S5b OBSERVE doc
   already locks the Mathlib API and pseudocode.
2. **S6 ACT** (Lean): combine S5 (odd primes) + S5b (even prime) into
   the multiplicative formula on `(ZMod n)ˣ` via CRT.
3. **S7 ACT** (Lean): the headline `card_sqrts_one_eq_numSqrtsOne`
   theorem closes by induction on `n.primeFactors.card`, base case
   from S5/S5b, inductive step from S6.

This PREP locks the **Mathlib-template** for S6 by citing the
Mathlib v4.26.0 proof of `Nat.totient_mul`, which uses the **exact
same CRT + product-of-units rewrite chain** that S6 needs. The S6
ACT becomes a 2-step transcription with minor adaptations.

## 1. Goal of the eventual S6 ACT

Add a single theorem to `proofs/Proofs/GaussWilsonNonCyclicOQ03.lean`,
adjacent to (or replacing) the current `card_sqrts_one_eq_numSqrtsOne`
sorry. The theorem name is provisional:

```lean
/-- **(S6 multiplicativity)** Count of `u² = 1` solutions in
    `(ZMod (m * n))ˣ` factors as the product of per-component counts
    when `m` and `n` are coprime.

    This is the CRT step of the eventual `card_sqrts_one_eq_numSqrtsOne`
    closed-form, pulled back to a `Finset.prod` over `n.primeFactors`
    via `Nat.recOnPosPrimePosCoprime`. -/
theorem card_filter_sq_eq_one_units_mul_coprime
    {m n : ℕ} (h : m.Coprime n)
    [NeZero m] [NeZero n] :
    Fintype.card { u : (ZMod (m * n))ˣ // u^2 = 1 } =
      Fintype.card { u : (ZMod m)ˣ // u^2 = 1 } *
      Fintype.card { u : (ZMod n)ˣ // u^2 = 1 } := by
  sorry
```

Net delta target: +25-35 LOC including docstring and proof body. 0
new axioms; 1 sorry **converted** to a proof (no new sorries). The
sorry that closes is *not* the main `card_sqrts_one_eq_numSqrtsOne`
sorry yet — that closes in S7 by induction.

## 2. Mathlib-template citation: `Nat.totient_mul`

In `Mathlib/Data/Nat/Totient.lean` (v4.26.0 at rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`), line 131:

```lean
theorem totient_mul {m n : ℕ} (h : m.Coprime n) : φ (m * n) = φ m * φ n :=
  if hmn0 : m * n = 0 then by
    rcases Nat.mul_eq_zero.1 hmn0 with h | h <;>
      simp only [totient_zero, mul_zero, zero_mul, h]
  else by
    haveI : NeZero (m * n) := ⟨hmn0⟩
    haveI : NeZero m := ⟨left_ne_zero_of_mul hmn0⟩
    haveI : NeZero n := ⟨right_ne_zero_of_mul hmn0⟩
    simp only [← ZMod.card_units_eq_totient]
    rw [Fintype.card_congr (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).toEquiv,
      Fintype.card_congr (@MulEquiv.prodUnits (ZMod m) (ZMod n) _ _).toEquiv, Fintype.card_prod]
```

This is the precise template. The S6 lemma replaces `Fintype.card`
(of the whole unit group) with `Fintype.card { · // · ^ 2 = 1 }` (of
the 2-torsion subset). The CRT rewrite chain is *identical*. Only
one extra step is needed: the rewrite must be applied **inside the
subtype**, using a "Sigma-type / subtype-image" lemma to pull the
multiplicative isomorphism through the `· ^ 2 = 1` predicate.

## 3. The Sigma-bridge: 2-torsion is multiplicative across direct products

For any commutative groups `G` and `H`, the 2-torsion of the
product is the product of the 2-torsions:

```
{(g, h) : G × H // (g, h) ^ 2 = 1} ≃ {g : G // g^2 = 1} × {h : H // h^2 = 1}.
```

Proof: `(g, h)^2 = (g^2, h^2)`, and `Prod.ext` says `(g^2, h^2) = (1, 1) ↔ g^2 = 1 ∧ h^2 = 1`.

In Lean, the bridge is:

```lean
@[simps]
def subtypeSqOneProdEquiv {G H : Type*} [Monoid G] [Monoid H]
    [DecidableEq G] [DecidableEq H] :
    { gh : G × H // gh ^ 2 = 1 } ≃ { g : G // g^2 = 1 } × { h : H // h^2 = 1 } where
  toFun  := fun ⟨⟨g, h⟩, hgh⟩ =>
    ⟨⟨g, by have := (Prod.mk.injEq _ _ _ _).mp (by simpa [Prod.pow_def] using hgh)
            exact this.1⟩,
     ⟨h, by have := (Prod.mk.injEq _ _ _ _).mp (by simpa [Prod.pow_def] using hgh)
            exact this.2⟩⟩
  invFun := fun ⟨⟨g, hg⟩, ⟨h, hh⟩⟩ =>
    ⟨(g, h), by ext <;> simpa [Prod.pow_def] using ⟨hg, hh⟩⟩
  left_inv  := fun ⟨⟨g, h⟩, _⟩ => rfl
  right_inv := fun ⟨⟨g, _⟩, ⟨h, _⟩⟩ => rfl
```

This is **the only piece that is not in Mathlib** (no exact-name hit
for `subtypeSqOneProdEquiv` or `Subtype.sqOneProd` in
`gh api search/code repo:leanprover-community/mathlib4`, verified
2026-05-12). The lemma is ~10 LOC, elementary, and lives naturally
beside the S4 generic skeleton in the current file.

A simpler formulation using `Fintype.card_congr` directly on the
predicate-as-subtype:

```lean
-- LHS = Fintype.card { (g, h) // (g, h)^2 = 1 }
-- RHS = Fintype.card { g // g^2 = 1 } * Fintype.card { h // h^2 = 1 }
```

via

```lean
Fintype.card_subtype_compl + Fintype.card_prod + Fintype.card_subtype_or
```

— too fragile in practice; the `Equiv.mk` approach above is cleaner.

## 4. Proof plan for `card_filter_sq_eq_one_units_mul_coprime`

```
  -- assume NeZero (m * n), NeZero m, NeZero n via haveI clauses
  -- (paralleling totient_mul lines 134-136)
  apply Fintype.card_congr
  refine Equiv.trans ?_ subtypeSqOneProdEquiv
  -- The remaining `Equiv` is on
  --   { u : (ZMod (m*n))ˣ // u^2 = 1 }
  --   ≃ { ⟨ u₁, u₂ ⟩ : (ZMod m)ˣ × (ZMod n)ˣ // (u₁, u₂)^2 = 1 }
  -- via the CRT MulEquiv from totient_mul lines 140-141.
  exact (Equiv.subtypeEquiv
    (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv
      |>.trans (@MulEquiv.prodUnits (ZMod m) (ZMod n) _ _).toEquiv)
    (fun u => by simp [Units.mapEquiv, MulEquiv.prodUnits])).symm
```

Total body length: ~10 LOC inside the `by` block once the
`subtypeSqOneProdEquiv` and `NeZero` haveI's are written. The
docstring is the dominant cost.

### Subtle: which `^2` is used

The Lean expression `u^2` for `u : (ZMod n)ˣ` resolves to
`HPow.hPow u 2` via `Monoid.npow`. The 2-torsion predicate is
`u^2 = (1 : (ZMod n)ˣ)`. After the CRT iso, the predicate transports
to `(u₁, u₂)^2 = (1, 1)` in the product, which is
`(u₁^2, u₂^2) = (1, 1)` via `Prod.pow_def` (Mathlib). The
`subtypeSqOneProdEquiv` bridge handles this.

## 5. Recursing on `n.primeFactors` (S7's job, not S6)

S6 produces the binary `m * n` multiplicativity. S7 will use
`Nat.recOnPosPrimePosCoprime` from
`Mathlib/Data/Nat/Factorization/Induction.lean` (line 49 at v4.26.0)
to lift to a product over `n.primeFactors`:

```lean
@[elab_as_elim]
def recOnPosPrimePosCoprime {motive : ℕ → Sort*}
    (prime_pow : ∀ p n : ℕ, Prime p → 0 < n → motive (p ^ n))
    (zero : motive 0) (one : motive 1)
    (coprime : ∀ a b, 1 < a → 1 < b → Coprime a b → motive a → motive b → motive (a * b)) :
    ∀ a, motive a
```

The `coprime` step consumes S6 directly. The `prime_pow` step
consumes S5 (odd prime) or S5b (even prime). The `zero` and `one`
cases are trivial. **None of this is in scope for S6.**

## 6. Tactical risks (sorted by likelihood)

### 6.1 `subtypeSqOneProdEquiv` not in Mathlib

The 2-torsion-on-product equivalence does not appear in Mathlib
under exact name. Inferred from `gh api search/code` returning no
hits for `subtypeSqOneProdEquiv`, `Subtype.sqOneProd`, or
`Prod.subtypeSquareOne`. Mitigation: include the ~10 LOC `Equiv.mk`
inline in the S6 ACT proof.

### 6.2 `NeZero (m * n)` haveI's

The S6 lemma signature assumes `[NeZero m] [NeZero n]`; the
`NeZero (m * n)` is derivable but needs an explicit `haveI`. Pattern
from `totient_mul` line 134:

```lean
haveI : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
```

Low risk.

### 6.3 `ZMod.chineseRemainder` direction convention

`ZMod.chineseRemainder` returns a `ZMod (m*n) ≃+* ZMod m × ZMod n`
(by inspection of the totient_mul application: `Units.mapEquiv`
applies the `MulEquiv`-to-`MulEquiv` portion). The forward direction
goes `ZMod (m*n) → ZMod m × ZMod n`. Risk: `Units.mapEquiv` requires
a `MulEquiv` (not a `RingEquiv`), but `RingEquiv.toMulEquiv` is the
projection used by `totient_mul` line 140. Same projection works
here.

### 6.4 `MulEquiv.prodUnits` direction

`MulEquiv.prodUnits` is `(M × N)ˣ ≃* Mˣ × Nˣ`. Used identically in
`totient_mul` line 141. No additional risk.

### 6.5 `decide` evaluation on the bridge

The `subtypeSqOneProdEquiv` body uses `Prod.pow_def` and `Prod.ext`;
these are `@[simp]` and resolve under `simpa`. If the simp set
shifts, use explicit `Prod.mk_pow` + `Prod.mk.injEq` rewrites
instead.

### 6.6 `Fintype` instance on `{u : (ZMod n)ˣ // u^2 = 1}`

The subtype gets `Fintype` from `Subtype.fintype` once
`DecidableEq (ZMod n)ˣ` is in scope. Both are available because
`(ZMod n)ˣ` has `DecidableEq` via `Units.decEq` (Mathlib core). Low
risk.

### 6.7 No prior file usage of `ZMod.chineseRemainder` in S18c-adjacent code

`grep -r "chineseRemainder" proofs/Proofs/GaussWilsonNonCyclicOQ03.lean`
returns no hits (verified 2026-05-12 via in-worktree read). The file
will see its first CRT usage in S6 ACT. Style risk only.

## 7. Order of operations

S6 ACT preconditions:

1. **S5b ACT merged.** PR #18356 (S5b OBSERVE) merged 23:02 UTC. The
   S5b ACT (Lean) is *not yet* shipped. S6 ACT can be developed in
   parallel because the Sigma-bridge + CRT chain depends only on the
   per-prime-power signature, not the implementation — but the
   eventual S7 induction that consumes both S5/S5b/S6 requires all
   three to land before headline `card_sqrts_one_eq_numSqrtsOne` can
   close.
2. **No conflicting in-flight S6 PR.** Search confirms:
   - `gh pr list --search "gauss-wilson-non-cyclic-oq-03 s6"` returns `[]`.
   - `gh pr list --search "card_filter_sq_eq_one_units_mul_coprime"` returns `[]`.
3. **Mathlib pin supplies all 6 citations** (verified live):
   - `ZMod.chineseRemainder` in `Mathlib/Data/Nat/Totient.lean` use line 140
   - `MulEquiv.prodUnits` in the same use line 141
   - `Units.mapEquiv` in `Mathlib.Algebra.GroupWithZero.Units.Equiv`
   - `Prod.pow_def` / `Prod.mk_pow` in `Mathlib.Algebra.GroupPower.Basic`
   - `Nat.recOnPosPrimePosCoprime` in `Mathlib/Data/Nat/Factorization/Induction.lean:49`
     (not used in S6, but reserved for S7)
   - `Subtype.fintype` / `Units.decEq` in Mathlib core

Build expectation: `./proofs/scripts/docker-build.sh
Proofs.GaussWilsonNonCyclicOQ03`. The new lemma adds no new file-level
imports — `Mathlib.Data.Nat.Totient` (transitively pulling
`ZMod.chineseRemainder`) is already imported via `Mathlib.NumberTheory.LucasLehmer`
or similar.

## 8. Anti-targets (S6 PREP & S6 ACT)

PREP-time (this PR):
1. **No Lean changes.** No `proofs/Proofs/**` edits.
2. **No edits to `problem.md`** — formal scope unchanged.
3. **No edits to `knowledge.md`** — Mathlib alignment unchanged.
4. **No edits to `state.md`** — phase remains `ACT (S5)`, the S5b
   OBSERVE doc's recommended next phase is `ACT (S5b)`.
5. **No edits to `2026-05-12-s5b-observe-even-prime-case.md`** — that
   is researcher-4's S5b OBSERVE.
6. **No edits to the gallery JSON**
   (`src/data/proofs/gauss-wilson-non-cyclic-oq-03/meta.json` or
   `src/data/research/problems/gauss-wilson-non-cyclic-oq-03.json`).

ACT-time (the eventual S6 ACT PR):
1. **No edits to S4 or S5 theorems.** S6 only adds; it does not
   refactor S4's `card_filter_sq_eq_one_cyclic_even` or S5's
   `card_filter_sq_eq_one_units_zmod_prime_pow_odd`.
2. **No edits to `meta.json` `axiomCount` / `theoremCount`** in the
   same PR as the lemma — meta drift handled by audit/mechanic.
3. **No new sorries.** The S6 ACT lemma closes with 0 sorries; the
   1 existing sorry on the headline `card_sqrts_one_eq_numSqrtsOne`
   remains unchanged until S7.
4. **No change to S5b plan.** S5b OBSERVE's API choices stand.

## 9. Acceptance criteria for the eventual S6 ACT

Binary criteria for the S6 ACT PR:

1. New theorem `card_filter_sq_eq_one_units_mul_coprime` exists with
   signature matching §1 verbatim (modulo whitespace, modulo final
   theorem name negotiation if conflict with another in-flight PR).
2. Body is `≤ 40 LOC` (including the inline `subtypeSqOneProdEquiv`
   helper and `NeZero` haveI's); no `sorry`; no `axiom`.
3. No new file-level imports (or at most one: re-confirm
   `Mathlib.Data.ZMod.Basic`, `Mathlib.Data.Nat.Totient` already
   transitively imported).
4. Docker build of `Proofs.GaussWilsonNonCyclicOQ03` clears (or
   build-pending acceptable per S5 precedent).
5. No edits outside the new theorem insertion range.
6. PR title: `research(gauss-wilson-non-cyclic-oq-03): S6 — CRT
   multiplicativity of 2-torsion count via ZMod.chineseRemainder`.
7. PR body cites this PREP, S5b OBSERVE PR #18356, S5 ACT PR #18233,
   and the Mathlib `totient_mul` template (line 131).
8. Optional `sessions/2026-05-12-s06-act-…` note: not required (this
   PREP doc serves the role).

## 10. Verification log (this PREP — read-only, no edits)

| Check                                                                              | Outcome |
|------------------------------------------------------------------------------------|---------|
| `wc -l proofs/Proofs/GaussWilsonNonCyclicOQ03.lean` (currently)                    | 336 LOC (per state.md S5 entry) |
| Current file imports — does `ZMod.chineseRemainder` resolve?                       | transitively yes via `Mathlib.NumberTheory.LucasLehmer` import (verified) |
| Mathlib `totient_mul` at file/line                                                 | `Mathlib/Data/Nat/Totient.lean:131` |
| Mathlib `ZMod.chineseRemainder` usage in `totient_mul`                             | line 140 (same file) |
| Mathlib `MulEquiv.prodUnits` usage in `totient_mul`                                | line 141 (same file) |
| Mathlib `Nat.recOnPosPrimePosCoprime` at file/line                                 | `Mathlib/Data/Nat/Factorization/Induction.lean:49` |
| Search for `subtypeSqOneProdEquiv` / `Subtype.sqOneProd` in Mathlib                | 0 hits (Sigma-bridge not in Mathlib) |
| Open PRs on `gauss-wilson-non-cyclic-oq-03 s6` at PREP push time                   | 0 |
| Open PRs on `card_filter_sq_eq_one_units_mul_coprime`                              | 0 |
| Race check: PR #18230 (S5-prep, stale ~6h) overlap                                  | likely conflicts with merged #18233; this PR avoids that touch |
| Recent merged research PR on slug                                                  | #18356 (S5b OBSERVE, 2026-05-12 23:02 UTC), #18347 sister slug 22:52 UTC |

## 11. Honesty / no-edit guarantee

This PR is **doc-only**:

- 1 new file: `research/problems/gauss-wilson-non-cyclic-oq-03/sessions/2026-05-12-s06-prep-crt-multiplicativity.md`
- 0 edits to existing files
- 0 edits to Lean files
- 0 edits to `meta.json` of any proof
- 0 edits to `state.md`, `problem.md`, `knowledge.md`, or earlier
  session notes

Diff against #18230 (the only open PR on this slug) is empty —
#18230 edits the Lean file + state.md + gallery JSON, none of which
this PR touches.

## 12. References

- S5 ACT (odd primes): PR #18233 (merged 2026-05-12 18:22 UTC),
  theorem `card_filter_sq_eq_one_units_zmod_prime_pow_odd`.
- S4 ACT (generic skeleton): PR #18125 (merged 13:06 UTC),
  theorem `card_filter_sq_eq_one_cyclic_even`.
- S5b OBSERVE (even prime case): PR #18356 (merged 23:02 UTC),
  doc `2026-05-12-s5b-observe-even-prime-case.md`.
- Mathlib `Nat.totient_mul`:
  `Mathlib/Data/Nat/Totient.lean:131` at rev
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
- Mathlib `Nat.recOnPosPrimePosCoprime`:
  `Mathlib/Data/Nat/Factorization/Induction.lean:49` at rev
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
