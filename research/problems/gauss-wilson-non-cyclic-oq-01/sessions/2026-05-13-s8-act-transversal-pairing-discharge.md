# S8 ACT — Discharge Phase B transversal-pairing strategic sorry

**Date**: 2026-05-13
**Researcher**: researcher-12
**Phase**: ACT (closes Phase B; advances the slug from 2 sorries to 1)
**Branch**: `research/gauss-wilson-non-cyclic-oq-01-s8-1778717838`

## 0. Goal

Close the Phase B strategic sorry in
`proofs/Proofs/GaussWilsonNonCyclicOQ01B.lean:131-137`:

```lean
theorem prod_univ_eq_pow_card_div_two_of_elementary
    [Fintype H] [DecidableEq H]
    (hexp : ∀ x : H, x ^ 2 = 1) {h : H} (hne : h ≠ 1) :
    ∏ x : H, x = h ^ (Fintype.card H / 2)
```

Per state.md "Next Action" (post-S7 ACT STATE-SYNC #18942), this is the
last gating step before Phase B is fully verified. Phase C's
non-cyclic-direction sorry consumes this lemma transitively.

## 1. Route chosen

Neither Route A.2 (`Quot.out` transversal + `Finset.prod_image`) nor
Route B (`MulAction.selfEquivSigmaOrbits`) from S4 PREP (PR #18347) +
S4b PREP (PR #18467). Both require `MulAction (Subgroup.zpowers h) H`
machinery and an `orderOf h = 2` calculation (~65-95 LOC).

**Chosen: strong induction on `Finset H`.** Generalize to: *any
Finset `S` closed under left-multiplication by `h` has cardinality
`2k` and product `h^k`*. By strong induction on `S`, erase one orbit
`{x, h*x}` per step. Specialize to `S = univ` (closure is automatic).

LOC: ~75 lines for the strategic-sorry discharge (vs. 50-100 estimated
in S4 PREP §4). No `MulAction` / `Subgroup.zpowers` / `orderOf`
machinery.

## 2. Proof structure (high level)

```
prod_univ_eq_pow_card_div_two_of_elementary
├── suffices h_aux : ∀ S, (closed under h·) → ∃ k, |S|=2k ∧ ∏ S = h^k
├── specialize to S = univ:
│   ├── h_aux univ (closure trivial)
│   ├── Fintype.card H = 2k via card_univ
│   └── h^k = h^(card/2) via `congr 1; omega`
└── Strong induction on S (Finset.strongInduction):
    ├── Base: S = ∅. ⟨0, by simp, by simp⟩
    └── Step: pick x ∈ S, then h*x ∈ S and h*x ≠ x:
        ├── S' := (S.erase x).erase (h*x)
        ├── S' ⊂ S via lt_of_le_of_lt (erase_subset) (erase_ssubset hx)
        ├── S' closed under h· (left cancellation + mul_left_self_inv)
        ├── IH gives ⟨k, |S'|=2k, ∏ S' = h^k⟩
        ├── |S| = |S'| + 2 = 2(k+1) (via card_erase_of_mem ×2 + omega)
        └── ∏ S = x * (h*x) * ∏ S' = h * ∏ S' = h * h^k = h^(k+1)
            ├── e1, e2 via Finset.mul_prod_erase
            ├── pair_id: x * (h*x) = h via mul_left_comm + hx_sq
            └── pow_succ' for h * h^k = h^(k+1)
```

## 3. Key Mathlib lemmas (all v4.26.0-verified)

| Lemma | File | Use |
|---|---|---|
| `Finset.strongInduction` | `Data/Finset/Card.lean:810` | recursion principle |
| `Finset.erase_subset` | `Data/Finset/Erase.lean:95` | `(S.erase x).erase _ ⊆ S.erase x` |
| `Finset.erase_ssubset` | `Data/Finset/Basic.lean:151` | `S.erase x ⊂ S` |
| `Finset.mem_erase` | (re-exported) | unfold membership |
| `Finset.card_erase_of_mem` | `Data/Finset/Card.lean:145` | `|s.erase a| = |s| - 1` |
| `Finset.card_pair` | `Data/Finset/Card.lean:140` | `|{a,b}| = 2` for `a ≠ b` |
| `Finset.card_le_card` | (mono) | sub-finset card bound |
| `Finset.mul_prod_erase` | `BigOperators/Group/Finset/Basic.lean:749` | factor element |
| `Finset.card_univ` | (std) | `|univ| = Fintype.card` |
| `mul_left_cancel` | (std `Group`) | `h*a = h*b → a = b` |
| `mul_left_comm` | (std `CommMonoid`) | `a*(b*c) = b*(a*c)` |
| `pow_succ'` | `Algebra/Group/Defs.lean:647` | `a^(n+1) = a*a^n` |
| `mul_left_self_inv_of_elementary` | this file:54 | `h*(h*x) = x` (h²=1) |
| `mul_left_ne_self_of_ne_one` | this file:65 | `h≠1 → h*x ≠ x` |

No new axioms, no `Subgroup.zpowers`, no `MulAction`, no `orderOf`.

## 4. Why strong induction beats the routes from S4 PREP

| Aspect | Route A.2 (transversal) | Route B (sigma) | Strong induction (this PR) |
|---|---:|---:|---:|
| LOC estimate | 50-70 | 65-95 | ~75 |
| Mathlib API surface | Quot.out + prod_image + zpowers | selfEquivSigmaOrbits + zpowers + orderOf | strongInduction + erase + mul_prod_erase |
| Setoid/quotient machinery | yes (`H ⧸ ⟨h⟩`) | yes (`orbitRel.Quotient`) | none |
| `orderOf h = 2` lemma chase | yes | yes | none |
| Reusability | low (slug-specific) | medium (FPF involutions) | medium (any "closed under left-mul" subset) |

The strong-induction approach is **structurally simpler**: the closure
predicate `∀ x ∈ S, h * x ∈ S` is propositional (no instance synthesis,
no quotient construction), and the recursion is on `Finset.strongInduction`
which is well-supported in Mathlib (used by `Finset.prod_involution` itself
in `BigOperators/Group/Finset/Basic.lean:673`).

## 5. Cardinality bookkeeping

The induction step needs `|S| = |S'| + 2`, hence `|S| ≥ 2`. The slug's
own helper `exists_two_distinct_ne_one` (line 90) is a stronger statement
than needed; here we get `|S| ≥ 2` from the simpler fact `{x, h*x} ⊆ S`
with `Finset.card_pair`:

```lean
have hpair_sub : ({x, h * x} : Finset H) ⊆ S := by ...
have h_ge : 2 ≤ S.card := by
  have hpair_card : ({x, h * x} : Finset H).card = 2 :=
    Finset.card_pair hhx_ne_x.symm
  have := Finset.card_le_card hpair_sub
  rwa [hpair_card] at this
```

`hhx_ne_x.symm` flips `h*x ≠ x` to `x ≠ h*x` (the form `Finset.card_pair`
needs for `{x, h*x}`).

## 6. Sorry / axiom delta

|                  | Before S8 | After S8 |
|------------------|-----------|----------|
| Phase A sorries (`GaussWilsonNonCyclicOQ01A.lean`) | 0 | 0 |
| Phase B sorries (`GaussWilsonNonCyclicOQ01B.lean`) | 1 | **0** |
| Phase C sorries (`GaussWilsonNonCyclicOQ01.lean`)  | 1 | 1 (unchanged) |
| Slug-level sorry count | 2 | **1** |
| Slug-level axiom count | 0 | 0 |

Phase C's `prod_eq_one_of_not_isCyclic_aux` (at
`GaussWilsonNonCyclicOQ01.lean:149`) is NOT touched by this PR. Per its
in-file docstring, the next step composes (i) Phase A,
(ii) parent's `card_sq_eq_one_ge_three` + power-of-2-cardinality upgrade,
(iii) Phase B `prod_univ_eq_one_of_elementary_card_ge_four`. With S8
closing Phase B, that composition is now mechanically tractable.

## 7. Build status

**Build-verified** via `./proofs/scripts/docker-build.sh Proofs.GaussWilsonNonCyclicOQ01B`:

```
✔ [3058/3058] Built Proofs.GaussWilsonNonCyclicOQ01B (4.5s)
Build completed successfully (3058 jobs).
=== Build succeeded ===
```

**First-attempt build failure (recovered same session).** The initial
draft used
```lean
have hS'_ssub : S' ⊂ S :=
  lt_of_le_of_lt (Finset.erase_subset _ _) (Finset.erase_ssubset hx)
```
which failed with:
```
Type mismatch: lt_of_le_of_lt ... has type ?m < ?m
but is expected to have type S' ⊂ S
```

Diagnosis: `Finset.HasSSubset` is defined separately from `LT` in
`Mathlib/Data/Finset/Defs.lean:200-202`:
```lean
instance : HasSSubset (Finset α) := ⟨fun s t => s ⊆ t ∧ ¬t ⊆ s⟩
```
Although the `IsTrans` instances for `(· ⊂ ·)` are
`inferInstanceAs <| IsTrans (Finset α) (· < ·)`, the *types* `S' < S`
and `S' ⊂ S` are not definitionally inferred by Lean's elaborator
inside `lt_of_le_of_lt`'s result-type.

**Fix**: inline the `HasSSubset.SSubset` constructor via
`refine ⟨..., ...⟩`:
```lean
have hS'_ssub : S' ⊂ S := by
  refine ⟨fun y hy => ?_, ?_⟩
  · simp only [hS'_def, Finset.mem_erase] at hy
    exact hy.2.2
  · intro hsub
    have hx_in_S' : x ∈ S' := hsub hx
    simp only [hS'_def, Finset.mem_erase] at hx_in_S'
    exact hx_in_S'.2.1 rfl
```

**Per-lemma risk surface (post-build, now all verified):**

| Step | Verified |
|---|---|
| `induction S using Finset.strongInduction with | H S ih =>` | ✅ |
| `refine ⟨fun y hy => ?_, ?_⟩` for `⊂` | ✅ (preferred over `lt_of_le_of_lt`) |
| `simp only [hS'_def, Finset.mem_erase] at hy` | ✅ |
| `(Finset.mul_prod_erase S (fun y => y) hx).symm` | ✅ (β-reduction handled by elaborator) |
| `congr 1; omega` for `h^k = h^(card/2)` | ✅ |
| `(pow_succ' h k).symm` | ✅ |
| `Finset.card_pair hhx_ne_x.symm` | ✅ (symm direction needed: `Finset.card_pair` wants first ≠ second) |

## 8. Race awareness (pre-push)

At edit time (2026-05-13 23:30 UTC):
- `gh pr list -R rjwalters/lean-genius --search "gauss-wilson-non-cyclic-oq-01 in:title" --state open` → `[]` (only sibling OQ-03 has open PR #18230)
- 11 prior PRs all MERGED (S1, S2, S3, S4, S4b, S5, S5b, S6, S7-prep, S7-act, STATE-SYNC #18942)
- No race on the strategic sorry — this is the first ACT attempt at it.

## 9. Cross-references

- **PR #18742** (S7 ACT, cyclic-direction discharge, merged 2026-05-13 11:13 UTC)
- **PR #18942** (STATE-SYNC for S7 ACT, merged 2026-05-13 23:02 UTC)
- **PR #18347** (S4 PREP route survey, merged 2026-05-12 22:53 UTC)
- **PR #18467** (S4b PREP Mathlib v4.26.0 audit, merged 2026-05-13 02:21 UTC)
- **PR #18232** (S3 ACT Phase B partial, introduced the strategic sorry,
  merged 2026-05-12 18:20 UTC)

## 10. Next action (S9)

With Phase B verified (modulo build), the Phase C non-cyclic-direction
sorry at `GaussWilsonNonCyclicOQ01.lean:149` is the last gating sorry
for the slug. Estimated 30-50 Lean lines per S7 ACT docstring (lines
133-135 of that file). The composition is:

1. Apply Phase A `prod_univ_eq_prod_two_torsion` to reduce
   `∏ univ` over `(ZMod p^k)ˣ` to `∏ 2-torsion`.
2. Invoke parent `card_sq_eq_one_ge_three` to get `|2-torsion| ≥ 3`.
3. Use power-of-2-cardinality (Lagrange + 2-torsion has exponent 2) to
   upgrade to `|2-torsion| ≥ 4`.
4. Apply Phase B `prod_univ_eq_one_of_elementary_card_ge_four` to the
   2-torsion subgroup.

The hardest step is (3) — Mathlib has `IsPGroup.card_eq_pow_one_iff_orderOf_dvd`
and similar, but the exact assembly was scoped out in S5b PREP (PR #18607).

## 11. Honesty caveats

- **No build verification yet.** The proof is written against
  v4.26.0-verified lemma names but has not been typechecked locally.
- **The cardinality `omega` step assumes natural-number subtraction
  saturates at 0.** With `h_ge : 2 ≤ S.card`, `S.card - 2 + 2 = S.card`
  holds in `ℕ`. `omega` should close this with `h_ge` in scope.
- **The `Finset.card_pair` direction**: I use `hhx_ne_x.symm` (i.e.,
  `x ≠ h*x`) because the Finset literal `{x, h*x}` has `x` first.
- **No claim that this is the only / shortest discharge.** Routes A.2
  and B from S4 PREP remain valid alternatives.

---

**End of S8 ACT session log.**
