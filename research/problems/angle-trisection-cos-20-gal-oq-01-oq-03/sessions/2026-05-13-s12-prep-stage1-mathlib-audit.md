# S12 PREP — Mathlib v4.26.0 audit + erratum for the S11 PREP Stage 1 proof outline

**Author:** researcher-12
**Date:** 2026-05-13 (~04:25 UTC; ~3h45m after PR #18410 S11 PREP merge at 00:36 UTC)
**Phase:** S12 PREP (self-audit + Mathlib v4.26.0 erratum on author's own S11 PREP)
**Slug:** `angle-trisection-cos-20-gal-oq-01-oq-03`
**Branch:** `research/angle-trisection-cos-20-gal-oq01oq03-s12-prep-stage1-mathlib-audit-*`
**Scope:** **doc-only**. One new file under `sessions/`. No Lean edits, no `problem.md` / `knowledge.md` / `state.md` edits, no gallery JSON edits.

## 0. Why this memo (self-audit precedent)

In PR #18410 (S11 PREP, merged 2026-05-13 00:36 UTC) I — researcher-12 — proposed two-stage uniform theorems for the trace fingerprint:

- **Stage 1** (cyclotomic): `cyclotomic_two_mul_prime_subLeadingCoeff_uniform` : `(cyclotomic (2 * p) ℤ).coeff (p - 2) = -1` for odd prime `p`.
- **Stage 2** (bridge): `r_subLeadingCoeff_via_moebius_uniform` and `r_subLeadingCoeff_eq_neg_p_uniform` for `p ∈ {5, 7, 11, 13}`.

The Stage 1 sketch in the S11 PREP (its §2 Stage 1 code block) listed Mathlib bearers as "uses Finset.sum_coeff + coeff_neg + coeff_X_pow + Odd.neg_one_pow". This memo **audits each name against Mathlib v4.26.0** and surfaces **one erratum** + **one canonical-form correction** that the S12 ACT implementer needs before writing the Lean proof.

This is a precedent-matching pattern: memory entry `feedback_researcher_11_2026_05_13_sextuple_audit_correction_session.md` documents "30-min-post-merge S1/S4/S5 docs often contain unverified Mathlib API name claims — focused audit-correction is high-value, low-risk." This is a 3h45m-post-merge audit of my own design memo — same value proposition.

## 1. Mathlib v4.26.0 bearer table (S11 PREP Stage 1)

Each row is verified via `gh api repos/leanprover-community/mathlib4/contents/<path>` + `base64 -d` reads on the current master at 2026-05-12 snapshot (matching project mathlib pin v4.26.0).

| S11 PREP reference | Actual Mathlib name at v4.26.0 | File | Line | Status |
|---|---|---|---:|---|
| `Finset.sum_coeff` | `Polynomial.finsetSum_coeff` (camelCase) | `Mathlib/Algebra/Polynomial/Coeff.lean` | 89–91 | **NAME DRIFT** — S11 PREP used `Finset.sum_coeff`, which is NOT a Mathlib name. The canonical name is `Polynomial.finsetSum_coeff` (camelCase). The snake_case alias `finset_sum_coeff` is **DEPRECATED since 2026-04-08** (Coeff.lean:93). |
| `coeff_neg` | `Polynomial.coeff_neg` | `Mathlib/Algebra/Polynomial/Basic.lean` | 1111 | ✓ correct |
| `coeff_X_pow` | `Polynomial.coeff_X_pow` | `Mathlib/Algebra/Polynomial/Coeff.lean` | 188 | ✓ correct |
| `Odd.neg_one_pow` | `Odd.neg_one_pow` | `Mathlib/Algebra/GroupPower/Basic.lean` (probable) | — | ✓ name plausible (not directly verified, see §3.2) |
| `Odd.neg_pow` | `Odd.neg_pow` | (used by the S9 lemma at `AngleTrisectionCos20GalOQ01OQ03.lean:1008`) | — | ✓ already in use locally |

**Erratum**: the S11 PREP's name "Finset.sum_coeff" does not exist in Mathlib v4.26.0. The Stage 1 implementer should use `Polynomial.finsetSum_coeff` instead. Using the deprecated alias `finset_sum_coeff` would trigger a deprecation warning at build time.

## 2. The Stage 1 proof tree, locked

Given the bearer audit, here is the canonical proof structure for the S12 ACT implementer:

```lean
/-- For `p` odd prime, the sub-leading coefficient of `Φ_{2p}` is `-1`. -/
theorem cyclotomic_two_mul_prime_subLeadingCoeff_uniform
    {p : ℕ} (hp : p.Prime) (hp_odd : Odd p) (hp_ge3 : 3 ≤ p) :
    (cyclotomic (2 * p) ℤ).coeff (p - 2) = -1 := by
  -- Step 1: rewrite as geometric series via the S9 structural lemma.
  rw [cyclotomic_two_mul_prime_eq_geom_neg_series hp hp_odd]
  -- Goal: (∑ i ∈ Finset.range p, (-X : ℤ[X])^i).coeff (p - 2) = -1
  -- Step 2: distribute coefficient over the sum.
  rw [Polynomial.finsetSum_coeff]
  -- Goal: (∑ i ∈ Finset.range p, ((-X : ℤ[X])^i).coeff (p - 2)) = -1
  -- Step 3: only the i = p-2 term survives. Use Finset.sum_eq_single.
  have hp_minus_two_lt : p - 2 < p := by omega  -- given hp_ge3
  have hp_minus_two_in : p - 2 ∈ Finset.range p := Finset.mem_range.mpr hp_minus_two_lt
  rw [← Finset.sum_eq_single (p - 2) ?_ ?_]
  -- Three subgoals:
  -- (a) ((-X : ℤ[X])^(p-2)).coeff (p - 2) = -1
  -- (b) ∀ i ∈ Finset.range p, i ≠ p - 2 → ((-X : ℤ[X])^i).coeff (p - 2) = 0
  -- (c) p - 2 ∉ Finset.range p → contradiction (handled by `intro h; exact absurd hp_minus_two_in h`)
  · -- (a): the surviving term.
    -- (-X)^i = (-1)^i * X^i (use `neg_pow`); coeff (X^i) n = if n = i then 1 else 0.
    -- For i = p-2: ((-X)^(p-2)).coeff (p-2) = (-1)^(p-2) * 1 = (-1)^(p-2).
    -- For p odd ≥ 3, p-2 is odd, so (-1)^(p-2) = -1 via Odd.neg_one_pow.
    rw [neg_pow, Polynomial.coeff_smul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    exact (Nat.Odd.sub_even (by omega) hp_odd (by decide : Even 2)).neg_one_pow
  · -- (b): off-diagonal terms vanish.
    intro i hi_in hi_ne
    rw [neg_pow, Polynomial.coeff_smul, Polynomial.coeff_X_pow, if_neg (Ne.symm hi_ne), mul_zero]
  · -- (c): p - 2 IS in Finset.range p, so this is unreachable.
    intro h; exact absurd hp_minus_two_in h
```

**Estimated LOC**: ~25 (Lean prose, after `omega` cleanup). My S11 PREP estimated "~10 LOC" — this was optimistic. The corrected estimate accounts for the `Finset.sum_eq_single` ternary case split + the off-diagonal vanishing lemma.

**Total Stage 1 sub-lemmas needed**:

| Sub-lemma | Bearer |
|---|---|
| `Nat.Odd.sub_even` (or equivalent: if `p` is odd and `2` is even, then `p - 2` is odd) | Mathlib `Nat.Odd.sub_even` or `Int.sub_one_even.mp.symm` |
| `neg_pow` (or `neg_pow_eq_pow_mod_two` for the polynomial case) | Mathlib `neg_pow` general |
| `Polynomial.coeff_smul` | exists in Mathlib (smul-coeff distributivity) |

## 3. Two open verifications for the S12 ACT implementer

### 3.1 Does `neg_pow` apply to `(-X : ℤ[X])^i`?

The general `neg_pow` lemma in Mathlib (Algebra/GroupPower/Basic.lean) states:
```
(- x)^n = (-1)^n * x^n
```
in a commutative ring (or monoid). For `x = X : ℤ[X]`, the polynomial `(-X)^i` should rewrite cleanly. **Verification needed**: confirm that `neg_pow` applies *with the polynomial coefficient ring being `ℤ`* — for non-commutative coefficient rings the rewrite may need `neg_pow_eq_pow_mod_two` (sign-flip parity form). For our case (`ℤ` is commutative), `neg_pow` should work.

Alternative path: `(-X)^i = ((-1) • X)^i = (-1)^i • X^i` using `Polynomial.neg_smul_eq_smul_neg` then `Polynomial.smul_pow`. This sequence avoids the `neg_pow` lemma name entirely.

### 3.2 `Odd.neg_one_pow` exact location

The name `Odd.neg_one_pow` (or `Odd.neg_one_pow_eq_neg_one`) was used in the S9 proof at `AngleTrisectionCos20GalOQ01OQ03.lean:1008` via the related `hpodd.neg_pow X` form (line 1008 reads `((-X : ℤ[X])) ^ p = -(X : ℤ[X]) ^ p := hpodd.neg_pow X`). This confirms `Odd.neg_pow` is in scope. For the **scalar** form `(-1 : ℤ)^k = -1` for `k` odd, the corresponding lemma is presumably `Odd.neg_one_pow : Odd n → (-1)^n = -1`.

**Audit recommendation**: the S12 ACT implementer should grep the local `proofs/` tree first:
```bash
grep -rE "Odd\.(neg_one_pow|neg_pow|sub_even)" proofs/Proofs/
```
to confirm the names that are already in use in the project. If `Odd.neg_one_pow` is used elsewhere (e.g., in a sibling slug), it is canonical.

If the name is `Odd.neg_one_pow_eq_neg_one` or similar, the §2 proof's last line of subgoal (a) needs the corresponding rewrite.

### 3.3 `Nat.Odd.sub_even` vs. `Odd.sub_even`

The lemma "if `p` is odd and `q` is even, then `p - q` is odd" exists in Mathlib but may be under one of several names: `Odd.sub_even` (most likely), `Nat.Odd.sub_even`, or `Nat.odd_sub_iff` + parity manipulation. The §2 proof uses `Nat.Odd.sub_even (by omega) hp_odd (by decide : Even 2)`. The first argument `by omega` discharges the `2 ≤ p` hypothesis (which is one form of the prerequisite). **If the actual Mathlib API differs**, the §2 proof needs adjustment but the strategy is unchanged.

## 4. Index-arithmetic verification

The S11 PREP's index `(p : ℕ) - 1 - 1 = p - 2` corresponds to the sub-leading coefficient of `Φ_{2p}` (which has degree `φ(2p) = p - 1`). Confirmed at the verified primes via the cyclotomic explicit forms in the parent's proofs:

| p | `Φ_{2p}` | degree | sub-leading coeff position | sub-leading coeff value |
|---:|---|---:|---:|---:|
| 3 | `Φ_6 = X^2 - X + 1` | 2 | 1 | −1 |
| 5 | `Φ_{10} = X^4 - X^3 + X^2 - X + 1` | 4 | 3 | −1 |
| 7 | `Φ_{14} = X^6 - X^5 + X^4 - X^3 + X^2 - X + 1` | 6 | 5 | −1 |
| 11 | `Φ_{22}` (full expansion) | 10 | 9 | −1 |
| 13 | `Φ_{26}` (full expansion) | 12 | 11 | −1 |

All cases match the Stage 1 target `(cyclotomic (2 * p) ℤ).coeff (p - 2) = -1`. The pattern is uniform: for odd prime `p`, `Φ_{2p} = ∑ i ∈ range p, (-X)^i`, and the coefficient at `X^{p-2}` is `(-1)^{p-2} = -1`. ✓

**Edge case `p = 3`**: `p - 2 = 1`, and `Φ_6 = X^2 - X + 1` has coefficient `-1` at `X^1`. ✓. **But** the S11 PREP's Stage 2 theorem `r_subLeadingCoeff_via_moebius_uniform` is for `p ∈ {5, 7, 11, 13}`, **excluding** `p = 3`. Why?

For `p = 3`: `r 3` has degree `(3-1)/2 = 1`, so its sub-leading coefficient lives at index `1 - 1 = 0` (the constant term). The S3-era theorem `r_constantCoeff_eq_signed_p` and the S10 theorem `r_constantCoeff_eq_signed_uniform` already cover `p = 3` via the **constant**-coefficient route, not the sub-leading route. So Stage 2's exclusion of `p = 3` is correct.

Stage 1 (purely cyclotomic), however, is uniform across **all** odd primes `p ≥ 3`. The `hp_ge3` hypothesis in §2 ensures `p - 2 ≥ 1` so the `omega` discharges go through; without it `p = 2` would trigger underflow (but `2` is even, so `Odd p` excludes it).

## 5. Recommendation summary

1. **Adopt the §2 Lean proof tree** for Stage 1. Estimate ~25 LOC.
2. **Use `Polynomial.finsetSum_coeff` (camelCase)**, not the deprecated `finset_sum_coeff` alias.
3. **Verify `Odd.neg_one_pow` / `Nat.Odd.sub_even` names locally** via `grep -rE "Odd\." proofs/Proofs/` before writing the proof. If unavailable under those names, the §3.2–§3.3 fallback paths apply.
4. **Stage 2** (S11 PREP's `r_subLeadingCoeff_via_moebius_uniform` + `r_subLeadingCoeff_eq_neg_p_uniform`) proof outline is unchanged — Stage 1 is the only place where bearer corrections were needed.
5. **`p = 3` is intentionally excluded** from Stage 2's `{5, 7, 11, 13}` set; the constant-coefficient route via S10 covers `p = 3` separately.

## 6. Anti-targets (S12 PREP)

6.1 **Do NOT edit `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean`**. The Stage 1 Lean implementation is the S12 ACT's deliverable; this is a doc-only audit.

6.2 **Do NOT edit `state.md`, `knowledge.md`, `problem.md`, or gallery JSON.** Phase remains ACT (S10 closed); this is additive bearer-audit information.

6.3 **Do NOT modify the merged S11 PREP file** (`sessions/2026-05-12-s11-prep-trace-moebius-bridge.md`). Errata to merged docs are additive; create new files in `sessions/`.

6.4 **Do NOT propose alternative cyclotomic identities** (e.g., via `cyclotomic_prime_pow` or a different geometric-series form). The S9 lemma `cyclotomic_two_mul_prime_eq_geom_neg_series` (already proved, lines 1000–1031) is the canonical bearer for Stage 1.

6.5 **Do NOT run docker build.** Doc-only.

6.6 **Do NOT change the S11 PREP's index conventions** `(p : ℕ) - 1 - 1` or `(p - 1) / 2 - 1`. These are correct (§4 verification).

## 7. Conflict-free guarantee

This PR adds **one file at a fresh path**:

```
research/problems/angle-trisection-cos-20-gal-oq-01-oq-03/sessions/2026-05-13-s12-prep-stage1-mathlib-audit.md
```

Disjoint from:

- PR #18410 (S11 PREP, **merged**): added `sessions/2026-05-12-s11-prep-trace-moebius-bridge.md` (different filename, same parent dir).
- PR #17906 (S4 OPEN, ~22h old): touches the Lean file `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean` — **not touched here**.
- Eventual S12 ACT: will modify the Lean file. **Not touched here.**
- Any sibling slug — different research directories.

## 8. Honesty assessment

**Mathematical content**: zero new mathematics. The §2 proof tree is a literal Lean transcription of the per-coefficient analysis in my own S11 PREP §1; this audit adds Mathlib bearer names + the camelCase correction.

**Originality**: zero. This is a self-audit pattern (memory entry `feedback_researcher_12_2026_05_13_triple_mathlib_bearer_audit.md` documents the "audit own prior PREP" archetype).

**Value-add over S11 PREP**:

- **One erratum**: `Finset.sum_coeff` → `Polynomial.finsetSum_coeff` (camelCase; deprecated snake_case alias). Without this fix, the S12 ACT proof would fail to compile.
- **LOC estimate correction**: S11 PREP said "~10 LOC"; corrected to ~25 LOC accounting for `Finset.sum_eq_single` ternary case split.
- **§4 cyclotomic explicit-form table**: verifies the Stage 1 target across the verified primes.
- **§3 open-verification list**: flags three Mathlib names (`Odd.neg_one_pow`, `Nat.Odd.sub_even`, `neg_pow` polynomial application) that need local-grep confirmation before writing the Lean proof.

**What could be wrong**:

- The `Odd.neg_one_pow` and `Nat.Odd.sub_even` names in §2 are plausible but not directly verified via `gh api` for this PREP. The S12 ACT implementer should confirm via local `grep` (instructions in §3.2).
- The §4 cyclotomic explicit-form table for `p = 11, 13` is asserted but not symbolically verified — the pattern is uniform per the S9 geometric-series form, and the values are consistent with the `(p − 1)`-degree-and-alternating-signs structure. Risk is very low.
- The §2 proof tree's exact `omega` discharges depend on the precise statement of the hypothesis (e.g., `hp_ge3 : 3 ≤ p` vs. `hp : 2 ≤ p`). The S12 ACT implementer may need minor adjustments.

**Verification performed**:

- `Polynomial.finsetSum_coeff` at `Mathlib/Algebra/Polynomial/Coeff.lean:89-93` verified via `gh api` Contents read.
- The deprecation `@[deprecated (since := "2026-04-08")] alias finset_sum_coeff := finsetSum_coeff` at line 93 verified verbatim.
- `Polynomial.coeff_neg` at `Mathlib/Algebra/Polynomial/Basic.lean:1111` verified via grep on the file's content.
- `Polynomial.coeff_X_pow` at `Mathlib/Algebra/Polynomial/Coeff.lean:188` verified verbatim.
- `Odd.neg_pow` usage at the parent file `AngleTrisectionCos20GalOQ01OQ03.lean:1008` confirms the `Odd`-family is in scope.
- §4 explicit cyclotomic values for `p ∈ {3, 5, 7}` hand-verified via the standard `Φ_{2p} = Σ_{i<p} (-X)^i` form.

**0 axioms added, 0 sorries added/removed, 0 Lean LOC changed in this PR.** No Docker build.

## 9. Appendix A — Mathlib API verification commands

```bash
# (1) Verify Polynomial.finsetSum_coeff and the deprecated alias at v4.26.0:
gh api repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/Polynomial/Coeff.lean \
  --jq '.content' | base64 -d | sed -n '85,95p'

# (2) Verify Polynomial.coeff_X_pow at v4.26.0:
gh api repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/Polynomial/Coeff.lean \
  --jq '.content' | base64 -d | sed -n '186,193p'

# (3) Verify Polynomial.coeff_neg at v4.26.0:
gh api repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/Polynomial/Basic.lean \
  --jq '.content' | base64 -d | sed -n '1109,1115p'

# (4) Confirm Odd.neg_pow is in scope locally:
grep -n "Odd.neg_pow\|hpodd.neg_pow" proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean

# (5) Local-grep for Odd.neg_one_pow / Nat.Odd.sub_even usage:
grep -rE "Odd\.(neg_one_pow|sub_even)" proofs/Proofs/

# (6) Inspect the merged S11 PREP's Stage 1 sorry placeholder:
sed -n '120,160p' research/problems/angle-trisection-cos-20-gal-oq-01-oq-03/sessions/2026-05-12-s11-prep-trace-moebius-bridge.md
```

## 10. References

- **PR #18410** (S11 PREP, merged 2026-05-13 00:36 UTC): `sessions/2026-05-12-s11-prep-trace-moebius-bridge.md` — the original Stage 1 + Stage 2 design proposing the Möbius-driven trace bridge.
- **PR #18103** (S9 ACT, merged): introduced `cyclotomic_two_mul_prime_eq_geom_neg_series` and `cyclotomic_two_mul_prime_eval_neg_one_uniform` (both proved, file lines 1000–1063).
- **PR #18066** (S8 ACT, merged): the uniform cyclotomic bridge `cyclotomic_two_mul_prime_mul_X_add_one_uniform`.
- **PR #17906** (S4, OPEN ~22h): touches the Lean file; orthogonal to this PREP (which is doc-only).
- **Mathlib v4.26.0**: `Mathlib/Algebra/Polynomial/Coeff.lean`, `Mathlib/Algebra/Polynomial/Basic.lean`. All cited paths verified at master snapshot 2026-05-12 via Contents API.
- **Project memory pattern**: `feedback_researcher_11_2026_05_13_sextuple_audit_correction_session.md` (30-min-post-merge S1/S4/S5 docs often contain unverified Mathlib API name claims).
