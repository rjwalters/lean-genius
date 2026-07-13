# Iteration 43 PREP — 28a `linear_combination` algebraic gap + corrected ℕ-descent discharge

**Date**: 2026-06-03
**Researcher**: researcher-1
**Phase**: PREP (audits the Iter 42 paste-ready block and finds a load-bearing
algebraic gap in the terminal `linear_combination` discharge; supplies a
corrected ℕ-level descent that closes the gap; also surfaces a fresh
Docker-host degradation that further blocks ACT.)
**Type**: Doc-only. No edits to `Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean`,
`knowledge.md`, `problem.md`, or gallery `meta.json`. Edits limited to this
session log, `state.md` (Iter 43 narrative + header refresh), and
`src/data/research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03.json`
(`currentState.iteration`/`phase`/`focus`/`nextAction` + `lastUpdate`).
**Lake-pinned Mathlib SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(unchanged since Iter 36).
**Base HEAD**: `7b6dc1c2c09b` (post Iter 42 PREP merge; intervening unrelated
gallery drains for Wiedijk-100 / Yang-Mills / abel-ruffini).

## Headline

Iter 42 PREP's terminal `linear_combination` call —

```
linear_combination
  ((n - k)! : ℂ) * h_choose_C - (((n - k)! : ℕ) : ℂ) * h_asc_C
```

— **cannot close** the polynomial identity it targets, and the documented
fallback `ring_nf` + `linarith` cannot either. The gap is **mathematical**,
not a syntax-drift Medium-risk: closing the goal requires cancelling a
`k!` factor, and that is **not a linear operation over the three hypothesis
identities**, so no linear combination over `h_asc_C`, `h_choose_C`,
`h_succ_C` discharges the goal. The corrected strategy is to prove the
identity at `ℕ` level via `Nat.eq_of_mul_eq_mul_right` (using
`Nat.factorial_pos k`), then cast the result to `ℂ` and discharge with a
single `linear_combination` over the cast hypothesis.

This finding would have surfaced on the first `docker-build.sh` attempt of
Iter 42's block. The Iter 42 PREP explicitly skipped build verification
(sibling Docker container `lean-build-57602` flagged as risky); Iter 43
makes that miss explicit and provides the corrected ACT path.

## The algebraic gap

Iter 42 sets up three cast hypotheses at the ACT-time goal-state:

| Name | Statement (in ℂ, all casts from ℕ) |
|------|-------------------------------------|
| `h_asc_C` | `k! · (k+1).ascFactorial(n-k+1) = (n+1)!` |
| `h_choose_C` | `Nat.choose n k · k! · (n-k)! = n!` |
| `h_succ_C` | `(n+1)! = (n+1) · n!` |

After Iter 42's Step 1+2 rewrites (`Complex.betaIntegral_eval_nat_add_one_right`
and `Nat.ascFactorial_eq_prod_range`), and after the prescribed `field_simp`
(Step 5), the goal reduces (modulo `field_simp`'s normaliser) to the
**polynomial identity** (with all symbols treated as independent
indeterminates over ℂ):

```
(n - k)! · (n + 1) · Nat.choose n k  =  (k + 1).ascFactorial (n - k + 1)
```

Iter 42 attempts to discharge this via
`linear_combination ((n-k)! : ℂ) * h_choose_C - ((n-k)! : ℂ) * h_asc_C`.

**Claim**: this linear combination cannot close the goal.

**Proof.** `linear_combination e` proves `a = b` by certifying that
`(a - b) - e = 0` is a polynomial identity provable by `ring`. With
the proposed `e`, we have

```
e = (n-k)! · (Nat.choose n k · k! · (n-k)! - n!)
  - (n-k)! · (k! · ascFact - (n+1)!)
  = (n-k)!² · Nat.choose n k · k!
    - (n-k)! · n!
    - (n-k)! · k! · ascFact
    + (n-k)! · (n+1)!
```

The residual `(a - b) - e` contains the monomial `(n-k)!² · choose · k!`,
which is **not** present in `a - b` and is **not cancelled** by any other
term in the expansion. So `ring` cannot close it. The literal call is
algebraically wrong. ∎

**The deeper gap.** Even with the *correct* coefficients (Iter 42's
narrative gloss `(n+1) · h_choose_C - h_succ_C - h_asc_C` is what its
mid-proof comment actually describes), `linear_combination` still cannot
close it:

```
(n+1) · h_choose_C  - h_succ_C - h_asc_C
  = (n+1) · choose · k! · (n-k)! - (n+1)·n!
  - (n+1)! + (n+1)·n!
  - k!·ascFact + (n+1)!
  = (n+1) · choose · k! · (n-k)! - k! · ascFact.
```

This is the **k!-augmented goal** `(n+1) · choose · k! · (n-k)! = k! · ascFact`,
not the target `(n+1) · choose · (n-k)! = ascFact`. The two differ by a
factor of `k!`; cancelling that factor is **not** a ring operation in any
polynomial ring over ℂ, so `ring` (and hence `linear_combination`'s
residual check) cannot close it. The documented fallback
`ring_nf` + `linarith [h_asc_C, h_choose_C, h_succ_C]` fails for the
same reason — `linarith` cannot multiply hypotheses by the variable
`(n+1)`, and `ring_nf` does not use hypotheses.

The cancellation step is fundamentally **non-linear**: it requires
dividing by `k!` (equivalently, applying `Nat.eq_of_mul_eq_mul_right` /
`mul_right_cancel₀`), and that is not in `linear_combination`'s scope.

## The corrected discharge — ℕ-level descent

The fix is to prove the underlying identity at the `ℕ` level (where
`Nat.eq_of_mul_eq_mul_right` is available, taking the `k! > 0`
hypothesis from `Nat.factorial_pos k`), then cast the single resulting
identity to `ℂ` and close with a one-line `linear_combination`. This
**replaces** Iter 42's terminal `linear_combination` and **eliminates**
the `field_simp` + three-hypothesis dance.

```lean
-- KEY ℕ IDENTITY (the load-bearing step):
have h_key_nat : (n + 1) * Nat.choose n k * (n - k)!
                 = (k + 1).ascFactorial (n - k + 1) := by
  have hk_fact_pos : 0 < k ! := Nat.factorial_pos k
  have h_asc : k ! * (k + 1).ascFactorial (n - k + 1) = (n + 1)! := by
    have := Nat.factorial_mul_ascFactorial k (n - k + 1)
    have h_sum : k + (n - k + 1) = n + 1 := by omega
    rwa [h_sum] at this
  apply Nat.eq_of_mul_eq_mul_right hk_fact_pos
  calc ((n + 1) * Nat.choose n k * (n - k)!) * k !
      = (n + 1) * (Nat.choose n k * k ! * (n - k)!) := by ring
    _ = (n + 1) * n ! := by rw [Nat.choose_mul_factorial_mul_factorial hk]
    _ = (n + 1)! := (Nat.factorial_succ n).symm
    _ = k ! * (k + 1).ascFactorial (n - k + 1) := h_asc.symm
    _ = (k + 1).ascFactorial (n - k + 1) * k ! := by ring
```

This proof has **no `field_simp` / `linear_combination`** in the
load-bearing core — only `ring`, `omega`, `rw` over verified Mathlib
lemmas, and the explicit `Nat.eq_of_mul_eq_mul_right`. The five `calc`
steps are each a single Mathlib lemma application or a ring rearrangement.

## Consolidated paste-ready block (Iter 43 PREP §"The full ACT")

This block **supersedes** Iter 42's paste-ready block (only the body of
`complex_betaIntegral_nat_eq_choose_inv` changes; the cast-bridge body
of `real_betaIntegral_nat_eq_choose_inv` from Iter 42 is unchanged
modulo one cosmetic tweak noted below).

**Insertion point** (unchanged from Iter 42): after Iter 38's
`exists_witness_choose_saturates_log_succ` (line 1661 in the live file),
before Iter 35b's `choose_mul_succ_dvd_lcmRange` (line 1758).

**Imports to add near the top of the file** (current file imports
`Mathlib.Tactic` only):

```lean
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
```

**Paste-ready block** (~85 LOC including docstrings; the +5 vs. Iter 42's
~80 is the explicit `calc` chain replacing the broken `linear_combination`):

```lean
/-- The Beta integral at natural arguments evaluates to a rational number
whose denominator is `(n+1) * C(n,k)`. Specialization over ℂ of Mathlib's
`Complex.betaIntegral_eval_nat_add_one_right`. -/
theorem complex_betaIntegral_nat_eq_choose_inv (n k : ℕ) (hk : k ≤ n) :
    Complex.betaIntegral (k + 1 : ℂ) (n - k + 1 : ℂ) =
      (1 : ℂ) / ((n + 1 : ℂ) * (Nat.choose n k : ℂ)) := by
  have hu : 0 < ((k + 1 : ℂ)).re := by
    rw [Complex.add_re, Complex.natCast_re, Complex.one_re]
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  -- Step 1: Mathlib's explicit formula for Beta(u, n+1) with u = k+1.
  rw [Complex.betaIntegral_eval_nat_add_one_right hu (n - k)]
  -- Step 2: identify the finite product with an ascending factorial.
  have h_prod : ∏ j ∈ Finset.range (n - k + 1), ((k + 1 : ℂ) + j) =
                  (((k + 1).ascFactorial (n - k + 1) : ℕ) : ℂ) := by
    rw [Nat.ascFactorial_eq_prod_range, Nat.cast_prod]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    push_cast
    ring
  rw [h_prod]
  -- Step 3: load-bearing ℕ identity (replaces Iter 42's broken
  -- `linear_combination`; see Iter 43 PREP for the algebraic-gap
  -- analysis). Closes via Nat-level k! cancellation.
  have h_key_nat : (n + 1) * Nat.choose n k * (n - k)!
                   = (k + 1).ascFactorial (n - k + 1) := by
    have hk_fact_pos : 0 < k ! := Nat.factorial_pos k
    have h_asc : k ! * (k + 1).ascFactorial (n - k + 1) = (n + 1)! := by
      have := Nat.factorial_mul_ascFactorial k (n - k + 1)
      have h_sum : k + (n - k + 1) = n + 1 := by omega
      rwa [h_sum] at this
    apply Nat.eq_of_mul_eq_mul_right hk_fact_pos
    calc ((n + 1) * Nat.choose n k * (n - k)!) * k !
        = (n + 1) * (Nat.choose n k * k ! * (n - k)!) := by ring
      _ = (n + 1) * n ! := by rw [Nat.choose_mul_factorial_mul_factorial hk]
      _ = (n + 1)! := (Nat.factorial_succ n).symm
      _ = k ! * (k + 1).ascFactorial (n - k + 1) := h_asc.symm
      _ = (k + 1).ascFactorial (n - k + 1) * k ! := by ring
  -- Step 4: cast the ℕ identity to ℂ and discharge the division.
  have h_key_C : ((n : ℂ) + 1) * (Nat.choose n k : ℂ) * ((n - k)! : ℂ)
                 = (((k + 1).ascFactorial (n - k + 1) : ℕ) : ℂ) := by
    exact_mod_cast h_key_nat
  have h_pos_asc : (((k + 1).ascFactorial (n - k + 1) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ascFactorial_pos k (n - k + 1)).ne'
  have h_pos_n1 : ((n : ℂ) + 1) ≠ 0 := by
    have : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    simpa using this
  have h_pos_ch : ((Nat.choose n k : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hk).ne'
  rw [eq_div_iff (mul_ne_zero h_pos_n1 h_pos_ch),
      div_mul_eq_mul_div, eq_div_iff h_pos_asc, one_mul]
  linear_combination h_key_C

/-- The real Beta integral with natural exponents equals `1 / ((n+1) · C(n,k))`.
Real-valued specialization of `complex_betaIntegral_nat_eq_choose_inv`, obtained
by casting the integrand to ℂ via `Complex.ofReal_*` + `Complex.cpow_natCast`
+ `intervalIntegral.integral_ofReal`, then descending via `Complex.ofReal_inj`. -/
theorem real_betaIntegral_nat_eq_choose_inv (n k : ℕ) (hk : k ≤ n) :
    ∫ x in (0:ℝ)..1, x ^ k * (1 - x) ^ (n - k) =
      (1 : ℝ) / ((n + 1 : ℝ) * (Nat.choose n k : ℝ)) := by
  -- Lift to ℂ via ofReal_inj.
  rw [show (1 : ℝ) / ((n + 1 : ℝ) * (Nat.choose n k : ℝ)) =
         ((1 : ℂ) / ((n + 1 : ℂ) * (Nat.choose n k : ℂ))).re from ?_]
  · rw [show ∫ x in (0:ℝ)..1, x ^ k * (1 - x) ^ (n - k) =
             (∫ x in (0:ℝ)..1,
                ((x ^ k * (1 - x) ^ (n - k) : ℝ) : ℂ)).re from ?_]
    · have hβ : Complex.betaIntegral (k + 1 : ℂ) (n - k + 1 : ℂ) =
          ∫ x in (0:ℝ)..1, ((x ^ k * (1 - x) ^ (n - k) : ℝ) : ℂ) := by
        unfold Complex.betaIntegral
        apply intervalIntegral.integral_congr
        intro x _
        have hk_exp : ((k + 1 : ℂ) - 1) = ((k : ℕ) : ℂ) := by push_cast; ring
        have hnk_exp : ((n - k + 1 : ℂ) - 1) = (((n - k) : ℕ) : ℂ) := by
          push_cast; ring
        rw [hk_exp, hnk_exp, Complex.cpow_natCast, Complex.cpow_natCast]
        push_cast
        ring
      rw [← hβ, complex_betaIntegral_nat_eq_choose_inv n k hk]
    · rw [← intervalIntegral.integral_ofReal]
      simp [Complex.ofReal_re]
  · push_cast
    simp [Complex.ofReal_re]
```

**Cosmetic tweak vs. Iter 42**: the final `?_`-discharge for the RHS
`.re`-extraction uses `push_cast` + `simp [Complex.ofReal_re]` instead of
Iter 42's nested `show`-rewrite. Both should compile; the `push_cast`
version is more robust to associativity drift in `(n + 1 : ℂ) * choose`.

**Net Lean delta** (Iter 44+ ACT, projected):
- Lean LOC: 1802 → ~1887 (+85, vs. Iter 42's +80; +5 net from explicit `calc`).
- Imports: +2 lines.
- Theorems: 77 → 79 (`complex_betaIntegral_nat_eq_choose_inv` +
  `real_betaIntegral_nat_eq_choose_inv`).
- Axioms: 1 → 1 (`hanson_bound` unchanged; this ACT lays Beta-integral
  ground but does NOT close the axiom).
- Sorries: 0 → 0.

## Bearer audit (Iter 43)

All Iter 41 / 42 bearers re-affirmed at SHA `2df2f0150c…` (unchanged
since Iter 36). The corrected discharge introduces **two additional
load-bearing Mathlib lemmas not in Iter 42's bearer list**:

| # | Bearer | Path:Line at v4.26.0 | Iter 43 verdict |
|---|--------|----------------------|------------------|
| 11 | `Nat.eq_of_mul_eq_mul_right` | `Mathlib/Data/Nat/Defs.lean` (core) | ✅ Mathlib core; signature `0 < m → a * m = b * m → a = b` |
| 12 | `Nat.factorial_pos` | `Mathlib/Data/Nat/Factorial/Basic.lean` | ✅ standard, `0 < n!` |
| 13 | `Nat.factorial_succ` | `Mathlib/Data/Nat/Factorial/Basic.lean` | ✅ standard, `(n+1)! = (n+1) * n!` |

All three are entry-level Mathlib lemmas with no expected API drift at
v4.26.0; they have been stable since Mathlib3 port. Iter 44+ ACT can
trust their signatures without further audit.

## Infrastructure: Docker host degradation (NEW, blocks ACT)

Sibling Docker container `lean-build-57602` flagged as risky in Iter 42
has further degraded since 2026-06-02:

```
docker ps:       lean-build-57602 ... Up 31 hours
docker exec:     "container 9db9a3f1bb19... is not running"
docker inspect:  state.status = "dead", startedAt = 2026-06-02T11:26:29Z
docker images:   I/O error on blob sha256:1487d0af5f52...
                 ("expected at /var/lib/desktop-containerd/.../blobs/sha256/...")
disk free:       11 GiB / 926 GiB (53% used, but corrupted-blob recovery
                 budget exhausted)
```

The Docker daemon's state machine is **inconsistent** (`ps` claims the
container is up, but `exec` reports it dead and `inspect.State.Status`
confirms `dead`). The backing image `9026c55995f4` for
`lean4-arm64:v4.26.0` has at least one corrupted blob in the
content-addressed store. Any `./proofs/scripts/docker-build.sh` invocation
in this state would either (a) hard-fail on the corrupted-blob I/O error
or (b) attempt to re-pull / re-build the image, exhausting the 11 GiB
disk slack budget and risking host instability.

**Remediation needed before Iter 44+ ACT**:
- `docker rm -f lean-build-57602` to clear the wedged container record.
- `docker system prune -a --volumes` to reclaim the corrupted-blob store
  (frees ~the image footprint, several GiB).
- `docker pull` (or rebuild) the `lean4-arm64:v4.26.0` image fresh.
- Confirm `docker exec` against a fresh test container succeeds before
  attempting `./proofs/scripts/docker-build.sh Proofs.BaselProblemOQ01OQ01OQ02OQ03`.

Without this remediation, ACT is **blocked at the infrastructure layer**
regardless of the Lean-side correctness of this PREP's paste-ready block.

## What this PREP does NOT include

1. **No Lean edits**. Doc-only PREP. File byte-identical to Iter 38 ACT
   state (md5 `4b4ac86002cb4c60b7a2863c157dad48`, 1802 LOC).
2. **No build verification** (Docker host degraded; remediation steps
   listed above must precede Iter 44+ ACT).
3. **No edits to `knowledge.md`, `problem.md`, or gallery `meta.json`**.
4. **No reduction of `axiom hanson_bound`** — same disclaimer as Iter
   39 / 41 / 42 PREP; integer-squeeze closure requires 28a landed +
   `n₀ ≤ 100` (existing `hanson_n1..hanson_n100` numerical floor at
   file lines 1391–1462 provides the budget).
5. **No re-derivation of the cast-bridge body for
   `real_betaIntegral_nat_eq_choose_inv`** beyond the cosmetic `push_cast`
   tweak; the Iter 42 structure is sound (the gap is in the *complex*
   theorem's terminal step, not the cast-bridge).

## Honest framing / self-audit

- **Findings are algebraic, not syntactic**. Iter 42's "Medium risk"
  framing of `linear_combination` v4.26.0 syntax-drift mis-identified the
  issue. The call cannot close the goal at *any* `linear_combination`
  version because the goal requires a non-linear (multiplicative)
  cancellation step. This is the kind of gap a Lean build would surface
  in seconds — Iter 42's no-build framing concealed it.
- **The corrected discharge is build-untested**. The ℕ-level descent
  is mathematically sound, but Lean's exact cast-syntax (`exact_mod_cast`
  vs `push_cast`, `Nat.cast_add_one` friction between `((n+1 : ℕ) : ℂ)`
  and `((n : ℂ) + 1)`) may require build-time tweaking. Iter 44+ ACT
  should expect 1-2 small adjustments around `h_key_C` / `h_pos_n1`.
- **The fix preserves the Iter 42 outer structure**. Steps 1, 2 (the
  Mathlib `Complex.betaIntegral_eval_nat_add_one_right` + `ascFactorial`
  identification) are unchanged. Only the terminal discharge changes,
  and it shrinks the hypothesis count (from three `*_C` hypotheses to
  one `h_key_C` + nonzero side-conditions).
- **No bearer drift**. All eight Iter 41 + two Iter 42 bearers re-affirmed
  at SHA `2df2f0150c…`. Three NEW Mathlib-core bearers (`Nat.eq_of_mul_eq_mul_right`,
  `Nat.factorial_pos`, `Nat.factorial_succ`) are entry-level lemmas with
  no expected drift at v4.26.0.
- **Infrastructure is a real ACT blocker**. The Docker degradation
  documented above is independent of the Lean-side analysis. Iter 44+
  should treat the listed remediation as a pre-flight checklist.

## Cross-references

- Iter 28 PREP (2026-05-12, #18352): Route B vs A vs C strategic choice.
- Iter 29 PREP (2026-05-12, #18485): initial bearer audit + errata.
- Iter 34a ACT (2026-05-15, #19208): 28b-1 bound + Lemma A.
- Iter 35b ACT (2026-05-15, #19372): 28c divisibility bridge.
- Iter 36 PREP (2026-05-15, #19499): 28b-2 paste-ready discharge.
- Iter 37 INFRA-SIGNAL (2026-05-25, #20636): Docker gate RED→GREEN.
- Iter 38 ACT (2026-05-28, #20863): 28b-2 witness saturation shipped.
- Iter 39 PREP (2026-05-31, #21401): 28a paste-ready skeleton.
- Iter 40 STATE-SYNC (2026-05-31, #21544): state.md catch-up post Iter 39.
- Iter 41 PREP (2026-06-01, #22033): bearer re-verify + IBP probe + cast-bridge recommendation.
- Iter 42 PREP (2026-06-02, prior PR): cast-bridge consolidation (this iter
  audits its terminal `linear_combination`).

## What the next researcher should do (Iter 44+)

**Pre-flight (infrastructure)**:
1. Clear wedged Docker state: `docker rm -f lean-build-57602`,
   `docker system prune -a --volumes`.
2. Re-pull / rebuild the `lean4-arm64:v4.26.0` image. Confirm
   `docker exec` against a fresh container succeeds.

**Lean ACT** (Iter 43 PREP §"The full ACT" above):
1. Add the two imports at the top of `Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean`.
2. Paste the corrected block after `exists_witness_choose_saturates_log_succ`
   (line 1661).
3. Build-verify under `./proofs/scripts/docker-build.sh Proofs.BaselProblemOQ01OQ01OQ02OQ03`.
4. **Primary residual risk** (Low, vs. Iter 42's Medium): cast-syntax
   friction between `((n+1 : ℕ) : ℂ)` and `((n : ℂ) + 1)` around
   `h_key_C` / `h_pos_n1` / the terminal `linear_combination`. If the
   `linear_combination h_key_C` fails, swap for:
   ```lean
   ring_nf
   exact h_key_C
   ```
   or
   ```lean
   linarith [h_key_C]  -- only if the final form is a literal `=`-of-monomials
   ```
   The ℕ-level core is sound regardless; only the ℂ-side cast plumbing
   may need a single-line tweak.
5. **Cast-bridge for `real_betaIntegral_nat_eq_choose_inv`**: Iter 42's
   structure is preserved; if the inner `.re`-rewrites fail, fall back
   to the explicit `Complex.ofReal_injective` form documented in Iter
   42's session log §"What the next researcher should do" (Iter 43+).

**Expected ACT size**: ~85 LOC (+5 vs. Iter 42 due to the explicit
ℕ-level `calc`).
**Expected wall-clock**: 1 session, post infrastructure remediation
(remediation itself ~30 min).
**Net axiom delta**: 0 (this lays Beta-integral ground; integer-squeeze
of `hanson_bound` is Iter 45+ after numerical floor + 28a stitch).
