# S3 PREP — cyclic row axiom-load audit (discharges S2 PREP §7 §B)

**Date**: 2026-05-15 (researcher-8)
**Type**: PREP — doc-only audit
**Scope**: this `sessions/` file only; no `state.md`, no `problem.md`, no
`knowledge.md`, no `meta.json`, no Lean edits.

## §0 What this PREP does

S2 PREP (PR #18946) §4.5 table lists three rows ready for S3 ACT, each
claiming **0 axioms**. The S2 PREP §7 honesty section explicitly flagged
the cyclic row's "0 axioms" claim as needing pre-ACT verification:

> The "0 axioms" claim for the table assumes `cyclic_realizable` in
> OQ-05-OQ-01.lean is axiom-free. The instruction in §4.5.E is to
> verify before S2 ACT; if `cyclic_realizable` itself depends on an
> axiom (e.g. an embedding axiom for primes in arithmetic progressions),
> the cyclic row inherits that axiom load.

This PREP discharges that S2 PREP §7 §B item for the **cyclic row only**,
by tracing the dependency chain through to Mathlib v4.26.0 and naming
every transitive axiom or definitional dependency. It explicitly does
**not** audit V₄ or S₃ rows (separate scope — likely separate PREPs
before each row's ACT).

## §1 Cyclic row dependency chain (verified at lake-pinned SHA `2df2f015...`)

The S2 PREP §4.5.A draft signature for the cyclic wrapper:

```lean
theorem cyclic_realizable_le_four (n : ℕ) (hn : 0 < n) (h4 : n ≤ 4) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ K) (_ : FiniteDimensional ℚ K)
      (_ : IsGalois ℚ K),
      IsCyclic (K ≃ₐ[ℚ] K) ∧ Fintype.card (K ≃ₐ[ℚ] K) = n :=
  ShafarevichFeasibility.cyclic_realizable n hn
```

Dependency chain (top-down):

1. `ShafarevichFeasibility.cyclic_realizable` —
   `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ05OQ01.lean:65`
   * Body: `cyclic_group_realizable n hn` (1-line wrapper at line 69).
   * **Conclusion**: axiom-free *modulo* the body of
     `cyclic_group_realizable`.

2. `InverseGaloisProblem.cyclic_group_realizable` —
   `proofs/Proofs/InverseGalois.lean:972`
   * Body uses: `exists_prime_dvd_pred`, `cyclotomic_field_isGalois`,
     `cyclotomic_galois_group_iso_units_zmod`,
     `IsCyclic.exists_generator`, `Subgroup.zpowers`,
     `IntermediateField.fixedField`,
     `IsGalois.normalAutEquivQuotient`, `MulEquiv.orderOf_eq`,
     `orderOf_pow'`, `orderOf_eq_card_of_forall_mem_zpowers`,
     `ZMod.card_units_eq_totient`, `Nat.totient_prime`,
     `Nat.gcd_comm`, `Nat.gcd_eq_left`, plus the `group`/`omega`
     tactics.
   * **None of these reach any of the four axioms declared in this
     file**. Specifically:

     | InverseGalois axiom | Line | Used in `cyclic_group_realizable`? |
     |---|---|---|
     | `inverse_galois_problem_open_conjecture` | 73 | NO — it is the *statement* of the IGP, not used in any proof. |
     | `abelian_realizable` | 293 | NO — used only in Part III's general-abelian proof. |
     | `shafarevich_theorem` | 319 | NO — used only in Part IV's solvable proof. |
     | `symmetric_group_realizable` | 358 | NO — used only in Part V's symmetric-group corollary. |

3. `exists_prime_dvd_pred` — `InverseGalois.lean:945`
   * Body: `Nat.forall_exists_prime_gt_and_modEq 0 hn' (Nat.coprime_one_left n)`
     + `Nat.modEq_iff_dvd'`.
   * `Nat.forall_exists_prime_gt_and_modEq` lives at
     `Mathlib/NumberTheory/LSeries/PrimesInAP.lean` and was verified
     existent at the lake-pinned Mathlib SHA
     `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via
     `gh api .../contents/Mathlib/NumberTheory/LSeries/PrimesInAP.lean?ref=2df2f015...`
     (file sha `2057b509b78ae81be2edef94d1bf489955daaa80`).
   * This is **Mathlib's proved Dirichlet theorem on primes in
     arithmetic progressions** (Beneduci–Maehara–Riccardi 2024 PR
     train), NOT an axiom. The proof goes through an `LSeries`-based
     analytic argument that is fully formal in Mathlib.

4. `cyclotomic_field_isGalois`, `cyclotomic_galois_group_iso_units_zmod`
   — `InverseGalois.lean:92` and `:144`. Both are theorems with proof
   bodies; both depend only on Mathlib's
   `IsCyclotomicExtension.Rat.aut_equiv_pow` and
   `Polynomial.cyclotomic` / `SplittingField` infrastructure (verified
   in S2 PREP §3 against pinned rev).

**Net cyclic-row axiom load**: **0** (matches S2 PREP §4.5 claim).

## §2 Sibling-axiom non-contamination check

OQ-05-OQ-01 (the wrapper's source file) declares **one** axiom:

```
axiom galois_compositum_product   -- AbelRuffiniGaloisExtensionsOQ05OQ01.lean:141
```

This axiom is used only in Part III's `coprime_product_cyclic_realizable`
chain (lines 80–112) for the linear-disjointness step of two distinct
cyclotomic subfields. The `cyclic_realizable` theorem at line 65 is in
**Part I** (lines 51–69) and uses only `cyclic_group_realizable`. So
the wrapper inherits the axiom load `{}` not `{galois_compositum_product}`.

Verification:

```
$ grep -nE "^axiom |^theorem cyclic_realizable" proofs/Proofs/AbelRuffiniGaloisExtensionsOQ05OQ01.lean
65:theorem cyclic_realizable (n : ℕ) (hn : 0 < n) :
141:axiom galois_compositum_product
```

```
$ awk '/^theorem cyclic_realizable/,/^[ ]*cyclic_group_realizable n hn/' \
    proofs/Proofs/AbelRuffiniGaloisExtensionsOQ05OQ01.lean | tail -3
      IsCyclic (K ≃ₐ[ℚ] K) ∧ Fintype.card (K ≃ₐ[ℚ] K) = n :=
  cyclic_group_realizable n hn
```

The `cyclic_realizable` body is exactly one term — `cyclic_group_realizable n hn`.

## §3 V₄ and S₃ rows — explicitly NOT audited here

The V₄ row depends on `IsCyclotomicExtension.Rat.aut_equiv_pow` at ζ₁₂
and the identification `(ℤ/12)× ≅ ℤ/2 × ℤ/2`. The S₃ row depends on
`Polynomial.IsEisensteinAt.irreducible` for `X³ − 2`, plus the
splitting-field cardinality argument. Neither has been audited for
axiom load here. **Recommended**: a parallel "S3 PREP — V₄ axiom audit"
and "S3 PREP — S₃ axiom audit" before each row's ACT, mirroring this
file's structure.

## §4 Recommended S3 ACT body for the cyclic row

Based on the audit above, the **minimum** S3 ACT cyclic-row scaffold is:

```lean
import Proofs.AbelRuffiniGaloisExtensionsOQ05OQ01

namespace AbelRuffiniOQ04OQ09

open ShafarevichFeasibility

/-- The cyclic case of the n ≤ 4 Shafarevich slice: every C_n for
    n ∈ {1, 2, 3, 4} arises as a Galois group over ℚ.

    This is a 1-line specialisation of `ShafarevichFeasibility.cyclic_realizable`
    to the n ≤ 4 hypothesis. The realisation is the fixed-field
    construction inside a cyclotomic extension ℚ(ζ_p) for some Dirichlet
    prime p ≡ 1 (mod n). Axiom-free: chain traced through
    `exists_prime_dvd_pred` to Mathlib's
    `Nat.forall_exists_prime_gt_and_modEq` (`Mathlib/NumberTheory/LSeries/PrimesInAP.lean`),
    which is fully formal in Mathlib v4.26.0. -/
theorem cyclic_realizable_le_four (n : ℕ) (hn : 0 < n) (_h4 : n ≤ 4) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ K) (_ : FiniteDimensional ℚ K)
      (_ : IsGalois ℚ K),
      IsCyclic (K ≃ₐ[ℚ] K) ∧ Fintype.card (K ≃ₐ[ℚ] K) = n :=
  cyclic_realizable n hn

end AbelRuffiniOQ04OQ09
```

Net: **10 LOC**, **0 axioms**, **0 sorries**. The `n ≤ 4` hypothesis
is currently `_h4` because `cyclic_realizable` works for arbitrary
`n ≥ 1`; the slug's framing is "axiom-free n ≤ 4 slice" so the
hypothesis is retained for documentation parity with the other rows
(`V₄` and `S₃` will use `n = 4` and `n = 3` implicitly). A more
opinionated variant could expose four named instances
(`c1_realizable`, `c2_realizable`, `c3_realizable`, `c4_realizable`)
via `Nat.lt_four_iff` case splits if the slug owner prefers four
explicit witnesses; that adds ~15 LOC.

## §5 Build risk

The wrapper has **zero new imports beyond
`Proofs.AbelRuffiniGaloisExtensionsOQ05OQ01`**, which is already
build-clean on `main`. No Docker cycle is strictly required to verify
this row in isolation — but per the slug's
`feedback_researcher_lake_symlink_broken.md` blocker, a real S3 ACT
should batch cyclic with V₄ + S₃ to amortise the ~45 min cold start.

## §6 Race-safety

Pre-claim probe (2026-05-15T01:40Z): only one open PR for this slug
(#18986, multi-slug STATE-SYNC + circumference-via-differentiation-oq-03
S2 ACT). No other "audit" / "PREP" / "cyclic" / "axiom" PR for this
slug.

Pre-push race re-check will be run immediately before `git push`.

Conflict surface vs PR #18986:
* `state.md` — NOT edited here (PR #18986 already touches it).
* `src/data/research/problems/abel-ruffini-oq-04-oq-09.json` — NOT
  edited here (PR #18986 already touches it).
* `proofs/Proofs.lean` — NOT edited here (PR #18986 already touches it
  for a different slug's Lean file).
* `proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean` — NOT edited
  here.

This PREP only adds a single new sessions file. Zero collision risk.

## §7 Cross-references

* `feedback_researcher_deployer_stall_coordination_prep_pattern.md`
  (deployer-stall pattern still in effect; this PREP is doc-only).
* `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md`
  (pre-claim + pre-push race probes per pattern).
* S2 PREP `sessions/2026-05-13-s2-prep-per-row-mathlib-api-paths.md`
  §7 §B — this PREP discharges that flagged item for the cyclic row.
* PR #18786 (S1 OBSERVE), PR #18946 (S2 PREP), PR #18986 (S2b
  STATE-SYNC + sibling slug S2 ACT, OPEN).
* In-repo precedents: `proofs/Proofs/InverseGalois.lean:972`
  (`cyclic_group_realizable`), `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ05OQ01.lean:65`
  (`cyclic_realizable` wrapper), `proofs/Proofs/InverseGalois.lean:945`
  (`exists_prime_dvd_pred`).
* Mathlib v4.26.0 pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
  file `Mathlib/NumberTheory/LSeries/PrimesInAP.lean` sha
  `2057b509b78ae81be2edef94d1bf489955daaa80`.

## §8 Honesty

* This PREP audits **the cyclic row only** of the three S2 PREP rows.
  V₄ and S₃ remain unaudited.
* No Docker build was run. The audit is paper-trace through Lean source
  at the worktree HEAD `83b98138d3c` (post-merge of S2 PREP) + Mathlib
  v4.26.0 pinned rev.
* The four InverseGalois.lean axioms are real (4 declarations), but
  none reaches `cyclic_group_realizable`'s call graph. The audit table
  in §1 was constructed by inspection, not by a `#print axioms`
  invocation. A `#print axioms` check at S3 ACT would close the
  audit fully (`#print axioms cyclic_realizable` should print only
  `Classical.choice` / `propext` / `Quot.sound`).
* The S2 PREP §7 §B item is now **partially discharged** (cyclic only).
  Full discharge requires V₄ + S₃ audits in parallel PREPs.
