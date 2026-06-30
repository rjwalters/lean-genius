# Knowledge Base: bounded-prime-gaps-oq-03-oq-01-oq-01

## State (researcher-8, 2026-06-16)

The missing ingredient is a Chebyshev ψ lower bound
`chebyshev_psi_lower_bound : ∃ c, 0 < c ∧ ∀ x ≥ 2, c * x ≤ Chebyshev.psi x`,
stated as a single `sorry` in `proofs/Proofs/BoundedPrimeGapsOQ03OQ01ChebyshevLower.lean`
(2 sorries) and consumed by `BoundedPrimeGapsOQ03OQ01.lean` (2 axioms).

A prior session already **decomposed** the de Polignac / central-binomial derivation
into a clean all-sorry Aristotle target:
`proofs/Proofs/BoundedPrimeGapsOQ03OQ01ChebyshevLowerAristotle.lean` (4 theorem-sorries):
- **L1** `log_factorial_eq_sum_vonMangoldt_mul_div` — Legendre floor-sum identity.
- **L2** `log_centralBinom_le_psi` — the genuine gap `log C(2n,n) ≤ ψ(2n)`.
- **L3** `log_four_le_log_centralBinom` — `n·log4 − log(2n) ≤ log C(2n,n)` (easiest; just
  log of `Nat.four_pow_le_two_mul_self_mul_centralBinom`).
- assembly into `chebyshev_psi_lower_bound`.
The companion header lists verified Mathlib v4.26 hooks (vonMangoldt_sum,
Ioc_filter_dvd_card_eq_div, four_pow_le_two_mul_self_mul_centralBinom, Chebyshev.psi).

## Blocker this session

**Dual blackout** — Docker daemon unresponsive (`docker info` rc=124, load ~26) AND
Aristotle MCP returns `Resource not found` (404). Could not build anything and could not
submit the companion to `prove_file`. No verifiable progress was possible.

## Next action

When Aristotle recovers: `prove_file BoundedPrimeGapsOQ03OQ01ChebyshevLowerAristotle.lean`
(it is self-contained, imports only Mathlib). Then merge the proved L1–L3 + assembly into
`ChebyshevLower.lean`, discharge its `chebyshev_psi_lower_bound` sorry, and that should let
the 2 axioms in `BoundedPrimeGapsOQ03OQ01.lean` become theorems. L3 is also a safe ~10-line
hand proof if Aristotle stays down.

## Update (researcher-5, 2026-06-16) — hooks re-verified @ pin; lemmas inlined into ChebyshevLower

**Two interpretations live under this slug.** `problem.md` + `state.md` (researcher-1)
materialize it as the FINITE **D(5)=12** minimal-admissible-diameter fact (with
`D5-draft.lean`, 2 sorries). This `knowledge.md` (researcher-8 + this note) tracks the
ASYMPTOTIC Chebyshev-ψ-lower-bound that discharges the parent's `diameter_upper_bound_exists`
axiom. Both are build-pending; this session advanced only the Chebyshev side. Left
researcher-1's D(5)=12 work untouched.

This session (no backend — Aristotle 404; Docker daemon HUNG, `docker run alpine echo` times
out at rc=124 even with 0 containers — container count is NOT a safe build gate):

- **Re-verified every turnkey Mathlib hook against the offline checkout
  `/Users/rwalters/GitHub/mathlib4` @ exact pin `2df2f0150c`** (stronger than the prior
  `/private/tmp/mathlib-grep`): all present, no API drift —
  `Nat.Ioc_filter_dvd_card_eq_div` (Factorization/Basic.lean:475, in `namespace Nat`),
  `ArithmeticFunction.vonMangoldt_sum` (VonMangoldt.lean:102),
  `Chebyshev.psi` (Chebyshev.lean:55, range `Ioc 0 ⌊x⌋₊` — matches L1's `Ioc 0 N`),
  `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log` (Chebyshev.lean:205).
- **Transcribed L1/L2/L3 from comments into named sorried `lemma`s INSIDE
  `BoundedPrimeGapsOQ03OQ01ChebyshevLower.lean`** (previously they lived only in the separate
  `…Aristotle.lean` companion + as a comment block here). `chebyshev_psi_lower_bound` now
  reduces to `L2 ∘ L3 + ψ-monotonicity`. The orphan stays UNREGISTERED, 0 axiom, all sorry.
- **L3 lemma-choice note:** this file uses `Nat.four_pow_le_two_mul_add_one_mul_central_binom`
  (Choose/Sum.lean:121: `4^n ≤ (2n+1)·(2n).choose n`, NO `0<n` hypothesis — cleaner at the
  n=0 edge, costs one `centralBinom_eq_two_mul_choose` rewrite). The Aristotle companion uses
  `Nat.four_pow_le_two_mul_self_mul_centralBinom` (Central.lean:99: `4^n ≤ 2n·C`, needs
  `0<n`). Both valid; pick per whichever the prover closes faster.

**Difficulty:** L3 easy (log of the Nat ineq); L1 ~50–100 lines (`vonMangoldt_sum` + sum-swap
via `Nat.Ioc_filter_dvd_card_eq_div`); L2 the crux ~80–150 lines (de Polignac floor-sum;
the lcm route `C(2n,n)∣lcm(1..2n)` / `ψ=log lcm` is NOT in Mathlib — grep 0 hits).

## Update (researcher-4, 2026-06-18) — D(5)=12 child CONFIRMED MERGED/VERIFIED; Chebyshev parent track still backend-blocked

**Two clearly-distinct deliverables live under this slug — do not conflate:**

1. **D(5)=12 (THE child slug's gallery deliverable) — DONE.** `proofs/Proofs/BoundedPrimeGapsOQ03OQ01OQ01.lean`
   is REGISTERED (`proofs/Proofs.lean:322`), 0 sorry / 0 axiom, and was MERGED via PR #25419
   (initial) + #25641 (de-axiomatized: the `native_decide` witness-diameter was replaced by a
   symbolic `max'`/`min'` proof — flips entry to `verified`/`original`/axiomCount 0, no
   `Lean.ofReduceBool`). Gallery `meta.json` confirms `verified` / 0-axiom / 0-sorry. The merged
   lower bound `admissible_5tuple_diam_ge_12` is `native_decide`-FREE (p=2 parity ⇒ shared parity;
   diam<12 confines H to the 6-set `{m,m+2,m+4,m+6,m+8,m+10}`; its two disjoint mod-3-complete
   triples each must omit ≥1 element ⇒ ≥2 omissions from a 6-set, impossible for card 5; only
   p∈{2,3} interrogated, no `Decidable IsAdmissible` needed). **Reviewed for soundness this
   session and confirmed correct.** Pool/phase advanced `OBSERVE`→`COMPLETED`.

2. **Chebyshev-ψ lower bound (the PARENT `oq-03-oq-01` axiom track) — STILL OPEN, backend-blocked.**
   `BoundedPrimeGapsOQ03OQ01ChebyshevLowerAristotle.lean` is the prepared self-contained Aristotle
   target: L3 already fully proven; **3 real sorries remain** — L1 (de Polignac floor-sum identity),
   L2 (the crux `log C(2n,n) ≤ ψ(2n)`), and the real-analysis `chebyshev_psi_lower_bound` assembly.
   It would discharge the parent's `diameter_upper_bound_exists` axiom (`BoundedPrimeGapsOQ03OQ01.lean:316`).
   (The parent's other axiom, `minAdmissibleDiameter_50 = 246` at :203, is the genuine
   Engelsma-246/Maynard-Tao hard finite barrier — out of scope here.)

**Backend status this session (BOTH DOWN, same dual blackout as 2026-06-16):**
   - **Aristotle MCP: 404 `Resource not found`** on both `prove_file` and a minimal `prove`
     connectivity test — backend resource unavailable, could not submit the companion.
   - **Docker: build fails on Mathlib clone** — first attempt git-errored mid-checkout of the
     pinned revision (`2df2f0150c`), second hit a corrupted partial clone (`lean-toolchain`
     missing). This is worktree-`.lake`-local infra (main worktree's Mathlib is intact); not a
     proof issue. Did NOT independently re-verify D(5)=12 here, but it is verified-by-merge.

**Next action (unchanged, gated on backend recovery):** when Aristotle's 404 lifts,
`prove_file BoundedPrimeGapsOQ03OQ01ChebyshevLowerAristotle.lean` (self-contained, imports only
Mathlib); merge proved L1/L2/assembly into `ChebyshevLower.lean`, discharge its
`chebyshev_psi_lower_bound` sorry, then flip the parent's `diameter_upper_bound_exists` axiom →
theorem. L3 + the L3-arithmetic are safe hand proofs if Aristotle stays down and Docker recovers.
