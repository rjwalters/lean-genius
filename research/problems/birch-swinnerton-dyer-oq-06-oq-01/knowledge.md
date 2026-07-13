# Knowledge Base: birch-swinnerton-dyer-oq-06-oq-01

## Problem Understanding

Goal: formalize that 389a1 (y² + y = x³ + x² - 2x, conductor 389) has the
**smallest conductor among all rank-2 elliptic curves over ℚ** (Cremona's
classification).

## Key finding: the deep content is infeasible in-Lean

The genuine statement — *no* rank-2 curve has conductor < 389 — is Cremona's
exhaustive computation: enumerate every isogeny class of conductor < 389 and
determine its Mordell–Weil rank by descent. This is thousands of rigorous rank
computations and cannot be reproduced in Lean today (Mathlib has no usable
2-descent / rank-upper-bound machinery). So a fully unconditional proof is BLOCKED.

## Approach taken (SHIPPED, verified / 0-axiom)

Separate verifiable structure from infeasible computation:

1. **Abstract minimal-conductor framework** over a carrier `E` with
   `cond, rk : E → ℕ`:
   - `IsMinConductorForRank cond rk E₀ r := rk E₀ = r ∧ ∀ E', rk E' = r → cond E₀ ≤ cond E'`
   - `isMinConductorForRank_of_lb` (lower bound ⟹ minimality)
   - `minConductor_unique`, `le_conductor_of_minConductor`, `rank_ne_of_conductor_lt`
2. **Cremona rank-record registry** (verified `decide`/`norm_num` arithmetic):
   records 11/37/389/5077 at ranks 0/1/2/3; strict monotonicity 11<37<389<5077;
   389 prime; uniqueness of the rank-2 record.
3. **Headline conditional theorem** `curve389a_isMinConductorForRank2`: takes
   Cremona's lower bound (`∀ E', rk E' = 2 → 389 ≤ cond E'`) as an explicit
   HYPOTHESIS (not an axiom) and concludes minimality. Corollaries:
   `rank2_conductor_ge_389`, `conductor_lt_389_rank_ne_two`.

`#print axioms curve389a_isMinConductorForRank2` ⟹ depends on NO axioms.
Self-contained (imports only Mathlib; does NOT pull the 7,400-line BSD chain).

File: `proofs/Proofs/BirchSwinnertonDyerOQ06OQ01.lean` (215 lines, 13 thm, 6 def,
1 structure, 0 axiom, 0 sorry). Built on host (`lake env lean`, docker down),
exit 0.

## Insights

- Minimality = "rank matches" + "lower bound holds for all of that rank"; once
  the lower bound is granted, minimality is one line. All difficulty is in the
  lower bound → isolate it as a hypothesis to stay 0-axiom and honest.
- The parent OQ-06 "Minimal Conductor Property" section only proved 389 = 389 and
  Nat.Prime 389 — this entry supplies the actual minimality content, so it is
  non-trivial and distinct from the parent.

## Dead Ends / Not attempted

- Importing the parent BirchSwinnertonDyer.lean chain to reference the concrete
  `curve389a`/`conductor`/`algebraicRank`: rejected — would require building a
  7,400-line file with docker down; the abstract framework is directly
  instantiable by those symbols when desired, so no loss of content.
- Decidable minimality over a finite enumeration of *all* sub-389 curves:
  infeasible (need the whole database + rank certificates).

## Next steps (for a future unconditional proof)

Discharge `hcremona` via a verified Cremona-database slice with descent-based
rank certificates; needs Mathlib elliptic-curve descent first.
