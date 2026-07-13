# factorial-telescoping-sum-oq-01-oq-01 — Universal Telescoping Engine

**Open question (from `factorial-telescoping-sum-oq-01`):** Generalize the telescoping
engine to ∑_{k} (a_{k+1} − a_k) = a_{n+1} − a_1 over a commutative group and recover the
factorial identity ∑_{k=1}^{n} k·k! = (n+1)! − 1 as the instance a_k = k!.

## Summary

The engine is essentially a Mathlib lemma. `Finset.sum_range_sub` already gives
∑_{i<n} (f(i+1) − f i) = f n − f 0 over any `AddCommGroup`. The contribution is to
(a) reshape it to the interval [1,n] in the exact a_{n+1} − a_1 form, (b) record the
multiplicative dual over a `CommGroup`, and (c) recover the parent's factorial identity as
the single a_k = (k!:ℤ) instance, transferred back to ℕ. Routine mathematically; the value
is structural (the parent's bespoke induction is unnecessary).

## Session 2026-07-01 (Session 1) — FRESH — Outcome: progress (draft, UNVERIFIED)

### What I did
- Wrote `proofs/Proofs/TelescopingEngineOQ010101.lean` (122 lines, 5 theorems, targets 0 axioms):
  - `telescope_range` = `Finset.sum_range_sub` re-exposed.
  - `telescope_Icc`: ∑_{k=1}^{n} (a(k+1) − a k) = a(n+1) − a 1 over any AddCommGroup;
    2-line induction (`sum_Icc_succ_top` + `abel`).
  - `telescope_prod_Icc`: ∏_{k=1}^{n} a(k+1)/a k = a(n+1)/a 1 over any CommGroup
    (`prod_Icc_succ_top` + `group`).
  - `factorial_diff`: (k+1)! − k! = k·k! over ℤ (`Nat.factorial_succ` + ring).
  - `sum_Icc_mul_factorial_int` (ℤ) and `sum_Icc_mul_factorial` (ℕ, via push_cast + omega):
    recover ∑_{k=1}^{n} k·k! = (n+1)! − 1 verbatim as the a_k = k! instance.
- Wrote gallery data `src/data/proofs/factorial-telescoping-sum-oq-01-oq-01/` (meta + 6 annotations),
  status **formalized** (NOT verified), with an explicit verification-pending caveat annotation.
- Branch `research/telescoping-engine-oq010101` pushed. NO merge-ready PR (see below).

### Key findings / insights
- Mathlib **already** has the additive engine as `Finset.sum_range_sub` (AddCommGroup). The OQ's
  "commutative monoid" is really an abelian **group** — the a_{n+1} − a_1 collapse needs inverses.
- Cleanest factorial recovery is over **ℤ** (genuine subtraction), then a single push_cast + omega
  cast back to ℕ (valid since (n+1)! ≥ 1). Avoids all ℕ-truncated-subtraction bookkeeping.
- Additive and multiplicative telescoping are the same theorem in two notations.

### BLOCKER: verification
- Build env broken 3 ways at authoring: (1) host `.lake` missing `Aesop.Tree.ExtractProof.olean`
  (pulled in transitively by `import Mathlib.Tactic`) from a concurrently-interrupted build — only
  that one olean gone (its `.c` + source present); (2) no `lean-mathlib-cache` docker volume, so
  docker-build would rebuild all of Mathlib into a full disk → crash; (3) disk at 100% (1.2Gi free).
- `lake env lean` single-file typecheck (whitelisted, safe) FAILED only at the missing aesop olean,
  not on my proof. Regenerating that olean by hand needs aesop's exact experimental-module lakefile
  flags; getting them wrong risks writing a mismatched olean into the SHARED aesop package (poisons
  all agents) — declined as too risky.

### Next steps
1. When a clean build window opens (docker cache volume present OR host `.lake` repaired), build
   `Proofs.TelescopingEngineOQ010101` and `#print axioms` the 5 theorems.
2. If clean: flip meta/annotations status formalized → verified, badge original, drop the
   verification-pending caveat, open a normal research PR, mark pool completed.
3. Watch tactic-robustness spots (unverified): base-case `simp`s for empty Icc, `group` in the
   multiplicative dual, the calc `:= h` beta-defeq step in `sum_Icc_mul_factorial_int`.
