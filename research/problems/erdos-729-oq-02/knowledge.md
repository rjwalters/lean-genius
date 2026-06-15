# Knowledge Base: erdos-729-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Session 2026-06-15 (Session 1) — RESOLVED (build-pending)

**Mode**: FRESH
**Outcome**: progress — target theorem proved axiom-free (companion file)

### What I Did
- Found that Mathlib v4.26 already contains Legendre's theorem in digit-sum form:
  `sub_one_mul_padicValNat_factorial` (Mathlib/NumberTheory/Padics/PadicVal/Basic.lean:587):
  `(p - 1) * padicValNat p (n!) = n - (Nat.digits p n).sum`, needing `[Fact p.Prime]`.
- At p = 2 the `(p-1)=1` factor disappears, so the problem.md target
  `padicValNat 2 n! = n - (Nat.digits 2 n).sum` is a one-line corollary.
- Wrote unregistered companion `proofs/Proofs/Erdos729OQ04.lean` (0 axioms / 0 sorries):
  - `legendre_for_two_native` — the problem.md statement, via the Mathlib lemma.
  - `binDigitSum` — recursive binary digit sum (structural `0/succ` split on `n/2`,
    so its equation lemmas unfold one step without looping, unlike the parent's
    `if`-based `digitSum`).
  - `binDigitSum_eq_digits_sum` — strong induction + `Nat.digits_def'` proves it
    equals `(Nat.digits 2 n).sum`.
  - `legendre_for_two` — `padicValNat 2 n! = n - binDigitSum n`.

### Key Findings
- problem.md "approach 3" (already in Mathlib) was correct; no induction needed for the core.
- Parent `Erdos729Problem.lean` proves `legendre_for_two` only by forwarding to
  `axiom legendre_identity`. That axiom is now unnecessary.
- Name-checked all lemmas against the pinned v4.26 sibling (`~/GitHub/mathlib4`):
  `sub_one_mul_padicValNat_factorial`, `Nat.digits_def'` (sig `1<b`, `0<n`),
  `Nat.div_lt_self (Nat.succ_pos _) h` (verbatim `decreasing_by` from Digits/Defs.lean:54),
  `induction … using Nat.strong_induction_on with | _ n ih` (Order/Fin/Basic.lean:414),
  `List.sum_cons`.

### Blackout
- Docker build hung (exit124); Aristotle MCP returned 404. Shipped build-pending,
  name-checked. No build verification was possible this session.

### Files Modified
- `proofs/Proofs/Erdos729OQ04.lean` (new, unregistered)
- `src/data/research/problems/erdos-729-oq-02.json` (knowledge)

### Next Steps
- Docker-gated: retire `legendre_identity` directly in registered `Erdos729Problem.lean`
  (4 axioms → 3) and sync `src/data/proofs/erdos-729/meta.json` in the SAME PR. The parent
  `digitSum` is `if`-based, so unfold one step with `digitSum.eq_def` (not `simp only`,
  which loops) — or rewrite the def structurally as `binDigitSum` here.
