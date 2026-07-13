# Knowledge Base: lucas-lehmer-test-oq-01

The Lucas–Lehmer primality test for Mersenne numbers, packaged as a biconditional
with worked prime and composite witnesses.

---

## Problem Understanding

For `3 ≤ p`, the Mersenne number `M_p = 2^p − 1` is prime **iff** the
Lucas–Lehmer test passes:

    s₀ = 4,   s_{i+1} = s_i² − 2,   M_p prime ⟺ s_{p-2} ≡ 0 (mod M_p).

Mathlib supplies the two implications separately (`lucas_lehmer_sufficiency`,
`1 < p`; `lucas_lehmer_necessity`, `3 ≤ p`) plus a `norm_num` extension
`evalLucasLehmerTest` that decides `LucasLehmerTest p`. It does NOT bundle the
biconditional nor record worked instances.

---

## Insights

- The deciding `norm_num` extension `evalLucasLehmerTest` works by **kernel
  reduction** of the tail-recursive residue `sModNatTR` and closes via `rfl`
  (`testTrueHelper`/`testFalseHelper`). This means it is foundational-axiom-only:
  NO `native_decide`, hence NO `Lean.ofReduceBool`. The entry is genuinely
  0-axiom (`propext`/`Classical.choice`/`Quot.sound` only).
- The Mathlib docstring states the extension proves up to `2^4423 − 1`
  "nearly instantly", so `M₅, M₇, M₁₃, M₁₇` are trivial for the kernel.
- The biconditional is assembled under the stronger hypothesis `3 ≤ p`:
  necessity gives `→` directly, sufficiency gives `←` after `omega` weakens
  `3 ≤ p` to `1 < p`.
- A failing test (`p = 11`) certifies compositeness via the SAME biconditional
  rewritten in the `¬` direction; confirmed by the explicit `M₁₁ = 2047 = 23·89`.

---

## Mathlib Gaps

- Mathlib has both directions and the decision procedure but NOT the packaged
  biconditional `(mersenne p).Prime ↔ LucasLehmerTest p` and NOT any worked
  prime/composite witnesses. These are the original content here.

---

## Outcome

COMPLETED — `proofs/Proofs/LucasLehmerTestOQ01.lean`, 11 theorems, 0
definitions, 0 sorries, 0 axioms (foundational only; no `native_decide`,
no `Lean.ofReduceBool`). Status verified / badge mathlib (the two implications
and the decision procedure are Mathlib's; the biconditional packaging + worked
witnesses are new). Registered in `Proofs.lean`.

Content: recurrence `s_zero`/`s_succ`/`s_one`/`s_two`/`s_three`,
`lucasLehmerTest_iff_residue`, the keystone
`mersenne_prime_iff_lucasLehmerTest`, prime witnesses `M₅/M₇/M₁₃/M₁₇`, and the
composite witness `p = 11` (`lucasLehmerTest_eleven_false`,
`mersenne_eleven_not_prime`, `mersenne_eleven_factorization`).

---

## Follow-Ups

- Seed-independence: same verdict from `s₀ = 10`; characterize admissible seeds.
- Connect to the gallery's Euclid–Euler perfect-number characterization (every
  even perfect number arises from a Mersenne prime certified by this test).

---

## Dead Ends

None — the biconditional assembly and the norm_num witnesses went through
cleanly on the first structured attempt.

---

## Session 2026-06-20 (Session 1) — FRESH, claim & ship

**Mode**: FRESH
**Outcome**: completed (pending Docker build confirmation at write time)

### What I Did
- Claimed `lucas-lehmer-test-oq-01` (atomic lock), branched
  `research/lucas-lehmer-test-oq-01` off `origin/main`.
- Inspected `Mathlib/NumberTheory/LucasLehmer.lean`: confirmed
  `lucas_lehmer_sufficiency`/`necessity` spellings, the `s` recurrence, and that
  `evalLucasLehmerTest` uses kernel reduction (0-axiom).
- Wrote `LucasLehmerTestOQ01.lean` (11 theorems), registered in `Proofs.lean`,
  authored `meta.json` + `annotations.json`.

### Key Findings
- `evalLucasLehmerTest` is `rfl`-backed kernel reduction → axiom-free; use
  `norm_num` (NOT `native_decide`).
- Biconditional needs `3 ≤ p` + `omega` to feed sufficiency's `1 < p`.

### Files Modified
- `proofs/Proofs/LucasLehmerTestOQ01.lean`, `proofs/Proofs.lean`
- `src/data/proofs/lucas-lehmer-test-oq-01/{meta,annotations}.json`

### Next Steps
- On green build: commit, open PR to `main` (no `loom:review-requested`).
