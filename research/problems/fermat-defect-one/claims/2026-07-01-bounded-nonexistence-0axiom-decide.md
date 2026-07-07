# Claim: 0-axiom (`decide`) bounded non-existence for n = 4, 5 — researcher-2, 2026-07-01

## Summary

Drafted `proofs/Proofs/FermatDefectOneBounded.lean` (branch
`research/fermat-defect-bounded`, commit `b2cc2bff352`, pushed to origin, **no
PR**). It proves, by kernel `decide` (0-axiom — **no** `native_decide`, no
`Lean.ofReduceBool`), that no primitive Fermat defect-one witness exists at
exponent 4 or 5 with `c < 20`, either sign:

- `no_defect_witness_n4_below_20 : ∀ a b c, c < 20 → ¬ FermatDefectWitness 4 a b c`
- `no_defect_witness_n5_below_20 : ∀ a b c, c < 20 → ¬ FermatDefectWitness 5 a b c`
- plus decidable kernels `defect_n{4,5}_below_20_kernel` and the combined
  `no_defect_witness_n4_n5_below_20`.

This directly targets the gallery's named research target
`no_witness_n_eq_4_below_20`.

## Status: UNVERIFIED (build infra failure)

The file was **never compiled**. Build attempt on 2026-07-01 crashed Docker
Desktop: with 6 concurrent `lean-build` containers racing the shared cache
volume, the host disk fell from ~1.6 GB to **119 MB free** while building Mathlib
(reached module 7274/7744 — never reached `FermatDefectOne.lean` or my file),
triggering "Docker Desktop is unable to start". A `.trace` cache-corruption
warning ("unexpected end of input") also appeared mid-build — the concurrent
`.lake` race documented across researcher memories. Aborted to protect the host;
freed disk by removing the worktree (work preserved on origin).

The math is Python-confirmed: **no** defect-one solution (even without the gcd
filter) for n = 4 or n = 5 with c ≤ 60; none for n = 4 with c < 300. The Lean is
a routine `decide` over `Nat.decidableBallLT`/`decidableBallLE` bounded
quantifiers at bound 20, so it is very likely to compile — but this must be
confirmed on working infra before any "verified" claim.

## Value assessment: MARGINAL / duplicative — decide before shipping

`FermatDefectOneOQ04.lean` **already** proves the strictly stronger bounded
result `no_small_witness_{4,5,6}` for `c ≤ 100`, both signs, via `native_decide`.
So the *mathematical content* here is fully subsumed. The **only** delta is
verification purity: my `c < 20` slice is axiom-free (`decide`) whereas OQ04
relies on `Lean.ofReduceBool` (`native_decide`).

- Kernel `decide` cannot scale to OQ04's `c ≤ 100` (170k+ triples with 4th–6th
  powers) — that is exactly why OQ04 used `native_decide`. `c < 20` (~1.3k
  triples) is the realistic ceiling for a 0-axiom certificate.
- This delta does **not** change the entry's `axiomatized` status (headline
  `sorry` + native_decide n=3 benchmarks remain), so practical gallery value is
  low.

Recommendation for a future session with healthy infra: build the branch; if it
compiles, it is a legitimate (if small) verification-quality improvement closing
the named `no_witness_n_eq_4_below_20` target axiom-free — worth a small PR then.
If not deemed worth the churn, drop it. Do **not** ship unverified.

## Infra note

Building from a fresh `$HOME` worktree tries to *clone* Mathlib (worktree lacks
`.lake/packages/mathlib`); build from the main checkout which has packages +
partial olean volume. Even so, this branch's Mathlib toolchain required
rebuilding ~500+ modules from source against a partial cache volume, which is
what exhausted the disk under concurrency. Retry only when
`docker ps | grep -c lean-build` is low AND `df` shows several GB free.
