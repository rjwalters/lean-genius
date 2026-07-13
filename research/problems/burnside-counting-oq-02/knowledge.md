# Knowledge Base: burnside-counting-oq-02

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

## Session 2026-07-10 (researcher-1) — BUILD REPAIR: BurnsideCounting.lean broken by Mathlib drift

Entry marked phase=COMPLETE (since April) with empty knowledge.md. Verifying the primary
`BurnsideCounting.lean` (671 L, Mathlib-only, claimed 0-axiom/0-sorry) via lean-elab
([[reference-docker-down-lean-elab-verification-path]]) found it **does NOT build** against the
current pin — 4 Mathlib-drift errors (the file had not been rebuilt since a Mathlib bump; the
Fermat-little-via-Burnside block `necklaces_prime_length_mul`/`prime_dvd_pow_sub_self` was
apparently added and never compiled):

1. `627 failed to synthesize NeZero p` — `coloringSetoid`/`coloringQuotientFintype` require
   `[NeZero n]`, but `necklaces_prime_length_mul`'s STATEMENT (return type) lacked it (the
   `haveI : NeZero p` was only in the proof body, too late for the type). FIX: add `[NeZero p]`
   to the theorem binders; add `haveI : NeZero p := ⟨hp.pos.ne'⟩` in the caller
   `prime_dvd_pow_sub_self` before the call.
2. `639 zero_vadd c` type mismatch — ★Mathlib changed `zero_vadd` to take the MONOID `M` as its
   FIRST EXPLICIT arg: `zero_vadd (M) {α} [AddMonoid M] [AddAction M α] (b) : 0 +ᵥ b = b`. So
   `zero_vadd c` put `c` in the `M`-slot. FIX: `zero_vadd (ZMod p) c`.
3. `670 Nat.dvd_sub'` unknown — removed in v4.26. FIX: `Nat.dvd_sub'` → `Nat.dvd_sub` (same
   truncated-subtraction signature `k∣m → k∣n → k∣m-n`).
(the `668 uses sorry` warning was a cascade from #1, cleared once the statement type fixed.)

Re-elaborated: whole file EXIT 0, 0 errors (3 benign pre-existing unused-simp-arg warnings).
`#print axioms necklaces_prime_length_mul` / `prime_dvd_pow_sub_self` = [propext,
Classical.choice, Quot.sound] — genuinely 0-axiom/0-sorry. The 4-necklace Polya deliverable +
the Burnside proof of Fermat's little theorem (`prime_dvd_pow_sub_self : p ∣ kᵖ − k`) now build.

★LESSON: gallery entries marked "COMPLETE" months ago can be SILENTLY BROKEN by Mathlib bumps
(build not re-run). Verifying them via lean-elab is high-value. ★zero_vadd/one_smul-family now
take the acting monoid as an explicit first arg.
