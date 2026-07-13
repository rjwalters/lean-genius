# erdos-729-oq-02 — Session (researcher-3, 2026-07-08)

## Result: honest UNIFORM real-log Erdős 1968 bound, axiom-free

Added to the verified companion `Erdos729DigitSumBound.lean` (0 axioms / 0 sorries):

- `natLog_two_mul_log_two_le_log` — `(⌊log₂ n⌋ : ℝ)·log 2 ≤ log n` (Real-log form
  of `2^⌊log₂ n⌋ ≤ n`).
- `erdos_1968_uniform` —
  `∃ C = 4/log 2 > 0, ∀ n ≥ 2, ∀ a b, a!·b! ∣ n! → (a+b:ℝ) ≤ n + C·log n`.

## Why this matters: the parent axiom is defective
The parent `Erdos729Problem.lean` carries the classical bound only via the axiom
`erdos_1968_classical : ∀ n a b, a!b! ∣ n! → ∃ C>0, (a+b:ℝ) ≤ n + C·log n`.
That axiom is wrong on two counts:
1. **Unsound at n ∈ {0,1}.** `Real.log 0 = Real.log 1 = 0`, so the bound reads
   `a+b ≤ n`. But `n=0, a=b=1`: `1!·1! = 1 ∣ 1 = 0!` holds while `a+b = 2 ≤ 0`
   is false. So the axiom (and `erdos_729_statement`'s first conjunct) is false.
2. **Vacuous for n ≥ 2.** With `∃C` INSIDE the `∀`, pick `C = (a+b)/log n`; the
   inequality becomes `a+b ≤ n + (a+b)`, trivially true and independent of the
   divisibility. It does not express Erdős's content.

The meaningful statement puts a **single uniform C outside the quantifiers**.
`erdos_1968_uniform` proves exactly that, axiom-free, with explicit `C = 4/log 2`
for `n ≥ 2`.

## Proof
From the elementary `erdos_two_adic_bound_log` (a+b ≤ n + ⌊log₂ a⌋ + ⌊log₂ b⌋ + 2
for a,b ≥ 1) plus `a,b ≤ n` (since a!∣a!b!∣n! ⟹ a!≤n! ⟹ a≤n via `Nat.factorial_lt`)
one gets `a+b ≤ n + 2⌊log₂ n⌋ + 2` in ℕ. Bridge to reals with
`natLog_two_mul_log_two_le_log`: `⌊log₂ n⌋ ≤ log n / log 2 =: L`, and for n ≥ 2,
`L ≥ 1`, so `2⌊log₂ n⌋ + 2 ≤ 2L + 2L = 4L = (4/log 2)·log n`. Cases a=0 / b=0
handled directly (`a+b ≤ n`).

## Verification
Host `lake env lean Proofs/Erdos729DigitSumBound.lean` → EXIT 0.
`#print axioms erdos_1968_uniform` / `natLog_two_mul_log_two_le_log`
→ [propext, Classical.choice, Quot.sound]. 0 axioms / 0 sorries / no native_decide.

## Remaining
- Main file still declares the defective `erdos_1968_classical` (axiomCount 3).
  Recommend a follow-up/auditor pass to restrict it to `2 ≤ n` and back it by
  `erdos_1968_uniform` (or import companion + delete → axiomCount 3→2). Left
  untouched here to avoid destabilising the merged gallery entry.
- The two `barreto_leeham_*` axioms (mod-small-primes resolution) are deep
  research inputs, not Mathlib-eliminable.
