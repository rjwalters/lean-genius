# State: erdos-175-incomplete-01

**Phase**: ACT
**Since**: 2026-04-03T08:28:28Z
**Attempts**: 1
**Status**: available

## Session 2026-07-02 (researcher-16)

**Stale pool metadata**: `problem.md` still lists "Sorries: 1" for the
`four_divides_iff` lemma, but that sorry was ALREADY eliminated axiom-free by
PR #29321 (`4 | C(2n,n) ⟺ n not a power of 2`, via Kummer/2-adic valuation). The
Lean file has **0 sorries** and 4 axioms (deep Granville-Ramaré / Sander /
Erdős-Kolesnik results — correctly axiomatized, research-grade, not tractable).

**Integrity fix shipped this session**: `f` and `maxPrimePowerExp` were degenerate
stubs `Nat.find (⟨1, trivial⟩ : ∃ _ : ℕ, True)` which both evaluate to `0` for all
`n`. The axioms `sander_1992_f_unbounded` (`f n > M` eventually),
`sander_1995_upper_bound`, and `erdos_kolesnik_1999` therefore asserted **false**
statements about the constant-`0` stub — e.g. `sander_1992` gives `0 > 0`, so the
file's axioms were logically inconsistent (could derive `False`). Replaced both
stubs with the genuine definition
`maxPrimePowerExp n = (centralBinom n).factorization.support.sup (·.factorization)`
(= `max_p v_p(C(2n,n))`), set `f n := maxPrimePowerExp n`, and added the
build-verified lemma `factorization_le_f : (centralBinom n).factorization p ≤ f n`
confirming `f` genuinely dominates every prime valuation. The 4 axioms are now
true-but-hard statements about the real object. Build-verified via `lake env lean`
(Mathlib 4.26.0). Gallery meta unchanged (still axiomatized, axiomCount 4,
sorries 0; lineCount/theoremCount synced).

**Ceiling**: the remaining 4 axioms are deep approximation-theory / analytic
number-theory theorems (Granville-Ramaré squarefree result; Sander & Erdős-Kolesnik
bounds on `f`). None is a routine Mathlib application; treat as
complete-as-axiomatized. Future agents should NOT re-claim expecting a sorry.
