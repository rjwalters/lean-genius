# Knowledge Base: erdos-16-wip-01

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

## Session note (2026-07-20, researcher-1): 13 axiom-free foundational lemmas

`Erdos16Problem.lean` was a definitions-only stub (10 defs, 0 theorems; meta prose
was already honest about this). Added 13 axiom-free foundational lemmas about its
own definitions (host-verified, Lean v4.31.0, Mathlib-only, no Docker; `#print axioms`
= propext/Classical.choice/Quot.sound):

- `isRomanoff_four_le` — Romanoff floor `2^k+p ≥ 4` (k≥1 ⟹ 2^k≥2, p prime ⟹ p≥2).
- `not_isRomanoff_one/three`, `one/three_mem_exceptionalSet` — small odd numbers are exceptional.
- `isRomanoff_five` (5=2+3), `isRomanoff_seven` (7=4+3), `five_not_mem_exceptionalSet`.
- `mem_exceptionalSet_iff`, `density_nonneg`, `density_le_one` (density range 0..1).
- `erdosCovering_moduli_pos`, **`erdosCovering_isCoveringSystem`** — the explicit Erdős
  covering `{0 mod 2, 0 mod 3, 1 mod 4, 1 mod 6, 3 mod 8, 7 mod 12, 23 mod 24}` genuinely
  covers ℤ. Proof: every modulus divides 24, so the covering disjunction is provable
  directly by `omega`; then the residue-class witness is exhibited per `rcases` branch.

Deep results (Romanoff 1934 positive density, Erdős 1950 covering-progression, Chen 2023
disproof) remain documented-only — they need analytic number theory absent from Mathlib.
Meta counts synced (theoremCount 0 → 13, lineCount 203 → 290).

## Session note (2026-07-20, researcher-1, session 2): isRomanoff_iff + 127/149 exceptional

Built on the 13 foundational lemmas already merged. Added 5 axiom-free theorems
(host-verified, Lean v4.31.0, `#print axioms` = propext/Classical.choice/Quot.sound):

- **`isRomanoff_iff`** — `IsRomanoff n ↔ ∃ k, 1 ≤ k ∧ 2^k < n ∧ Nat.Prime (n − 2^k)`.
  Eliminates the prime variable `p` (forced to `n − 2^k`) and bounds the search
  (`2^k < n ⟹ k ≤ log₂ n`), turning membership into a finite per-exponent check.
- **`not_isRomanoff_127` / `oneHundredTwentySeven_mem_exceptionalSet`** — the first
  nontrivial OEIS A006285 term (the file previously only *asserted* "127 is in the
  exceptional set" in a comment). Proof: bound `k ≤ 6` via `by_contra` +
  `Nat.pow_le_pow_right`, then `interval_cases k <;> norm_num at hp` refutes
  `Prime (127 − 2^k)` for each `k` (125,123,119,111,95,63 all composite).
- **`not_isRomanoff_149` / `oneHundredFortyNine_mem_exceptionalSet`** — same technique,
  `k ≤ 7` (147,145,141,133,117,85,21 all composite).

Meta synced: theoremCount 13→18, lineCount 290→337. Deep results (Romanoff 1934
density, Erdős 1950 covering-progression, Chen 2023 disproof) remain documented-only.

## Session note (2026-07-20, researcher-1, session 3): Decidable instance + 251/331 exceptional

Built on the 18 merged theorems. Added 5 axiom-free theorems + 1 instance
(host-verified, Lean v4.31.0, `#print axioms` = propext/Classical.choice/Quot.sound):

- **`isRomanoff_iff_mem_range`** — refines `isRomanoff_iff` to a *bounded*
  existential `∃ k ∈ Finset.range n, 1 ≤ k ∧ 2^k < n ∧ Prime (n − 2^k)`. The
  bound `k < n` comes from `Nat.lt_two_pow_self` (`k < 2^k`) and `2^k < n`.
- **`decidableIsRomanoff`** — `instance : Decidable (IsRomanoff n)`, via
  `decidable_of_iff _ isRomanoff_iff_mem_range.symm`. Kernel reduction only (no
  `native_decide`), so axioms stay clean. `decide` settles small `n` directly
  (e.g. `IsRomanoff 5`). Practical caveat: naive `decide` over `Finset.range n`
  makes the kernel evaluate `2^{n-1}` (exponentiation-threshold / recursion-depth
  blow-up) for the A006285 terms >250, so those still use the explicit
  `interval_cases` refutation below (bounding `k ≤ log₂ n` keeps `2^k` small).
- **`not_isRomanoff_251` / `..._mem_exceptionalSet`** — 3rd nontrivial A006285
  term (`k ≤ 7`; 249=3·83, 247=13·19, 243=3⁵, 235=5·47, 219=3·73, 187=11·17,
  123=3·41 all composite).
- **`not_isRomanoff_331` / `..._mem_exceptionalSet`** — 4th term (`k ≤ 8`;
  329=7·47, 327=3·109, 323=17·19, 315=5·63, 299=13·23, 267=3·89, 203=7·29,
  75=3·25 all composite).

Meta synced: theoremCount 18→23, definitionCount 10→11, lineCount 337→395. Deep
results (Romanoff 1934, Erdős 1950 covering, Chen 2023) remain documented-only.
