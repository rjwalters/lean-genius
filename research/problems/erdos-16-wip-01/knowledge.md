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

## Session note (2026-07-20, researcher-1, session 4): covering-congruence obstruction mechanism

Instead of adding more A006285 terms (enumeration theater — the per-`k` refutation
technique was already at 4 terms), this session formalized the **structural mechanism**
behind Erdős's 1950 covering-congruence argument. 5 new axiom-free theorems
(host-verified, Lean v4.31.0, `#print axioms` = propext/Classical.choice/Quot.sound):

- **`two_pow_mod_three`** — `2^k % 3 = if k % 2 = 0 then 1 else 2` (order of 2 mod 3
  is 2). The smallest gear; proved by induction with an omega-driven parity split.
- **`two_pow_modEq_of_dvd`** — the algebraic core: `2^d ≡ 1 [MOD p]` ∧ `d ∣ (k−r)`
  (with `r ≤ k`) ⟹ `2^k ≡ 2^r [MOD p]`. Proof writes `k = r + d·t` and uses
  `(2^d)^t ≡ 1^t`. This is exponent-periodicity of 2 mod p — the fact that lets one
  prime cover an entire residue class of exponents.
- **`covering_prime_not_prime_sub`** — the general obstruction gear: given a prime
  `p` with `2^d ≡ 1 [MOD p]`, an exponent `k ≡ r (mod d)`, and `n ≡ 2^r (mod p)`,
  then `p ∣ n − 2^k`; hence `n − 2^k` is **composite** whenever `p < n − 2^k`.
  This is exactly the step that eliminates one whole residue class of exponents in
  Erdős's construction (vs. the earlier one-`k`-at-a-time A006285 checks).
- **`not_prime_sub_even_mod_three`** — concrete gear (prime 3, order 2): for
  `n ≡ 1 (mod 3)`, every even exponent `k` with `n − 2^k > 3` gives a composite
  complement. So no even exponent witnesses a Romanoff representation of such `n`.
- **`not_prime_sub_mod_seven`** — concrete gear (prime 7, order 3): for
  `n ≡ 1 (mod 7)`, every exponent `k ≡ 0 (mod 3)` with `n − 2^k > 7` gives a
  composite complement. A second, different prime — the mechanism is general.

Meta synced: theoremCount 23→28, lineCount 395→479. **Remaining deep step** (still
documented-only): CRT-assemble the individual gears over a full covering system of
the exponent (moduli 2,3,4,6,8,12,24 with primes whose order of 2 matches) to force
an infinite arithmetic progression of `n` into the exceptional set — this would
formalize Erdős 1950 itself. It needs the order-of-2 facts for primes 5,13,17,241
plus a CRT packaging, but **no analytic number theory** — a tractable (if sizable)
future BUILD. Romanoff 1934 density and Chen 2023 disproof remain analytic/deep.

## Session note (2026-07-20, researcher-1, session 5): CRT assembly of the covering obstruction

Built on the session-4 gears. The remaining "deep step" flagged in session 4 (CRT-assemble
the gears over a full covering system) is now formalized as a conditional but unconditional-
mechanism theorem. 8 new axiom-free theorems (host-verified, Lean v4.31.0, `#print axioms`
= propext/Classical.choice/Quot.sound):

- **Four order-of-2 gears** — `two_pow_four_modEq_five` (2⁴≡1 mod 5),
  `two_pow_eight_modEq_seventeen` (2⁸≡1 mod 17), `two_pow_twelve_modEq_thirteen`
  (2¹²≡1 mod 13), `two_pow_twentyfour_modEq_241` (2²⁴≡1 mod 241). These are the primes
  closing the four exponent classes k≡1 mod 4, k≡3 mod 8, k≡7 mod 12, k≡23 mod 24
  (the p=3, p=7 gears already existed as `two_pow_two/three_modEq_*`, added here too).
  Small ones by `decide`; 2¹² and 2²⁴ by `norm_num [Nat.ModEq]` (kernel `decide` on 2²⁴
  = 16777216 is heavy).

- **`covering_obstruction_not_isRomanoff`** — the crown jewel. Any `n` satisfying the six
  CRT congruences `n≡1 (3), 1 (7), 2 (5), 8 (17), 11 (13), 121 (241)` AND the size condition
  `n − 2^k > 241` for every `k≥1` with `2^k < n` is **not Romanoff**. Proof: `isRomanoff_iff`
  reduces to a witness exponent `k`; `omega` shows `k` lands in one of the six covering classes
  `{0 mod 2, 0 mod 3, 1 mod 4, 3 mod 8, 7 mod 12, 23 mod 24}` (a covering system of ℤ); the
  attached prime `p` (order of 2 = the modulus) divides `n − 2^k` via `covering_prime_not_prime_sub`,
  and the size hypothesis (`p ≤ 241 < n − 2^k`) makes the complement composite. This is Erdős's
  1950 construction in full — every exponent killed by a single fixed prime — so the **entire**
  CRT progression `n ≡ a (mod 3·5·7·13·17·241)` meeting the size condition is exceptional.

- **`covering_progression_mem_exceptionalSet`** — membership form: odd `n` with the six
  congruences + size condition ⟹ `n ∈ ExceptionalSet`.

The n-residue per class is `2^r mod p` (r = the class residue): 2⁰=1 (p=3,7), 2¹=2 (p=5),
2³=8 (p=17), 2⁷=128≡11 (p=13), 2²³≡121 (p=241). Verified 2²³ mod 241 = 121 (and 2·121=242≡1).

Meta synced: theoremCount 28→36, lineCount 479→582. **Remaining documented-only** (genuinely
analytic, not a covering gap anymore): the wrapper showing infinitely many progression members
satisfy the size hypothesis `n − 2^k > 241` — i.e. Erdős's actual infinite-AP conclusion needs
that near the top exponent `2^k` never lands within 241 of `n`, which the covering alone does not
force. Romanoff 1934 density and Chen 2023 disproof remain analytic/deep.
