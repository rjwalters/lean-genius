# chinese-remainder-constructive-oq-03-oq-02 — knowledge

## Status
VERIFIED (extended). The three-moduli core {2^n−1, 2^n, 2^n+1} was already
verified (0 sorry / 0 axiom; PR #30734, #30762). This session (researcher-1,
2026-06-28) extended the file with a four-moduli **parity dichotomy** — also
0 sorry / 0 axiom, foundational axioms only.

## Session 2026-06-28 (researcher-1): four-moduli parity dichotomy

SOLVED-strategy: the core was already done, so I looked outward. The "nextSteps"
flagged a 4-moduli extension. Working it out revealed a genuine sharp boundary.

### Result
The natural fourth (n+1)-bit modulus has two candidates, 2^(n+1)+1 and
2^(n+1)−1, and exactly one is admissible depending on the parity of n:

- **odd n**: {2^n−1, 2^n, 2^n+1, **2^(n+1)+1**} is pairwise coprime
  (`fourModuli_pairwise_coprime_odd`, `fourModuliBaseOdd`). The other candidate
  2^(n+1)−1 FAILS — `gcd(2^n+1, 2^(n+1)−1) = 3` (`not_coprime_high_extMersenne_odd`).
- **even n**: {2^n−1, 2^n, 2^n+1, **2^(n+1)−1**} is pairwise coprime
  (`fourModuli_pairwise_coprime_even`, `fourModuliBaseEven`). Now 2^(n+1)+1 FAILS —
  `gcd(2^n−1, 2^(n+1)+1) = 3` (`not_coprime_lowMersenne_extHigh_even`).
- Capstone `fourModuli_base_exists`: every n ≥ 2 admits SOME valid 4-channel base.

### Why it works (the math)
The only non-free pair is between an odd channel and the new odd modulus; their
gcd always divides 3 (the difference combination collapses to 3). Whether 3
actually divides depends on 2^n mod 3, which is governed entirely by parity:
- `two_pow_mod_three_of_odd`:  2^n ≡ 2 (mod 3) for odd n  ⟹ 3 ∤ 2^n−1, 3 ∣ 2^n+1.
- `two_pow_mod_three_of_even`: 2^n ≡ 1 (mod 3) for even n ⟹ 3 ∣ 2^n−1, 3 ∤ 2^n+1.
So 2^n+1 picks up the factor 3 for odd n and 2^n−1 for even n — and the matching
"+1 / −1" candidate is the one that dodges it.

### Lean gotchas hit
- `rw [hpow]` (hpow : 2^(n+1) = 2*2^n) rewrites the `2^(n+1)` INSIDE the gcd's
  second argument too, so a follow-up `hdl.mul_left 2` (still phrased with the
  original 2^(n+1)) type-mismatches. Fix: prove `d ∣ 2*2^n` first, then
  `rwa [← hpow] at this` to land on `d ∣ 2^(n+1)` without touching the gcd term.
- `two_pow_mod_three`: `((2:ℕ)^2) ≡ 1 [MOD 3] := by decide`, then `.pow m` and
  `simpa [Nat.ModEq]`; finish odd case via `pow_succ, pow_mul, Nat.mul_mod`.
- `Even.add_one : Even n → Odd (n+1)`, `Odd.add_one : Odd n → Even (n+1)`.
- `omega` closes `3 ∣ 2^n ± 1` directly from a `2^n % 3 = c` hypothesis.
- Coprime ⇒ gcd=1 used as `have hco' : Nat.gcd .. = 1 := hco` (defeq) before `rw`.

### Verification
`lake env lean Proofs/ChineseRemainderConstructiveOQ03OQ02.lean` — clean, no
errors/warnings. `#print axioms` on all new theorems = [propext, Classical.choice,
Quot.sound] only (no sorryAx, no Lean.ofReduceBool; small examples use kernel
`decide`, not `native_decide`). File now 540 lines, 42 theorems, 5 defs, 0 axioms.

### Possible follow-ups (left for Seeker; slug depth = 2, child depth 3 OK)
- 5-moduli extensions {2^n−1, 2^n, 2^n+1, 2^(n+1)±1, ?} and whether the
  coprimality obstruction is again pinned by small-prime residues of n.
- Exact closed-form dynamic range of the 4-moduli set
  (= (2^(3n)−2^n)·(2·2^n ± 1)).
