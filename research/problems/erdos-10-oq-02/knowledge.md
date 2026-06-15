# erdos-10-oq-02 — Granville–Soundararajan (k = 3 for odd integers)

**Parent:** Erdős Problem #10 — sums of a prime and powers of 2.
**Question (open):** Is the Granville–Soundararajan conjecture true, i.e. is every
odd integer `n > 1` a sum of a prime and **at most 3** powers of 2?

  `n = p + 2^{a_1} + ... + 2^{a_j}`, `p` prime, `0 ≤ j ≤ 3`.   (GS-odd)

Companion even part: every even `n ≥ 2` needs at most 4 (GS-even). Both open
(Granville–Soundararajan 1998).

Status this session: **ORIENT** (build-free — Docker + Lean unavailable). No proof
attempted; the conjecture is open. Contribution = a precise combinatorial reduction
+ a reproducible numerical experiment that is honest about what small-N data can and
cannot show.

## Reduction lemma (the cleanest formalizable fact here)

For `m ∈ ℕ` and `k ∈ ℕ`:

  `m` is a sum of **at most `k`** powers of 2 (multiset of exponents of size ≤ k,
  repetitions allowed)  **⟺**  `popcount(m) ≤ k`.

- (⟸) `popcount(m) = t ≤ k` ⟹ `m` is the sum of its `t` distinct set bits.
- (⟹) `2^a + 2^a = 2^{a+1}` merges equal powers, only shrinking the multiset;
  iterate to ≤ k **distinct** powers, so `popcount(m) ≤ k`.

Hence, with `S_k = { n : n = p + (≤ k powers of 2), p prime }`,

  `n ∈ S_k  ⟺  ∃ m ≥ 0, popcount(m) ≤ k, n − m ≥ 2, (n − m) prime`.   (*)

`(*)` turns membership and the *minimal number of powers* into a cheap finite
search (offsets `m` with `popcount ≤ k` number only `~ C(b,≤k) ~ b^k/k!`,
`b = #bits(n)`). This is the natural target for a future ACT (Lean) iteration:
it is elementary, self-contained, and converts the existing `sumPrimeAndTwoPows`
definition into a decidable predicate.

## Numerical evidence (verify_granville_soundararajan_odd.py)

Verified with `N = 10^6` (odd and even), plus a separate odd `S_2` sweep to
`3·10^6`. All reproducible with stdlib + sympy.

**E1 — odd side (GS-odd).** Every odd `n ∈ [3, 10^6]` is in `S_3`. Minimal-#powers
distribution: 0→15.70%, 1→78.71%, 2→5.59%, **3→0.00%**. I.e. ≤ 2 powers always
suffice in range; up to `3·10^6` *no* odd `n` even leaves `S_2`.

  ⚠️ **Honest caveat.** A direct odd sweep therefore confirms GS-odd only
  *trivially* — it never exercises the third power. The conjecture is stated with
  `k = 3` (not `k = 2`) because of **Crocker (1971)**: there are infinitely many
  odd `n ∉ S_2`. But Crocker's witnesses come from covering systems and are
  astronomically large, far beyond brute force. So small-N data is genuine but
  **weak** evidence for GS-odd.

**E2 — even side (where `S_3` is genuinely exercised).** Every even `n ∈ [2, 10^6]`
is in `S_3`. Distribution: 0→0.00%, 1→15.70%, 2→78.71%, **3→5.59%**. The third
power is genuinely required for ~5.6% of even `n`; the **smallest even `n` needing
exactly 3 powers is `906`**. No even `n ≤ 10^6` needs more than 3.

**E3 — Grechuk's counterexample.** `1117175146` (even, popcount 16) is **not** in
`S_3` but **is** in `S_4` — confirming both Grechuk's observation (`k = 3` fails on
the even side) and the even part of GS (`k = 4` suffices there in this instance).
It is the first known even failure of `S_3`, well beyond the `10^6` sweep.

## Parity structure (the heart of the conjecture)

The odd/even split is the +1-power offset, visible directly in the data:
in range, **odd** `n` need at most **2** powers, **even** `n` need at most **3** —
exactly the `k = 3` (odd) vs `k = 4` (even) gap GS conjectures. Mechanism: for odd
`n`, subtracting one even power `2^a` (`a ≥ 1`) leaves an odd number `n − 2^a`,
which has a Goldbach/Romanoff-dense chance of being prime; even `n` must spend an
extra power to fix parity before the prime can be odd.

## Next steps

1. **ACT (Lean, Docker-gated):** formalize the reduction lemma `(*)` and turn
   `sumPrimeAndTwoPows`/`IsPrimePlusKPowers` (already in `Erdos10Problem.lean` /
   `Erdos10OQ01.lean`) into a `Decidable` membership via `popcount`; discharge the
   `906`/Grechuk witnesses by `decide`/`native_decide`.
2. Cite Crocker (1971) in the gallery as the reason `k = 3` (not 2) for odd —
   the gallery currently lists it only obliquely.
3. The conjecture itself is open and needs sieve/large-sieve machinery (Gallagher
   line); not within brute-force or near-term Lean reach.

## References

- Granville, A.; Soundararajan, K. (1998). *A binary additive problem of Erdős and
  the order of `2 mod p²`.* Ramanujan J. 2, 283–298.
- Crocker, R. (1971). *On the sum of a prime and of two powers of two.* Pacific J.
  Math. 36, 103–107. (Infinitely many odd `n ∉ S_2`.)
- Gallagher, P.X. (1975). *Primes and powers of 2.* Invent. Math. 29, 125–142.
- Erdős, P.; Graham, R. (1980). *Old and New Problems and Results in Combinatorial
  Number Theory.*
