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

## Session 2 (2026-06-15) — sharpening the parity caps (build-free)

Session 1 noted the +1 offset (odd ≤ 2, even ≤ 3 in range) but framed the odd side
as *only trivially* in `S_3` and did not check whether **2 powers is ever necessary**
on odds. `verify_min_powers_parity.py` (pure stdlib, exact sieve, `N = 10^6`) settles
this and quantifies the offset across the *whole* distribution.

**P1 — the odd cap is genuinely 2, first attained at 905.** The smallest odd `n`
with `minPowers(n) = 2` is **905 = 5·181**, a *de Polignac number* (odd, composite,
and not of the form `2^a + prime`). So `S_2` is **not** trivial on odds: there exist
odd `n ∉ S_1`. Every odd `n ≤ 10^6` (and `≤ 3·10^6`, S1) has `minPowers ≤ 2`.

**P2 — 905 and 906 are consecutive.** Smallest odd needing 2 powers = **905**;
smallest even needing 3 powers = **906** (S1). The smallest forcing value for each
parity sits back-to-back — a clean illustration of the +1 offset at the extreme.

**P3 — the offset holds across the entire distribution (approximately).** The even
`minPowers` distribution is the odd one shifted up by exactly 1, matching to within
~0.02%:

| k        | 0      | 1      | 2      | 3     |
|----------|--------|--------|--------|-------|
| odd  [k] | 78497  | 393538 | 27964  | 0     |
| even [k] | 1      | 78511  | 393529 | 27959 |

so `even[k] ≈ odd[k−1]` (diffs `+14, −9, −5`). **Mechanism (honest, not an exact
identity):** `minPowers(2j) ≤ 1 + minPowers(2j−1)` — an even `n` spends one `2^0`
to repair parity and is left with the odd subproblem on `n−1`. Equality holds
*usually*; the small deviations come from even `n` that reach the prime `2` directly
via the even offset `m = n−2`, occasionally beating the +1 route.

**P4 — reading of GS.** The conjectured caps `3` (odd) / `4` (even) are exactly the
in-range caps `2` / `3` **plus one**. The extra power is a safety margin beyond what
is forced for `n ≤ 10^6`; the cases that actually force it (Crocker odd `∉ S_2`,
Grechuk even `1117175146 ∉ S_3`) live far beyond brute force. This is consistent with
GS but, as in S1, only weak evidence for it.

**Files (S2):** `research/problems/erdos-10-oq-02/verify_min_powers_parity.py` (new).

## Session 4 (2026-06-15) — the decidability keystone (build-pending Lean)

S3 (`Erdos10OQ02.lean`, PR #24287) proved the **reduction lemma**
`RepWithAtMost k n ↔ RepDistinct k n` (≤ k powers ⟺ ≤ k *distinct* powers, via
the `2^a + 2^a = 2^{a+1}` merge). That collapses repeats but leaves exponents
unbounded, so it does **not** yet make membership a finite search. S4 supplies
the missing finiteness ingredient and bounds the prime side.

**New file** `proofs/Proofs/Erdos10OQ02Decidable.lean` (build-pending,
UNREGISTERED — Docker + Aristotle down). All proofs elementary `Multiset`
algebra + the S3 lemmas; verified on paper, validated numerically (below).

- **K1 — exponent bound.** `lt_two_pow_self : a < 2^a` (self-contained
  induction, no binary API) ⟹ `exp_lt_of_powSum : a ∈ s → powSum s = n → a < n`
  (each summand `2^a ≤ powSum s` via `Multiset.single_le_sum`). The one fact S3
  lacked.
- **K2 — bounded reduction lemma.**
  `repWithAtMost_iff_repBoundedDistinct : RepWithAtMost k n ↔ RepBoundedDistinct k n`
  where `RepBoundedDistinct k n := ∃ s, s.Nodup ∧ s.card ≤ k ∧ (∀ a ∈ s, a ≤ n)
  ∧ powSum s = n`. Exponents now live in `{0,…,n}`, at most `k` of them ⟹ only
  finitely many candidate multisets ⟹ membership is decidable in principle.
- **K3 — prime-side bound.** `isPrimePlusKPowers_bounded`: the prime is `p ≤ n`,
  the power-part `n − p`; `isPrimePlusKPowers_iff_bounded_distinct` combines both
  bounds into a finite two-sided search — the predicate a `decide`/`native_decide`
  membership check enumerates.

**Remaining mechanical step** (next build session): the explicit
`Decidable (RepWithAtMost k n)` instance via a `Finset.range (n+1)` powerset
encoding (`Multiset.toFinset` bridge), after which `906 ∉ S_2`, `906 ∈ S_3`, and
Grechuk `1117175146 ∉ S_3` close by `native_decide`. The file documents this
encoding precisely.

**Numerical cert** `verify_decidable_membership.py` (new, exact arithmetic,
PASS): C1 `a < 2^a` and `2^a ≤ n ⟹ a < n`; C2 `RepWithAtMost k n ⟺
bounded-distinct ⟺ popcount n ≤ k` (n ≤ 200, k ≤ 5, vs naive multiset search);
C3 `IsPrimePlusKPowers` bounded form ⟺ naive form (n < 400, k < 4), and it
reproduces the parity caps (905/906 consecutive; all odd n < 2000 in `S_2`, all
even in `S_3`) plus the Grechuk witness (`1117175146 ∉ S_3`, `∈ S_4`).

## References

- Granville, A.; Soundararajan, K. (1998). *A binary additive problem of Erdős and
  the order of `2 mod p²`.* Ramanujan J. 2, 283–298.
- Crocker, R. (1971). *On the sum of a prime and of two powers of two.* Pacific J.
  Math. 36, 103–107. (Infinitely many odd `n ∉ S_2`.)
- Gallagher, P.X. (1975). *Primes and powers of 2.* Invent. Math. 29, 125–142.
- Erdős, P.; Graham, R. (1980). *Old and New Problems and Results in Combinatorial
  Number Theory.*
