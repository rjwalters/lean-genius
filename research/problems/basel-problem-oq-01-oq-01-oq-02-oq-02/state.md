# Current State

**Phase**: ACT
**Since**: 2026-05-08
**Iteration**: 9

## Session 9 (this session, planning + tactical analysis)

Documentation-only iteration. No Lean changes; no sorry/axiom delta.
Work product: a sharper, **operational** plan for the S10 m=3 even-n
proof, correcting two pessimistic claims in S8's blockers list.

**Headline finding**: BOTH parity-of-`n/2` sub-cases admit a clean
**coprime decomposition** of `3 · C(n, 3)` into three pairwise-coprime
factors that each divide `lcmRange n`. The S8 blockers list incorrectly
suggests `n ≡ 2 mod 4` "probably needs Kummer"; in fact a different
factorization removes the obstacle.

### Concrete factorizations

Parametrize `n = 2 * m` (`m ≥ 2`). From Part 7
`two_mul_three_mul_choose_three_eq`, plus `n - 2 = 2 * (m - 1)`:

  `3 * C(2m, 3) = (2m) * (2m - 1) * (m - 1)`     — uniform identity (*)

Equivalently, by re-grouping `(2m) * (m - 1) = m * (2(m - 1)) = m * (2m - 2)`:

  `3 * C(2m, 3) = m * (2m - 1) * (2m - 2)`        — alternative identity (**)

Pairwise-coprime check on the three factors:

| sub-case | parity of `m` | factorization | gcd checks |
|---|---|---|---|
| `n ≡ 0 mod 4` | `m` even | (*) `(2m)(2m-1)(m-1)` | gcd(2m, 2m-1)=1; gcd(2m, m-1)=1 (since m-1 odd → gcd | 2 → gcd=1); gcd(2m-1, m-1)=1 (2m-1 = 2(m-1)+1) |
| `n ≡ 2 mod 4` | `m` odd | (**) `m(2m-1)(2m-2)` | gcd(m, 2m-1)=1 (≡ -1 mod m); gcd(m, 2m-2)=1 (gcd | 2; m odd); gcd(2m-1, 2m-2)=1 (consecutive) |

Each factor `≤ n` and `≥ 1` for `m ≥ 2`, so each divides `lcmRange n`
via Part 1 `dvd_lcmRange`. Two applications of
`Nat.Coprime.mul_dvd_of_dvd_of_dvd` (mirroring S8) then give
`3 · C(n, 3) ∣ lcmRange n`.

### Lean tactical notes for S10

1. **Helper algebraic identity**: prove `(*)` as a private helper
   `three_mul_choose_three_eq_of_double {m : ℕ} (hm : 2 ≤ m) :
   3 * Nat.choose (2 * m) 3 = (2 * m) * (2 * m - 1) * (m - 1)`. Proof:
   `two_mul_three_mul_choose_three_eq` (Part 7) plus `2m - 2 = 2(m-1)`
   plus `Nat.eq_of_mul_eq_mul_left`. ~10 lines.

2. **Avoid ℕ division**: parametrize via `m` rather than `n`. The
   sub-case proofs take `m : ℕ` with hypotheses `2 ≤ m` plus
   `Even m` / `Odd m`; the gallery callers convert `n = 2 * m` via
   `obtain ⟨m, rfl⟩ := h_n_even`.

3. **Coprime API hiccups** (m even sub-case): `gcd(2m, m-1) = 1` for
   `m` even is the trickiest gcd; the cleanest tactic is
   `Nat.Coprime.coprime_dvd_left` after establishing `gcd | 2` from
   `2m - 2(m-1) = 2`, combined with `m - 1` odd. Alternatively, use
   `obtain ⟨j, rfl⟩ := h_m_even` to expose `m = 2j` and reduce to
   `gcd(4j, 2j-1) = 1` via `Nat.coprime_self_add_right` after
   rewriting `4j = 2(2j-1) + 2`.

4. **Coprime API hiccups** (m odd sub-case): `gcd(m, 2m-2) = 1` for
   `m` odd reduces to `gcd(m, 2) = 1` since `gcd(m, 2m-2) | 2(m-1)`
   and `gcd(m, m-1) = 1` (consecutive). Use
   `(Nat.Coprime.coprime_dvd_right ⟨1, ...⟩).mul_right`.

5. **Sub-case combiner**: `mul_choose_dvd_lcmRange_three_even` takes
   `n ≥ 4` and `Even n`, then `rcases Nat.even_or_odd m` (where
   `m = n / 2`) and dispatches to the two sub-case lemmas.

6. **Full theorem combiner**: `mul_choose_dvd_lcmRange_three` takes
   `n ≥ 3`, then `rcases Nat.even_or_odd n` and dispatches to S8's
   `mul_choose_dvd_lcmRange_three_odd` or the new
   `mul_choose_dvd_lcmRange_three_even`.

### Cost estimate (revised)

~30-50 lines per sub-case (was ~50-80). The uniform helper identity
(*) saves ~15 lines per sub-case, and S8's `mul_choose_dvd_lcmRange_three_odd`
provides a direct template for the coprime-assembly pattern.

### What this S9 corrects

S8 state.md (lines 96-100, prior version) said "n ≡ 2 mod 4 ...
Probably Kummer" — based on observing that `n` and `n-2` both have
`v_2 = 1` and concluding the coprime argument can't close. **This is
false**: re-grouping the `2` into the `n-2 = 2(m-1)` factor (formula
(**)) gives a coprime triple `m, 2m-1, 2m-2` with all gcd's equal to
1 because `m` is odd. No Kummer needed.

**Axiom delta**: 0 (documentation-only).

## Session 8 (PR #17175, merged)

Added two helpers as Part 8 of `BaselProblemOQ01OQ01OQ02OQ02.lean`,
discharging the **odd-n** case of the m=3 divisibility:

1. `lcmRange_dvd_of_le` (Part 8a, generic): `m ≤ n → lcmRange m
   ∣ lcmRange n`. Pure structural lemma — `Finset.lcm_dvd` over a
   subset. Reusable in any chain-of-`lcmRange` argument.
2. `mul_choose_dvd_lcmRange_three_odd` (Part 8b): for `n ≥ 3` odd,
   `3 · C(n, 3) ∣ lcmRange n`. Proof by coprime assembly: `n` is
   coprime to `(n-1)(n-2)` (gcd | 2 but n odd), so the
   `Nat.Coprime.mul_dvd_of_dvd_of_dvd` route gives
   `n · (n-1)(n-2) ∣ lcmRange n`. By Part 7
   (`two_mul_three_mul_choose_three_eq`),
   `n · (n-1)(n-2) = 2 · (3 · C(n, 3))`, and `3 · C(n, 3)` divides
   its own multiple by 2.

The even-n case (Sessions 9+) requires the carry analysis on
`v_2(C(n, 3))`. For n=2k with k even (n ≡ 0 mod 4), the
factorization `n(n-1)(n-2)/2 = 2k · (n-1) · (k-1)` keeps the
factor-of-2 inside `n/2`, so a similar coprime argument may close
that subcase (since `n/2 = k` and `(n-1)(n-2)/2` no longer has a
common factor with k). For n=2k with k odd (n ≡ 2 mod 4), the
factorization is more delicate and Kummer is likely needed.

**Axiom delta**: 0 (algebraic identities + structural divisibility,
no new assumptions).

## Session 7 (PR #17146, merged)

Added two algebraic identities for the m=3 case as Part 7 of
`BaselProblemOQ01OQ01OQ02OQ02.lean`:

1. `three_mul_choose_three_eq` (n ≥ 3): `3 · C(n, 3) = n · C(n - 1, 2)`.
   Direct one-line corollary of `mul_choose_eq_mul_choose_pred`.
2. `two_mul_three_mul_choose_three_eq` (n ≥ 3):
   `2 · (3 · C(n, 3)) = n · (n - 1) · (n - 2)`. Combines (1) with the
   m=2 absorption step `2 · C(n - 1, 2) = (n - 1) · (n - 2)`.

These reduce the m=3 divisibility question
`3 · C(n, 3) ∣ lcmRange n` to whether `n(n-1)(n-2)/2 ∣ lcmRange n`
(the `/2` being the substantive obstacle that needs Kummer's theorem
or a careful coprimality argument). Either route — Kummer or double
induction — can use these identities as the entry point.

**Axiom delta**: 0 (algebraic identities, no divisibility yet).

## Current Focus

Discharging base cases of the binomial-denominator divisibility
  `mul_choose_dvd_lcmRange : 0 < m → m ≤ n → m · C(n, m) ∣ lcmRange n`,
which is needed for the alternating-bilinear half of the van der
Poorten denominator analysis (route F).

Session 6 (this session) proved the m=1 and m=2 cases:
  `mul_choose_dvd_lcmRange_one`, `mul_choose_dvd_lcmRange_two`.
The general theorem (m ≥ 3) requires either Kummer's theorem on
`v_p(C(n, m))` or a double `(n, m)` induction (~100-200 lines).

Earlier sessions:
- Session 5: added `mul_choose_eq_mul_choose_pred` (binomial absorption)
  + `dvd_mul_choose` (n divides m·C(n,m)) + `lcmRange_pos` + numerical
  witnesses 6, 7. Identified that the full
  `mul_choose_dvd_lcmRange` is harder than the Session 5 next-action
  implied (absorption only proves divisibility by `n`, not by
  `lcmRange n`).
- Session 4: discharged the H_n^{(3)} half of vdP (`harmonicCubed_lcm_clear`).
- Sessions 1-3: route selection + infrastructure.

## Active Approach

**Route (F)**: van der Poorten closed form for `aperyA n`.

Two halves of the denominator analysis:
- **H_n^{(3)} half** (this OQ-02-OQ-02): DONE Session 4.
- **Alternating-bilinear half**: m=1, 2 base cases DONE in
  Session 6; m=3 odd-n case DONE in Session 8 (this session);
  m=3 even-n case + m ≥ 4 remain.

## Blockers

For `mul_choose_dvd_lcmRange_three` (full m=3, even-n case):
- **No Kummer needed** (S9 finding). Both parity-of-`m` sub-cases
  admit a clean coprime decomposition (see S9 §"Concrete
  factorizations"). The S10 task is purely arithmetic Lean coding
  (~30-50 lines per sub-case), not an upstream Mathlib gap.

For `mul_choose_dvd_lcmRange` (m ≥ 4):
- Genuine Kummer-or-double-induction territory. The m=3 trick
  (parametrize `n = 2m` and re-group the lone `/2`) does **not**
  generalize to m ≥ 4: the binomial `C(n, m)` has `v_2` controlled
  by `s_2(m) + s_2(n-m) - s_2(n)` (digit-sum carry count), which
  cannot be uniformly absorbed by parametrization of `n`.

For the full `denominator_control`:
- The alternating bilinear summand
  `∑_{m=1}^{k} (-1)^{m-1}/(2 m^3 C(n,m) C(n+m,m))`
  needs `mul_choose_dvd_lcmRange` (general m) as input.
- `aperyA_explicit_formula` must be stated and validated numerically.

## Next Action

Session 10: implement Approach (A) per S9's tactical plan.

1. **Add Part 9 helper**: `three_mul_choose_three_eq_of_double` for
   `m ≥ 2`: `3 * C(2m, 3) = (2m)(2m - 1)(m - 1)`. Proof via Part 7
   `two_mul_three_mul_choose_three_eq` plus `2m - 2 = 2(m - 1)` plus
   `Nat.eq_of_mul_eq_mul_left`. ~10 lines.

2. **Add Part 10a** `mul_choose_dvd_lcmRange_three_double_even` for
   `m ≥ 2`, `Even m`: `3 * C(2m, 3) ∣ lcmRange (2m)`. Coprime triple
   `(2m)(2m-1)(m-1)`. ~30 lines.

3. **Add Part 10b** `mul_choose_dvd_lcmRange_three_double_odd` for
   `m ≥ 2`, `Odd m`: `3 * C(2m, 3) ∣ lcmRange (2m)`. Coprime triple
   `m(2m-1)(2m-2)` (re-group of (2m)(m-1) = m·2(m-1)). ~30 lines.

4. **Add Part 10c** `mul_choose_dvd_lcmRange_three_even` for `n ≥ 4`,
   `Even n`: dispatch on parity of `n / 2`. ~10 lines.

5. **Add Part 10d** `mul_choose_dvd_lcmRange_three` for `n ≥ 3`:
   dispatch on parity of `n` (S8 odd-case + S10 even-case). ~5 lines.

Total: ~85 lines of Lean. Build via Docker wrapper or "build pending"
per precedent. NO new sorries or axioms.

After S10 closes m=3, the next-action shifts to either:
- m ≥ 4 via Kummer (~150 lines for the generic prime-power-divides
  translation), OR
- bypass via the alternating bilinear summand needing a different
  divisibility lemma (the precise statement should be derived by
  re-reading the vdP §6 layout from S5).

## Attempt Counts

- Total attempts: 7
- Current approach attempts: 4 (route F: S4, S5, S6, S7 all forward
  progress; S8 m=3 odd case; S9 m=3 even-n tactical analysis).
- Approaches tried: 2 (recurrence-induction ruled out in S1;
  van der Poorten closed form being executed S2-S9+)
