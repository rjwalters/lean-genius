# Knowledge Log: frobenius-number-oq-03

## S1 (researcher-4, 2026-05-12)

**OBSERVE phase**. Text-only survey establishing the formal target,
literature map, and decomposition into 6 staged iterations.

### Key Findings

1. **Three-consecutive integers is the cleanest target**. The formula
   `g(n, n+1, n+2) = ⌊(n-2)/2⌋ · n + (n-1)` for `n ≥ 3` was
   verified by direct enumeration for `n ∈ {3, 4, 5, 6, 7}` and admits
   an elementary proof (no advanced numerical-semigroup machinery
   strictly required — though Apéry sets do streamline it). This is
   the recommended S2-onward target.

2. **Mathlib has no numerical-semigroup theory**. Confirmed via
   GitHub Contents API at pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:
   `Mathlib.Combinatorics.NumericalSemigroup` does **not exist**, and
   the only Frobenius content is `frobeniusNumber_pair` (two coprime
   generators). Any three-generator formalization in this entry would
   be **net new** to the Lean ecosystem.

3. **Existing gallery infrastructure ports directly**. The parent file
   `Proofs/FrobeniusNumber.lean` (310 lines) provides
   `Representable a b n`, `representable_add_a`, `large_representable`,
   `frobenius_not_representable` and the supporting `mul_mod_injective`.
   Each of these has a natural three-generator analog; the
   `Representable3 a b c n := ∃ x y z, n = a*x + b*y + c*z` predicate
   inherits all closure properties (`representable3_add_a`, etc.)
   from the underlying multiplicative structure.

4. **The Brauer–Shockley identity `g(S) = max Ap(S, a) − a`** is the
   single conceptual lemma needed for the closed-form derivation.
   This is **not in Mathlib** but is a one-page proof
   (Brauer–Shockley 1962; restated in Rosales–García-Sánchez
   monograph §2.4). For the three-consecutive case it can be
   *bypassed entirely* by direct case analysis modulo `n`.

5. **The literature is mature** (Ramírez Alfonsín monograph 2005;
   Rosales–García-Sánchez 2009). 70+ explicit closed-form families
   are catalogued. The S6+ iterations could pick any of:
   - 3-AP (Roberts 1956) — most natural generalization of S5
   - Fibonacci triples (Marín–Ramírez–Revuelta 2007)
   - Mersenne triples (Cooper–Karikomi–Snabb)
   - Square-free pairs, geometric sequences, etc.

### Cross-References (Existing Gallery Entries)

- `frobenius-number` (parent, status: verified): `FrobeniusNumber.lean`
  provides 2-generator Representable / frobeniusNumber / Apéry
  infrastructure.
- `frobenius-number-oq-01` (status: verified): SylvESTER count formula
  `|nonRep| = (a-1)(b-1)/2`, in `FrobeniusNumberOQ01.lean`.
- `frobenius-number-oq-02` (sister): Frobenius symmetry
  `Rep(k) ↔ ¬Rep(g − k)`, in `FrobeniusNumberOQ02.lean`.
- `frobenius-two-coprime` (status: completed, no formal entry — replaced
  by Mathlib's `frobeniusNumber_pair`).

### Concrete Numerical Verification

The following table was computed by hand for the survey, validating
both the Roberts formula at `d = 1` and the proposed case-analysis
proof strategy:

| `n` | `g(n, n+1, n+2)` formula | Direct max non-rep |
|-----|--------------------------|--------------------|
| 3   | 2                        | 2                  |
| 4   | 7                        | 7                  |
| 5   | 9                        | 9                  |
| 6   | 17                       | 17                 |
| 7   | 20                       | 20                 |

All five values match. The pattern is: for even `n`,
`g = (n/2 - 1) · n + (n-1) = n²/2 − 1`; for odd `n`,
`g = ((n-3)/2) · n + (n-1) = (n² − n − 2)/2`. Both unified by the
`⌊(n-2)/2⌋ · n + (n-1)` form.

### Mathlib API Sanity (v4.26.0)

Searched for relevant decls at pinned rev:

- `Nat.le_div_iff_mul_le`, `Nat.div_lt_iff_lt_mul` — useful for
  `⌊·/2⌋` manipulations.
- `Nat.dvd_iff_mod_eq_zero`, `Nat.add_mod` — standard residue tools.
- `Finset.range`, `Finset.sum_range_succ` — for the Apéry-set
  enumeration if pursued.
- `Nat.Coprime.dvd_of_dvd_mul_right` — used in parent file
  `FrobeniusNumber.lean` line 107 (`mul_mod_injective`).

All standard. No drift surprises anticipated for S2+ implementation.

### Race-Risk Assessment

At S1 commit time (~14:25 UTC, 2026-05-12), `gh pr list --search
"frobenius-number-oq-03"` returned 0 open PRs. The slug was selected
by seeker at `2026-05-12T09:56:28Z` (4.5 hours prior); no recent
researcher activity. `git branch -a | grep frobenius-number-oq-03`
returned only the local feature branch. **Low race risk** for S1
text-only deliverable.

### Next Action (S2)

Implement `Representable3` predicate + four basic closure lemmas in
new file `Proofs/FrobeniusNumberOQ03.lean`. Target: ~100 lines,
0 sorries, 0 axioms. Verbatim port of the S1-skeleton
`Representable a b n` block from `FrobeniusNumber.lean` lines 43-69
with one extra generator threaded through.

Suggested S2 PR scope:
- `def Representable3 (a b c n : ℕ) : Prop`
- `theorem representable3_zero`
- `theorem representable3_a`, `..._b`, `..._c`
- `theorem representable3_add_a`, `..._add_b`, `..._add_c`
- Gallery metadata: minimal `meta.json` + `index.ts` boilerplate
  (defer full annotation set to S5+ when the main theorem lands).

### Bibliography Selected for S1

- Roberts (1956) — primary source for AP formula.
- Sylvester (1882) — historic 2-generator formula, on which this builds.
- Ramírez Alfonsín, *The Diophantine Frobenius Problem* (OUP 2005) —
  encyclopedic monograph; chapter 3 covers 3-generator formulas
  exhaustively.
- Rosales–García-Sánchez (Springer 2009) — algebraic / numerical-semigroup
  perspective; chapter 4 develops Apéry-set machinery.
- Brauer–Shockley (1962) — `g(S) = max Ap(S, a) − a` identity.

## Session 2026-07-08 (S9) - Sharpness of coprimality hypothesis

**Mode**: REVISIT (pool file absent; selected by knowledge score, active/tractable)
**Outcome**: progress (SOLVED-state outward extension, VERIFIED 0-axiom)

### What I Did
- Found S8 (general 3-AP Roberts closed form `frobenius_three_ap`) already merged (#33913); JSON progressSummary was stale at S7.
- Added S9 sharpness section proving `gcd(a,d)=1` in `frobenius_three_ap` is NECESSARY.

### Key Findings
- If `g := gcd(a,d) >= 2`, then `g` divides all three generators `a, a+d, a+2d`, hence every representable number (`gcd_dvd_of_representable3_ap`).
- The non-representable set then contains `{g*k+1 : k}` (injective, none divisible by g), so it is `Set.Infinite` and not `BddAbove` — no finite Frobenius number.
- Concrete: `(2,4,6)` has infinitely many non-representable (all odds).

### Files Modified
- proofs/Proofs/FrobeniusNumberOQ03.lean (743 -> 814 lines, 39 -> 43 thm)
- src/data/proofs/frobenius-number-oq-03/meta.json (count sync)
- src/data/research/problems/frobenius-number-oq-03.json (knowledge)

### Next Steps
- Genus/Sylvester-sum count for coprime AP triples via `representable3_ap_iff`.
- General s-term Roberts formula (variadic collapse).
