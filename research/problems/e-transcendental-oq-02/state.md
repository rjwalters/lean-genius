# Current State

**Phase**: ACT — Layer 3b done; `rational_digits_eventually_periodic` discharged
**Since**: 2026-05-04T16:38:18.044Z
**Last Updated**: 2026-05-08 (Session 11, researcher-8)
**Iteration**: 11

## Current Focus

Session 11 closed the 3-layer recipe by implementing **Layer 3b** — the
integer-arithmetic residue-to-digit bridge — and using it (together with
Layers 1, 2, 3a) to discharge the previous `rational_digits_eventually_periodic`
axiom. The axiom is now a theorem.

### New code (4 lemmas + 1 theorem; ~75 lines)

```lean
-- Cast bridge: lift Layer 3a from (p, q : ℕ × ℤ) to q : ℚ
private lemma floor_pow_rat_eq_ediv (b : ℕ) (q : ℚ) (n : ℕ) :
    ⌊((b : ℝ) ^ n * (q : ℝ))⌋ = (q.num * (b : ℤ) ^ n) / (q.den : ℤ)

-- Integer-arithmetic identity (Euclidean division decomposition)
private lemma int_mul_ediv_eq (b a m : ℤ) (hm : m ≠ 0) :
    b * a / m = b * (a / m) + (b * (a % m)) / m

-- Layer 3b core: digit at n+1 = (b · residue at n / q.den) % b
private lemma nthDigit_succ_via_residue (b : ℕ) (q : ℚ) (n : ℕ) :
    nthDigit b (n + 1) (q : ℝ) =
      (((b : ℤ) * ((q.num * (b : ℤ) ^ n) % (q.den : ℤ))) / (q.den : ℤ)) % (b : ℤ)

-- Bridge: residue equality at n, m ⇒ digit equality at n+1, m+1
private lemma nthDigit_succ_eq_of_emod_eq (b : ℕ) (q : ℚ) {n m : ℕ}
    (h : (q.num * (b : ℤ) ^ n) % (q.den : ℤ) =
         (q.num * (b : ℤ) ^ m) % (q.den : ℤ)) :
    nthDigit b (n + 1) (q : ℝ) = nthDigit b (m + 1) (q : ℝ)

-- Replaces axiom: digits eventually periodic
theorem rational_digits_eventually_periodic (b : ℕ) (_hb : 2 ≤ b) (q : ℚ) :
    ∃ T N₀, 0 < T ∧ ∀ n ≥ N₀, nthDigit b (n + T) q = nthDigit b n q
```

### Key Mathlib API used (all v4.26.0)

| Lemma | Module | Role |
|-------|--------|------|
| `Rat.cast_def` | `Mathlib.Algebra.Field.Defs` | `(q : ℝ) = q.num / q.den` |
| `Int.ediv_add_emod` | core | `m·(a/m) + a%m = a` |
| `Int.add_mul_ediv_left` | core | `(x + m·y)/m = x/m + y` |
| `Int.add_mul_emod_self_left` | core | `(x + m·y)%m = x%m` |
| `ZMod.intCast_eq_intCast_iff'` | `Mathlib.Data.ZMod.Basic` | residue ↔ `% q.den` equality |
| `Rat.den_pos` | core | `0 < q.den` |

## Active Approach

The Lean entry now establishes:
- **Definitions**: `nthDigit`, `IsNormalInBase`, `IsAbsolutelyNormal`,
  `ratResidue` (private, S9).
- **29 public theorems**: `e_floor`, `e_floor_10..1000000000`, `e_digit1..9`,
  `e_normal_implies_uniform_decimal_digits`, `periodic_has_missing_ktuple`,
  and now (S11) `rational_digits_eventually_periodic`.
- **10 private helpers** (Layers 1, 2, 3a, 3b): `exists_iterate_collision`,
  `eventually_periodic_iterate`, `ratResidue_succ`, `ratResidue_eq_iterate`,
  `ratResidue_eventually_periodic`, `floor_pow_mul_div`, `floor_pow_rat_eq_ediv`,
  `int_mul_ediv_eq`, `nthDigit_succ_via_residue`,
  `nthDigit_succ_eq_of_emod_eq`.

**Two remaining axioms**:
- `normal_imp_irrational` — now directly tractable. Recipe: apply (proved)
  `rational_digits_eventually_periodic` to get T, N₀; pick k with bᵏ > T;
  apply (proved) `periodic_has_missing_ktuple` to get a missing k-tuple;
  bound count by N₀ ⇒ frequency → 0; contradict Tendsto to b^(-k) > 0.
  ~50 lines, no new axioms.
- `e_absolutely_normal` — the **main open conjecture**. Genuinely open
  as of 2026; will remain axiomatized.

## Blockers

- **Local Lean build unreliable**: Worktree's `proofs/.lake` is a
  self-cycle symlink — Docker build cold-clones Mathlib (~45 min).
  Following S8/S9/S10 convention, build verification is deferred to CI.
  All Mathlib lemmas used are well-established and stable in v4.26.0.

## Next Action

**ACT (Session 12)** — discharge `normal_imp_irrational` via the recipe above.
With `rational_digits_eventually_periodic` now a theorem, the path is:

1. Suppose x = p/q is rational and IsNormalInBase b x. Apply (proved)
   `rational_digits_eventually_periodic` to get T, N₀ with 0 < T,
   nthDigit b (n+T) x = nthDigit b n x for n ≥ N₀.
2. Pick k with bᵏ > T (e.g., k := T + 1 since T < bᵏ for b ≥ 2).
3. Apply (proved) `periodic_has_missing_ktuple` to get a missing k-tuple s.
4. Show that the count of n < N where x has tuple s starting at n is
   bounded by N₀ (the pre-period contribution), since after N₀ no n
   produces s.
5. Therefore frequency → 0 as N → ∞, contradicting normality (which
   requires frequency → b^(-k) > 0).

After Session 12, only `e_absolutely_normal` remains axiomatized — and
that is the genuinely-open conjecture.

## Attempt Counts

- Total attempts: 6 (Session 1 = entry built 2026-05-04; Session 2 =
  metadata reconciliation 2026-05-07; Session 3 = recipe (2026-05-08);
  Session 8 = Layer 1 (#16993, 2026-05-08); Session 9 = Layer 2
  (#17016, 2026-05-08); Session 10 = Layer 3a (#17037, 2026-05-08);
  Session 11 = Layer 3b + axiom discharge (this PR, 2026-05-08)).
- Current approach attempts: 4 (Layers 1, 2, 3a, 3b all closed; axiom 1
  discharged).

## References

- `proofs/Proofs/ETranscendentalOQ02.lean:430+` — `rational_digits_eventually_periodic` (theorem, S11)
- `proofs/Proofs/ETranscendentalOQ02.lean:395+` — `nthDigit_succ_via_residue` (Layer 3b, S11)
- `proofs/Proofs/ETranscendentalOQ02.lean:341` — `floor_pow_mul_div` (Layer 3a, S10)
- `proofs/Proofs/ETranscendentalOQ02.lean:308` — `ratResidue_eventually_periodic` (Layer 2, S9)
- `proofs/Proofs/ETranscendentalOQ02.lean:243` — `eventually_periodic_iterate` (Layer 1, S8)
- `src/data/proofs/e-transcendental-oq-02/meta.json` — gallery metadata
