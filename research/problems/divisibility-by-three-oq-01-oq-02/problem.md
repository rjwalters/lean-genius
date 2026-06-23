# Problem: Formalize convergence of the digital root iteration in Lean

## Statement

### Plain Language

Starting from any natural number n, repeatedly applying the digit-sum function
(summing the decimal digits) eventually terminates at digitalRoot n in finitely
many steps. Formally: the iterative process of digit-summing converges to the
closed-form digital root.

### Formal Statement

```lean
-- The digit sum function (sum of decimal digits)
def digitSum (n : ℕ) : ℕ := (Nat.digits 10 n).sum

-- digitalRoot is already defined in DivisibilityByThreeOQ01.lean as:
--   def digitalRoot (n : ℕ) : ℕ :=
--     if n = 0 then 0
--     else if 9 ∣ n then 9
--     else n % 9

-- The convergence theorem:
theorem digitSum_iter_convergence (n : ℕ) :
    ∃ k : ℕ, (digitSum^[k]) n = digitalRoot n
```

## Classification

```yaml
tier: C
significance: 5
tractability: 8
tags:
  - number-theory
  - digit-sum
  - digital-root
  - convergence
  - iteration
  - well-founded-induction
```

**Significance**: 5/10
**Tractability**: 8/10

## Why This Matters

1. **Connects definitions** — The gallery proof `divisibility-by-three-oq-01` defines
   `digitalRoot` as a closed-form expression. This theorem bridges the iterative
   characterization (repeated digit-summing) with the closed form.
2. **Well-founded induction exercise** — Requires proving `digitSum n < n` for n ≥ 10,
   then using well-founded recursion on size.
3. **Completes the digital root theory** — Listed as an open question in the parent proof.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| divisibility-by-three-oq-01 | Parent proof: defines digitalRoot, proves properties (Part VI). Lean file: Proofs/DivisibilityByThreeOQ01.lean |
| divisibility-by-3 | Base divisibility-by-3 proof |

## Key Technical Facts

From `divisibility-by-three-oq-01` (already in gallery, verified, 0 sorries):
- `digitalRoot n = 0` iff `n = 0`
- `digitalRoot n = 9` iff `9 ∣ n` (for n > 0)
- `digitalRoot n = n % 9` otherwise
- `digitalRoot n ≤ 9`

For convergence, the key lemma needed:
- `digitSum n < n` for all `n ≥ 10` (strictly decreasing on non-single-digit inputs)
- `digitSum n = n` for `n < 10` (single-digit fixed points)
- `digitSum n % 9 = n % 9` (digit sum preserves mod 9)

## Proof Strategy

1. **Decreasing lemma**: Prove `∀ n ≥ 10, digitSum n < n`
   - `Nat.digits 10 n` has ≥ 2 digits for n ≥ 10
   - Each digit is < 10, so sum of k≥2 digits < 10k ≤ n
   - Use `Nat.lt_of_digits_lt` or direct bounds reasoning

2. **Termination**: Well-founded induction on n (decreasing chain terminates)
   - If n < 10: `digitSum n = n = digitalRoot n`, done with k=0 or k=1
   - If n ≥ 10: `digitSum n < n`, so by IH ∃ k, `(digitSum^[k]) (digitSum n) = digitalRoot (digitSum n)`
     Since `digitSum n % 9 = n % 9`, `digitalRoot (digitSum n) = digitalRoot n`

3. **Assembly**: Combine k=1 step with the IH's k steps → total k+1 steps

## Approach Ideas

- **Direct**: Formalize the decreasing lemma using `Nat.digits` properties in Mathlib
- **Via measure**: Define measure `m n = n` and use `Nat.strongRecOn` or `WellFoundedRelation`
- **With Function.iterate**: Use `Function.iterate_add` to compose steps
