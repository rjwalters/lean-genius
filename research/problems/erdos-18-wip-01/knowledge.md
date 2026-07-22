# Knowledge Base: erdos-18-wip-01

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

## Session 2026-07-20 (researcher-1) — decidability + foundations for the def-only stub

**Mode**: FRESH (knowledge score 0). **Outcome**: progress — 13 axiom-free lemmas + 2
Decidable instances, **host-verified v4.31** (`lake env lean`, exit 0; `#print axioms`
spot-check = `[propext, Classical.choice, Quot.sound]`, no `native_decide`).

Erdős Problem 18 (practical numbers, $250): `m` is practical if every `1 ≤ k < m` is a
sum of distinct divisors of `m`; the open questions concern the growth of `h(m)`.
`Erdos18Problem.lean` held only defs + `one_practical`/`two_practical`. Added:

- **decidableIsRepresentable** — `IsRepresentable k m` (`∃ S ⊆ divisors m, S.sum id = k`)
  is decidable by searching `(divisors m).powerset` (`decidable_of_iff`, the iff is
  `Finset.mem_powerset`).
- **decidableIsPractical** — reorders the two implications of the bounded `∀ k` so
  `Nat.decidableBallLT` fires, giving a full decision procedure.
- Worked examples by plain kernel `decide`: `four_practical`, `six_practical`,
  `eight_practical`, `not_practical_three`, `not_practical_five` — **axiom-free**
  (no `Lean.ofReduceBool`; confirmed via `#print axioms`).
- Witnesses/bounds: `zero_isRepresentable` (∅), `one_isRepresentable`,
  `isRepresentable_self`, `isRepresentable_le_sigma` (`k ≤ Σ divisors` via
  `Finset.sum_le_sum_of_subset`), `mem_divisors_le` (`Nat.divisor_le`),
  `isPractical_pos`, `not_isPractical_zero`, `mem_practicalNumbers_iff`.

### Notes / gotchas
- The bounded quantifier in `IsPractical` is `∀ k, 1 ≤ k → k < m → …`; `Nat.decidableBallLT`
  needs the `k < m` bound outermost, so the decidability iff swaps the two hypotheses.
- Plain `decide` (kernel) keeps the examples axiom-free; `native_decide` would pull in
  `Lean.ofReduceBool` and must be avoided for a clean status.

### Still open
`h(m)` and its growth (`conjecture_part1`, `conjecture_part2_weak/strong`, the $250
`h(n!) < n^{o(1)}` question) are deep and unformalized — this session builds only the
elementary decidable scaffolding around the definitions.

## Session 2026-07-22 (researcher-1-3) — first STRUCTURAL results: powers of two + infinitude + even necessary condition

**Mode**: BUILD on the def-only foundations. **Outcome**: progress — new file
`proofs/Proofs/Erdos18WIP01.lean` (imports `Proofs.Erdos18Problem`), 5 theorems, all
axiom-free (`#print axioms` = `[propext, Classical.choice, Quot.sound]`, no `sorry`, no
`native_decide`). Verified BOTH Docker (`docker-build.sh Proofs.Erdos18WIP01`, exit 0,
8577 jobs) and host (`lake env lean` after building the Mathlib-only parent olean).

The parent established practicality only for the finite `decide`-checked examples
`1,2,4,6,8`. This session gives the first results covering **infinitely many `m` at once**:

- `repr_lt_two_pow (n k) (hk : k < 2^n)` — every `k < 2^n` is a sum of distinct powers of
  two drawn from `{2^0,…,2^{n-1}}`. Proof: strong induction on `n`; in the step, if
  `k < 2^n` use IH directly, else `2^n ≤ k < 2·2^n` so `k − 2^n < 2^n`, apply IH to
  `k − 2^n`, then `insert (2^n)` (disjoint because every element used is `< 2^n`).
- `image_two_pow_subset_divisors (n)` — `{2^i : i<n} ⊆ (2^n).divisors` (`pow_dvd_pow`).
- **`two_pow_practical (n) : IsPractical (2^n)`** — every power of two is practical.
- **`infinite_practicalNumbers : PracticalNumbers.Infinite`** — infinitely many practical
  numbers, via `Set.infinite_of_injective_forall_mem` with `f = (2 ^ ·)` and
  `Nat.pow_right_injective (le_refl 2)`.
- **`two_dvd_of_practical (hm : 3 ≤ m) (h : IsPractical m) : 2 ∣ m`** + `even_of_practical`
  — a matching NECESSARY condition. To represent `2`, since `1` is the only divisor `< 2`,
  the divisor `2` itself must appear. Proof idiom: `Finset.single_le_sum` bounds each
  summand `≤ 2`, so the representing set `S ⊆ {1,2}`; `sum = 2` rules out `S ⊆ {1}`
  (`Finset.sum_le_sum_of_subset` + `Finset.sum_singleton`), forcing `2 ∈ S ⊆ divisors m`.

### Reusable v4.31 Lean idioms (host `lake env lean` EXIT=0)
- **Binary-representation induction**: to represent `k < 2^n` as distinct powers of two,
  strong-induct on `n`; step splits on `k < 2^n` vs `2^n ≤ k`, peeling `2^n` via
  `Finset.insert_subset_iff` + `Finset.sum_insert hnotmem`. Disjointness `2^n ∉ S` from
  every element `< 2^n` (`Nat.pow_lt_pow_right (by norm_num) hi` + `omega`).
- **`2^(n+1) = 2^n + 2^n`** to feed `omega`: `by rw [pow_succ]; ring` (omega can't do pow).
- **Range-image monotonicity**: `Finset.image_subset_image (by intro x hx; rw [Finset.mem_range] at hx ⊢; omega)`
  — cleaner than `Finset.range_subset.mpr` (which mis-elaborated the `.mpr` argument here).
- **`Even m` from `2 ∣ m`** (no `Nat.even_iff_two_dvd` in v4.31): `obtain ⟨c,hc⟩ := hdvd; exact ⟨c, by omega⟩`.
- **`Set.infinite_of_injective_forall_mem`** (needs `[Infinite α]` domain): pass injectivity
  (`Nat.pow_right_injective (le_refl 2)`) then `∀ a, f a ∈ s`.
- **Necessary-condition idiom** "subset of positive divisors summing to `c` is forced":
  `Finset.single_le_sum (fun i _ => Nat.zero_le i) hx` + `rw [hsum, id_eq]` bounds each
  element `≤ c`; `interval_cases` + membership then pins the set.

### Still open (unchanged, deep)
`h(m)` and its growth — `conjecture_part1`, `conjecture_part2_weak/strong`, the $250
`h(n!) < n^{o(1)}` question — remain unformalized. Natural next elementary bricks:
Stewart–Sierpiński necessary structure (`p ≤ σ(small divisors)+1` for the least
non-dividing prime `p`), the Stewart product-closure criterion, and practicality of `n!`.

## Session 2026-07-22 (researcher-1-3): Full Stewart–Sierpiński characterisation (iff)

Closed the practicality criterion into a genuine **iff** in `Erdos18WIP01.lean`
(0-axiom, `#print axioms` = propext/Classical.choice/Quot.sound, Docker-built):

- `divisor_chain_of_practical` — **necessary** divisor-gap condition: for practical `m`,
  every divisor `d ∣ m` obeys `d ≤ 1 + ∑_{e ∣ m, e < d} e`. Mechanism: `d − 1 < m` is a
  distinct-divisor sum (practicality), and each coin used is `≤ d − 1 < d`
  (`Finset.single_le_sum`), so the smaller divisors already sum to `≥ d − 1`. This is the
  converse of the coin-chain sufficiency — previously it existed only as the inline
  `hchain` block inside `representable_le_sigma_of_practical`; now a named theorem.
- `practical_of_divisor_chain_condition` — **sufficient** direction: `finset_chain_covers`
  on the full `divisors m` covers `[0, σ(m)] ⊇ [0, m)` (since `m ∈ divisors m` ⟹ `σ ≥ m`).
- `practical_iff_divisor_chain` — `IsPractical m ↔ 1 ≤ m ∧ ∀ d ∈ divisors m,
  d ≤ 1 + ∑_{e ∣ m, e < d} e`. The full Stewart–Sierpiński characterisation in
  divisor-theoretic (not prime-factorisation) form. The `1 ≤ m` conjunct is essential:
  `m = 0` has `divisors 0 = ∅` so the chain condition is vacuously true but `0` is not
  practical.

### Idiom notes
- Reused the exact `hchain` derivation from `representable_le_sigma_of_practical` verbatim
  as `divisor_chain_of_practical`'s body — a clean refactor target for a future dedup.
- Sufficiency needs `k ≤ ∑ divisors m`: bound `m ≤ σ(m)` via `Finset.single_le_sum` on
  `m ∈ divisors m`, then `omega` against `k < m`.

### Remaining open (unchanged, deep)
The prime-factorisation form (`p₁ = 2`, `pᵢ ≤ σ(∏_{j<i} pⱼ^aⱼ)+1`) would follow from this
divisor-chain iff plus a sorted-prime bookkeeping layer — mechanical but sizeable. `h(m)`
growth (`conjecture_part1/2`, the $250 `h(n!) < n^{o(1)}`) remains unformalized and deep.
