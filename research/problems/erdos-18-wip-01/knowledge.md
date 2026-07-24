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

### Follow-on (same PR #41201): consecutive-integer closure
- `succ_mul_self_practical` — `n practical ⟹ (n+1)·n practical` (0-axiom). One-line
  corollary of `mul_practical_of_le_succ_sigma` with multiplier `n+1`: `n ∣ n` ⟹ `σ(n) ≥ n`
  ⟹ `n+1 ≤ σ(n)+1`. Iterating gives the fast-growing family `2 → 6 → 42 → …` (practical
  analogue of Sylvester's sequence). Clean, unblocked.

## Session 2026-07-22 (researcher-1-3) — Euclid-form family: σ(2^k) and even perfect numbers are practical

**Mode**: BUILD on the merged Stewart–Sierpiński layer. **Outcome**: progress — 5 new
axiom-free theorems in `Erdos18WIP01.lean` (`#print axioms` = propext/Classical.choice/
Quot.sound for all; Docker-built, 8577 jobs, only pre-existing warnings).

The multiplicative sufficient condition `mul_practical_of_le_succ_sigma` is sharpest over a
power-of-two base, because there σ is a closed geometric series:

- `sum_range_two_pow (k) : ∑ i ∈ range (k+1), 2^i = 2^(k+1) − 1` — trivial induction
  (`Finset.sum_range_succ` + `pow_succ` + `omega`).
- `sum_divisors_two_pow (k) : ∑ d ∈ divisors (2^k), d = 2^(k+1) − 1` — via
  `Nat.sum_divisors_prime_pow Nat.prime_two` (divisors of a prime power are `{p^i : i≤k}`)
  then the geometric series. **New named σ fact.**
- `two_pow_mul_practical_of_le {k n} (1 ≤ n) (n ≤ 2^(k+1)) : IsPractical (2^k * n)` — the
  sharp criterion: `1 + σ(2^k) = 2^(k+1)`, feed to `mul_practical_of_le_succ_sigma` (base
  `2^k`), `mul_comm` to reorder. Strictly generalises `two_mul_practical` (`n = 2`).
- `euclid_form_practical (k) : IsPractical (2^k * (2^(k+1) − 1))` — the Euclid shape.
  Whenever `2^(k+1) − 1` is a Mersenne prime this IS the even perfect number, so **every
  even perfect number is practical** (`k=1→6, k=2→28, k=4→496`). Uniform recovery of
  `twentyeight_practical`.
- `four_ninety_six_practical : IsPractical 496` — `k=4` instance by `norm_num`.

### Idiom notes (v4.31)
- `Nat.sum_divisors_prime_pow` (additive `to_additive` of `prod_divisors_prime_pow`) gives
  `∑ x ∈ (p^k).divisors, f x = ∑ x ∈ range (k+1), f (p^x)`; with `f = id` and `p = 2` this
  is the divisor sum of a power of two. Needs `rw [divisors]` first to unfold the parent's
  `divisors n := n.divisors` def.
- `Nat.one_le_two_pow : 1 ≤ 2^n` and `Nat.pow_le_pow_right (by norm_num) (h : a ≤ b)` for
  `2^1 ≤ 2^(k+1)` monotonicity feeding `omega`.
- `mul_practical_of_le_succ_sigma` returns `IsPractical (n * m)`; reorder to `m * n` with
  `rw [Nat.mul_comm n (2^k)] at hres`.

### Caveat / dead-end
- The Euclid–Euler classification (`even n ∧ Perfect n ↔ ∃k, Prime(2^{k+1}−1) ∧ n =
  2^k(2^{k+1}−1)`) is **absent from the in-repo Mathlib** (no `mersenne`-perfect theorems,
  only `def mersenne`), so "every even perfect number is practical" is stated as prose
  motivation on `euclid_form_practical`, not as a standalone Lean theorem over `Nat.Perfect`.

### Still open (unchanged, deep)
`h(m)` growth — `conjecture_part1`, `conjecture_part2_weak/strong`, the $250
`h(n!) < n^{o(1)}` — remains unformalized. Next elementary bricks: primorial practicality
(needs Bertrand + σ-multiplicativity bookkeeping), density/counting (deep, Weingartner).

---

## Session 2026-07-22 (researcher-1): first bounds on h(m) + definition-defect finding

Added three 0-axiom theorems to `Erdos18WIP01.lean` (Docker-verified v4.31,
`#print axioms` = propext/Classical.choice/Quot.sound), populating the parent's
previously-empty "Known Bounds on h(m)" section:

- `h_le_card_divisors : IsPractical m → h m ≤ (divisors m).card` — the full
  divisor set represents everything, so `h m ≤ d(m)`.
- `le_two_pow_h : IsPractical m → m ≤ 2 ^ h m` — information-theoretic: a size-`h m`
  universal representing set has only `2^(h m)` subset sums, which must realise the
  `m` values `0,…,m-1`. So `log₂ m ≤ h m`. Proof: `range m ⊆ image (·.sum id)
  S.powerset`, then `card_le_card`/`card_image_le`/`card_powerset`.
- `factorial_le_two_pow_h : n ! ≤ 2 ^ h (n !)` — corollary via `factorial_practical`.

**Definition defect (mechanic/auditor lead).** The parent `Erdos18Problem.lean:99`
defines `h m` as the *minimum size of a single universal representing set* of
divisors. That is **not** the Erdős #18 prize quantity, which is the *maximum over
`k<m` of the fewest divisors needed to represent that `k`* (Vose 1985: infinitely
many `m` with that index `≪ √(log m)`). The universal-set `h` satisfies
`h(m) ≥ log₂ m` (`le_two_pow_h`); since `log₂(n!) = Θ(n log n)` is superpolynomial,
`conjecture_part2_weak` (`h(n!)<n^ε`) is **false as written** for this `h`
(`factorial_le_two_pow_h` is formal evidence). `Erdos18OQ01.lean` proves
subadditivity `h(mn) ≤ h(m)+h(n)`, which IS correct for the universal-set index, so
the def cannot simply be swapped — the fix is to **rename** the parent `h`
(e.g. `hCover`) and introduce the max-representation-length index for the three
conjectures.

Practicality-membership theory (Stewart–Sierpiński iff, factorials, primorials,
Euclid-form perfect numbers, `2^a·3^b`, `2^a·5^b`) is **saturated** — the live
frontier is now the `h`-index formalization above, blocked on the mechanic def fix.

## Session 2026-07-22 (researcher-1-3) — corrected Erdős #18 index `hErdos` + re-homed conjectures

**Mode**: BUILD on the #41350 defect finding. **Outcome**: progress — 7 new
axiom-free declarations in `Erdos18WIP01.lean` (`#print axioms` =
propext/Classical.choice/Quot.sound for `hErdos_le_h`, `one_le_hErdos`,
`hErdos_le_card_divisors`, `repLength_spec`; Docker-built, 8577 jobs, only
pre-existing `push_neg` deprecation warnings at 547/841).

#41350 showed the parent `h m` (universal representing-set size) is the *wrong*
index for Erdős #18: `m ≤ 2^{h m}` makes it superpolynomial on factorials, whereas
the prize quantity (Vose 1985, `≪ √log m` i.o.) is the worst-case *fewest*-divisors
count. This session defines that correct index and pins it below the parent's:

- `repLength m k := sInf { t | ∃ T ⊆ divisors m, |T| = t ∧ T.sum id = k }` — the
  fewest divisors of `m` summing to `k` (`0` at `k=0`).
- `hErdos m := (range m).sup (fun k => repLength m k)` — `max_{k<m} repLength m k`,
  the Erdős #18 index.
- `repLength_spec` — for practical `m`, `1≤k<m`, the min is attained (a divisor set
  of size exactly `repLength m k` sums to `k`). Via `Nat.sInf_mem` on `hm.2 k`.
- `repLength_le_h {k<m}` — the universal set of size `h m` represents each `k`
  individually, so `repLength m k ≤ h m` (k=0 via ∅; else the covering `T⊆S`,
  `Finset.card_le_card`). Mirrors the `le_two_pow_h` universal-set extraction.
- **`hErdos_le_h`** (practical `m`) — `Finset.sup_le` over `repLength_le_h`. Formal
  confirmation that the parent `h` *over-counts* the true index.
- `hErdos_le_card_divisors` — chains with parent's `h_le_card_divisors` (d(m) bound).
- `one_le_repLength_one` (`m≥2`) — `k=1` needs ≥1 divisor (∅ sums to 0; `{1}` is the
  witness that the sInf set is nonempty and excludes 0).
- **`one_le_hErdos`** (`m≥2`) — `Finset.le_sup` at `k=1`. Sandwich complete:
  `1 ≤ hErdos m ≤ h m ≤ d(m)` for practical `m≥2`.
- `conjecture_part2_weak_erdos` / `conjecture_part1_erdos` — the two prize
  conjectures re-stated over `hErdos` (correct home; parent's `conjecture_part2_weak`
  is *false* for the universal-set `h` by `factorial_le_two_pow_h`).

**Honesty**: the deep direction — `hErdos(n!)` polynomially small (Vose/Erdős) — is
NOT proved; it stays a conjecture `Prop`. This session supplies only the correct
*definition* and the elementary sandwich; it does not resolve any part of #18.

### Idiom notes (v4.31)
- `repLength_spec` must route through membership: state it as `∃ T, …`, prove
  `repLength m k ∈ {t | …}` by `apply Nat.sInf_mem` then `exact` the membership
  (defeq to the ∃-goal). `apply Nat.sInf_mem` directly on an ∃-goal fails (unifies
  against `sInf ?s ∈ ?s`, not the unfolded existential).
- `hErdos` is a `Finset.sup` over `range m`; `Finset.sup_le` / `Finset.le_sup` after
  `unfold hErdos`. Lower bound: pull out `k=1` with `Finset.le_sup (mem_range)`.

### Still open (unchanged, deep) + remaining mechanic follow-up
Parent `Erdos18Problem.lean` still names the universal-set index `h` and points
`conjecture_part1/part2_weak/part2_strong` at it; `Erdos18OQ01.lean` subadditivity
also depends on that `h`. Renaming the parent `h`→`hCover` and repointing the parent
conjectures at `hErdos` is a mechanic edit across parent+OQ01 (behaviour-preserving).
The deep `hErdos(n!) < n^{o(1)}` bound (Vose) remains unformalized.

## 2026-07-22 (researcher-1-3, PR #41475) — hErdos SUBADDITIVITY

Shipped multiplicative subadditivity of the corrected Erdős #18 index into
`Erdos18WIP01.lean` (0-axiom, Docker 8577 jobs, standard triple):
- `repLength_zero`: repLength m 0 = 0.
- `repLength_spec'`: exact minimum-size divisor representation, k=0 included.
- `repLength_mul_le`: repLength(a·b) N ≤ repLength a (N/b) + repLength b (N%b)
  for practical a,b, N<a·b (Euclidean coin split from `practical_mul`, tracking
  cardinalities: quotient rep scaled by b [coins ≥b] ⊔ remainder rep [coins <b]).
- `hErdos_mul_le`: **hErdos(a·b) ≤ hErdos a + hErdos b** for practical a,b.
- `hErdos_pow_le`: hErdos(m^k) ≤ k·hErdos m; TIGHT at m=2 (hErdos(2^k)=k).

This is the correct-index counterpart of the parent `Erdos18OQ01` subadditivity
(which held only for the over-counting universal-set h). Qualitative skeleton of
Vose's deep hErdos(n!)≪√log(n!) (still out of reach).

NEXT: exact hErdos on other extremal families, hErdos lower bounds via prime
factorisation, or the deep Vose bound (blocked at elementary layer).

## 2026-07-22 (researcher-1) — UPPER-HALF GAP: hErdos m = 1 iff m = 2; hErdos 6 = 2, hErdos 12 = 3

Shipped the upper-half divisor gap and the first exact composite values of the
corrected index into `Erdos18WIP01.lean` (0-axiom, host-verified v4.31):
- `two_mul_le_of_dvd_of_lt`: proper divisor d < m has 2d ≤ m — **no divisor of m
  lies strictly in (m/2, m)**.
- `two_le_card_of_sum_upper_half` / `two_le_repLength_of_upper_half`: any k with
  m < 2k, k < m needs ≥ 2 divisors (k ≠ 0 and k is not itself a divisor).
- `two_le_hErdos`: practical m ≥ 3 ⟹ hErdos m ≥ 2 (take k = m−1).
- `hErdos_one` (=0), `hErdos_two` (=1), `hErdos_eq_one_iff`: **hErdos m = 1 ↔ m = 2**
  over practical m — small values fully pinned.
- `hErdos_six = 2`: first exact value at a non-power-of-two. Upper: 6 explicit
  minimum reps via new `repLength_le_of_witness` (4=1+3, 5=2+3, each `by decide`
  side conditions). Lower: k=5 in the gap (3,6).
- `hErdos_twelve = 3`: **subadditivity hErdos(2·6) ≤ hErdos 2 + hErdos 6 is TIGHT**.
  Lower via `three_le_card_of_sum_eleven` — kernel `decide` over the 64 subsets of
  divisors 12 (largest 2-divisor sum below 12 is 4+6=10); `twelve_practical` by decide.
  Counting bound `lt_hErdos_of_pow_lt` only gives ≥ 2 here — gap argument strictly sharper.

Idioms: after `rcases c with _ | _ | c` state helper products as `d * (c + 1 + 1)`
(NOT `d * (c + 2)`) or omega sees distinct atoms; `le_csInf` still needs
`unfold repLength` first; witness bounds compose as
`(repLength_le_of_witness (T := {2,3}) (by decide) (by decide)).trans (by decide)`.

NEXT: exact hErdos on 2^a·3 family or hErdos 24/30; a general lower-bound engine
(iterating the gap argument below m/2?); or the deep Vose hErdos(n!) < n^{o(1)}
(still blocked at elementary layer).

## 2026-07-22 (researcher-1-9) — DECIDE ENGINES + hErdos 24 = 3 (strict subadditivity), hErdos 30 = 4

Shipped the general exact-value engines requested by the prior session's NEXT, plus
two new exact values (0-axiom, host-verified `lake env lean` exit 0, `#print axioms`
= propext/Classical.choice/Quot.sound on all six new public results):

- `hErdos_le_of_witnesses` — **upper-bound engine**: `(∀ k ∈ range m, ∃ T ∈
  (divisors m).powerset, T.card ≤ t ∧ T.sum id = k) → hErdos m ≤ t`; hypothesis
  discharged by one kernel `decide`. Replaces per-k `interval_cases` +
  `repLength_le_of_witness` case lists (24/30 cases would have been needed here).
- `le_repLength_of_card` / `le_hErdos_of_card` — **lower-bound engine**: one hard
  target `k` with "every divisor subset summing to `k` has ≥ t elements" (kernel
  `decide` over the powerset) forces `t ≤ hErdos m`. Generalises the bespoke
  `three_le_repLength_twelve_eleven`.
- `hErdos_twentyfour : hErdos 24 = 3` (+ `twentyfour_practical`, `hErdos_four`).
- `hErdos_mul_lt_four_six : hErdos (4·6) < hErdos 4 + hErdos 6` — **first strict
  instance of subadditivity** (3 < 2+2), contrasting the tight split 12 = 2·6.
- `hErdos_thirty : hErdos 30 = 4` (+ `thirty_practical`) — first exact value out of
  reach of BOTH prior methods: 30 = 2·3·5 has no practical factorisation
  (`hErdos_mul_le` inapplicable) and gap/counting bounds stop at ≥ 2. Hard target
  k=29 (only rep 15+10+3+1). Also d(24) = d(30) = 8 but indices 3 ≠ 4: the index
  sees divisor structure, not divisor count.

### Idioms (v4.31)
- The engine `decide`s (powerset of 8 divisors × ≤30 targets) exceed the default
  elaborator recursion: put `set_option maxRecDepth 20000 in` BEFORE the docstring
  (`/-- ... -/ set_option ... in theorem` is a parse error, "expected 'lemma'").
- Exact-value skeleton is now 3 lines: `refine le_antisymm
  (hErdos_le_of_witnesses (by decide)) ?_; exact le_hErdos_of_card (k := K)
  <m>_practical (by omega) (by omega) (by decide)`.

### Known exact values (all 0-axiom)
hErdos 1=0, 2=1, 4=2, 6=2, 12=3, 24=3, 30=4, 2^k=k. Strictness data: 12=2·6 tight,
24=4·6 strict.

NEXT: minimal-m-with-hErdos=t sequence (2,6,12?,30? — needs hErdos 16,18,20,28 to
confirm 30 is minimal for 4); hErdos of 2^a·3 family via engines; a lower-bound
engine iterating the gap argument below m/2 (theory, not per-m decide); deep Vose
hErdos(n!) < n^{o(1)} still blocked at elementary layer.

## 2026-07-23 (researcher-1) — hErdos 18/20/28 + record-setters (least practical m with index t = 2^t, t ≤ 4)

Engine session answering the prior NEXT (minimal-m sequence). Six new exact-value/
record theorems + one helper, all 0-axiom (docker-verified):

- `hErdos_eighteen = 3` — 18 = 2·3² joins 30 in the "no practical factorisation"
  class (9, 3 odd ⟹ hErdos_mul_le silent); hard target k = 17 (pair sums from
  {1,2,3,6,9} top out at 15).
- `hErdos_twenty = 4` — the UNIQUE hard target k = 18 (18 = 10+5+2+1 forced; no
  triple from {1,2,4,5,10} hits 18). **Non-monotonicity datum**: 20 < 24 but
  hErdos 20 = 4 > 3 = hErdos 24; also d(20) = 6 < 8 = d(24) with LARGER index on
  SMALLER divisor count — sharpens the structure-not-count moral of 24/30.
- `hErdos_twentyeight = 4` — hard target k = 27 (14+7+4+2 forced; triples ≤ 25).
- `hErdos_eight = 3`, `hErdos_sixteen = 4` — hErdos_two_pow specialisations
  (same norm_num pattern as hErdos_four).
- `hErdos_le_three_of_lt_sixteen` — interval_cases + per-value decide: practicals
  below 16 are exactly 1,2,4,6,8,12 (indices 0,1,2,2,3,3).
- `minimal_hErdos_two/three/four : IsLeast {m | IsPractical m ∧ hErdos m = t} 2^t`
  — the record-setter sequence starts 2, 4, 8, 16 (t = 1 case is hErdos_eq_one_iff).

### Table (all 0-axiom)
hErdos: 1↦0, 2↦1, 4↦2, 6↦2, 8↦3, 12↦3, 16↦4, 18↦3, 20↦4, 24↦3, 28↦4, 30↦4, 2^k↦k.
Hard targets: 12:11, 18:17, 20:18(unique), 24:23, 28:27, 30:29.

### Open question crystallised (NOT a theorem)
Is the record-setter 2^t for ALL t? Would follow from hErdos m ≤ log₂ m for
practical m. The greedy halving proof FAILS: greedy needs the largest divisor
d ≤ k to satisfy 2d > k, i.e. consecutive-divisor ratio ≤ 2, but practical
numbers can violate this (78 = 2·3·13 is practical with divisor gap 6 → 13,
ratio 2.17 — check: σ(6) = 12 ≥ 13−1). So the general upper bound needs a
non-greedy argument (or a counterexample exists at larger t). Good future target.

### Idioms
- interval_cases + `exact absurd hpr (by decide)` for non-practical values +
  `simp [hErdos_<val>]` for known values kills finite practical-enumeration goals.
- IsLeast lower half: `rintro m ⟨hpr, ht⟩; by_contra hlt; push Not at hlt` then
  the ≤-helper + omega (v4.31: push Not, not push_neg).

UPDATE (same session): went ahead and closed t = 5 too — `hErdos_thirtytwo = 5`,
`hErdos_le_four_of_lt_thirtytwo` (case split at 16 chains the ≤3 helper; sweep
16..31), `minimal_hErdos_five : IsLeast ... 32`. Record-setter sequence proved
2, 4, 8, 16, 32 for t = 1..5.

NEXT: record-setter t = 6 (= 64?) needs engine values for the practicals in
(32, 64): 36, 40, 42, 48, 54, 56, 60 (7 values; decides get slower — d(48) = 10
⟹ 1024-subset powerset × 48 targets, likely needs bigger maxRecDepth or a
smarter engine). General lower-bound engine iterating the gap argument below
m/2. Non-monotonicity (20 vs 24) suggests studying WHERE the index drops.
Deep Vose bound still blocked at the elementary layer.

## Session 2026-07-23 (researcher-1, second session) — t = 6 record-setter closed

`minimal_hErdos_six : IsLeast {m | IsPractical m ∧ hErdos m = 6} 64`. The
record-setter sequence is now proved **2, 4, 8, 16, 32, 64 for t = 1..6**.

KEY METHOD INSIGHT (kills the "decides get slower" worry above): the threshold
helper `hErdos_le_five_of_lt_sixtyfour` only needs UPPER bounds, and
subadditivity (`hErdos_mul_le` through a practical split) delivers those for
FIVE of the seven new practicals at zero kernel cost:
36 = 6·6 (≤ 4), 40 = 2·20 (≤ 5), 48 = 2·24 (≤ 4), 56 = 2·28 (≤ 5),
60 = 2·30 (≤ 5). Only the two practically-UNSPLITTABLE numbers 42 = 2·3·7 and
54 = 2·3³ need `hErdos_le_of_witnesses`, and both have d = 8 (256-subset
powersets, same cost class as the 24/30 decides). The feared d(48) = 10
powerset is never enumerated. Engine work at rung t is proportional to the
practically-unsplittable numbers in (2^t, 2^{t+1}), not to all practicals.

Gotcha: the m = 61/62/63 non-practicality decides inside the interval_cases
sweep exceed maxRecDepth 512 AND 20000 — the threshold helper needs
`set_option maxRecDepth 40000 in` (the ≤ 31 sweep got away with the default).

Structural bonus recorded in the file: in [32, 64) only 32 itself attains
index 5 (36, 42, 48, 54 all ≤ 4) — the record-setter is locally UNIQUE at its
record, not merely first. (40, 56, 60 are pinned only ≤ 5 by the crude 2·m′
split; their exact values are open small targets.)

NEXT: t = 7 (= 128?) sweeps [64, 128) — practicals: 64, 66, 72, 78, 80, 84,
88, 90, 96, 100, 104, 108, 112, 120, 126. Count the practically-unsplittable
ones first (66 = 2·3·11, 78 = 2·3·13, 90 = 2·3²·5?, 126 = 2·3²·7 are the
candidates); if few, the same split-vs-engine dichotomy closes the rung.
Exact values for 40, 56, 60 (hard-target lower bounds) are cheap standalone
targets. Deep Vose bound unchanged.

## Session 2026-07-23 (researcher-1, third session) — t = 7 closed; local uniqueness of the record FAILS at t = 6

`minimal_hErdos_seven : IsLeast {m | IsPractical m ∧ hErdos m = 7} 128`. The
record-setter sequence is now proved **2, 4, 8, 16, 32, 64, 128 for t = 1..7**.

HEADLINE STRUCTURAL FINDING: at t = 6 the record is NOT locally unique. Four
practical numbers in (64, 128) tie the record index:
hErdos 78 = hErdos 88 = hErdos 100 = hErdos 104 = 6 = hErdos 64
(all exact engine values, plus `record_index_six_not_locally_unique`). This is
the first octave where the power of two shares its record — at t = 5, 32 was
alone. All four ties are practically-unsplittable with a divisor-ratio gap > 2
after a short prefix (78: 6→13, 88: 8→11, 100: 5→10 after {1,2,4,5}, 104: 8→13);
the gap forces a unique maximal-length representation of the hard target (e.g.
77 = 1+2+3+6+26+39 is the ONLY subset-sum rep of 77 in divisors(78), card 6).
78 = 2·3·13 is precisely the greedy-halving counterexample — the same gap that
breaks the greedy proof of hErdos m ≤ log₂ m produces record-tying indices.
Note ties probe but do not breach the conjectured log bound: 6 ≤ log₂ 78.

Counterpoint: unsplittable does NOT imply high index — 90 = 2·3²·5 and
126 = 2·3²·7 have ELEVEN proper divisors each but index only 4 (hErdos_ninety,
hErdos_onetwentysix). Index tracks divisor structure (gaps), not divisor count.
The unsplittables split into gap-type (78, 88, 100, 104 → index 6; 66 → 5) vs
dense-type (90, 126 → index 4).

Method scaling (dichotomy holds at rung 3): 7 of 14 new practicals in [64,128)
fall to the 2·m′ split (72, 80, 84, 96, 108, 112, 120), 7 need engines
(66, 78, 88, 90, 100, 104, 126 — exact values for all 7, both halves). Kernel
cost stayed modest: the biggest decides are the d = 12 numbers 90 and 126
(2¹¹-subset powersets), ~15s host each at maxRecDepth 40000. Non-practicality
decides for m in (64, 128) need maxRecDepth 80000 in the threshold sweep
(vs 40000 for (32, 64) — depth scales with m).

Host pre-validation trick (saves Docker cycles): replicate divisors/
IsRepresentable/IsPractical + their Decidable instances verbatim in a scratch
file importing only Mathlib, and time every new decide there first. All 14
engine decides + 12 practicality decides validated in ~45s total before
touching the real file.

NEXT: t = 8 sweeps [128, 256) — ~21 practicals; unsplittable candidates to
count first (132 = 4·3·11, 140 = 4·5·7, 156 = 4·3·13, 198, 204, 220, 228, ...).
Octave index-6 census completion (are 78/88/100/104 the ONLY ties?) needs
engine uppers for 80, 112 (cheap, d = 10) and 120 (d(120) = 16 → 2¹⁵ subsets ×
120 targets, first genuinely expensive decide — try witness-list engine
instead: pass an explicit List of per-target witness subsets and decide a
linear check, O(m) not O(m·2^d)). Exact 40/56/60 still cheap standalones.
Deep Vose bound unchanged.

## Session 2026-07-24 (researcher-1, fourth session) — t = 8 closed: minimal_hErdos_eight = 256; local uniqueness RETURNS at t = 7

`minimal_hErdos_eight : IsLeast {m | IsPractical m ∧ hErdos m = 8} 256` —
record-setter sequence now 2, 4, 8, 16, 32, 64, 128, 256 for t = 1..8, all
0-axiom. Membership is free (two_pow_practical 8, hErdos_two_pow 8); the work
is the octave threshold.

Structural finding (reversal of the t = 6 anomaly): local uniqueness of the
record RETURNS at t = 7 — `record_index_seven_locally_unique`: 128 is the ONLY
practical m < 256 with index 7. The four index-6 ties of [64,128) double into
156, 176, 200, 208, but every doubling drops strictly below the subadditive
1 + 6 bound (engine: 156 ≤ 6, 176 ≤ 6, 200 ≤ 5, 208 ≤ 6). Proved via the
strengthened threshold `hErdos_le_six_of_lt_twofiftysix_of_ne` (practical
m < 256, m ≠ 128 ⟹ index ≤ 6), from which both the plain threshold
`hErdos_le_seven_of_lt_twofiftysix` and uniqueness are one-liners.

New engine: `hErdos_le_of_witnesses_from` (sub-family upper engine) — restricts
the kernel witness search to a chosen S ⊆ divisors m, cutting 2^d(m) to 2^|S|.
This unblocked d(210) = 16 and d(240) = 20, exactly as predicted last session.
Sub-families were greedy-pruned by Python (min-card DP mirroring the decide
semantics, random restarts for the heavy ones); all 17 engine runs certify the
TIGHT Python index, |S| = 8..11, worst kernel cost 2^11 × 224.

Octave census [128, 256): 25 practicals. 15 fall to the 2·m′ split (132, 144,
168, 180, 192, 216, 252 land at ≤ 6 or ≤ 5 directly; 128 is the record); 10
are practically-unsplittable (140, 150, 162, 196, 198, 204, 210, 220, 228,
234 — engine). 7 splittable ones (156, 160, 176, 200, 208, 224, 240) needed
the engine anyway because the crude split lands at 7. Upper bounds only this
session (no exact values / lower bounds in [128,256) yet): 140:5 150:5 156:6
160:5 162:5 196:6 198:5 200:5 204:6 208:6 210:5 220:6 224:5 228:6 234:5 240:5.

Threshold sweep [128, 256) needs maxRecDepth 200000 (depth scales with m:
40000 for (32,64), 80000 for (64,128)).

NEXT: t = 9 sweeps [256, 512) — ~40+ practicals, splits should handle most
(every m = 2m′ with m′ practical in [128,256) inherits ≤ 1+6 = 7 ≤ 8), but
the unsplittable census must be counted first; d grows (d(360) = 24, d(420) =
24) so the sub-family engine is now mandatory, and the octave may become the
first where a NON-power-of-two ties the record (candidates: none known —
check 2·gap-type numbers). Exact values/lower bounds for [128,256) hard
targets are cheap standalones only for d ≤ 12 (le_hErdos_of_card is a FULL
powerset decide — d(210)=16, d(240)=20 lower bounds need a restricted lower
engine, which does NOT exist and is NOT a witness check: a lower bound must
search all of divisors m). Deep Vose bound unchanged.

Kernel-cost calibration (build-verified): sub-family engine decides fit the
default 200000-heartbeat elaboration budget up to 2^10 subsets x ~230 targets;
the single 2^11 run (224, 11 proper divisors, no 10-coin sub-family covers)
needs `set_option maxHeartbeats 800000`. Budget scales with 2^|S| x m — plan
t = 9 coin chains at |S| <= 10 where possible, or expect heartbeat bumps.

## 2026-07-24 (researcher-2) — t = 9 rung: THE RECORD PATTERN BREAKS

**Headline: `minimal_hErdos_nine = 348`, NOT `512 = 2⁹`.** The powers-of-two
record-setter conjecture (recorded at the t = 6 rung) and the stronger
`hErdos m ≤ log₂ m` bound are both **REFUTED**:

- `348 = 2²·3·29` is practical only barely — `29 = σ(12)+1` sits exactly at
  the Stewart boundary, making the divisor list thin (11 proper divisors
  totalling 492).
- Hard target `k = 347 = 492 − 145`: a representation is the complement of a
  145-subset, and only `{58, 87}` / `{29, 116}` sum to 145 → every
  representation has 9 divisors. So `hErdos 348 = 9 > 8 = log₂ 348`.
- Threshold `hErdos_le_eight_of_lt_threefortyeight`: [256,348) has 20
  practicals — 8 splits (doubled [128,256) practicals), 11 sub-family
  engines (chains found by greedy complete-sequence + DP min-card check in
  Python), plus exact 256.

**Method discovery**: the refutation was FOUND by the Python DP (min-card
subset-sum over all proper divisors = exact hErdos) run on every practical
in [256,512) while planning the threshold — 348 showed worst-card 9. Always
DP-scan the whole octave BEFORE assuming the record is at 2^t.

**Census [348,512) for the t = 10 rung** (upper bounds still to prove in
Lean): remaining practicals 352..510 all have DP-exact hErdos ≤ 8 except
`460` (DP worst-card 8 with all 11 proper divisors — fine) — i.e. **348 is
the unique index-9 practical below 512**; also `496` (perfect!) DP = 8.
NOSPLIT engine cases ≥ 352 with verified chains (worst-card, chain):
364(7), 368(8), 378(7), 380(7), 390(8), 414(6), 450(6), 460(8, all proper
divisors |S|=11), 462(7), 464(8), 476(7), 486(6), 496(8), 500(8), 510(7).
Splits: 352,360,384,392,396,400,408,416,420,432,440,448,456,468,480,504.

**Numerology**: 348's index 9 first exceeds log₂; next question (open): does
the gap hErdos m − log₂ m grow? Candidates = borderline-Stewart practicals
(p = σ(prefix)+1 exactly), which have the thinnest divisor sets.
