# Erdős #18 OQ-01 (practical numbers) — Knowledge Base

## Session 2026-07-08 (researcher-1) — first STRUCTURAL theorem: practical ⇒ even

The predecessor `Erdos18OQ01.lean` had representability algebra + verified practical
numbers 4,6,8 but NO structural constraint. Added the classic Srinivasan (1948) fact:
- `practical_even : 2 ≤ m → IsPractical m → 2 ∣ m` — every practical number ≥ 2 is even.
- `practical_even' : … → Even m` — restatement.

Proof: 2 must be a sum of distinct divisors of m. For m=2 immediate; for m≥3 the
representing set S ⊆ divisors m has S.sum id = 2, all elements positive ⇒ each ≤ 2 (via
`Finset.single_le_sum`). If 2 ∉ S, every element is exactly 1 ⇒ S ⊆ {1} ⇒ S.sum id ≤ 1 < 2
(`Finset.sum_le_sum_of_subset`), contradiction. So 2 ∈ S ⊆ divisors m ⇒ 2 ∣ m.

★Gotchas (v4.26):
- `Nat.even_iff_two_dvd` REMOVED → build `Even m` directly: `obtain ⟨c,hc⟩ := practical_even..;
  exact ⟨c, by omega⟩` (Even m = ∃r, m=r+r; from m=2*c).
- `Finset.sum_le_sum_of_subset hsub` needs its TYPE PINNED (`have hle : S.sum id ≤
  ({1}:Finset ℕ).sum id := …`) else "typeclass instance problem is stuck" (f is a metavar).
- ★Do NOT `simp only [id_eq] at hle` to normalize `S.sum id` — it eta-expands to `∑ x∈S, x`
  while `hSsum` keeps `S.sum id`, so omega sees two DISCONNECTED atoms and fails
  ("a := ↑m/2, b := ↑(∑ x∈S,x)"). Keep both sides as `S.sum id` and `rw [hSsum]`.

Verified 0 axioms / 0 sorries, no native_decide; built first try (7744 jobs). The open
questions (asymptotic h(m)/Mertens-Vose bounds) stay out of elementary reach.

## Session 2026-07-08 (researcher-1) — first INFINITE family + odd classification

SOLVED-state look-outward. The file previously had only finite practical examples
(1,2,4,6,8) and one structural fact (practical ⇒ even). Added:

- `two_pow_representable (k) : n < 2^k → IsRepresentable n (2^k)` — binary-expansion
  lemma. Proof by induction on k: when 2^k ≤ n < 2^{k+1}, peel the high bit 2^k
  (fresh because every element of the remainder's representing set is ≤ n-2^k < 2^k)
  and recurse on n - 2^k < 2^k. Uses `Nat.divisors_subset_of_dvd`, `pow_dvd_pow`,
  `Finset.single_le_sum`, `Finset.sum_insert`, `Finset.insert_subset_iff`.
- `two_pow_practical (k) : IsPractical (2^k)` — the FIRST infinite family in the file
  (covers infinitely many practical numbers, not just examples).
- `odd_practical_eq_one : IsPractical m → Odd m → m = 1` — classification corollary of
  practical_even (1 is the only odd practical number).

★Gotchas (v4.26, all worked first try):
- `Nat.one_le_pow k 2 (by norm_num)` for `1 ≤ 2^k` (avoids guessing `Nat.one_le_two_pow`).
- fresh-bit `omega`: keep both `2^k` and `n - 2^k` as atoms; `hpow : 2^(k+1)=2*2^k`
  as a linear fact lets omega derive `n - 2^k < 2^k` from `n < 2^(k+1)`.
- `Finset.sum_insert hnotmem` then `simp only [id_eq]` then `omega` (with hge : n ≥ 2^k).

Verified 0 axioms / 0 sorries, no native_decide; built clean (7744 jobs). 13 theorems.
Remaining OQ (asymptotic h(m)/Mertens-Vose density) still out of elementary reach.

## Session 2026-07-08 (researcher-9) — multiplicative closure: product of practicals

SOLVED-state look-outward. The file already had the doubling closure `practical_two_mul`
and its `2^k · m` generator `practical_two_pow_mul`. Added the **full multiplicative
closure**: the set of practical numbers is closed under products.

- `representable_scale (c) (hc : 1 ≤ c) : IsRepresentable k m → IsRepresentable (c*k) (c*m)`
  — scale every divisor used by `c`; `c·d ∣ c·m` and `c ≥ 1` keeps the scaled divisors
  distinct (`Finset.sum_image` with `Nat.eq_of_mul_eq_mul_left`).
- `practical_mul : IsPractical m → IsPractical n → IsPractical (m*n)` — for `1 ≤ k < m·n`
  write `k = m·q + r` (`q = k/m < n`, `r = k%m < m`); represent `q` by divisors of `n`,
  scale by `m` to a sum of distinct divisors of `m·n` all `≥ m`; represent `r` by divisors
  of `m ∣ m·n` all `< m`; the two sets are disjoint (multiples of `m` vs values `< m`), so
  `representable_union` gives `m·q + r = k`. Strictly generalises `practical_two_mul`
  (`n = 2`) and `practical_two_pow_mul`.

Verified 0 axioms / 0 sorries, no native_decide; theoremCount 25→27, lineCount 362→444
(`docker-build.sh Proofs.Erdos18OQ01` → `✔ Built (3.6s)`).

★Gotchas (v4.26):
- The parent `Erdos18Problem.lean` defines a LOCAL wrapper `def divisors (n) : Finset ℕ :=
  n.divisors`. So `rw [Nat.mem_divisors]` FAILS (pattern `Nat.divisors ?` ≠ syntactic
  `divisors m`). Use term-mode instead — it unfolds `divisors` up to defeq:
  `Nat.dvd_of_mem_divisors h`, `Nat.pos_of_mem_divisors h`, `(Nat.mem_divisors.mp h).2`
  (for `m ≠ 0`), and construct membership with `Nat.mem_divisors.mpr ⟨hdvd, hne0⟩`.
- `Nat.pos_of_mem_divisors` wants membership in `divisors n`, NOT in the representing set
  `Sq`: feed it `hSq hdSq`, not `hdSq`.
- `Nat.div_lt_iff_lt_mul (0<m) : k/m < n ↔ k < n*m` — note `n*m` (commuted); close the mpr
  with `by rw [Nat.mul_comm]; exact hkmn`.
- `k = m*(k/m) + k%m` is `Nat.div_add_mod k m`; `k%m < m` is `Nat.mod_lt k (0<m)`.

Remaining open (unchanged): the asymptotic `h(m)` / Mertens–Vose density bounds — analytic,
out of elementary reach.

## Session 2026-07-11 (researcher-6) — full range to abundancy 4

SOLVED-state look-outward. The file had two full-range results reaching only abundancy
`σ(m)/m ≤ 2` (`practical_represents_all_of_sigma_le_two_mul`, tiling `[0,σ(m)]` with two
width-`m` end segments). Pushed the reach to **abundancy < 4** by using the double-width
bottom block `[0,2m)` (`practical_represents_lt_two_mul`, already present) plus its mirror
under complement symmetry.

- `practical_top_block` — practical `m` represents its TOP double-block `(σ(m)−2m, σ(m)]`:
  for `k ≤ σ(m)` with `σ(m)−k < 2m`, the reflected `σ(m)−k` is in the bottom block, then
  `representable_compl` complements back. Proof is 3 lines (`representable_compl` +
  `omega` cancel `σ−(σ−k)=k`).
- `practical_represents_all_of_sigma_lt_four_mul` — `IsPractical m → σ(m) < 4m → k ≤ σ(m)
  → IsRepresentable k m`. `rcases lt_or_ge k (2*m)`: bottom block for `k<2m`, else
  `practical_top_block` with `σ−k<2m` (omega from `k≥2m, σ<4m`). Strictly generalizes the
  abundancy-≤2 result; covers band (2,4): 12 (σ=28<48), 20 (42<80), 24 (60<96), 120
  (360<480).

Verified 0 axioms / 0 sorries, no native_decide; theoremCount 37→39
(`docker-build.sh Proofs.Erdos18OQ01` → `✔ Built (4.2s)`, 7744 jobs). PR #38162.

★Gotchas / ops:
- ★★.loom worktree REAPED TWICE mid-session (once mid docker-build → wiped uncommitted
  edits + working tree clean; once the whole dir deleted → cwd recovered to /Users/rwalters).
  Fix confirmed: EXTERNAL `git worktree add /Users/rwalters/lg-r6-erdos18` + COMMIT before
  building. docker-build uses its own Azure cache volume, works fine from external worktree.
- Dropped a concrete `twelve_represents_all` corollary that needed `(divisors 12).sum id =
  28 := by decide` — the decide risks heavy kernel reduction (exit 135/SIGBUS ambiguity);
  the docstring lists the σ values as illustration instead. Kept file 0-axiom.
- Pre-existing `le_or_lt` deprecation warning at line 318 (in the abundancy-≤2 theorem, not
  mine) — harmless, left as-is.

Remaining open (unchanged): abundancy ≥ 4 full range needs the greedy sorted-divisor
characterization (d_{i+1} ≤ σ_i+1), a larger project; asymptotic h(m)/Vose density stays
out of elementary reach.

## Session 2026-07-12 (researcher-2) — third-smallest divisor `d₃ ≤ 4`

SOLVED-state look-outward. The file had one structural divisibility constraint,
`practical_even` (`d₂ = 2`: every practical `m ≥ 2` is even). Added the next
constraint from requiring **`4` itself** to be a sum of distinct divisors:

- `practical_three_or_four_dvd : 4 < m → IsPractical m → 3 ∣ m ∨ 4 ∣ m` — the only
  distinct-divisor sums equal to `4` are `{4}` and `{1,3}`, so `4 ∈ S` (⇒ `4 ∣ m`) or
  `3 ∈ S` (⇒ `3 ∣ m`); otherwise `S ⊆ {1,2}` and `S.sum ≤ 3 < 4`. This is `d₃ ≤ 4`.
- `practical_four_or_six_dvd : 4 < m → IsPractical m → 4 ∣ m ∨ 6 ∣ m` — combining the
  `3 ∣ m` case with `practical_even` (`2 ∣ m`) via `Nat.Coprime 2 3` gives `6 ∣ m`.
  So every practical number `> 4` is a multiple of `4` or of `6` (the two smallest
  practical numbers above `2`). Verified against OEIS A005153 (6,8,12,16,18,20,24,…).

Proof reuses the `four_not_representable_ten` / `practical_even` bounding pattern:
each element of the representing set is positive and `≤ 4` (`Finset.single_le_sum`),
excluding `3,4` pins it into `{1,2}`, then `Finset.sum_le_sum_of_subset` caps the sum.

★Gotchas (v4.26, built first try, 7744 jobs, `✔ Built (8.3s)`, 0 axioms / 0 sorries):
- `Nat.Coprime.mul_dvd_of_dvd_of_dvd (h : Coprime k n) (k∣m) (n∣m) : k*n ∣ m` gives
  `2*3 ∣ m`; `norm_num at h6` rewrites `2*3 → 6` to land the `6 ∣ m` goal.
- Elements-are-`{1,2}` step: `by rintro rfl; exact h3 hx` for `x ≠ 3` (substitutes and
  reuses the `3 ∉ S` hypothesis), then `simp only [Finset.mem_insert, Finset.mem_singleton]`
  reduces `x ∈ {1,2}` to `x = 1 ∨ x = 2`, closed by `omega` from `1 ≤ x ≤ 4, x≠3, x≠4`.

Two pre-existing warnings untouched (unused `n` in Erdos18Problem:47, `le_or_lt`
deprecation at Erdos18OQ01:318). theoremCount 43→45 (grep), lineCount 660→725.

Remaining open (unchanged): abundancy ≥ 4 full range needs the greedy sorted-divisor
characterization (d_{i+1} ≤ σ_i+1); asymptotic h(m)/Vose density out of elementary reach.
The `dₖ` chain could continue (`5,6` representable ⇒ further constraints) but grows in
subset-enumeration complexity.
