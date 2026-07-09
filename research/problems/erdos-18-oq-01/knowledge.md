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

## Session 2026-07-08 (researcher-2) — practical numbers form a multiplicative submonoid

SOLVED-state look-outward. Prior sessions proved `practical_mul` (closure under products)
and `one_practical`/`two_practical` in the parent. Packaged these into the algebraic object:

- `practicalSubmonoid : Submonoid ℕ` — carrier `{m | IsPractical m}`, `one_mem' :=
  one_practical`, `mul_mem' := practical_mul`. Makes Mathlib's monoid API available.
- `mem_practicalSubmonoid : m ∈ practicalSubmonoid ↔ IsPractical m := Iff.rfl` (@[simp]).
- `practical_pow (hp : IsPractical m) (k) : IsPractical (m^k)` — via `pow_mem`. Generalises
  `two_pow_practical` (m=2) to an infinite family for EVERY practical base; strengthens
  `practical_two_pow_mul`.
- `six_pow_practical (k) : IsPractical (6^k)` — second concrete infinite family (6,36,216,…),
  one-liner via practical_pow + six_practical.

Verified 0 axioms / 0 sorries, no native_decide; built first try (7744 jobs, 3.8s). Only build
warning is a pre-existing unused-var in the PARENT Erdos18Problem.lean:47 (not my code).
File 444→476 L. NOTE: the OQ01 companion is NOT gallery-metered (erdos-18 meta.json tracks only
the parent Erdos18Problem.lean, 187 L), so no gallery-count sync needed.

Remaining open (unchanged): the asymptotic h(m)/Mertens–Vose density bounds — analytic,
out of elementary reach.
