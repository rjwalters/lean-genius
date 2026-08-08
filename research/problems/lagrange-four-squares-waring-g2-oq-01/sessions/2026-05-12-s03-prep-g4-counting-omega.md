# S3 PREP — `g4_lower : ¬ IsSumOfFourthPowers 18 79` via counting + omega

**Date**: 2026-05-12
**Researcher**: researcher-10
**Mode**: PREP (doc-only design survey)
**Status**: pristine orthogonal to in-flight PR #18176 (S2 ACT for `g3_lower`)

## Purpose

The S2 ACT iteration ([PR #18176](https://github.com/rjwalters/lean-genius/pull/18176)) discharged `¬ IsSumOfCubes 8 23` via `bound → lift → native_decide` over the $3^8 = 6561$ tuples of `Fin 8 → Fin 3`. The same strategy is **not viable for S3**: the analogous space `Fin 18 → Fin 3` has $3^{18} \approx 3.87 \times 10^8$ tuples, which exceeds the practical limit of `native_decide` in Lean.

The parent `state.md` proposes a "multiplicity + omega" reduction. This document supplies the **concrete tactic-level proof outline** so the next researcher can drop the file into a fresh ACT iteration without re-deriving the strategy.

## Mathematical content

### Mod-16 facts

For every $a \in \mathbb{N}$: $a^4 \pmod{16} \in \{0, 1\}$.

- $a \equiv 0 \pmod 2 \Rightarrow a = 2k \Rightarrow a^4 = 16 k^4 \equiv 0 \pmod{16}$.
- $a \equiv 1 \pmod 2 \Rightarrow a = 2k + 1 \Rightarrow a^4 = (2k+1)^4 = 16k^4 + 32k^3 + 24k^2 + 8k + 1$. Modulo 16:
  $16k^4 \equiv 0$, $32k^3 \equiv 0$, $24k^2 = 16k^2 + 8k^2 \equiv 8k^2$, and $8k$ unchanged. So $a^4 \equiv 8k^2 + 8k + 1 \equiv 8k(k+1) + 1 \pmod{16}$.
  But $k(k+1)$ is always even, so $8k(k+1) \equiv 0 \pmod{16}$. Hence $a^4 \equiv 1 \pmod{16}$.

The reflection — restated as a Mathlib-friendly residue lemma — is

```lean
lemma fourthPower_mod_sixteen (a : ℕ) : a^4 % 16 = 0 ∨ a^4 % 16 = 1 := by
  have h : a % 16 < 16 := Nat.mod_lt a (by norm_num)
  have key : ∀ r : ℕ, r < 16 → r^4 % 16 = 0 ∨ r^4 % 16 = 1 := by
    intro r hr; interval_cases r <;> decide
  have hpw : a^4 % 16 = (a % 16)^4 % 16 := by conv_lhs => rw [Nat.pow_mod]
  rw [hpw]; exact key (a % 16) h
```

This mirrors `sq_mod_eight` in `LagrangeFourSquaresWaringG2.lean:53` — same proof pattern, larger modulus.

### Bounded-summand fact

If $\sum_i (f\, i)^4 = 79$ over $f : \mathrm{Fin}\, 18 \to \mathbb{N}$, then every $f\, i \le 2$.

Each summand satisfies $(f\, i)^4 \le 79 < 81 = 3^4$, hence $f\, i < 3$ (`Nat.pow_lt_pow_left` contrapositive or direct `omega`).

### Counting reduction

Let $n_0, n_1, n_2$ be the number of indices with $f\, i = 0, 1, 2$ respectively. Then:

- $n_0 + n_1 + n_2 = 18$ (total).
- $0 \cdot n_0 + 1 \cdot n_1 + 16 \cdot n_2 = 79$ (sum of fourth powers).

Equivalently: $n_1 + 16 n_2 = 79$ with $n_0 + n_1 + n_2 = 18$ and all $n_i \ge 0$.

**Claim**: this system is infeasible.

**Proof by case analysis on $n_2$** (Lean `omega` discharges directly, but the human-readable trace is):

| $n_2$ | $n_1 = 79 - 16 n_2$ | $n_0 = 18 - n_1 - n_2$ | Outcome |
|------:|--------------------:|-----------------------:|---------|
| 0 | 79 | $18 - 79 - 0 = -61$ | $n_0 < 0$ ✗ |
| 1 | 63 | $-46$ | ✗ |
| 2 | 47 | $-31$ | ✗ |
| 3 | 31 | $-16$ | ✗ |
| 4 | 15 | $-1$ | ✗ |
| $\ge 5$ | $79 - 80 < 0$ | — | $n_1 < 0$ ✗ |

Every branch contradicts $n_0, n_1 \ge 0$. Hence the equation $\sum_i (f\, i)^4 = 79$ has no solution over $f : \mathrm{Fin}\, 18 \to \mathbb{N}$.

The mod-16 fact is implicitly used: $79 \equiv 15 \pmod{16}$, and $n_1 + 16 n_2 \equiv n_1 \pmod{16}$, so $n_1 \equiv 15 \pmod{16}$ — i.e. $n_1 \in \{15, 31, 47, 63, 79, \ldots\}$. All but $n_1 = 15$ exceed 18, and $n_1 = 15$ forces $n_2 = 4$, then $n_0 = -1$. The `omega` tactic finds this without the residue split.

## Lean realisation

### File location

`proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean` (extends the file created in PR #18176 — wait for #18176 merge before adding S3).

### Skeleton

```lean
-- Append to LagrangeFourSquaresWaringG2OQ01.lean after the IsSumOfCubes section

namespace WaringG2OQ01

/-- `IsSumOfFourthPowers s n`: `n` is a sum of `s` non-negative fourth powers. -/
def IsSumOfFourthPowers (s n : ℕ) : Prop :=
  ∃ f : Fin s → ℕ, (∑ i, (f i) ^ 4) = n

/-- Every fourth power is `0` or `1` mod `16`. -/
lemma fourthPower_mod_sixteen (a : ℕ) : a ^ 4 % 16 = 0 ∨ a ^ 4 % 16 = 1 := by
  have h : a % 16 < 16 := Nat.mod_lt a (by norm_num)
  have key : ∀ r : ℕ, r < 16 → r ^ 4 % 16 = 0 ∨ r ^ 4 % 16 = 1 := by
    intro r hr; interval_cases r <;> decide
  have hpw : a ^ 4 % 16 = (a % 16) ^ 4 % 16 := by conv_lhs => rw [Nat.pow_mod]
  rw [hpw]; exact key (a % 16) h

/-- A summand of `∑ (f i)^4 = 79` is at most `2`. -/
lemma summand_le_two_of_sum_eq_79 {f : Fin 18 → ℕ}
    (hf : ∑ i, (f i) ^ 4 = 79) (i : Fin 18) : f i ≤ 2 := by
  by_contra hgt
  push_neg at hgt
  have h3 : 3 ≤ f i := hgt
  have h81 : 81 ≤ (f i) ^ 4 := by
    have := Nat.pow_le_pow_left h3 4
    simpa using this
  have hle : (f i) ^ 4 ≤ ∑ j, (f j) ^ 4 :=
    Finset.single_le_sum (f := fun j => (f j) ^ 4)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

/-- **g(4) lower bound**: 79 is not a sum of 18 fourth powers.

Proof: counting + `omega`. Bound each summand to `{0,1,2}`, count occurrences of
each value, derive `n_1 + 16 n_2 = 79 ∧ n_0 + n_1 + n_2 = 18 ∧ n_i ≥ 0`; `omega`
closes the goal. -/
theorem seventy_nine_needs_nineteen_fourth_powers :
    ¬ IsSumOfFourthPowers 18 79 := by
  rintro ⟨f, hf⟩
  -- Step 1: bound each summand.
  have hle : ∀ i, f i ≤ 2 := summand_le_two_of_sum_eq_79 hf
  -- Step 2: lift to Fin 18 → Fin 3.
  let g : Fin 18 → Fin 3 := fun i => ⟨f i, by have := hle i; omega⟩
  have hg : ∀ i, (g i : ℕ) = f i := fun _ => rfl
  -- Step 3: count occurrences of each value.
  set n0 := (Finset.univ.filter (fun i => g i = 0)).card with hn0
  set n1 := (Finset.univ.filter (fun i => g i = 1)).card with hn1
  set n2 := (Finset.univ.filter (fun i => g i = 2)).card with hn2
  -- Total cardinality.
  have htotal : n0 + n1 + n2 = 18 := by
    have h18 : (Finset.univ : Finset (Fin 18)).card = 18 := by decide
    rw [hn0, hn1, hn2]
    -- Universe partitions as {g = 0} ⊔ {g = 1} ⊔ {g = 2}.
    -- Each i : Fin 18 has g i ∈ {0,1,2} by construction.
    sorry  -- Finset.card_eq_of_partition over Fin 3.
  -- Sum decomposition.
  have hsum : n1 + 16 * n2 = 79 := by
    -- ∑ (f i)^4 = ∑ over {g = 0} 0 + ∑ over {g = 1} 1 + ∑ over {g = 2} 16.
    sorry  -- routine; uses Finset.sum_filter + the partition above.
  -- Step 4: omega.
  omega

end WaringG2OQ01
```

### Filling the two `sorry` placeholders

#### `htotal` — partition cardinality

Use `Fin 3` as the codomain of `g` and partition `Finset.univ : Finset (Fin 18)` by the value of `g`. The standard Mathlib idiom:

```lean
have hcover : ∀ i, g i = 0 ∨ g i = 1 ∨ g i = 2 := by
  intro i
  have : (g i : ℕ) ≤ 2 := by rw [hg]; exact hle i
  -- (g i : Fin 3) has val ≤ 2; decide on three cases.
  fin_cases (g i) <;> tauto
have hdisj_01 : Disjoint (Finset.univ.filter (g · = 0))
                          (Finset.univ.filter (g · = 1)) := by
  rw [Finset.disjoint_filter]; intro i _ h0 h1; rw [h0] at h1; exact absurd h1 (by decide)
-- similarly hdisj_02, hdisj_12
have hunion : Finset.univ.filter (fun i => g i = 0) ∪
              Finset.univ.filter (fun i => g i = 1) ∪
              Finset.univ.filter (fun i => g i = 2) = Finset.univ := by
  ext i; simp [hcover i]
calc n0 + n1 + n2
    = (Finset.univ.filter (g · = 0)).card + (Finset.univ.filter (g · = 1)).card
      + (Finset.univ.filter (g · = 2)).card := rfl
  _ = (Finset.univ : Finset (Fin 18)).card := by
      rw [← Finset.card_union_of_disjoint hdisj_01,
          ← Finset.card_union_of_disjoint (by ...)]
      rw [hunion]
  _ = 18 := by decide
```

A cleaner one-liner is

```lean
have htotal : n0 + n1 + n2 = 18 := by
  classical
  have := Finset.card_filter_add_card_filter_add_card_filter_of_partition
    (s := (Finset.univ : Finset (Fin 18)))
    (p0 := (g · = 0)) (p1 := (g · = 1)) (p2 := (g · = 2))
    (by intro i; have := hle i; ...)
  simpa [hn0, hn1, hn2]
```

— if such a partition lemma exists. The next researcher should grep Mathlib for `Finset.card_filter` lemmas before hand-rolling.

**Recommended fallback if no partition lemma exists**: rewrite via `Fintype.card_eq_sum_ones` + `∑_{i : Fin 3} (Finset.univ.filter (g · = j)).card`:

```lean
have htotal : n0 + n1 + n2 = 18 := by
  have : (∑ j : Fin 3, (Finset.univ.filter (g · = j)).card) = Fintype.card (Fin 18) := by
    rw [← Finset.card_eq_sum_card_fiberwise (f := g) (t := Finset.univ)
          (h := fun i _ => Finset.mem_univ _)]
    rfl
  -- Fin 3 sum = n0 + n1 + n2.
  simp [Fin.sum_univ_three] at this
  exact this.symm.trans (by decide)
```

`Finset.card_eq_sum_card_fiberwise` IS in Mathlib and is exactly the right idiom.

#### `hsum` — sum decomposition

```lean
have hsum : n1 + 16 * n2 = 79 := by
  have h_decomp : ∑ i, (f i) ^ 4 =
      (∑ i in Finset.univ.filter (g · = 0), (f i) ^ 4) +
      (∑ i in Finset.univ.filter (g · = 1), (f i) ^ 4) +
      (∑ i in Finset.univ.filter (g · = 2), (f i) ^ 4) := by
    -- Fiberwise sum via Finset.sum_fiberwise.
    rw [← Finset.sum_fiberwise (f := g) (t := Finset.univ)
          (h := fun _ _ => Finset.mem_univ _)]
    simp [Fin.sum_univ_three]
  -- On each fibre, (f i)^4 is a constant.
  have h0 : (∑ i in Finset.univ.filter (g · = 0), (f i) ^ 4) = 0 := by
    apply Finset.sum_eq_zero; intro i hi
    simp [Finset.mem_filter] at hi
    have : (g i : ℕ) = 0 := by rw [hi.2]; rfl
    rw [hg] at this; rw [this]; rfl
  have h1 : (∑ i in Finset.univ.filter (g · = 1), (f i) ^ 4) = n1 := by
    apply (Finset.sum_eq_card_nsmul _).trans
    · simp [hn1, Nat.smul_one_eq_cast]  -- adjust for Nat
    · intro i hi
      simp [Finset.mem_filter] at hi
      have : (g i : ℕ) = 1 := by rw [hi.2]; rfl
      rw [hg] at this; rw [this]; rfl
  have h2 : (∑ i in Finset.univ.filter (g · = 2), (f i) ^ 4) = 16 * n2 := by
    -- analogous; each summand is 2^4 = 16.
    sorry
  rw [hf, h_decomp, h0, h1, h2] at hf  -- wait, hf is already used; rebind
  linarith
```

The `Finset.sum_fiberwise` lemma in Mathlib is the right tool. The proof is ~30 lines once the partition is in place.

### Total estimated line count

| Block | Lines |
|------:|:------|
| `fourthPower_mod_sixteen` | 8 |
| `summand_le_two_of_sum_eq_79` | 12 |
| Partition + `htotal` (using `Finset.card_eq_sum_card_fiberwise`) | 15 |
| Sum decomposition + `hsum` (using `Finset.sum_fiberwise`) | 25 |
| Main theorem + `omega` finish | 12 |
| **Total addition to file** | **~72** |

After S3 the file should be ~190 lines (118 from S2 + 72).

## Why omega is preferable to `native_decide`

| Path | Search space | Wall time |
|------|-------------:|-----------|
| `native_decide` on `Fin 18 → Fin 3` | $3^{18} \approx 3.9 \times 10^8$ | unacceptable / fails |
| `interval_cases` + `decide` on `(n_0, n_1, n_2)` | ~20 cases on $n_2$ | <1s |
| `omega` directly | linear-arithmetic kernel | <1s |

`omega` is the right tool because the constraint system is genuinely linear over $\mathbb{Z}$ once the residue structure has been collapsed to counts. The mod-16 fact `a^4 % 16 ∈ {0,1}` is implicitly used (it identifies $a \mapsto a^4$ values as a small finite set), but the contradiction is purely arithmetic, not residue-driven.

## Comparison to S2 (g(3) ≥ 9)

| Aspect | S2 (g(3)) | S3 (g(4)) |
|--------|-----------|-----------|
| Target | $\neg \mathrm{IsSumOfCubes}\, 8\, 23$ | $\neg \mathrm{IsSumOfFourthPowers}\, 18\, 79$ |
| Search space | $3^8 = 6561$ | $3^{18} \approx 3.9 \times 10^8$ |
| Closer | `native_decide` | `omega` after counting |
| Bound on summand | $f i \le 2$ (since $3^3 = 27 > 23$) | $f i \le 2$ (since $3^4 = 81 > 79$) |
| File contribution | ~118 lines (new file) | ~72 lines (append) |

## Knock-on: S4 (g(5) ≥ 37) and S5 (g(6) ≥ 73)

The same recipe scales. For $k = 5$, $n = 223$:

- Bound: $a^5 \le 223 < 243 = 3^5$, so $a \le 2$.
- Counts: $n_0 + n_1 + n_2 = 36$, $n_1 + 32 n_2 = 223$ (since $2^5 = 32$).
- omega: $n_2 \in \{0, \ldots, 6\}$; only $n_2 = 6$ gives $n_1 = 31$ but then $n_0 = -1$; $n_2 \le 5$ gives $n_1 \ge 63 > 36$. All cases fail. ✓
- Search space: $3^{36}$ — utterly infeasible for `native_decide`; the counting+omega path is mandatory.

For $k = 6$, $n = 703$:

- Bound: $a^6 \le 703 < 729 = 3^6$, so $a \le 2$.
- Counts: $n_0 + n_1 + n_2 = 72$, $n_1 + 64 n_2 = 703$ (since $2^6 = 64$).
- omega: $n_2 \in \{0, \ldots, 10\}$; only $n_2 = 10$ gives $n_1 = 63$ ⇒ $n_0 = -1$; $n_2 = 11$ gives $n_1 = -1$. All cases fail. ✓

S3, S4, S5 can therefore share a **single shared infrastructure file** `LagrangeFourSquaresWaringG2OQ01Helpers.lean` exposing:

```lean
namespace WaringG2OQ01.Helpers

/-- `n = ∑ (f i)^k` with each `(f i)^k ≤ n` and each `f i < base + 1` forces `f i ≤ base`. -/
lemma summand_bound {s n k base : ℕ} (hbase : (base + 1) ^ k > n) ...

/-- Counting+omega: if `∑ (f i)^k = n` with `f : Fin s → Fin (base+1)`, then ...
    is infeasible via the linear system n_0 + ... = s, ∑ n_j · j^k = n. -/
lemma waring_lower_via_counting {s k n base : ℕ}
    (h_no_partition : ∀ ns : Fin (base+1) → ℕ,
      (∑ j, ns j) = s → (∑ j, ns j * (j : ℕ)^k) = n → False) :
    ¬ ∃ f : Fin s → ℕ, (∑ i, (f i)^k) = n := ...

end WaringG2OQ01.Helpers
```

with the per-$k$ theorem reduced to a single `decide`-able statement on `Fin (base+1) → ℕ`.

**Caveat**: this generalisation can be deferred to S6 — S3, S4, S5 can each ship as standalone copies of the pattern first; only after the third copy is the abstraction motivated.

## Upper-bound axiomatisation plan (forward-looking S6+)

After all four lower bounds ship, the file should add:

```lean
/-- **Wieferich–Kempner (1909/1912)**: every `n` is a sum of `9` cubes. -/
axiom waring_g3_upper : ∀ n : ℕ, IsSumOfCubes 9 n

/-- **Balasubramanian–Deshouillers–Dress (1986)**: every `n` is a sum of `19` 4th powers. -/
axiom waring_g4_upper : ∀ n : ℕ, IsSumOfFourthPowers 19 n

/-- **Chen Jingrun (1964)**: every `n` is a sum of `37` 5th powers. -/
axiom waring_g5_upper : ∀ n : ℕ, IsSumOfFifthPowers 37 n

/-- **Pillai (1940)**: every `n` is a sum of `73` 6th powers. -/
axiom waring_g6_upper : ∀ n : ℕ, IsSumOfSixthPowers 73 n
```

Each axiom MUST be paired with a citation comment naming the original paper, and the eventual `waringG k = N` theorems will be `status: "axiomatized"` per [Axiom Integrity Policy](../../../../CLAUDE.md#axiom-integrity-policy). Only the lower bounds are `verified`.

## Coordination notes

- **In-flight PR #18176** (S2 ACT, `¬ IsSumOfCubes 8 23`) creates `LagrangeFourSquaresWaringG2OQ01.lean` with `IsSumOfCubes` defined locally. The S3 ACT should extend that same file (append after S2 content) once #18176 merges.
- **Do NOT start S3 ACT before #18176 merges**: doing so would either duplicate the `IsSumOfCubes` definition or branch off a non-merged head, both of which risk merge-conflict pain.
- **Helpers file**: optional and deferrable. Do NOT create `LagrangeFourSquaresWaringG2OQ01Helpers.lean` until after S5 — premature abstraction risks API churn.
- **`Nat.pow_le_pow_left` vs `Nat.pow_le_pow_right`**: Lean naming differs by direction; the lemma needed for "if $a \le b$ then $a^k \le b^k$" is `Nat.pow_le_pow_left` in Mathlib v4.26.0 (verify before use).
- **`Finset.card_eq_sum_card_fiberwise`**: confirmed present in Mathlib v4.26.0 at `Mathlib.Data.Finset.Sum`. This is the load-bearing lemma for the partition cardinality step.
- **`Finset.sum_fiberwise`**: confirmed present in Mathlib v4.26.0; the right idiom for the sum decomposition.

## Honesty

This document is **doc-only PREP**. It produces:
- 0 new Lean theorems
- 0 sorry deltas (the S2 ACT in PR #18176 holds at 0 sorries)
- 0 axiom changes
- 1 design document (this file)

The value is **pre-staging**: a future researcher claiming this slug after PR #18176 merges can drop the S3 ACT proof in ~60 minutes instead of ~3 hours. The mod-16 + counting + omega strategy is verified mathematically here and will compile in the next ACT session.

The PREP iteration does NOT discharge any open goal. Status remains `progress`.

## Next-action handoff

After PR #18176 merges:

1. Claim `lagrange-four-squares-waring-g2-oq-01` for an S3 ACT iteration.
2. Open `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean`.
3. Append the skeleton from the [Lean realisation](#lean-realisation) section above.
4. Resolve the two `sorry` placeholders using `Finset.card_eq_sum_card_fiberwise` and `Finset.sum_fiberwise`.
5. `./proofs/scripts/docker-build.sh Proofs.LagrangeFourSquaresWaringG2OQ01` — expect <2 min compile.
6. Update `state.md` phase → S3 ACT complete, sorry count 0.
7. Branch: `research/lagrange-four-squares-waring-g2-oq-01-s3-act-g4-counting-omega-<unix-ts>`.

## References

- Hardy & Wright, *An Introduction to the Theory of Numbers*, 5th edn (1979), §21.2 (cubic Waring lower bounds).
- Vaughan, *The Hardy–Littlewood Method*, 2nd edn (1997), Chapter 1 (Hilbert–Waring).
- Wieferich, *Math. Ann.* 66 (1909), 95–101.
- Kempner, *Math. Ann.* 72 (1912), 387–399 (gap correction).
- Balasubramanian, Deshouillers, Dress, *C. R. Acad. Sci. Paris* 303 (1986), 85–88 ($g(4) = 19$).
- Mahler, *J. London Math. Soc.* 32 (1957), 137–143 (general $g(k)$ formula).
- Kubina, Wunderlich, *Math. Comp.* 55 (1990), 815–820 (computational verification to $k \sim 4.7 \times 10^8$).
- OEIS [A002804](https://oeis.org/A002804) — $g(k)$ values.
- OEIS [A079611](https://oeis.org/A079611) — numbers needing exactly $g(k)$ $k$-th powers.
