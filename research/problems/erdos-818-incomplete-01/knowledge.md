# Knowledge: Erdős 818 — Product Set Lower Bound for Small Sumsets (completion)

## Session 2026-07-20 (researcher-1)

Target file: `proofs/Proofs/Erdos818Problem.lean` (gallery entry `erdos-818`).
Started at 1 axiom (`solymosi_theorem`) + 1 sorry (`proof_outline`).

### What was added (axiom-free, host-verified under Mathlib v4.31)

- **`sumset_eq_add`** — `sumset A = A + A` (pointwise), the additive analogue of
  the file's `productSet_eq_mul`.
- **`sumset_lower_bound`** — `2|A| - 1 ≤ |A + A|` for nonempty `A ⊆ ℤ`, via
  Mathlib's `cauchy_davenport_add_of_linearOrder_isCancelAdd`. Fills the
  previously comment-only Part II.
- **`product_lower_of_mult_energy`** — the faithful Solymosi reduction. From
  `cauchy_schwarz_energy` (already proved) plus the multiplicative-energy upper
  bound `E×(A) ≤ C·|A+A|²·log|A|` supplied as an **explicit hypothesis**, it
  proves `|A·A| ≥ |A|² / (C·K²·log|A|)` when `|A+A| ≤ K·|A|`. This machine-checks
  the whole reduction and isolates the single genuine external input WITHOUT
  adding a new axiom.

Required adding `import Mathlib.Combinatorics.Additive.CauchyDavenport` (the
Cauchy–Davenport lemma is not transitively imported by `...Additive.Energy`).

### The remaining open sorry (`proof_outline`)

`proof_outline` claims the sharper `|A·A| ≥ |A|² / (K·log|A|)` (denominator
`K`, not `K²`). Two honest facts:

1. It is **not** derivable from the `solymosi_theorem` axiom (absolute constant
   `c·|A|²/log|A|`): that would require `c·K ≥ 1`, which the existential `c` does
   not provide.
2. It is **stronger** than the standard energy argument yields. Substituting
   `|A+A| ≤ K·|A|` into `E×(A) ≤ C·|A+A|²·log|A|` costs a square, giving only
   `1/(C·K²·log|A|)` (exactly `product_lower_of_mult_energy`). The `K`-linear
   form needs a materially different argument, or Solymosi's energy inequality
   formalized in Mathlib.

### Blocker (structured, in tracker `currentState.blockers`)

- route: proof_outline sharp `1/(K·log|A|)` product-set bound via multiplicative
  energy — reopen only with a materially new mechanism.

### Next external input to formalize

Solymosi's multiplicative-energy inequality `E×(A) ≤ C·|A+A|²·log|A|` (dyadic
pigeonhole on the multiplicative fibers `{(a,b) : ab = m}`) — not currently in
Mathlib. Formalizing it would discharge `product_lower_of_mult_energy`'s
hypothesis and give the `K²` product-set bound unconditionally.

## Session 2026-07-20 (researcher-1) — Aristotle companion cleanup (3 sorries → 0)

**Mode**: continue. **Outcome**: progress — host-verified, axiom-free, no Docker.
Cleaned `proofs/Proofs/Erdos818Aristotle.lean` (imports Mathlib only):

- **`mul_div_ge_div` was FALSE as stated** — `c*x/y ≥ x/y` fails for `x < 0`
  (`c=2, x=-1, y=1 ⟹ -2 ≥ -1`). Added the required `0 ≤ x` hypothesis; proof
  `(div_le_div_iff_of_pos_right hy).mpr (by nlinarith [mul_nonneg …])`.
- **`multEnergy_ge_sq`** `E×(A) ≥ |A|²`: inject the diagonal `(a,b) ↦ ((a,b),(a,b))`
  (always satisfies `ab = ab`) via `Finset.card_le_card_of_injOn`;
  `A.card² = (A ×ˢ A).card` by `Finset.card_product`. Destructure `p` to `(a,b)`
  first so the filter's pattern-match predicate reduces to `rfl`.
- **`cauchy_schwarz_energy`** (companion) `E×(A)·|A·A| ≥ |A|⁴`: connect the local
  `multEnergy` to `Finset.mulEnergy A A` (`multEnergy_eq_mulEnergy`, via
  `Finset.mulEnergy_eq_card_filter`), then `Finset.le_card_mul_mul_mulEnergy` + a
  ℕ→ℝ cast. The elementary CS energy bound **is** in Mathlib; only Solymosi's
  energy *upper* bound is the missing deep input.

The main file (`Erdos818Problem.lean`) is untouched: its `solymosi_theorem`
axiom and `proof_outline` sorry are both genuine deep external inputs (Solymosi
2009), not session-eliminable.

## Session 2026-07-20 (researcher-1) — product-set lower bound

**Mode**: continue. **Outcome**: progress — host-verified, axiom-free, no Docker.

Added `productSet_lower_bound` to `Erdos818Problem.lean` (Part II): for `A ⊆ ℤ`
with a nonzero element `a₀ ∈ A`, `|A| ≤ |A · A|`. This is the multiplicative
analogue of the already-proved `sumset_lower_bound` and fills the previously
comment-only "Lower bound on product set" of Part II. Proof: `a ↦ a₀ · a` is
injective on ℤ (domain, `mul_left_cancel₀`), and maps `A` into `A · A`, so
`|A| = |a₀·A| ≤ |A·A|`. `#print axioms` = `[propext, Classical.choice, Quot.sound]`
(axiom-free by project convention). File still compiles with only the
pre-existing `proof_outline` sorry warning.

**Saturation note.** With both Part II trivial bounds now proved, the file's
elementary content is exhausted. The two remaining items are research-depth and
unchanged:
- axiom `solymosi_theorem` — Solymosi's multiplicative-energy upper bound
  `E×(A) ≤ C·|A+A|²·log|A|`, not in Mathlib (dyadic pigeonhole on multiplicative
  fibers; BUILD/BLOCKED tier).
- sorry `proof_outline` — the sharp `1/(K·log|A|)` product-set bound, a
  registered blocked route (`currentState.blockers`) requiring a materially new
  mechanism (the standard energy argument yields only `1/(C·K²·log|A|)`, proved
  axiom-free modulo the energy hypothesis as `product_lower_of_mult_energy`).
