# S18 Specification: Axiom-Free Proof of `8 ∣ r4Count n`

**Author**: researcher-4 (S18 spec, 2026-05-11)
**Status**: analysis-only spec; companion to S17 (Part 26, PR #17677,
merged) which set up the `sigmaStar_uniqueness_from_canonical_hypotheses`
target.
**Goal**: produce an axiom-free proof of `8 ∣ r4Count n` for all `n > 0`,
casting `axiom jacobi_r4_formula` into S17's canonical form via the
identity `r4Count = 8 · (r4Count / 8) = 8 · sigmaStar = jacobiR4`.

## 1. Why S18 matters

S17's Part 26 reduced the open axiom `jacobi_r4_formula` to a clean
canonical multiplicative-arithmetic form:

> Any function `g : ℕ → ℕ` satisfying
> * `(Hodd)` `g n = σ n` for `¬ 2 ∣ n`
> * `(HtwoPow)` `g (2^k) = 3` for `k ≥ 1`
> * `(Hmul)` `g (m·n) = g m · g n` for coprime `m, n > 0`
>
> equals `sigmaStar` on every positive `n`.

To discharge `axiom jacobi_r4_formula` axiom-free, it suffices to prove
that `r4Count n / 8` satisfies these three hypotheses. Each of the three
pieces is realisable from classical 4-square-symmetry arguments, but
**all three depend on the prerequisite divisibility `8 ∣ r4Count n`**
without which `r4Count n / 8` is not arithmetically meaningful.

This spec decomposes that prerequisite into concrete sublemmas with
Mathlib API references.

## 2. Top-level statement

```lean
/-- **8 ∣ r4Count(n) for n > 0** (axiom-free, S18 target).

    The number of integer 4-tuples (a, b, c, d) ∈ ℤ⁴ with
    a² + b² + c² + d² = n is divisible by 8 for every positive n.
    The factor of 8 arises from the action of (ℤ/2)³ on solutions
    by independent sign flips on three of the four coordinates. -/
theorem eight_dvd_r4Count_axiom_free {n : ℕ} (hn : 0 < n) :
    8 ∣ r4Count n
```

The current file (Part 5, line 1461) has `eight_dvd_r4Count` which
chains through `axiom jacobi_r4_formula` — this S18 deliverable would
provide an axiom-free alternative.

## 3. Strategy: (ℤ/2)³ free action by sign flips

For `n > 0`, every solution `(a, b, c, d)` has at least one nonzero
coordinate. The naïve "sign-flip the first nonzero coordinate" approach
is awkward to formalise because the choice of "first nonzero" varies.

A cleaner approach: pick **three of the four coordinates** and act by
independent sign flips on those three. For `n > 0`, this action turns
out to be free — the orbit of every solution has size exactly 8 — but
the freeness depends on a subtle case analysis.

### 3.1 Why "three of four" works

Consider the action of `G := (ℤ/2)³` on `ℤ⁴`:

```
σ_b (a, b, c, d) := (a, -b, c, d)
σ_c (a, b, c, d) := (a, b, -c, d)
σ_d (a, b, c, d) := (a, b, c, -d)
```

These three commute and generate `G` of order 8. The orbit of
`(a, b, c, d)` under `G` has size `2^k` where
`k = #{x ∈ {b, c, d} | x ≠ 0}`.

For `n > 0`, we **don't** automatically have `b, c, d` all nonzero —
e.g., `(a, b, c, d) = (1, 0, 0, 0)` is a solution to `a² + b² + c² + d² = 1`
and its `G`-orbit has size only 1. So the naïve `G` does not act freely.

### 3.2 The fix: alternating sign-flip + permutation action

The 8-fold symmetry of `r4Count n` for `n > 0` is more subtly realised:
it is the orbit of the action of the **Weyl group of B₄ restricted to
the 8-element diagonal subgroup**, or equivalently, the action of the
following 8-element group `W ⊆ Sym(ℤ⁴)`:

```
W = ⟨ τ : (a, b, c, d) ↦ (-a, b, c, d) ⟩
  ⋊ ⟨ ρ : (a, b, c, d) ↦ (b, a, d, c) ⟩  (transposition (1 2)(3 4))
  ⋊ ⟨ ν : (a, b, c, d) ↦ (c, d, a, b) ⟩  (transposition (1 3)(2 4))
```

But analysing this presentation in Lean is more painful than necessary.
The classical algebraic-combinatorics route is cleaner.

### 3.3 Recommended route: pair-and-double via `(±·, ±·)` symmetry on (a, b)

The cleanest formalisation route uses two **commuting** sign-flip
actions on coordinate **pairs**:

* `α : (a, b, c, d) ↦ (-a, -b, c, d)` (flip first pair)
* `β : (a, b, c, d) ↦ (a, b, -c, -d)` (flip second pair)
* `γ : (a, b, c, d) ↦ (-a, b, -c, d)` (flip "diagonal" pair)

These generate a Klein 4-group `V₄ ⊆ G`, of order 4, **not** 8. So this
gives only `4 ∣ r4Count n`, not `8 ∣ r4Count n`. We need an additional
factor.

### 3.4 The cleanest known route: r4Count as orbit-summed Finset.card

The version that formalises smoothly is:

1. **Reformulate** `r4Count n = (Finset.Icc (-(n : ℤ)) n).card⁴`-filter, on
   the 4-tuples summing to `n` (Sublemma 3.1 below).
2. **Define** the involution `σ : (a, b, c, d) ↦ (-a, -b, -c, -d)` on
   the solution set (Sublemma 3.2). For `n > 0`, no fixed points
   ((0, 0, 0, 0) is not a solution to `n > 0`).
3. **Define** the involution `τ : (a, b, c, d) ↦ (b, -a, d, -c)` on the
   solution set (Sublemma 3.3). This is order-4, satisfying `τ² = σ`.
4. **Combine**: `⟨τ⟩` is a cyclic subgroup of `Sym(solutions)` of
   order 4. Its orbits on `solutions` have size dividing 4. Sublemma 3.4:
   for `n > 0`, no orbit has size 1 (because that would require `τ x = x`
   ⇒ `(a, b, c, d) = (b, -a, d, -c)` ⇒ `a = b`, `b = -a`, etc., forcing
   `a = b = 0`, hence `(a, b, c, d) = (0, 0, c, d)` with `c² + d² = n`;
   then `τ (0, 0, c, d) = (0, 0, d, -c)` so `c = d = 0` too, contradicting
   `n > 0`). So every orbit has size 2 or 4.
5. **Add a fifth involution** `υ : (a, b, c, d) ↦ (a, b, -c, -d)`
   commuting with `τ` (Sublemma 3.5), with `υ² = id`, `υτυ = τ⁻¹`. This
   makes `⟨τ, υ⟩` a dihedral group `D₄` of order 8.
6. **Show** the `D₄` action is free on solutions for `n > 0` (Sublemma
   3.6) — combining the τ-fixedness analysis (Sublemma 3.4) with the
   υ-fixedness analysis (`υ x = x` ⇒ `c = d = 0`).
7. **Conclude** via `Finset.card_orbit_dvd_card_of_freeAction`
   (Mathlib's standard orbit-divides-cardinality lemma).

This is ~250-300 lines of Lean. The bottleneck is **Sublemma 3.1** —
reformulating `r4Count` from `foldl` to `Finset.card`. The other
sublemmas are mechanical.

## 4. Sublemma decomposition

### Sublemma 3.1: r4Count as a Finset.card

```lean
private lemma r4Count_eq_finset_card (n : ℕ) :
    r4Count n =
    ((Finset.Icc (-(n : ℤ)) n).product
      ((Finset.Icc (-(n : ℤ)) n).product
        ((Finset.Icc (-(n : ℤ)) n).product (Finset.Icc (-(n : ℤ)) n)))).filter
      (fun ⟨a, b, c, d⟩ => a^2 + b^2 + c^2 + d^2 = (n : ℤ)) |>.card
```

**Proof idea**: induction on the foldl's `R := shiftedRange n`, transporting
the `if-then-else` accumulator into a `Finset.filter` argument. Or
equivalently, prove `R.toFinset = Finset.Icc (-(n : ℤ)) n` first, then
chain three rounds of `List.foldl_eq_finset_filter_card` (a standard
Mathlib induction).

**Mathlib API needed**: `List.foldl_succ`, `Finset.filter_filter`,
`Finset.card_filter`, `Multiset.toFinset_eq_iff_nodup`.

**Difficulty**: ~80 lines (the bottleneck of S18).

### Sublemma 3.2: The negation involution σ

```lean
private def negAll : (ℤ × ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ × ℤ) :=
  fun ⟨a, b, c, d⟩ => (-a, -b, -c, -d)

private lemma negAll_involutive : Function.Involutive negAll := by
  intro ⟨a, b, c, d⟩; simp [negAll]

private lemma negAll_preserves_sum : ∀ x : ℤ × ℤ × ℤ × ℤ,
    (negAll x).1^2 + (negAll x).2.1^2 + (negAll x).2.2.1^2 + (negAll x).2.2.2^2 =
    x.1^2 + x.2.1^2 + x.2.2.1^2 + x.2.2.2^2 := by
  intro ⟨a, b, c, d⟩; simp [negAll]; ring
```

**Difficulty**: ~10 lines (mechanical).

### Sublemma 3.3: The τ involution

```lean
private def τ : (ℤ × ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ × ℤ) :=
  fun ⟨a, b, c, d⟩ => (b, -a, d, -c)

private lemma τ_sq : τ ∘ τ = negAll := by
  funext ⟨a, b, c, d⟩; simp [τ, negAll]; ring_nf

private lemma τ_preserves_sum : ∀ x : ℤ × ℤ × ℤ × ℤ,
    (τ x).1^2 + (τ x).2.1^2 + (τ x).2.2.1^2 + (τ x).2.2.2^2 =
    x.1^2 + x.2.1^2 + x.2.2.1^2 + x.2.2.2^2 := by
  intro ⟨a, b, c, d⟩; simp [τ]; ring
```

**Difficulty**: ~15 lines.

### Sublemma 3.4: τ-fixedness implies all-zero on solutions

```lean
private lemma τ_fix_iff_zero {x : ℤ × ℤ × ℤ × ℤ} :
    τ x = x ↔ x = (0, 0, 0, 0) := by
  constructor
  · intro hτ
    have ⟨a, b, c, d⟩ := x
    simp [τ, Prod.mk.injEq] at hτ
    obtain ⟨hab, hba, hcd, hdc⟩ := hτ
    -- From b = a and -a = b, we get a = -a, so 2a = 0, so a = 0; similarly b
    have ha : a = 0 := by linarith [hba.symm ▸ hab]
    have hb : b = 0 := by rw [hab]; exact ha
    have hc : c = 0 := by linarith [hdc.symm ▸ hcd]
    have hd : d = 0 := by rw [hcd]; exact hc
    simp [ha, hb, hc, hd]
  · intro h; subst h; simp [τ]
```

**Difficulty**: ~20 lines.

### Sublemma 3.5: The υ involution and (τ, υ) commutation

```lean
private def υ : (ℤ × ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ × ℤ) :=
  fun ⟨a, b, c, d⟩ => (a, b, -c, -d)

private lemma υ_involutive : Function.Involutive υ := by ...

private lemma υτυ_eq_τinv : ∀ x, υ (τ (υ x)) = (negAll ∘ τ) x := by ...

private lemma υ_preserves_sum : ∀ x, ... := by ...
```

**Difficulty**: ~30 lines.

### Sublemma 3.6: D₄ acts freely on the solution set for n > 0

The 8 elements of `D₄` are `{id, τ, τ², τ³, υ, τυ, τ²υ, τ³υ}`. We need
to show none of them (except `id`) fixes any solution to
`a² + b² + c² + d² = n` for `n > 0`.

* `id`: fixed-point-free is vacuous.
* `τ`: Sublemma 3.4 says `τ x = x ⇒ x = 0 ⇒ n = 0`, contradicting `n > 0`.
* `τ² = negAll`: `negAll x = x ⇒ 2x = 0 ⇒ x = 0 ⇒ n = 0`.
* `τ³ = negAll ∘ τ`: similar to τ.
* `υ`: `υ x = x ⇒ (c, d) = (-c, -d) ⇒ c = d = 0`. So `x = (a, b, 0, 0)`
  with `a² + b² = n > 0`. But then `τ (a, b, 0, 0) = (b, -a, 0, 0)` and
  the τ-orbit of x has size at least 2 if `(a, b) ≠ (0, 0)`, so x's
  D₄-orbit doesn't reduce; we still need `υ ∘ x = x` which is the
  current case.

  Wait — the D₄-action freeness is the assertion that EVERY non-identity
  element acts fixed-point-free. For `υ`, this means showing
  `υ x ≠ x` for every solution x. But on `x = (a, b, 0, 0)` with
  `(a, b) ≠ (0, 0)`, indeed `υ x = (a, b, 0, 0) = x` — so υ DOES fix x!

  This means the D₄-action is **NOT free** on the full solution set;
  the route as stated in §3.4 is flawed.

### 3.7 Correction: D₄ acts on solutions, but not freely; need orbit decomposition

The (mistaken) "every orbit has size 8" claim of §3.4 step 6 fails on
solutions with two-zero coordinates. The corrected statement:

* For `n > 0`, the D₄-orbit of `(a, b, c, d)` has size:
  * 8 if all four coordinates are distinct in absolute value AND non-zero;
  * 4 if exactly two are zero (e.g. `(a, b, 0, 0)` orbit
    `{(a, b, 0, 0), (b, -a, 0, 0), (-a, -b, 0, 0), (-b, a, 0, 0)}`);
  * 8 in all other cases including all four nonzero with repeated absolute
    values.

The orbit of `(a, b, 0, 0)` for `(a, b) ≠ (0, 0)` has size 4, not 8. So
the orbit-summed sum gives only `4 ∣ r4Count n`, not `8 ∣ r4Count n`.

**Conclusion**: this 8-element group action route does not directly
yield divisibility by 8. The actual `8 ∣ r4Count n` requires either:
- a 16-element group action with orbits all of size dividing 16, AND a
  parity argument forcing orbit sizes to be at least 8 (intricate); OR
- the classical Jacobi-style proof via theta functions and Eisenstein
  series (i.e., S13's modular-form route — currently axiomatised); OR
- a more clever direct combinatorial argument.

### 3.8 The clean direct route: pair-up via a 16-element group

The 16-element group `(ℤ/2)⁴` acts on `ℤ⁴` by independent sign flips on
all four coordinates. The orbit of `(a, b, c, d)` has size `2^k` where
`k = |{i | xᵢ ≠ 0}|`.

For `n > 0`, `k ≥ 1`. The orbit sizes are `2, 4, 8, 16` for
`k = 1, 2, 3, 4` respectively.

**This action gives `2 ∣ r4Count n` immediately** (every orbit has size
`≥ 2`), but not `8 ∣`. The 8-divisibility requires an additional
permutation symmetry, and the cleanest route from there is the S₄
permutation action.

The S₄ permutation action multiplies the symmetry group's order by `4!
= 24`, giving a `(ℤ/2)⁴ ⋊ S₄`-action of order 384 on `ℤ⁴`. Orbit sizes
on solutions are bounded by `384`, but the precise sizes depend on the
multiset structure of `{|a|, |b|, |c|, |d|}`.

For `n > 0`, the smallest orbit size in this action equals 8 — achieved
by orbits of `(a, 0, 0, 0)` (4 positions × 2 signs = 8). All other orbit
sizes are multiples of 8. **This gives `8 ∣ r4Count n` directly via
orbit decomposition**.

The Lean-level proof requires:

1. Defining the 384-element group action explicitly (or as a quotient of
   `Sym(ℤ⁴)` by the kernel).
2. Computing orbit sizes case by case based on the multiset structure.
3. Showing all orbit sizes are divisible by 8.

This is substantial — **~400 lines** of Lean, and the case analysis is
delicate. A more economical route exists if Mathlib has a
"semi-direct-product action" + "orbit cardinality" packaged formalism;
the relevant Mathlib API is `MulAction.orbit_card_dvd_of_finite`
(currently in `Mathlib.GroupTheory.GroupAction.Basic`).

## 5. Estimated total length

* Sublemma 3.1 (Finset.card reformulation): ~80 lines.
* (ℤ/2)⁴ ⋊ S₄ action setup: ~80 lines.
* Orbit-cardinality dvd 8 case analysis (4 cases by multiset structure):
  ~150 lines.
* Final divisibility theorem: ~30 lines.
* Cross-validation `example`s: ~30 lines.

**Total**: ~370 lines. Single-session feasible, but tight. Recommended
to split as:

* **S18a**: Sublemma 3.1 only (the foldl ↔ Finset.card bridge). ~80
  lines, standalone.
* **S18b**: 384-element group action setup + orbit cardinality lemmas.
  ~150 lines.
* **S18c**: Case analysis + final `8 ∣ r4Count n`. ~150 lines.

Each `S18*` PR is build-checkable independently.

## 6. Why we don't ship S18 in the same session as this spec

The current `FourSquareDistributionOQ01.lean` is 2219 lines after the
S17 merge (PR #17677, 2026-05-11 23:59Z). Adding 400 lines without a
mid-session build verification creates a high-risk single PR. Splitting
across three follow-up sessions — each with build verification —
matches the prior incremental pattern (S11.alt → S15 → S16 → S17).

Additionally, the `(ℤ/2)⁴ ⋊ S₄` group-action machinery has no prior
existence in this file, so the **first** session should stage Sublemma
3.1 (the `foldl ↔ Finset.card` bridge) as a standalone before
introducing group-theoretic machinery.

## 7. Mathlib API audit

* `Finset.Icc (-(n : ℤ)) n`: `Mathlib.Order.LocallyFinite` — exists.
* `Finset.product`: `Mathlib.Data.Finset.Prod` — exists.
* `Finset.filter`: `Mathlib.Data.Finset.Filter` — exists.
* `Finset.card_filter_eq_card_of_eq_iff`: `Mathlib.Data.Finset.Card` — exists.
* `MulAction.orbit_card_dvd_of_finite`:
  `Mathlib.GroupTheory.GroupAction.Quotient` — exists.
* `Finset.card_filter_eq_sum_card_orbits`: existence in v4.26.0
  TBD; if absent, derivable from `Quotient.outEquiv` over the
  action's orbit space.
* `Equiv.Perm.cycleOf`, `Equiv.Perm.cycleOf_card_dvd_orderOf`:
  `Mathlib.GroupTheory.Perm.Cycle.Basic` — exists.

No new Mathlib upstream contributions needed.

## 8. Companion to S17

Once `8 ∣ r4Count n` is proved axiom-free (via S18a/b/c), the closure
of `axiom jacobi_r4_formula` becomes:

1. Define `r4CountDiv8 : ℕ → ℕ := fun n => r4Count n / 8`.
2. Prove `r4CountDiv8` satisfies S17's three canonical hypotheses:
   * `(Hodd)`: `r4CountDiv8 n = σ n` for `¬ 2 ∣ n` — requires the
     direct combinatorial computation `r4Count n = 8 σ(n)` for odd n.
     **Open**.
   * `(HtwoPow)`: `r4CountDiv8 (2^k) = 3` for `k ≥ 1` — requires
     `r4Count (2^k) = 24`. **Open** (proven for k = 1, 2, 3 via
     `native_decide` on the brute-force count; general k unknown
     except via the modular-form route).
   * `(Hmul)`: multiplicativity at coprime arguments — requires
     `r4Count (m·n) = r4Count m · r4Count n / 8` for coprime
     `m, n > 0`. **Open**.
3. Apply `sigmaStar_uniqueness_from_canonical_hypotheses r4CountDiv8` to
   conclude `r4CountDiv8 = sigmaStar` on positive `n`.
4. Multiply by 8: `r4Count n = 8 · sigmaStar n = jacobiR4 n`.

Each of the three hypotheses is independently a substantial proof — the
modular-form proof is the only known route for the `(Hodd)` and
`(HtwoPow)` ∀-statements without invoking `axiom jacobi_r4_formula`.
The S13 spec doc (`s13-modular-form-atomic-decomposition.md`) covers
the analytic route.

## 9. Recommendation

**Do not ship S18 in a single session**. Stage as:

1. **S18a (this PR's natural follow-up)**: Sublemma 3.1 only. ~80 lines,
   pure structural reformulation. No group theory.
2. **S18b**: `(ℤ/2)⁴ ⋊ S₄` action + orbit cardinality. ~150 lines.
3. **S18c**: Case analysis + final theorem. ~150 lines.

Total work surface: ~370 lines distributed over three sessions. Each
session is independently build-checkable and reviewable.

If the modular-form route (S13 spec) is closed first, S18 becomes
unnecessary — the Eisenstein E₂ identification gives `r4Count n = 8 σ*(n)`
directly, and `8 ∣ r4Count n` is a corollary. So S18 is contingent on
the S13 route remaining inaccessible (currently the case: Mathlib lacks
the `EisensteinSeries.E2_qExpansion` API).

## Provenance

- **Spec authored**: researcher-4, 2026-05-11.
- **Companion files**:
  - `s13-modular-form-atomic-decomposition.md` (S13, 2026-05-08).
- **Triggering PR**: #17677 (S17 merge, 2026-05-11 23:59Z) — the
  merge surfaced S18 as the next natural axiom-free closure step.
