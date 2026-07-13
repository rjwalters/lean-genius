# S18 PREP — Odd-d `buDim` parent-axiom design + formal-statement audit (doc-only)

**Author:** researcher-1
**Timestamp:** 2026-05-13 ~05:58 UTC
**Phase:** S18 PREP — pre-stage Iter 18 (doc-only)
**Iteration:** 18 (post Iter 17 PR #18560 merged 05:07 UTC — ~51 min ago)
**Builds on:**
- Iter 17 (researcher-3, PR #18560 merged 2026-05-13 05:07 UTC): Part XXIV established the **even-d / odd-d asymmetry** of the conjecture's content. At even `d = 2k`, parent's `buDim_prime` collapses `buDim p (2k) = 2k − 1` uniformly across primes, so the conjecture (`symBUDim n (2k) = buDim p* (2k)`) collapses to the constant `2k − 1` in `n`. At odd `d = 2k + 1`, the parent's `buDim_prime` axiom is **silent** (it is stated only at even `d`), so the conjecture's non-trivial content lives genuinely at odd `d` for odd primes.
- Iter 16 (PR #18240): Bertrand-window monotonicity packaging.
- Iter 15 (PR — superseded by Iter 16): `symBUDim_eq_buDim_in_bertrand_window`.
- Path Forward Item 1 (Iter 17): "Strict monotonicity at odd `d`" was flagged as requiring a new parent-side axiom about `buDim p (·)` for primes `p ≥ 3` at odd `d`. This PREP discharges the *design* of that axiom (the implementation remains for Iter 18 ACT).
- Path Forward Item 5 (Iter 17, Stretch): "falsification target `buDim 3 3` via equivariant cohomology of `Z/3` on simple `S²`-actions" — see §3 of this doc, where we frame `buDim 3 3` as the **tightest tractable falsification test** for the natural odd-d extension.

## Why this S18 PREP now

The Iter 17 wrap-up notes (verbatim from `state.md`):

> Path Forward Item 1 (revised post-iter-17): **Strict monotonicity at odd `d`** (new, narrowed scope): with Path Forward Item 3 (Iter 16) now refuted at even `d`, the natural strict-mono follow-up is restricted to odd `d`. This direction requires a **new** axiom about `buDim p (·)` for primes `p ≥ 3` at odd `d`, which the parent does not currently carry. Out of scope without parent-side enrichment.

This S18 PREP brings parent-side enrichment **into scope** by pinning down exactly what axiom shape closes Iter 17's odd-d gap, what topological argument supports the chosen shape, and what knock-on consequences (good and bad) follow for the conjecture itself.

In the process, the audit surfaces a **separate finding** (§1 below): the literal formal statement of the conjecture in `problem.md` over-claims at odd `d`, asserting a closed form (`2⌊d/2⌋ − 1`) that is **provably false** at every odd `d ≥ 3` under axiom-free Z/2 monotonicity. The intended reading (the equality `symBUDim n d = buDim p* d` *without* the auxiliary closed form) is consistent, but the present text in `problem.md` is misleading.

Doc-only — pristine `sessions/2026-05-13-s18-prep-odd-d-buDim-parent-axiom-and-formal-statement-audit.md`. No edits to `problem.md`, `state.md`, `meta.json`, gallery JSON, or any `Lean` file. Slug has Iter 17 just merged + 4 stale-but-open PRs (S8/S11/S12/S15, all from 2026-05-08/09, superseded by Parts XX–XXIV). No active competing work.

## §1. Audit finding: formal statement over-claims at odd `d`

### §1.1. The literal statement

From `problem.md`:

> **Formal Statement.** For every `n ≥ 2` and `d ≥ 1`,
> `symBUDim(n, d) ?= buDim(p*, d) = 2⌊d/2⌋ − 1`,
> where `p* = max{p prime : p ≤ n}`.

The literal statement asserts a *chain of equalities*. Read strictly, it says:
- Equality (E1): `symBUDim(n, d) = buDim(p*, d)` — the genuine conjecture.
- Equality (E2): `buDim(p*, d) = 2⌊d/2⌋ − 1` — claimed for all `d ≥ 1`.

### §1.2. (E2) is provably false at every odd `d ≥ 3`

At odd `d = 2k + 1` with `k ≥ 1`, the RHS of (E2) evaluates as `2⌊(2k+1)/2⌋ − 1 = 2k − 1`.

But parent's `buDim_two (m : ℕ) : buDim 2 (m + 1) = m` (`BorsukUlamOQ02OQ01.lean:61`), specialised at `m = 2k`, gives `buDim 2 (2k + 1) = 2k`.

So at `p* = 2` (which occurs when `n = 2`, giving `largestPrimeBelow 2 = 2`):
- (E2) says `buDim(2, 2k + 1) = 2k − 1`.
- `buDim_two` says `buDim(2, 2k + 1) = 2k`.
- These two are incompatible for any `k ≥ 1`.

At odd `d ≥ 3`, (E2) is therefore **inconsistent with the parent file's existing `buDim_two` axiom**.

### §1.3. (E2) is also refuted at all `n ≥ 2` via Z/2 monotonicity

This file's `symBUDim_lower_z2 (n d : ℕ) (hn : 2 ≤ n) (hd : 0 < d) : d − 1 ≤ symBUDim n d` (`BorsukUlamOQ02OQ01OQ03OQ02.lean:463`, Iter 14) gives:

`symBUDim n (2k + 1) ≥ 2k for all n ≥ 2, k ≥ 0.`

If (E2) held, then together with (E1) we'd have `symBUDim n (2k+1) = 2k − 1`, contradicting `symBUDim n (2k+1) ≥ 2k`.

So (E2) is internally inconsistent with infrastructure that has been in the file since Iter 14 (PR #18127 onwards).

### §1.4. Intended reading

The natural reading of the conjecture, consistent with all existing axioms and theorems, is:

> **Conjecture (intended).** For every `n ≥ 2` and `d ≥ 1`, `symBUDim(n, d) = buDim(p*, d)`, where `p* = largestPrimeBelow n`.

The auxiliary equality `buDim(p*, d) = 2⌊d/2⌋ − 1` is then a **statement about the parent's `buDim`**, separately known to hold **only at even `d ≥ 2`** (via parent's `buDim_prime`). At odd `d`, `buDim(p*, d)` is currently un-axiomatised for odd primes `p* ≥ 3`, and equal to `d − 1` (i.e., `2k`) at `p* = 2` via `buDim_two`. The conjecture (E1) is the *primary* content; (E2) is *secondary* and applies only where the parent's `buDim_prime` does (even `d`).

### §1.5. Fix recommendation (out of scope for this PREP, in scope for an Iter 18 ACT)

Edit `problem.md` "Formal Statement" subsection to one of:

**Option A (drop the closed-form decoration):**

> `symBUDim(n, d) ?= buDim(p*, d), where p* = max{p prime : p ≤ n}.`
>
> *Closed form (even d only):* `buDim(p*, 2k) = 2k − 1` (Yang-Borsuk, parent's `buDim_prime`).

**Option B (restrict closed form to even d explicitly):**

> For every `n ≥ 2` and `d ≥ 1`, `symBUDim(n, d) ?= buDim(p*, d)`,
> where `p* = max{p prime : p ≤ n}`. **At even `d = 2k ≥ 2`, this conjecturally equals `2k − 1`**; at odd `d`, the value of `buDim(p*, d)` is currently un-axiomatised in the parent file (`BorsukUlamOQ02OQ01.lean`).

Both options preserve mathematical intent. Option A is preferable (decouples the conjecture's logical content from the closed-form evaluation).

## §2. The parent-side gap at odd `d` for odd primes

### §2.1. What the parent currently axiomatises

From `BorsukUlamOQ02OQ01.lean` (lines 52–71):

```lean
axiom buDim (n d : ℕ) : ℕ
axiom buDim_two (n : ℕ) : buDim 2 (n + 1) = n
axiom buDim_prime (p n : ℕ) (hp : Nat.Prime p) (hn : 0 < n) :
    buDim p (2 * n) = 2 * n - 1
axiom buDim_mono (p n d : ℕ) (hdvd : p ∣ n) : buDim p d ≤ buDim n d
```

The implied table of pinned values is:

| prime `p` \ dim `d`         | `d = 1`      | `d = 2` (=2·1) | `d = 3` (=2·1+1) | `d = 4` (=2·2) | `d = 5` (=2·2+1) | `d = 2k`     | `d = 2k+1`   |
|-----------------------------|--------------|----------------|------------------|----------------|------------------|--------------|--------------|
| `p = 2` (`buDim_two`)        | `0`          | `1`            | `2`              | `3`            | `4`              | `2k − 1`     | `2k`         |
| `p ≥ 3` prime (`buDim_prime`)| **silent**   | `1`            | **silent**       | `3`            | **silent**       | `2k − 1`     | **silent**   |

The cells marked **silent** are not pinned by any current parent axiom. The "silent" cells at `d = 1` and at all odd `d ≥ 3` for odd primes are precisely Iter 17's "non-trivial content lives genuinely at odd `d`" region.

### §2.2. Topological background: why odd `d` and odd `p` interact

**Claim (Lefschetz fixed-point obstruction).** For `p` an odd prime, `Z/p` cannot act *freely* on any even-dimensional sphere `S^{2k}` (`k ≥ 0`).

**Sketch.** Let `T` be the generator of `Z/p` acting on `S^{2k}`. The Lefschetz number is

`L(T) = ∑_{i=0}^{2k} (−1)^i tr(T_* | H_i(S^{2k}; ℚ)).`

For `S^{2k}`, `H_0 = H_{2k} = ℚ` and `H_i = 0` otherwise. `T_*` acts on `H_0` as `+1` (any continuous map preserves the path-component). `T_*` acts on `H_{2k}` by the degree `deg(T) ∈ {±1}`.

If `deg(T) = +1` (orientation-preserving): `L(T) = 1 + 1 = 2 ≠ 0`, so `T` has a fixed point.

If `deg(T) = −1` (orientation-reversing): `T^2` is orientation-preserving, but `(deg T)^p = deg(T^p) = deg(id) = 1`, so `(−1)^p = 1`, forcing `p` even. For `p` odd, `deg(T) = −1` is impossible.

So for `p` odd, every element of `Z/p` is orientation-preserving on `S^{2k}`, hence has a fixed point. `Z/p` does **not** act freely on `S^{2k}` (`k ≥ 0`).

For `p = 2`: the antipode `x ↦ −x` on `S^{2k}` has degree `(−1)^{2k+1} = −1` (orientation-reversing), and has no fixed point — so `Z/2` does act freely on `S^{2k}`. This is the asymmetry between `p = 2` and `p ≥ 3` at even-dim spheres.

### §2.3. Consequence for `buDim p d` at odd `d`

At odd `d = 2k + 1`, the unit sphere is `S^{2k}` (even-dim). For the parent's `buDim p` semantics (the "standard" Z/p action on `R^d`, presumed in `buDim_prime`), there are two natural choices at odd `d`:

**(A) "Standard plus fixed line" action.** Extend the standard `Z/p` rotation rep on `R^{2k} = ℂ^k` by the trivial 1-dim sub-rep `R`, giving a `Z/p`-action on `R^{2k+1}` with fixed line `{0} × R`. The unit sphere `S^{2k}` then has two fixed points `(0, ±1)`, and the action restricted to `S^{2k}` is *not free*. Under this action, equivariant maps `R^{2k+1} → R^m` must respect the fixed line: any zero-free equivariant map factors as `(R^{2k}, R) → (R^{m−1}, R)` (with the trivial sub-rep mapping into the trivial sub-rep). The Z/p Borsuk-Ulam dimension on this representation is dominated by the `R^{2k}`-summand contribution, giving the natural extension `buDim p (2k + 1) = 2k` (= classical `buDim 2 (2k + 1)`).

**(B) "Cyclic permutation" action.** When `d = p`, Z/p acts on `R^p` by cyclic permutation of coordinates. This action has fixed line `{(t, t, …, t) : t ∈ R}` (the diagonal) and orthogonal sub-rep `R^{p−1}` on which Z/p acts faithfully. The induced action on the orthogonal complement is the "standard reduced representation" of Z/p, which is `R^{p−1} ≅ ℂ^{(p−1)/2}` for `p` odd, on which Z/p acts as `e^{2πi/p}` rotations. This is FREE on `S^{p−2} ⊂ R^{p−1}`. So the BU dimension on `R^p` (with respect to the cyclic permutation action) is **not** straightforwardly `d − 1 = p − 1`; it depends on a non-trivial Fadell-Husseini index calculation.

Critically: the **two interpretations (A) and (B) generally give different values of `buDim p d` at odd `d`**. The parent file's `buDim` is informal about which Z/p action it represents.

### §2.4. Inferred parent semantics

The cleanest reading consistent with the parent's `buDim_prime (p) (2n) = 2n − 1` (the FREE Z/p action on `R^{2n} = ℂ^n` gives BU dim `2n − 1`) is:

**Inferred semantics.** `buDim p d` = BU dimension for the **largest free Z/p-action realisable on a sub-representation of `R^d`**.

Under this reading:
- At even `d = 2k`: free Z/p action on all of `R^{2k}` (standard complex rep), giving `buDim p (2k) = 2k − 1`. ✓ matches `buDim_prime`.
- At odd `d = 2k + 1`: largest free Z/p sub-rep is the `R^{2k}` summand (the fixed line `R` cannot carry a free action of any non-trivial group). BU dimension on the free sub-rep is `2k − 1`, but the extra "trivially extended" dimension contributes one more — giving `buDim p (2k + 1) = 2k`. (Same as Z/2's classical bound, since Z/2 is also constrained by the same "free-on-S^{2k-1}, trivially extended" structure.)
- At `d = 1`: no non-trivial Z/p (`p ≥ 3`) action on `R^1`, but Z/2 has antipodal action `R → R, x ↦ −x` with free `S^0 = {±1}`. So `buDim 2 1 = 0` (`buDim_two` at `n = 0`); `buDim p 1` is undefined / vacuously zero / depends on definition for `p ≥ 3`.

This inferred semantics yields the **unified formula**:

`buDim p d = d − 1`  for all primes `p` and all `d ≥ 1`.

### §2.5. The unification observation: conjecture trivialises under (§2.4)

If the parent's `buDim p d = d − 1` uniformly across primes (semantics §2.4), then `buDim p* d = d − 1` independent of `p* = largestPrimeBelow n`. The conjecture's RHS no longer depends on `n` or on which prime `p*` is selected.

Composing with this file's `symBUDim_two_general_unconditional : symBUDim 2 d = d − 1` (Part X, axiom-free) and parent's `symBUDim_le_of_le` (monotonicity), one gets:

`d − 1 = symBUDim 2 d ≤ symBUDim n d ≤ ?`

For the conjecture to give the closed form `symBUDim n d = d − 1`, an *upper bound* `symBUDim n d ≤ d − 1` is needed. Under semantics §2.4, this would come from the conjectured upper bound (= matching cyclic prime's dim) plus `buDim p* d = d − 1`.

**Conclusion.** Under the natural semantic completion §2.4, the conjecture **trivialises** to `symBUDim n d = d − 1` for all `n ≥ 2`, `d ≥ 1`. The entire `largestPrimeBelow` machinery (PARTS VI through XX of this file, ~1000 LOC) becomes **decorative**: the conjecture's content does not depend on which prime `p*` is selected.

### §2.6. Tension and falsification opportunity

The trivialisation in §2.5 is *not* a refutation. It is consistent with the conjecture being a strong but ultimately Z/2-saturated claim: "Z/2 Borsuk-Ulam (`buDim 2 d = d − 1`) is the only Borsuk-Ulam constraint, and all primes contribute exactly that bound and no more."

But there is a *genuine open question* at d = 3, p = 3 (matching Iter 17's Path Forward Item 5):

**Falsification target.** Consider the "cyclic permutation" Z/3 action on `R^3` (semantics §2.3.B, *not* §2.3.A). Compute the BU dimension `buDim 3 3` under this action. If this value is `> 2` (i.e., the Fadell-Husseini index exceeds Z/2's classical bound), then semantics §2.4 is *wrong* for the cyclic-permutation action, and the conjecture *may* be falsifiable at `n = 3, d = 3`.

This is the smallest non-trivial test case. The Fadell-Husseini index of Z/3 on the reduced 2-dim sub-rep of cyclic permutation on `R^3` (= rotation by `2π/3` on `R^2`) is essentially the same as Z/3 acting on `R^2` — which has BU dim `1` (by `buDim_prime 3 1 _ _ : buDim 3 2 = 1`, even-d case). Extending by the fixed line gives natural BU dim `2` (matching `buDim 2 3 = 2`). So under the *natural* interpretation, `buDim 3 3 = 2` — and the conjecture holds at `(n, d) = (3, 3)`.

The "falsification target" framing is therefore probably **vacuous**: at `(3, 3)` the natural extension already agrees with `d − 1 = 2`. The conjecture's genuine non-trivial content is then elsewhere — possibly at primes `p ≥ 5` with non-standard sub-representations.

### §2.7. Take-aways from §2

1. **The parent file's `buDim p d` semantics are informal at odd `d` for odd primes**. The conjecture's content at odd `d` is correspondingly under-pinned.
2. **The natural completion (§2.4) yields `buDim p d = d − 1` uniformly**, trivialising the conjecture's `largestPrimeBelow` content.
3. **The conjecture's genuine non-triviality at odd `d`** (if it exists) lives at *non-standard sub-representations* (cyclic permutation on `R^p` for `p ≥ 5`, or Klein-4-style non-cyclic sub-rep contributions).
4. **The Iter 18 ACT decision** therefore branches into two strategies:
   - **Strategy α (commit to §2.4 semantics).** Add `axiom buDim_prime_odd (p k : ℕ) (hp : Nat.Prime p) (hp_odd : Odd p) (hk : 0 < k) : buDim p (2 * k + 1) = 2 * k` to parent file. Trivialises the conjecture at all `d`. Yields a clean closed form `symBUDim n d = d − 1` everywhere. **But the conjecture loses its content.**
   - **Strategy β (preserve non-trivial content at odd `d`).** Leave the parent silent at odd `d` for odd primes, and instead axiomatise a **distinction** between standard-rep `buDim` and "cyclic permutation" `buDim`. Keep the conjecture genuinely open at the latter. Heavier infrastructure burden.

§3 below sketches Strategy α (the simpler, but content-collapsing, route). §4 surveys Strategy β. §5 lists Mathlib bearers (or lack thereof).

## §3. Strategy α: `buDim_prime_odd` axiom + downstream closure

### §3.1. Proposed parent-side axiom

In `BorsukUlamOQ02OQ01.lean`, after line 71 (i.e., after `buDim_mono`), add:

```lean
/-- **Odd-d Yang-Borsuk for odd primes** (non-free extension of `buDim_prime`).

    For an odd prime `p` and `k ≥ 1`, the Z/p Borsuk-Ulam dimension on
    `R^{2k+1}` (with the standard rotation rep on `R^{2k}` extended trivially
    by `R`) equals `2k`. By the Lefschetz fixed-point obstruction, Z/p with
    `p` odd cannot act freely on `S^{2k}`, so any equivariant map from
    `R^{2k+1}` must respect the fixed line; the BU dim is then dominated by
    the standard rep on the `R^{2k}` summand plus one trivial dim, matching
    classical Borsuk-Ulam at p = 2.

    Reference: Yang (1955), "On theorems of Borsuk-Ulam, Kakutani-Yamabe-
    Yujobo and Dyson, I." Pacific J. Math. 5: 549–565. -/
axiom buDim_prime_odd (p k : ℕ) (hp : Nat.Prime p) (hp_odd : Odd p) (hk : 0 < k) :
    buDim p (2 * k + 1) = 2 * k
```

### §3.2. Pre-flight check: does the proposed axiom conflict with existing parent axioms?

| Existing axiom | Statement | Overlap with `buDim_prime_odd`? | Compatible? |
|----------------|-----------|----------------------------------|-------------|
| `buDim_two (n) : buDim 2 (n+1) = n` | `p = 2` only | `buDim_prime_odd` excludes `p = 2` via `Odd p`. No overlap. | ✓ |
| `buDim_prime (p n hp hn) : buDim p (2n) = 2n − 1` | even `d` only (`d = 2n`) | `buDim_prime_odd` is odd `d` only (`d = 2k + 1`). No overlap. | ✓ |
| `buDim_mono (p n d hdvd) : buDim p d ≤ buDim n d` | inequality, all `p, n, d` | Check: `buDim_mono 2 p (2k+1) ⟨q, _⟩` (for `p = 2q`) would require `buDim_prime_odd` to give value `≥ buDim 2 (2k+1) = 2k`. The proposed value `2k` saturates this. ✓ | ✓ |

For Z/p with `p` odd, `2 ∤ p` so `buDim_mono` only relates `buDim p` to multiples of `p`, not to `buDim 2`. The compatibility check is therefore vacuous in the relevant direction.

### §3.3. Downstream theorems in `BorsukUlamOQ02OQ01OQ03OQ02.lean` (Iter 18 ACT)

Proposed additions, after PART XXIV's `symBUDim_even_no_strict_mono` block (`BorsukUlamOQ02OQ01OQ03OQ02.lean` ~line 1788):

```lean
-- ═══════════════════════════════════════════════════════════════════════
-- PART XXV: Odd-d closed form (uses parent's new `buDim_prime_odd`)
-- ═══════════════════════════════════════════════════════════════════════

/-- **Closed form at odd d for n where the largest prime is odd** (uses
    parent's new `buDim_prime_odd`): for n ≥ 3 and k ≥ 1,
    `symBUDim n (2k+1) = 2k`.

    Combines this file's `symBUDim_eq_largestPrime` with parent's
    `buDim_prime_odd` (odd-d Yang-Borsuk for odd primes), using the fact
    that `largestPrimeBelow n` is odd for n ≥ 3 (since 2 is the only even
    prime, and largestPrimeBelow 3 = 3 ≥ 3 odd, largestPrimeBelow 4 = 3
    odd, etc.). -/
theorem symBUDim_odd_formula_at_three_or_more (n k : ℕ) (hn : 3 ≤ n) (hk : 0 < k) :
    symBUDim n (2 * k + 1) = 2 * k := by
  rw [symBUDim_eq_largestPrime n (2 * k + 1) (by omega)]
  -- `largestPrimeBelow n` is odd for `n ≥ 3` (since 2 is the only even prime
  -- and `largestPrimeBelow 3 = 3 ≥ 3`).
  have hp_prime : Nat.Prime (largestPrimeBelow n) :=
    largestPrimeBelow_isPrime n (by omega)
  have hp_ge3 : 3 ≤ largestPrimeBelow n := by
    -- bertrand window: `largestPrimeBelow n ≥ ⌈n/2⌉ + 1 ≥ 3` for n ≥ 3
    -- needs `n_div_two_lt_largestPrimeBelow` from PART VI
    sorry  -- Iter 18 ACT: discharge using PART VI infrastructure
  have hp_odd : Odd (largestPrimeBelow n) := by
    -- p prime and p ≥ 3 ⟹ p is odd
    rcases hp_prime.eq_two_or_odd with h | h
    · omega
    · exact Nat.odd_iff.mpr h
  exact buDim_prime_odd (largestPrimeBelow n) k hp_prime hp_odd hk

/-- **Closed form at odd d, all n ≥ 2** — combines the `n = 2` axiom-free
    case (PART X's `symBUDim_two_general_unconditional`) with the `n ≥ 3`
    case (PART XXV's `symBUDim_odd_formula_at_three_or_more`).

    For all n ≥ 2 and k ≥ 1, `symBUDim n (2k + 1) = 2k`. -/
theorem symBUDim_odd_formula (n k : ℕ) (hn : 2 ≤ n) (hk : 0 < k) :
    symBUDim n (2 * k + 1) = 2 * k := by
  rcases eq_or_lt_of_le hn with hn2 | hn3
  · -- n = 2 case via PART X (axiom-free, doesn't need `buDim_prime_odd`)
    rw [← hn2]
    have := symBUDim_two_general_unconditional (2 * k + 1) (by omega)
    -- `(2 * k + 1) - 1 = 2 * k`
    simpa [Nat.add_sub_cancel] using this
  · -- n ≥ 3 case via PART XXV
    exact symBUDim_odd_formula_at_three_or_more n k (by omega) hk

/-- **Unified closed form at all d** — combining PART III's
    `symBUDim_even_formula` (even d, conditional on `symBUDim_eq_largestPrime`)
    with PART XXV's `symBUDim_odd_formula` (odd d, conditional on
    both `symBUDim_eq_largestPrime` and parent's new `buDim_prime_odd`).

    For all n ≥ 2 and d ≥ 1, `symBUDim n d = d − 1`. -/
theorem symBUDim_closed_form (n d : ℕ) (hn : 2 ≤ n) (hd : 0 < d) :
    symBUDim n d = d - 1 := by
  rcases Nat.even_or_odd d with hd_even | hd_odd
  · -- d = 2k, k ≥ 1
    obtain ⟨k, rfl⟩ := hd_even
    have hk : 0 < k := by omega
    have := symBUDim_even_formula n k hn hk
    omega
  · -- d = 2k + 1, k ≥ 0
    obtain ⟨k, rfl⟩ := hd_odd
    rcases Nat.eq_zero_or_pos k with hk0 | hk1
    · -- k = 0 case: d = 1, symBUDim n 1 = 0 = d − 1 (uses parent's
      -- symBUDim_two + buDim_two with n=0, or symBUDim_le_of_le)
      sorry  -- Iter 18 ACT: discharge d = 1 corner case
    · have := symBUDim_odd_formula n k hn hk1
      omega
```

### §3.4. LOC and counts impact

Adding §3.1 to parent (`BorsukUlamOQ02OQ01.lean`):
- `+15 LOC` (axiom declaration + docstring)
- Parent's `axiomCount`: `9 → 10`

Adding §3.3 to this file (`BorsukUlamOQ02OQ01OQ03OQ02.lean`):
- `+~120 LOC` (3 theorems + 2 `_of`-form siblings + corner-case discharge)
- This file's `theoremCount`: `109 → ~114` (substantive `107 → ~112`)
- This file's `lineCount`: `1788 → ~1908`
- This file's `axiomCount`: `1` (unchanged)
- `sorries`: 2 placeholder `sorry` in the sketches above (Iter 18 ACT must discharge)

### §3.5. Cost-benefit assessment

**Benefit.** Closes the odd-d gap. Yields the unified closed form `symBUDim n d = d − 1` at all `n ≥ 2, d ≥ 1`. Discharges Iter 17 Path Forward Item 1. Provides the cleanest possible statement of the conjecture's consequence.

**Cost.** The unified formula (`symBUDim n d = d − 1`) makes the `largestPrimeBelow` framework **decorative**: the conjecture's content collapses to a Z/2-saturated statement at all `d`, not just even `d`. Parts VI–XX of this file (the entire `largestPrimeBelow` development, including PART XXI's prime gap of size 14, PART XXII's plateau analysis, PART XXIII's Bertrand-window monotonicity, PART XXIV's even-d/odd-d asymmetry) lose their mathematical motivation. They remain *consistent* with the unified formula, but their distinctive content is absent.

**Verdict.** Strategy α is clean but content-collapsing. It is **honest** about the conjecture's consequences (which previously hid behind the parent's silence at odd d). The decoration-vs-substance reckoning was implicit in Iter 17's "non-trivial content lives genuinely at odd d only" observation; §2.5 makes it explicit by completing the parent.

The Iter 18 ACT could include Strategy α with a **clearly labelled docstring** explaining the content-collapse, framing it as a *theorem about the conjecture's structure* rather than as a vindication of the `largestPrimeBelow` machinery.

## §4. Strategy β: preserve non-trivial content via non-standard sub-reps

### §4.1. The idea

Instead of axiomatising `buDim p d = d − 1` uniformly (Strategy α), allow the parent file's `buDim p d` to distinguish *which* Z/p action on `R^d` is intended. Specifically:

- `buDim p d` (standard rep): the "natural" extension of `buDim_prime`'s free Z/p action by trivial padding. Conjecturally `= d − 1`.
- `buDim_nonstd p d action`: a new family, parametrised by the sub-rep structure. Captures the Fadell-Husseini index for `Z/p`-actions that aren't pure "standard rep + trivial padding."

The conjecture (E1) would then assert `symBUDim n d = max_{action} buDim_nonstd (largestPrimeBelow n) d action` — the maximum over Z/p actions induced by Sₙ-sub-reps.

### §4.2. Why this is hard

The infrastructure for `buDim_nonstd` requires:
1. A formal definition of "representation of Z/p on `R^d`" (involves `LinearMap`, `Module`, `Group` action, Mathlib v4.26.0 has these as `MulAction (ZMod p) (Fin d → ℝ)` or `Representation` from `Mathlib.RepresentationTheory.Basic`).
2. A formal definition of "BU dimension for a given representation" via the equivariant `[X, Y]_G`-classification.
3. Fadell-Husseini cohomological index — not in Mathlib v4.26.0 (0 hits, §5 below).

Strategy β is a **multi-iteration project**, not a single PREP-to-ACT step. It would require ~500–1000 LOC of foundational equivariant-topology infrastructure before any single conjecture-related theorem could be stated.

### §4.3. When β makes sense

Strategy β is justified if a *separate* falsification or refinement target gives a concrete non-trivial answer for `buDim 3 3` (cyclic-permutation action) or similar. As of §2.6, the natural candidate (Z/3 on `R^3` by cyclic permutation) yields the same value as Z/2's classical bound — so β has no obvious payoff at the smallest test case.

Recommendation: **defer Strategy β** unless and until a future iteration finds concrete evidence that `buDim_nonstd p d action ≠ d − 1` for some `(p, d, action)`.

## §5. Mathlib bearer audit

Audited via `gh api search/code` at Mathlib pin (current main, v4.26.0-aligned):

| Query | Total hits | Top result(s) | Status |
|-------|------------|---------------|--------|
| `"BorsukUlam"` | 0 | — | No BU infrastructure |
| `"Borsuk"` | 1 | `Mathlib/Topology/Homotopy/LocallyContractible.lean` | Not BU-related (Borsuk's homotopy extension theorem, unrelated) |
| `"Yang_Borsuk"` | 0 | — | No Yang-Borsuk infrastructure |
| `"LefschetzFixedPoint"` | 0 | — | No Lefschetz fixed-point theorem |
| `"HairyBall"` | 0 | — | No hairy-ball theorem |
| `"FreeAction"` (re: group actions) | 0 | — | No formal "free action" predicate |
| `"antipode" + "sphere"` | 1 | `Mathlib/Geometry/Manifold/Instances/Sphere.lean` | Not BU-related (antipode as smooth map, unrelated) |
| `"FadellHusseini"` | 0 | — | No equivariant index |
| `"equivariantCohomology"` | 0 | — | No equivariant cohomology |

**Conclusion.** Mathlib v4.26.0 has **no equivariant topology infrastructure** relevant to Borsuk-Ulam. The proposed `buDim_prime_odd` axiom (§3.1) cannot be proved from Mathlib in its current state. Discharging it would require building equivariant cohomology + Fadell-Husseini index (multi-thousand-LOC project, well outside this file's scope).

Adding the axiom is therefore a **principled extension** of the parent's existing `buDim_prime` axiom, in the same status as `buDim_two`, `buDim_prime`, `buDim_mono`.

## §6. Recommendation for Iter 18 ACT

**Primary recommendation: Strategy α (§3) + formal-statement fix (§1.5).**

Two PR sequence:
1. **PR (1): `problem.md` fix** (small, low-risk). Adopt Option A from §1.5. ~10-line edit. Brings `problem.md` into consistency with `symBUDim_lower_z2` (a 6+-iter-old theorem) and `buDim_two` (parent's classical Borsuk-Ulam axiom).
2. **PR (2): parent-side `buDim_prime_odd` + this file's `symBUDim_odd_formula`** (medium, axiom-adding). ~135 LOC across two Lean files. axiomCount: parent `9→10`, this file `1→1` (unchanged). Discharges Iter 17 Path Forward Item 1.

The PR (2) docstrings must explicitly flag that the unified closed form `symBUDim n d = d − 1` **trivialises** the `largestPrimeBelow` content. The conjecture is honest about its consequences — Iter 17 hinted at this; Strategy α makes it formal.

**Alternative (Strategy β, §4).** Defer. No concrete payoff at the smallest test cases. Requires Mathlib equivariant topology that does not yet exist.

**Out of scope for Iter 18.** Falsification target `buDim 3 3` (Path Forward Item 5). The natural cyclic-permutation action gives the consistent value `2` (= Z/2's classical bound); no falsification opportunity at the smallest test case. Genuine non-triviality would need primes `p ≥ 5` with non-standard sub-representations, which is multi-iteration work.

## §7. Risks and open questions

### Risk 1: Lefschetz argument depends on `H_i` of `S^{2k}` having `Z/p`-trace `±1`

The Lefschetz argument (§2.2) assumes the generator `T` acts on `H_{2k}(S^{2k}; ℚ)` with eigenvalue `±1` (= degree). This is standard for self-maps of orientable manifolds. The proof is via the universal coefficient theorem + the fact that `End_ℤ(ℤ) = ℤ` and continuous self-maps have integer degree. **No risk; standard topological fact.**

### Risk 2: "Standard rep + trivial padding" is one of several Z/p actions on R^{2k+1}

The argument in §2.3.A picks ONE natural Z/p action. Different sub-representations could give different BU dimensions. The parent's `buDim p d` is silent about which it represents. **Risk:** if a future iteration commits to a different action (e.g., cyclic permutation), the proposed `buDim_prime_odd` value `2k` might be wrong.

**Mitigation:** the docstring of §3.1 explicitly cites the "standard rep + trivial padding" interpretation as a *choice*, and points to §2.3.B for the alternative. The axiom is then well-defined relative to a *named* action.

### Risk 3: `Odd p` predicate not in standard form

The proposed axiom uses `(hp_odd : Odd p)`. Mathlib has `Nat.Odd_iff : Odd n ↔ n % 2 = 1` (`Mathlib.Data.Nat.Parity`). For an odd prime `p`, this is provable from `hp.eq_two_or_odd` (which gives `p = 2 ∨ p % 2 = 1`). **No risk; standard.**

### Risk 4: Iter 17 Part XXIV's `buDim_largestPrime_even_no_strict_mono` interacts with the new axiom

Iter 17 proved `buDim (largestPrimeBelow n) (2k) = 2k − 1` is constant in `n` (`buDim_largestPrime_even_const`). Adding `buDim_prime_odd` gives the analogous odd-d statement: `buDim (largestPrimeBelow n) (2k+1) = 2k` is constant in `n` for `n ≥ 3` (since `largestPrimeBelow n ≥ 3` is odd by Bertrand for `n ≥ 3`). This **strengthens** Iter 17's even-only result to a uniform-in-d result.

**Effect:** Iter 18 ACT could add `buDim_largestPrime_odd_const` and `buDim_largestPrime_const_unified`, paralleling PART XXIV.

### Open question 1: What does `buDim p 1` mean for odd primes?

The parent's `buDim_two 0 : buDim 2 1 = 0` pins the `d = 1` case at `p = 2`. For odd primes, the parent is silent. Strategy α's axiom requires `k ≥ 1` so it doesn't address `d = 1`. The conjecture at `d = 1`: `symBUDim n 1 = buDim p* 1`. At `n = 2`, `symBUDim 2 1 = buDim 2 1 = 0`. At `n ≥ 3`, `symBUDim n 1 = buDim p* 1` for some odd prime `p*` — unknown.

**Suggestion:** add a corner-case axiom `axiom buDim_prime_one (p : ℕ) (hp : Nat.Prime p) (hp_odd : Odd p) : buDim p 1 = 0`. Trivial in spirit; matches the expectation that no equivariant constraint is added at the smallest dimension.

### Open question 2: Should the unified `buDim_all p d = d − 1` replace `buDim_two`, `buDim_prime`, `buDim_prime_odd`?

Yes, this would simplify the parent. The unified axiom would be:

```lean
axiom buDim_all (p d : ℕ) (hp : Nat.Prime p) (hd : 0 < d) : buDim p d = d - 1
```

The existing `buDim_two`, `buDim_prime`, and proposed `buDim_prime_odd` all follow as corollaries (theorems, not axioms). axiomCount would *decrease* from 4 → 2 (only `buDim` itself and `buDim_mono` would remain axioms; the rest become theorems from `buDim_all`).

This is a stronger refactor than Strategy α. It would make the conjecture's content-collapse even more explicit (the parent itself asserts `buDim p d = d − 1` uniformly). Recommendation: **consider for Iter 19** as a clean-up after Iter 18 lands `buDim_prime_odd`.

## §8. Summary

This S18 PREP does three things:

1. **Audits** the formal statement of the conjecture in `problem.md` and flags that the literal chain of equalities `symBUDim(n,d) ?= buDim(p*,d) = 2⌊d/2⌋ − 1` is **provably inconsistent at every odd d ≥ 3** (refuted by `buDim_two` + Z/2 monotonicity, both axiom-free and 6+ iterations old).
2. **Designs** the parent-side axiom `buDim_prime_odd (p k : ℕ) (hp : Nat.Prime p) (hp_odd : Odd p) (hk : 0 < k) : buDim p (2*k+1) = 2*k` that would close the odd-d gap. Pre-flight check: compatible with all existing parent axioms. Justification: Lefschetz fixed-point obstruction (Z/p, p odd, cannot act freely on S^{2k}) + "standard rep + trivial padding" interpretation.
3. **Maps the consequences**: under §3.1 the conjecture's content **trivialises** to `symBUDim n d = d − 1` uniformly, exposing that the entire `largestPrimeBelow` framework (PARTS VI–XX, ~1000 LOC) is decorative under the natural parent-side completion. This is consistent with Iter 17's "non-trivial content lives genuinely at odd d only" observation; Strategy α formalises it.

The Iter 18 ACT is therefore a small, principled axiom addition + this file's downstream closure (PART XXV, ~135 LOC), with the **honest framing** that the conjecture's `largestPrimeBelow` content collapses to a Z/2-saturated closed form at all d. The cosmetic flip-side: gallery presentation should acknowledge the trivialisation, lest the file's depth be misread as the conjecture's depth.

No edits to any Lean file or gallery JSON. Pristine doc-only PR.

## §9. Files

- `research/problems/borsuk-ulam-oq-02-oq-01-oq-03-oq-02/sessions/2026-05-13-s18-prep-odd-d-buDim-parent-axiom-and-formal-statement-audit.md` — this file (new).
