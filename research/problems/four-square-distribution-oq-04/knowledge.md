# Knowledge Base: four-square-distribution-oq-04

Generalizing the four-square type-decomposition to r_{2k}(n) via the
hyperoctahedral (signed-permutation) group B_{2k} = S_{2k} ⋉ (Z/2)^{2k}.

---

## Problem Understanding

The gallery proof `four-square-distribution` (the 2k = 4 case) writes
r_4(n) = Σ over "ordering types" of an orbit size 2^{#nonzero}·4!/∏m_i!. The seeker
stub (problem.md) asks: does this orbit–stabilizer bookkeeping generalize to
r_{2k}(n) under B_{2k} = S_{2k} ⋉ (Z/2)^{2k}, |B_{2k}| = (2k)!·2^{2k} (e.g.
|B_8| = 8!·2^8 = 10,321,920)? The arithmetic value of the total (Jacobi) is taken
as input; the open contribution is the purely group-theoretic orbit count.

---

## Insights

### Session 2026-06-15 (ACT, researcher-9) — the bridge: whole stack collapses to ONE residue

**Mode**: REVISIT · **Outcome**: progress (new connective lemma; Decomp/Keystone
`fiber_card_eq_contribution` sorry eliminated; build-pending — Docker OOM, Aristotle 404).

**What I did.** Found the stack had four sibling files that were never wired
together: `Decomp` (reduces OQ to `fiber_card_eq_contribution`, sorry), `Sign`
(sign-count half, proved), `Keystone` (assembles `fiber_card_eq_contribution`
**modulo a hypothesis** `harr` about `(shapeFiber m n s).image absMap`, no sorry),
and `Arrange` (`arrangement_card_div_form : (arrangements s).card = m!/∏count!`,
modulo the single residue `arrangement_card`). The unencoded gap: `harr` is phrased
about `image absMap`, Arrange's count about `arrangements s`.

**New file `FourSquareDistributionOQ04Bridge.lean`** (imports Decomp/Arrange/Keystone):
- `sumsq_invariant`: `Σ(a i)² = Σ(b i)²` whenever `multiset(a)=multiset(b)` — the
  sum of squares is a function of the value-multiset only (`Multiset.map_map` +
  `Finset.sum_map_val` + `sq_abs`).
- `image_absMap_eq_arrangements` (**the missing link, fully proved**): for an
  attained shape `s ∈ (reps m n).image shape`,
  `(shapeFiber m n s).image absMap = arrangements s`. Key facts: every part of `s`
  is `≥0` (it is some `|f₀ i|`); a profile in the image has `multiset = shape = s`;
  conversely `multiset(g)=s ⇒ g≥0 ⇒ |g|=g`, and `sumsq_invariant` carries `=n` from
  the witness `f₀`, so `g ∈ reps` with `shape g = s`.
- `card_of_mem_image_shape`: `card s = m` for attained `s`.
- `fiber_card_eq_shapeContribution`: discharges Keystone's `harr` via
  `arrangement_card_div_form`, proving Decomp's keystone for every attained shape.
- `reps_card_eq_sum_shapeContribution`: **re-proves the headline decomposition**
  `r_m(n) = Σ_shapes shapeContribution` with **no `sorry` of its own**.

**Net effect.** The entire OQ-04 generalization now rests on the *single* residue
`arrangement_card` (Arrange.lean:133) — the classic "orderings of a multiset =
multinomial coefficient" count. All Mathlib lemmas used were name-checked against
rev `2df2f0150c`; siblings + signatures confirmed on `origin/main`.

**Next.** Prove `arrangement_card` via orbit-stabilizer for the `Equiv.Perm (Fin m)`
precomposition action (needs a defined MulAction instance — precomposition on
`Fin m → ℤ` is not a registered Mathlib instance). Ideal Aristotle target (KNOWN
math) once the backend returns. Then register the stack and build-verify.

---

### Session 2026-06-15 (ORIENT) — the generalization holds; formula + bearers pinned

**Mode**: FRESH · **Outcome**: ORIENT (answer + exact durable verification; Lean
ACT is Docker-gated and scoped below).

**Answer: YES, verbatim, for every 2k.** Model a representation as a tuple
`x = (x_1,…,x_{2k}) ∈ Z^{2k}` with `Σ x_i² = n`. B_{2k} acts by permuting
coordinates and flipping signs. The orbits are exactly the **shape classes** (the
multiset of absolute values `{|x_i|}`), and for a shape `s` with `z` zero parts
and distinct-absolute-value multiplicities `{m_i}` (0 included, so `Σ m_i = 2k`):

        orbit(s)  =  2^(2k − z) · (2k)! / ∏_i (m_i!)
                  =  2^(#nonzero parts) · multinomial(2k; multiplicities),     (★)

        r_{2k}(n) =  Σ_{shapes s of n}  orbit(s).                              (DECOMP)

By orbit–stabilizer the stabilizer of a shape-`s` representation has order

        |stab(s)|  =  |B_{2k}| / orbit(s)  =  2^z · z! · ∏_{nonzero} (m_j!).    (STAB)

**Reading of (STAB) — the key subtlety for a Lean ACT.** The stabilizer is *not*
the full Young-subgroup `∏ m_i!`: of the `2^{2k}` sign flips, only the `2^z` flips
on the **zero** coordinates fix the tuple (flipping a 0 does nothing); flipping any
nonzero coordinate changes `x_i ↦ −x_i ≠ x_i`. So the sign group contributes `2^z`,
the permutations contribute `z!` (permuting the zeros) times `∏_{nonzero} m_j!`
(permuting equal nonzero values). The `2^z` zero-sign degeneracy is exactly why the
orbit carries `2^{#nonzero}` and not `2^{2k}`. Mishandling zeros is the one place a
naive `card B / Young-subgroup` computation goes wrong.

**Durable artifact** `verify_hyperoctahedral_2k.py` (stdlib, exact integers, all
checks PASS): for `2k ∈ {2,4,6,8}` and `n` up to `{300,200,120,80}` it checks
(a) the orbit formula (★) against an INDEPENDENT brute count of signed orderings;
(b) `orbit(s)·|stab(s)| = |B_{2k}|` (orbit–stabilizer) for every shape;
(c) `Σ_shapes orbit = r_{2k}(n)` where `r_{2k}` is computed independently by
convolving the single-coordinate signed-square distribution; plus anchors
`r_2 = 4(d_1−d_3)` and `r_4 = 8σ*` against the convolutional totals. Worked example
`n=30, 2k=4`: shapes `(0,1,2,5)→orbit 192, stab 2` and `(1,2,3,4)→orbit 384,
stab 1`, summing to `r_4(30)=576`.

**Mathlib bearers for the ACT (confirmed by code search at HEAD).**
- `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`
  (`Mathlib/GroupTheory/GroupAction/Quotient.lean`) — the orbit-size = |G|/|stab|
  engine; gives (★) once the action and stabilizer order are in place.
- `MulAction.orbitEquivQuotientStabilizer` (`Mathlib/GroupTheory/Index.lean`).
- `Nat.sum_four_squares` (existence). The signed-permutation group itself has **no
  Mathlib name** (`hyperoctahedral` = 0 hits): B_{2k} must be assembled as
  `Equiv.Perm (Fin (2k))` acting on `Fin (2k) → ℤ` together with sign flips
  `(ZMod 2)^{2k}` (or directly as the relevant `MulAction`).

---

### Session 2026-06-15 (ACT) — the `2k = 6` case formalized (build-pending)

**Mode**: continue · **Outcome**: ACT (Lean file mirroring the proven parent;
Docker/Aristotle blackout ⟹ build-pending, UNREGISTERED).

Chose the **computational route the parent actually uses**, not the heavier
`MulAction` one the prior ORIENT sketched: the parent
`FourSquareDistribution.lean` does *not* build `B₄` as a group action — it
defines `RepType` (sorted four-tuple) + `contribution = permutations · 2^nonzero`
and discharges concrete values by `native_decide`. New file
`proofs/Proofs/FourSquareDistributionOQ04.lean` mirrors this for **six**
coordinates:

- `RepType6 n` = sorted six-tuple `a₁≤…≤a₆`, `Σ aᵢ² = n` (`deriving DecidableEq`,
  exactly like the parent).
- `contribution = (720 / ∏ (count v)!) · 2^(#nonzero)` — the `(★)` formula at
  `m = 6`.
- Concrete shapes for `n ∈ {1,2,3,5,6,12,30}` with per-shape contributions by
  `native_decide`, and `r₆(n)` totals as `∑ contributions` (`r6_5=312`,
  `r6_6=544`, `r6_12=2080`, `r6_30=14144`).
- Structural lemmas `nonzeroCount_le_six`, `signFactor_le_64`.

This executes next-step #1 below at `m = 6` without the parametric
semidirect-product machinery. The (DECOMP) partition obstruction (next-step #2)
is handled the *same way the parent handles it* — case-by-case per small `n` via
the exhaustively-enumerated complete shape list (the cert checks the list is
complete); a uniform `MulAction` partition proof remains the deep open Lean work.

**Cert (new)** `verify_r6_decomposition.py` (PASS): for each embedded `n` it
checks (a) the exhaustive sorted-shape enumeration equals the file's shape list,
(b) the `(★)` orbit value equals an INDEPENDENT brute count of distinct signed
orderings *and* the embedded number, (c) `Σ orbits = r₆(n)` by an INDEPENDENT
signed-square convolution *and* the embedded total. Largest single `m=6` orbit
seen: `(0,0,1,2,3,4) → 5760` at `n=30`; all-nonzero-distinct would give
`6!·2⁶ = 46080`.

### Session 2026-06-15 (ACT) — the keystone ASSEMBLY (Sign-blueprint steps 1 & 3), build-pending

**Mode**: continue · **Outcome**: ACT (the previously-missing Lean wiring that
turns the Sign-file blueprint into a proof; Docker + Aristotle blackout ⟹
build-pending, UNREGISTERED).

The open question was, by now, reduced to ONE residue. The chain on `main`:
- `Decomp.lean` keystone `fiber_card_eq_contribution` (`sorry`): fiber size = (★).
- `Sign.lean` `signFiber_card` (proved): the sign half `2^{#nonzero}`.
- residue `arrangement_card` = `m!/∏count!` (the arrangement half), set up in
  `Nat.multinomial` form by **open PR #24518** (`Arrange.lean`, also `sorry`).

The Sign file's trailing comment listed steps (1) `absFiber_eq_signFiber` and (3)
the fiberwise assembly as "remaining bookkeeping" but **never encoded them in
Lean**. This session encodes them in `FourSquareDistributionOQ04Keystone.lean`
(0 sorry / 0 axiom of its own):

- `absFiber_eq_signFiber` (step 1, **unconditional**): for an abs-profile `g`
  attained on the shape-fiber, `{f | shape f = s, |f|=g} = signFiber g`. Witness
  `f₀` from the image gives `g ≥ 0`, `multiset(g)=s`, `Σ(g i)²=n`; forward via
  `abs_cases`, backward via `abs_of_nonneg`/`abs_neg` + `sq_abs` rebuilding
  membership in `reps`/`shape`. Key subtlety: `g ≥ 0` so `|g i| = g i`.
- `nonzero_card_eq`: `#{i | g i ≠ 0} = #nonzero(s)` via
  `rw [← Multiset.countP_eq_card_filter, Multiset.countP_map]` then `rfl`
  (`Finset.filter`/`Multiset.filter` defeq). Bridges signFiber_card's
  coordinate-exponent to shapeContribution's multiset-exponent.
- `shapeFiber_card_eq_arrangements_mul` (step 3, **unconditional**): fiber =
  `(#abs-profiles)·2^{#nonzero s}` via `Finset.card_eq_sum_card_fiberwise` over
  `absMap` + `Finset.sum_const` (each summand constant by the two lemmas above).
- `fiber_card_eq_contribution`: the Decomp keystone, conditional on `harr` (=
  `((shapeFiber).image absMap).card = m!/∏count!` = #24518's
  `arrangement_card_div_form`); final `rfl` against `shapeContribution`.

**Net effect.** The open question is now `sorry`-free *except* the single residue
`arrangement_card`. Everything from "fiber size = (★)" down to the
sign/arrangement split is proved (modulo that one count).

**Cert (new)** `verify_keystone_assembly.py` (PASS: 62 shape-fibers + 441
sign-fibers, m≤5/n≤12): brute-checks step 1 (each abs-fiber = the signed product
`∏{g_i,-g_i}`) and step 3 (fiber = #profiles·2^{#nonzero}) directly against the
genuine `reps(m,n)`; cross-checks the residue and full (★).

**API pinned** (repo-precedented; no Mathlib source materialized under blackout):
`Finset.card_eq_sum_card_fiberwise` (Erdos40, CountingG7),
`Multiset.countP_map` (`= (s.filter fun a => p (f a)).card`) +
`countP_eq_card_filter` (DescartesRuleOfSignsOQ01), `Finset.mem_image_of_mem _ h`.

## Next steps

1. **ACT (Lean, Docker-gated).** For a FIXED small `m = 2k ∈ {4,6,8}` (avoids the
   parametric semidirect-product construction): define the `MulAction` of
   `Equiv.Perm (Fin m) × (Fin m → Multiplicative (ZMod 2))` on `{f : Fin m → ℤ //
   Σ f² = n}`, compute `|stab|` for a shape via the zero/ nonzero split above, and
   invoke `card_orbit_mul_card_stabilizer_eq_card_group` to land (★). Reuse the
   parent's `RepType` shape machinery for the sorted-representative side.
2. **Honest obstruction.** As in the 2k=4 parent, (DECOMP) `r_{2k} = Σ orbit`
   needs the orbit partition of the full representation set, i.e. "every signed
   ordering lies in exactly one shape orbit" — a `MulAction` partition argument,
   not the orbit-size formula. That partition (not (★)) is the real Lean work; the
   parent discharged it only case-by-case for small `n`.
3. Optionally record the matching arithmetic inputs (r_6, r_8 Jacobi/modular
   formulas) so the decomposition can be stated with an explicit total.

## Dead Ends / Non-starters

- A fully *parametric in k* Lean proof is overkill for a first ACT: building
  `B_{2k}` as a generic semidirect product and computing its order/action is
  heavier than fixing `m ∈ {4,6,8}` and proving each by `decide`-friendly finite
  group actions.
- Treating the stabilizer as the full Young subgroup `∏ m_i!` (forgetting the
  `2^z` zero-sign factor) gives the wrong orbit size — the verifier rejects it.

---

### Session 2026-06-15 (ACT) — the uniform `(DECOMP)` partition, proved for all `m, n` against the *genuine* count

**Mode**: continue · **Outcome**: ACT (new build-pending file; Docker/Aristotle
blackout ⟹ UNREGISTERED, name-checked only).

**Gap noticed.** Both the parent `FourSquareDistribution.lean` and the open
`FourSquareDistributionOQ04.lean` (PR #24364, `2k=6`) establish the decomposition
**computationally and case-by-case**: per `n`, `contribution = value` by
`native_decide`, summed against a *hard-coded* Jacobi literal (`r₄(4)=24`,
`r₆(30)=14144`). There is no Lean object equal to the real representation count
`r_{2k}(n)=#{x∈ℤ^{2k}:Σxᵢ²=n}`, and so no proof that the contributions sum to it —
only an assertion validated by the Python certificate.

**New file** `proofs/Proofs/FourSquareDistributionOQ04Decomp.lean` (distinct from
PR #24364; different filename, no `.json`/parent edits ⟹ no collision). Supplies
the missing **uniform** step, for every `m` and every `n` at once, against the
actual count:

- `reps m n : Finset (Fin m → ℤ)` = representations as a filter on the box
  `[-n,n]^m`. `mem_reps_iff` proves it faithful (`f ∈ reps m n ↔ Σ(f i)²=n`); the
  box is lossless because `|x| ≤ x²` (lemma `abs_le_sq`) forces `|fᵢ| ≤ n`. So
  `(reps m n).card` *is* `r_m(n)`. For `m=2k` this is `r_{2k}(n)`.
- `shape f` = multiset `{|f i|}`, the `B_m`-orbit invariant.
- **`reps_card_eq_sum_fiber` — fully proved, no sorry** —
  `(reps m n).card = Σ_{s∈shapes} ((reps m n).filter (shape·=s)).card`, directly
  from `Finset.card_eq_sum_card_fiberwise`. This is `(DECOMP)` for **all** `m,n`
  simultaneously, about the real count — the step the parent files only asserted.
- `shapeContribution m s = (m!/∏(count v)!)·2^{#nonzero}` is `(★)`.
- The whole open question collapses to ONE isolated lemma
  `fiber_card_eq_contribution` (the **sole** `sorry`): each shape-fiber has size
  `(★)`. That is precisely the orbit-size statement of `B_m=S_m⋉(ℤ/2)^m`.
  `reps_card_eq_sum_contribution` assembles the full `r_{2k}=Σ contribution` from
  it via `sum_congr`.

**Why this is real progress (honest).** The fiberwise partition is *new*: the
prior files cannot state "contributions sum to `r_{2k}`" because they never form
the count. Here that sum law holds unconditionally for all `m,n`, and the residual
open content is pinned to one orbit-size lemma — the classic "isolate the heart"
reduction. The Jacobi arithmetic is no longer needed for the *partition*; it would
only evaluate the RHS in closed form.

**Bearers** (name-checked from memory; no sibling Mathlib this session):
`Fintype.piFinset`/`Fintype.mem_piFinset`, `Finset.card_eq_sum_card_fiberwise`,
`Finset.single_le_sum`, `Finset.mem_image_of_mem`, `sq_abs`, `abs_le`. Orbit count
of each fiber still validated by `verify_hyperoctahedral_2k.py` (PASS).

**Next-session ACT.** Build & register `…Decomp.lean`; discharge
`fiber_card_eq_contribution` by the `MulAction` orbit–stabilizer route (next-step
#1) — now the *single* remaining goal rather than a per-`n` enumeration.

## S4 (ACT — sign-count half of the keystone; dual blackout persists)
Backends re-tested live: `docker info` times out; Aristotle `prove` → "Resource
not found." No machine check possible.

**Keystone factorization.** `fiber_card_eq_contribution` (the sole real `sorry`
in `…Decomp.lean`) is a `B_m = S_m ⋉ (ℤ/2)^m` orbit-size. The formula `(★)`
factors cleanly:

    (★) = (arrangement count  m!/∏ count_v!) · (sign count  2^{#nonzero}).

Brute-force **confirmed both halves** (`verify_orbit_formula.py`, PASS):
orbit formula 58 fibers m≤5,n≤12 (0 mismatch); sign count 3905 abs-profiles m≤5
(0 mismatch).

**Shipped (build-pending, UNREGISTERED):** `…OQ04Sign.lean` proves the sign half
in full —
- `signFiber g := Fintype.piFinset (fun i => {g i, -g i})`,
- `card_pair_neg c : ({c,-c}).card = if c=0 then 1 else 2` (via `Finset.card_pair`
  + `c = -c ↔ c = 0`),
- `signFiber_card : (signFiber g).card = 2 ^ #{i : g i ≠ 0}` via
  `Fintype.card_piFinset` → `∏ (if … then 1 else 2)` → `Finset.prod_ite` +
  `Finset.prod_const`.

**Remaining = ONE standard lemma (arrangement_card).** With `signFiber_card`, the
keystone reduces (blueprint in the file footer) by `card_eq_sum_card_fiberwise`
over the abs-value map to:

    arrangement_card : #{g : Fin m → ℤ | g i ≥ 0, multiset(g)=s} = m!/∏ count_v!.

This multiset-permutation/multinomial count has no obvious Mathlib lemma —
candidate leads for a build session: `Nat.multinomial`, `Equiv.Perm (Fin m)`
action on functions, `Multiset.permutations`/`Multiset.Nodup` card. Good Aristotle
target once the backend returns.

## Remaining next steps (updated)
1. Build `…OQ04Sign.lean` (fix any `Fintype.card_piFinset`/`Finset.prod_ite`
   name drift), then register both `…Decomp` and `…Sign`.
2. Prove/locate `arrangement_card` (the multinomial count) — the sole residue.
3. Combine via the file-footer blueprint to discharge `fiber_card_eq_contribution`.

### Session 2026-06-15 (researcher-2) — Mathlib search resolving the `arrangement_card` lead

The keystone `fiber_card_eq_contribution` is reduced (in `…OQ04Sign.lean`'s blueprint) to
one open lemma, `arrangement_card`:
`#{g : Fin m → ℤ | g i ≥ 0 ∀i, multiset(g) = s} = m! / ∏_v (count_v s)!`.
This session ran the build-free Mathlib search the blueprint deferred "to a build session".

**Outcome (pinned mathlib4 v4.26.0):**
- `Nat.multinomial s f` EXISTS (`Data/Nat/Choose/Multinomial.lean:43`) with the algebraic
  identity `Nat.multinomial_spec : (∏ i ∈ s, (f i)!) * multinomial s f = (∑ i ∈ s, f i)!`
  (:50). So `m!/∏count!` is exactly `Nat.multinomial s.toFinset (fun v => s.count v)` — the
  `shapeContribution` numerator should be RE-EXPRESSED via `Nat.multinomial` to use
  `multinomial_spec` (avoids the `Nat.div` and matches the factored identity directly).
- There is **NO** ready cardinality lemma "number of functions/arrangements with a given
  multiset image = multinomial". `List.length_permutations : (permutations l).length = l.length!`
  counts ALL n! orderings (ignores repeats), so it is NOT the multiset count.
- `Combinatorics/Enumerative/Bell.lean` is the closest precedent: it computes a partition
  count via `Nat.multinomial … * ∏ …` and discharges it with `Nat.multinomial_spec` +
  `Finset.prod_multiset_map_count` (Bell.lean:77-94). That factorial-bookkeeping technique is
  the model for proving `arrangement_card` once the cardinality side is set up.

**Recommended route for the build session (sharper than the blueprint's "candidates"):**
prove `arrangement_card` via `Equiv.Perm (Fin m)` acting on `Fin m → ℤ` (precompose). The
orbit of an arranged `g` (with `multiset(g)=s`) is the set of arrangements; its stabilizer is
`{σ | g ∘ σ = g} ≅ ∏_v Equiv.Perm (g⁻¹{v})`, of order `∏_v (count_v s)!`. Then
`MulAction.card_orbit_mul_card_stabilizer_eq_card_group` gives
`|orbit| · ∏count! = m!`, i.e. `|orbit| = Nat.multinomial …` by `multinomial_spec`. The sole
remaining work is the **stabilizer-order computation** `∏_v (count_v)!` (the genuine residue;
`Equiv.Perm` of a fibered type ≅ product of perms of the fibers). Steps 1+3 of the Sign.lean
blueprint (fiberwise split over `absMap`) remain bookkeeping. Still Docker-gated (dual
blackout: docker exit 124, Aristotle 404); no Lean edits this session.

---

### Session 2026-06-15 (researcher-1, ACT) — the `2k = 8` (`|B₈|`) computational case + refined residue analysis

**Mode**: continue · **Outcome**: ACT (new build-pending file completing the
`{4,6,8}` fixed-`m` program; triple blackout re-confirmed live).

**Backends re-tested live (all down):** `docker info` → timeout/daemon down
(rc=124); no local Mathlib checkout under `proofs/.lake/`; Aristotle MCP `prove`
→ HTTP 404 (`mcp-smoke-test.sh` confirms `GET /api/v1/project` 404). So neither a
build nor an automated proof of the sole residue `arrangement_card` was possible.

**Shipped (build-pending, UNREGISTERED):**
`proofs/Proofs/FourSquareDistributionOQ04M8.lean` — the `2k = 8` case, mirroring
the **proven** computational route of the parent and the `2k = 6` sibling
(`RepType8` sorted eight-tuple + `(★) = 8!/∏count! · 2^{#nonzero}`, concrete
contributions by `native_decide`). This is the example the open question names
(`|B₈| = 8!·2⁸ = 10 321 920`) and the only one of `{4,6,8}` not previously
formalized, so it closes the documented "ACT fixed m in {4,6,8}" next-step.
Embedded for `n ∈ {1,2,3,4,5,6,7,8,12}`: complete sorted-shape lists, per-shape
contributions, and `r₈(n)` totals as `∑ contributions` (`r₈(8)=9328` includes the
all-equal-nonzero shape `(1,1,1,1,1,1,1,1) → 8!/8!·2⁸ = 256`; `r₈(12)=31808`).
Structural bounds `nonzeroCount_le_eight`, `signFactor_le_256`.

**Cert (new, PASS):**
`research/problems/four-square-distribution-oq-04/verify_r8_decomposition.py`
(stdlib, exact integers) — for each embedded `n`: (a) exhaustive sorted-shape
enumeration equals the file's shape list; (b) each shape's `(★)` orbit equals an
INDEPENDENT brute count of distinct signed orderings *and* the embedded number;
(c) `∑ orbits == r₈(n)` by INDEPENDENT signed-square convolution *and* the
embedded total. All 9 `n` PASS. Confirms `r₈(n) = 16 σ₃*(n)` (e.g. `r₈(4)=1136`).

**Refined residue analysis (honest correction to prior notes).** The prior
sessions framed the `arrangement_card`/orbit-size formula as "the easy half" and
the partition `(DECOMP)` as the only hard part. Working the orbit–stabilizer
proof of `arrangement_card` concretely this session surfaced **two** sub-steps
that each lack a direct Mathlib lemma, not one:
  1. **Surjectivity onto the orbit** — "two functions `g₀, g : Fin m → ℤ` with
     the same multiset image differ by a permutation" (∃σ, `g₀ ∘ σ = g`). This is
     needed to identify `arrangements s` with a *single* `Equiv.Perm (Fin m)`
     orbit, and is itself non-trivial (no obvious `Multiset.map`-to-permutation
     lemma).
  2. **Stabilizer order** — `|{σ | g₀ ∘ σ = g₀}| = ∏_v (count_v)!` (the
     fibered-permutation product), the step prior notes already flagged.
Plus nonemptiness (constructive via `s.toList`, length = `card s = m`). So a
hand-authored proof under blackout would be ~150 lines spanning three
sub-residues with high error risk and no way to check it — deferred. The clean,
canonical statement of `arrangement_card` in `…Arrange.lean` (`Nat.multinomial`
form, `arrangement_card_div_form` derived) remains the right setup; it just needs
Aristotle or an interactive build session.

**Ready-to-submit Aristotle target (for when the backend returns).** The exact
self-contained snippet to submit (30-day server cache makes re-submission cheap):
the `arrangements`/`mem_arrangements_iff`/`arrangement_card` block from
`…Arrange.lean` with `import Mathlib`, hint = the `Equiv.Perm (Fin m)`
precomposition orbit–stabilizer route (stabilizer = ∏ fiber-perms, order
∏count!) + `Nat.multinomial_spec`, with `Mathlib.Combinatorics.Enumerative.Bell`
as the bookkeeping precedent.

## Remaining next steps (updated)
1. **Build + register** the whole `…OQ04*` family (`Decomp`, `Sign`, `Arrange`,
   `Keystone`, the `2k=6` `OQ04`, and now the `2k=8` `M8`) once Docker returns;
   `native_decide` files (`OQ04`, `M8`) are lowest-risk to land first.
2. Discharge `arrangement_card` — submit to Aristotle the moment it returns, or
   prove the three sub-residues (nonemptiness, orbit-surjectivity, stabilizer
   order) interactively; then `fiber_card_eq_contribution` follows via the
   `Sign.lean` footer blueprint, closing the open question uniformly.

### Session 2026-06-15 (researcher-4, ACT) — the two native_decide leaves landed (Docker-verified, REGISTERED)

**Mode**: continue · **Outcome**: progress (two leaves graduated build-pending →
registered; PR #24848).

Docker recovered (4 build containers, host mem healthy). Built both native_decide
leaf files in isolation via `docker-build.sh`:
- `Proofs.FourSquareDistributionOQ04` (2k=6) — **green, 3058 jobs**, 0 sorry / 0
  axiom; native_decide table confirmed (`r6_30 = 14144`).
- `Proofs.FourSquareDistributionOQ04M8` (2k=8) — **green, 3058 jobs**, 0 sorry /
  0 axiom; native_decide table confirmed (`r8_8 = 9328`).

Both were on `main` already but **unregistered** in `Proofs.lean`; this session
adds the two imports (the lowest-risk landing per next-step #1). The remaining
stack files (Sign, Decomp, Keystone, Bridge, Arrange) stay unregistered — they
carry the `Fintype.card_piFinset`/`Finset.prod_ite` name-drift risk flagged in
prior sessions and should be built individually before registering.

Aristotle re-probed live this session: still **404** ("Resource not found" on a
trivial sorry). So `arrangement_card` remains the sole open residue and an
Aristotle target; no change to its status.
