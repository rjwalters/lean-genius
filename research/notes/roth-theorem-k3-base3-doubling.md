# Base-3 no-carry lower bound: `2·r₃(m) ≤ r₃(3m)` and `2ᵏ ≤ r₃(3ᵏ)`

**Problem**: `roth-theorem-k3-oq-01-wip-01` (Complete Quantitative Bounds for Roth's Theorem)
**Author**: researcher-5, 2026-07-04
**Status**: mathematics hand-audited; Lean formalization **drafted but UNVERIFIED**
(dual-tool blackout — see "Verification status" below).

This note records a new elementary lower bound for the cyclic Roth number
`r₃(N)` (max size of a 3-AP-free subset of `ZMod N`, as defined in
`proofs/Proofs/RothTheoremQuantitative.lean`, Part I). It complements Session 1's
supermultiplicativity result (`rothNumber_mul_coprime`, PR #34771), which is
*silent on prime powers* because `3ᵏ` has a single prime factor.

---

## Results

Write `r₃ = rothNumber`.

**Theorem A (general doubling step).** For every `m ≥ 1`,
> `2 · r₃(m) ≤ r₃(3m)`.

No coprimality hypothesis. This **strictly strengthens** the existing
`two_mul_rothNumber_le`, which concludes `2·r₃(N) ≤ r₃(3N)` only under
`Nat.Coprime 3 N` (via the CRT). Theorem A holds even when `3 ∣ m`, so it is the
version needed to iterate on powers of 3.

**Theorem B (explicit polynomial lower bound).** For every `k ≥ 0`,
> `2ᵏ ≤ r₃(3ᵏ)`.

Along the subsequence `N = 3ᵏ` this gives
`r₃(N) ≥ N^{log₃ 2} = N^{0.63092…}` — a genuine polynomial-density lower bound,
entirely elementary (no Fourier analysis, no Behrend sphere construction), and
**0 axioms** once verified. It is weaker than Behrend's
`N·exp(−c√log N)` but self-contained, and is the first super-constant explicit
`r₃` lower bound in the gallery.

---

## Proof of Theorem A

Fix `m ≥ 1` and abbreviate `n = 3m`. Let

* `π : ZMod n →+* ZMod m` be the reduction ring homomorphism
  (`ZMod.castHom (m ∣ 3m)`), and
* `L : ZMod m → ZMod n`, `L x = ↑(x.val)` the canonical set-section of `π`
  (cast the natural-number representative `x.val ∈ [0,m)` into `ZMod n`).

Two immediate facts:

1. `π (L x) = x` for all `x` (since `π (↑k) = ↑k` and `↑(x.val) = x` in `ZMod m`);
   in particular `L` is injective.
2. `π (↑m) = ↑m = 0` in `ZMod m`. Put `t := (↑m : ZMod n)`, the generator of the
   kernel of `π` (a copy of `ZMod 3` inside `ZMod n`).

**Nonvanishing lemma.** For `0 < c < 3`, `↑(c·m) ≠ 0` in `ZMod n`.
Indeed `↑(c·m) = 0 ⇔ 3m ∣ c·m ⇔ 3 ∣ c` (cancel the positive factor `m`), which
fails for `c ∈ {1,2}`. In particular `t ≠ 0` (`c = 1`) and `t + t ≠ 0` (`c = 2`).

**Construction.** Take a maximal AP-free set `A ⊆ ZMod m`, so `A` is AP-free and
`|A| = r₃(m)` (`rothNumber_achieved`). Define the "two top-digit translates"
$$
B \;=\; \{\, L x + s \;:\; x \in A,\ s \in \{0, t\} \,\} \;\subseteq\; \mathbb Z/n.
$$

*Cardinality.* The map `(x,s) ↦ L x + s` is injective on `A × {0,t}`: applying
`π` to `L x + s = L x' + s'` gives `x + π s = x' + π s'`, and `π s = π s' = 0`
for `s,s' ∈ {0,t}`, so `x = x'`; then `s = s'` by cancellation. Since `t ≠ 0`,
`|{0,t}| = 2`, hence `|B| = 2·|A| = 2·r₃(m)`.

*AP-freeness.* Suppose `a, a+d ∈ B` with `d ≠ 0` and, for contradiction,
`a+2d ∈ B`. Write
`a = L x₀ + s₀`, `a+d = L x₁ + s₁`, `a+2d = L x₂ + s₂`
with `xᵢ ∈ A`, `sᵢ ∈ {0,t}`. Applying `π` (and `π sᵢ = 0`):
$$
x_0 = \pi a,\qquad x_1 = x_0 + \pi d,\qquad x_2 = x_0 + 2\,\pi d .
$$

* **Case `π d ≠ 0`.** Then `x₀, x₀+πd = x₁, x₀+2πd = x₂` all lie in `A`, i.e. `A`
  contains the 3-term progression `x₀, x₀+πd, x₀+2πd` with nonzero common
  difference `πd` — contradicting AP-freeness of `A`. ∎(case)

* **Case `π d = 0`.** Then `x₁ = x₂ = x₀`, so all three points share the same
  `L`-part `L x₀`. Cancelling `L x₀`:
  $$
  s_0 + d = s_1, \qquad s_0 + 2d = s_2. \tag{$\ast$}
  $$
  From `(\ast)`, `d = s₁ − s₀`; since `d ≠ 0` we get `s₀ ≠ s₁`, so
  `{s₀,s₁} = {0,t}`. Eliminating `d` from `(\ast)` (compute `2·(s₀+d) − (s₀+2d)`):
  $$
  s_0 + s_2 = 2 s_1. \tag{key}
  $$
  Enumerate the two live sub-cases (`s₂ ∈ {0,t}` each):
  - `s₀=0, s₁=t`: (key) is `s₂ = 2t`. If `s₂=0` then `2t=0`; if `s₂=t` then
    `t=2t`, i.e. `t=0`. Both contradict the nonvanishing lemma.
  - `s₀=t, s₁=0`: (key) is `t + s₂ = 0`. If `s₂=0` then `t=0`; if `s₂=t` then
    `2t=0`. Both contradict the nonvanishing lemma.

  (Intuition: the middle term `a+d` would have to carry base-3 "top digit" `2`,
  which is excluded from `B`.) ∎(case)

Thus `B` is AP-free, and `2·r₃(m) = |B| ≤ r₃(3m)` by `card_le_rothNumber`. ∎

## Proof of Theorem B

Induction on `k`. Base: `2⁰ = 1 ≤ r₃(1) = r₃(3⁰)` by `rothNumber_pos`. Step:
with `NeZero (3ⁿ)`,
$$
2^{n+1} = 2\cdot 2^{n} \le 2\cdot r_3(3^{n}) \le r_3(3\cdot 3^{n}) = r_3(3^{n+1}),
$$
using the inductive hypothesis and Theorem A (`m = 3ⁿ`). ∎

---

## Relation to existing gallery results

| Result | Hypothesis | Conclusion |
|--------|-----------|-----------|
| `two_mul_rothNumber_le` (S1) | `Coprime 3 N` | `2·r₃(N) ≤ r₃(3N)` |
| **Theorem A (S2)** | none (`m ≥ 1`) | `2·r₃(m) ≤ r₃(3m)` |
| **Theorem B (S2)** | — | `2ᵏ ≤ r₃(3ᵏ)`, i.e. `r₃(N) ≥ N^{log₃2}` on `N=3ᵏ` |

Theorem A subsumes `two_mul_rothNumber_le` (drop the coprimality). Once verified,
`two_mul_rothNumber_le` can be re-derived as an immediate corollary of Theorem A,
or kept as the CRT-flavoured special case.

## Verification status

Written during a **dual-tool blackout**:
* the Docker build image `lean4-arm64:v4.26.0` was unusable — the containerd
  content store returned `input/output error` on the image blob
  (`sha256:3d1c9c6b…`), so both `docker image inspect` and a fresh `docker run`
  failed; and
* the Aristotle MCP endpoint returned `{"status":"error","message":"Resource
  not found."}` (404) for both `prove` and `prove_file`.

So neither machine-check path was available. The **mathematics above is
hand-audited**; the Lean below is a faithful but **unchecked** rendering and
will likely need minor repairs (exact Mathlib lemma names, `linear_combination`
signs, the `mem_image`/`mem_product` `simp` set) before it compiles.

**Next session**: once a build path recovers, port the two theorems into
`proofs/Proofs/RothTheoremQuantitative.lean` **Part II.C** (they use only Part-I
API: `APFree`, `rothNumber`, `rothNumber_achieved`, `card_le_rothNumber`,
`rothNumber_pos`), fix any elaboration errors, then update `axiomCount`/status
of the gallery entry. Do **not** add the `.lean` under `proofs/Proofs/` until it
builds — the lakefile globs that directory and an unbuildable file breaks the
whole gallery.

---

## Lean draft (UNVERIFIED — do not add under `proofs/Proofs/` until it builds)

```lean
import Mathlib

namespace Szemeredi.Roth.Quantitative  -- target namespace for integration

open Finset

-- ── Part-I API (already in RothTheoremQuantitative.lean; shown for standalone
--    elaboration of the two new theorems) ──────────────────────────────────
-- def APFree, noncomputable def rothNumber, rothNumber_def, apFree_empty,
-- apFree_singleton, card_le_rothNumber, rothNumber_achieved, rothNumber_pos
-- (verbatim from Part I — omitted here; see the file).

-- ══════════════════════════════════════════════════════════════════════════
-- PART II.C: EXPLICIT LOWER BOUND  r₃(3ᵏ) ≥ 2ᵏ  (base-3 no-carry)
-- ══════════════════════════════════════════════════════════════════════════

/-- Doubling step `2·r₃(m) ≤ r₃(3m)` for every `m ≥ 1`, with NO coprimality
    assumption (cf. `two_mul_rothNumber_le`, which needs `Coprime 3 N`). -/
theorem two_mul_rothNumber_le_three_mul (m : ℕ) [NeZero m] :
    2 * rothNumber m ≤ rothNumber (3 * m) := by
  haveI : NeZero (3 * m) := ⟨by positivity⟩
  have hdvd : m ∣ 3 * m := dvd_mul_left m 3
  set π : ZMod (3 * m) →+* ZMod m := ZMod.castHom hdvd (ZMod m) with hπdef
  set L : ZMod m → ZMod (3 * m) := fun x => ((x.val : ℕ) : ZMod (3 * m)) with hLdef
  set t : ZMod (3 * m) := (m : ZMod (3 * m)) with htdef
  have hπL : ∀ x : ZMod m, π (L x) = x := by
    intro x
    simp only [hLdef, hπdef, map_natCast, ZMod.natCast_zmod_val]
  have hπt : π t = 0 := by
    simp only [htdef, hπdef, map_natCast, ZMod.natCast_self]
  have hmulne : ∀ c : ℕ, 0 < c → c < 3 → ((c * m : ℕ) : ZMod (3 * m)) ≠ 0 := by
    intro c hc0 hc3 hcontra
    rw [ZMod.natCast_zmod_eq_zero_iff_dvd] at hcontra
    have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
    rw [Nat.mul_dvd_mul_iff_right hm] at hcontra
    have := Nat.le_of_dvd hc0 hcontra
    omega
  have ht_ne : t ≠ 0 := by
    have h := hmulne 1 (by norm_num) (by norm_num)
    rw [htdef]; simpa using h
  have h2t_ne : t + t ≠ 0 := by
    have h := hmulne 2 (by norm_num) (by norm_num)
    rw [htdef]; intro hh; apply h; push_cast; linear_combination hh
  have hπs : ∀ s ∈ ({0, t} : Finset (ZMod (3 * m))), π s = 0 := by
    intro s hs
    rcases Finset.mem_insert.mp hs with h | h
    · rw [h, map_zero]
    · rw [Finset.mem_singleton.mp h, hπt]
  obtain ⟨A, hAfree, hAcard⟩ := rothNumber_achieved (N := m)
  set f : ZMod m × ZMod (3 * m) → ZMod (3 * m) := fun p => L p.1 + p.2 with hfdef
  set B : Finset (ZMod (3 * m)) :=
    (A ×ˢ ({0, t} : Finset (ZMod (3 * m)))).image f with hBdef
  have memB : ∀ y, y ∈ B ↔ ∃ x ∈ A, ∃ s ∈ ({0, t} : Finset (ZMod (3 * m))), y = L x + s := by
    intro y
    simp only [hBdef, Finset.mem_image, Finset.mem_product, hfdef]
    constructor
    · rintro ⟨⟨x, s⟩, ⟨hx, hs⟩, rfl⟩; exact ⟨x, hx, s, hs, rfl⟩
    · rintro ⟨x, hx, s, hs, rfl⟩; exact ⟨⟨x, s⟩, ⟨hx, hs⟩, rfl⟩
  have hfinj : Set.InjOn f (A ×ˢ ({0, t} : Finset (ZMod (3 * m)))) := by
    rintro ⟨x, s⟩ hp ⟨x', s'⟩ hp' heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hp hp'
    simp only [hfdef] at heq
    have hx : x = x' := by
      have := congrArg π heq
      rw [map_add, map_add, hπL, hπL, hπs s hp.2, hπs s' hp'.2, add_zero, add_zero] at this
      exact this
    subst hx
    have hs : s = s' := by rwa [add_right_inj] at heq
    subst hs; rfl
  have hpair : ({0, t} : Finset (ZMod (3 * m))).card = 2 :=
    Finset.card_pair (Ne.symm ht_ne)
  have hBcard : B.card = 2 * rothNumber m := by
    rw [hBdef, Finset.card_image_of_injOn hfinj, Finset.card_product, hpair, hAcard]
    ring
  have hBfree : APFree B := by
    intro a d hd ha had hadd
    rw [memB] at ha had hadd
    obtain ⟨x0, hx0, s0, hs0, hae⟩ := ha
    obtain ⟨x1, hx1, s1, hs1, hbe⟩ := had
    obtain ⟨x2, hx2, s2, hs2, hce⟩ := hadd
    have hπa : π a = x0 := by
      rw [hae, map_add, hπL, hπs s0 hs0, add_zero]
    have hx1e : x1 = x0 + π d := by
      have h1 : π a + π d = x1 := by
        rw [← map_add, hbe, map_add, hπL, hπs s1 hs1, add_zero]
      rw [hπa] at h1; exact h1.symm
    have hx2e : x2 = x0 + 2 * π d := by
      have h2 : π (a + 2 * d) = x2 := by rw [hce, map_add, hπL, hπs s2 hs2, add_zero]
      have e : a + 2 * d = a + d + d := by ring
      rw [e, map_add, map_add, hπa] at h2
      rw [← h2]; ring
    have d0 : s0 = 0 ∨ s0 = t := by
      rcases Finset.mem_insert.mp hs0 with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_singleton.mp h)
    have d1 : s1 = 0 ∨ s1 = t := by
      rcases Finset.mem_insert.mp hs1 with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_singleton.mp h)
    have d2 : s2 = 0 ∨ s2 = t := by
      rcases Finset.mem_insert.mp hs2 with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_singleton.mp h)
    by_cases hpd : π d = 0
    · have hx10 : x1 = x0 := by rw [hx1e, hpd, add_zero]
      have hx20 : x2 = x0 := by rw [hx2e, hpd, mul_zero, add_zero]
      subst hx10; subst hx20
      rw [hae] at hbe hce
      have eq1 : s0 + d = s1 := by linear_combination hbe
      have eq2 : s0 + 2 * d = s2 := by linear_combination hce
      have hs01 : s0 ≠ s1 := by
        intro h; apply hd; linear_combination eq1 - h
      have key : s0 + s2 = 2 * s1 := by linear_combination 2 * eq1 - eq2
      rcases d0 with r0 | r0 <;> rcases d1 with r1 | r1 <;> rcases d2 with r2 | r2 <;>
        subst_vars <;>
        first
          | exact absurd rfl hs01
          | exact ht_ne (by linear_combination key)
          | exact ht_ne (by linear_combination -key)
          | exact h2t_ne (by linear_combination key)
          | exact h2t_ne (by linear_combination -key)
    · exact hAfree x0 (π d) hpd hx0 (hx1e ▸ hx1) (hx2e ▸ hx2)
  calc 2 * rothNumber m = B.card := hBcard.symm
    _ ≤ rothNumber (3 * m) := card_le_rothNumber B hBfree

/-- Explicit polynomial lower bound `2ᵏ ≤ r₃(3ᵏ)` (base-3 no-carry). -/
theorem pow_two_le_rothNumber_pow_three (k : ℕ) : 2 ^ k ≤ rothNumber (3 ^ k) := by
  induction k with
  | zero => simpa using rothNumber_pos 1
  | succ n ih =>
    haveI : NeZero (3 ^ n) := ⟨pow_ne_zero n (by norm_num)⟩
    calc 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      _ ≤ 2 * rothNumber (3 ^ n) := by gcongr
      _ ≤ rothNumber (3 * 3 ^ n) := two_mul_rothNumber_le_three_mul (3 ^ n)
      _ = rothNumber (3 ^ (n + 1)) := by rw [pow_succ']

end Szemeredi.Roth.Quantitative
```

---

## Verification-readiness audit (researcher-6, 2026-07-05)

**Context.** The dual-tool blackout that forced Session 2 to deliver notes-only
**persists unchanged**: the Docker build image `lean4-arm64:v4.26.0` still fails
with the same containerd content-store I/O error on blob
`sha256:3d1c9c6b…` (`docker run` aborts before any Lean runs; disk is now healthy
at 36 Gi free / 25 %, so this is image-blob corruption, **not** a space problem —
it needs a Docker restart / image re-pull, which is out of an agent's safe
scope), and the Aristotle MCP endpoint still returns `{"status":"error",
"message":"Resource not found."}` (404) for `prove`. There is **no local Mathlib
`.olean` cache** either (`proofs/.lake/packages/` is empty — Mathlib lives only
inside the corrupt image), so a bare `lean` type-check is not possible.

Machine-verification was therefore still unavailable. Instead this session did a
**static de-risking pass** that resolves, by construction, exactly the three
uncertainties Session 2 flagged ("exact Mathlib lemma names, `linear_combination`
signs, the `mem_image`/`mem_product` `simp` set"). Nothing below is a substitute
for a build; it upgrades the draft's confidence from "expect minor repairs" to
"ready to port verbatim the instant a build path recovers."

### 1. Part-I API cross-check (against the live file)

Every Part-I symbol the two theorems call was matched to its **current**
declaration in `proofs/Proofs/RothTheoremQuantitative.lean`:

| Symbol used in draft | Live decl | Signature note |
|---|---|---|
| `APFree` | L26 | `∀ a d, d ≠ 0 → a ∈ A → a + d ∈ A → a + 2*d ∉ A` — the `hBfree` proof's `intro a d hd ha had hadd` binds all 6, leaving goal `False`. ✓ |
| `rothNumber_achieved` | L140 | `{N} [NeZero N] : ∃ A, APFree A ∧ A.card = rothNumber N` — matches `obtain ⟨A, hAfree, hAcard⟩`. ✓ |
| `card_le_rothNumber` | L132 | `{N} [NeZero N] (A) (hA : APFree A) : A.card ≤ rothNumber N` — matches `card_le_rothNumber B hBfree`; the required `[NeZero (3*m)]` is supplied by the `haveI` at the top of the doubling proof. ✓ |
| `rothNumber_pos` | L118 | `(N) [NeZero N] : 1 ≤ rothNumber N` — base case `simpa using rothNumber_pos 1` (`[NeZero 1]` is a global instance). ✓ |

The target namespace `Szemeredi.Roth.Quantitative` (file L16, closed L393) is the
one the draft opens, so the two theorems drop in before `end` with no
`open`/namespace churn.

### 2. Mathlib lemma-name corpus check

Each Mathlib lemma the draft names was confirmed to appear in **other
already-compiling** `proofs/Proofs/*.lean` files (count = independent
compiling call-sites in this repo on v4.26.0):

| Lemma | sites | Lemma | sites |
|---|---|---|---|
| `ZMod.castHom` | 42 | `Finset.card_pair` | 96 |
| `ZMod.natCast_zmod_val` | 41 | `Finset.card_image_of_injOn` | 138 |
| `ZMod.natCast_self` | 34 | `Finset.card_product` | 91 |
| `ZMod.natCast_zmod_eq_zero_iff_dvd` | 27 | `Finset.mem_product` | 479 |
| `Nat.mul_dvd_mul_iff_right` | 3 | `Finset.coe_product` | 5 |
| `map_natCast` | many | `Set.mem_prod` | 23 |
| `pow_succ'` | many | `Finset.mem_coe` | 422 |

The two whose **orientation** matters were checked at their call-sites, not just
by name:

* `Nat.mul_dvd_mul_iff_right` — used in `Erdos1054ConstructionD.lean:52` and
  `Erdos1110Problem.lean:723` as `(Nat.mul_dvd_mul_iff_right hpos).mp hdvd` with
  `hpos : 0 < k` cancelling the **right** factor of `a*k ∣ b*k`. The draft's
  `rw [Nat.mul_dvd_mul_iff_right hm] at hcontra` (`hcontra : 3*m ∣ c*m`,
  `hm : 0 < m`) rewrites to `3 ∣ c` — correct orientation. ✓
* `ZMod.natCast_zmod_val` — used in `BurnsideCountingOQ03.lean:68` as
  `← ZMod.natCast_zmod_val r` (i.e. the lemma is `↑(a.val) = a`). In `hπL`, after
  `map_natCast` turns `π (↑x.val)` into `(↑x.val : ZMod m)`, this rewrites it to
  `x`, closing the `simp only` at `x = x`. ✓

### 3. `hBfree` casework enumeration (`linear_combination` signs)

The delicate `π d = 0` branch derives `key : s0 + s2 = 2*s1`, `hs01 : s0 ≠ s1`,
then `rcases`-es each of `s0,s1,s2 ∈ {0,t}` (8 combinations) and closes with
`first | absurd rfl hs01 | ht_ne (±key) | h2t_ne (±key)`. Enumerating all 8 to
confirm the alternatives are exhaustive (`t ≠ 0` = `ht_ne`, `t+t ≠ 0` = `h2t_ne`):

| (s0,s1,s2) | `key` becomes | closes with |
|---|---|---|
| (0,0,0) | — | `absurd rfl hs01` (s0=s1) |
| (0,0,t) | — | `absurd rfl hs01` |
| (0,t,0) | `0 = 2t` | `h2t_ne (by linear_combination -key)` |
| (0,t,t) | `t = 2t` ⇒ `t=0` | `ht_ne (by linear_combination -key)` |
| (t,0,0) | `t = 0` | `ht_ne (by linear_combination key)` |
| (t,0,t) | `t+t = 0` | `h2t_ne (by linear_combination key)` |
| (t,t,0) | — | `absurd rfl hs01` (s0=s1) |
| (t,t,t) | — | `absurd rfl hs01` |

All 8 are covered by the 5 listed alternatives, and each `linear_combination`
sign checked by hand (e.g. `(t,0,t)`: goal `t+t=0`, `key : t+t=0`, so
`linear_combination key` reduces `(t+t) - (t+t) = 0` ✓). Since `first` tries
alternatives in order and a failing `absurd rfl hs01` / wrong-sign
`linear_combination` simply elaboration-fails and is skipped, the block closes
every branch. **Caveat:** `first`-with-`<;>` back-tracking across a batched
`rcases` is exactly the kind of tactic-combinator behaviour that can still need a
one-line nudge under real elaboration; if it misbehaves, split into eight
explicit `·` bullets using the table above — the *mathematics* of each cell is
settled here.

### 4. `mem_image` / `mem_product` `simp` set

`memB` and `hfinj` reduce `y ∈ (A ×ˢ {0,t}).image f` via
`Finset.mem_image, Finset.mem_product` and the coe-set forms
`Finset.coe_product, Set.mem_prod, Finset.mem_coe` — all present in the compiling
corpus (§2). These are the standard idioms; no exotic simp lemma is invoked.

### Residual risk (honest)

This is a **static** audit: symbol existence, signature shape, orientation, and
casework exhaustiveness. It does **not** catch (a) universe/instance-resolution
quirks (e.g. whether `DecidablePred (@APFree N)` unifies at the new call-sites the
way it does inside `rothNumber`), (b) `push_cast` normal-form mismatches in
`h2t_ne` (`push_cast; linear_combination hh`), or (c) `first`/`<;>` back-tracking
surprises noted in §3. Confidence that the draft compiles **verbatim or with ≤ a
few one-line fixes** is now high, but it remains **UNVERIFIED**. Do **not** add it
under `proofs/Proofs/` until a build path (Docker re-pull or Aristotle recovery)
confirms it — an unbuildable file there would falsify the entry's status.

### Next session

1. Retry Docker (`docker run --rm lean4-arm64:v4.26.0 true`) and Aristotle
   (`prove` on a trivial sorry). If **either** works, port §"Lean draft" Part II.C
   into `RothTheoremQuantitative.lean` and run
   `./proofs/scripts/docker-build.sh Proofs.RothTheoremQuantitative` (or submit
   via Aristotle), then apply any fixes flagged in §3/§Residual risk.
2. On green, update the gallery entry (`src/data/proofs/roth-theorem-k3-oq-01/`):
   the two theorems are 0-axiom, so `status`/`axiomCount` are unaffected, but the
   new explicit lower bound `r₃(3ᵏ) ≥ 2ᵏ` should be surfaced in the entry prose.
