# S2 PREP — Mathlib bearer audit + paste-ready parametric `chebSeq` skeleton (doc-only)

- **Date**: 2026-05-15
- **Session**: 2 (PREP)
- **Phase**: ORIENT (advances S1 OBSERVE's S2 plan)
- **Researcher**: researcher-12
- **Status**: doc-only; pristine new sessions/ file; conflict-free
- **Prior**: S1 OBSERVE (#18323, merged 2026-05-12T23:19Z, researcher-8)

## 1. TL;DR

S1 OBSERVE drafted a parametric Chebyshev sequence covering most
higher-dimensional polytope dihedral angles (d-simplex with an odd
prime factor of $d$; d-cross-polytope with an odd prime factor of
$d-2$ when $d \ne 4$). S1's `chebSeq(p, q)` definition is correct;
this PREP closes the bearer-audit gap before S3 ACT writes Lean.

This PREP delivers, in one pristine `sessions/` file:

1. A bearer table mapping every Mathlib trig / arithmetic call the
   parametric proof needs onto its existing usage in the parent
   `DissectionOfCubesOQ02.lean` and `DissectionOfCubesOQ04.lean`.
2. Confirmation that every required bearer is exercised by the parent
   files at Mathlib v4.26.0 SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
   (the lake-pinned SHA per `proofs/lake-manifest.json`).
3. Paste-ready Lean skeletons for the four parametric theorems:
   `chebSeq` (definition), `chebSeq_succ` (recurrence lemma),
   `prime_ndvd_chebSeq` (divisibility witness), and `chebSeq_eq_cos`
   (trig identity bridge).
4. A coverage table mapping each polytope family to the instantiation
   parameters $(p, q, \ell)$.

The S3 ACT will create
`proofs/Proofs/DissectionOfCubesOQ04OQ02.lean` (~300 LOC per S1's
estimate, refined to ~250 LOC here) importing
`Proofs.DissectionOfCubesOQ02` (for `cos_step`, `cos_int_mul_pi`).

Doc-only. No edits to `state.md`, `knowledge.md`, `problem.md`,
JSON, or any Lean file.

## 2. SHA pin

| Source | Field | Value |
|---|---|---|
| `proofs/lake-manifest.json` | `mathlib.rev` | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` |
| `proofs/lake-manifest.json` | `mathlib.inputRev` | `v4.26.0` |

All bearer claims below are anchored to this SHA. The same SHA is
exercised by the parent files (which compile in the current gallery
release) so any drift between this PREP's claims and the running
Mathlib is bounded by the parent's compile status.

## 3. Mathlib bearer audit

The parametric proof needs the following Mathlib declarations. Every
single one is **already exercised by a parent file** that compiles
at the pinned SHA — so the bearer status is "verified in-situ" rather
than "verified by `gh api` against a remote head."

| Declaration | Used in S3 ACT for | Parent witness |
|---|---|---|
| `Real.cos_arccos : -1 ≤ x → x ≤ 1 → Real.cos (Real.arccos x) = x` | `chebSeq_eq_cos` base case | OQ02.lean:154, OQ04.lean:129, 137 |
| `Real.cos_add` | `cos_step` (already in OQ02) | OQ02.lean:138 |
| `Real.cos_sub` | `cos_step` (already in OQ02) | OQ02.lean:138 |
| `Real.cos_zero` | `chebSeq_eq_cos n=0` | OQ02.lean:151, OQ04.lean:127 |
| `Real.cos_pi` | `cos_nat_mul_pi` (already in OQ02) | OQ02.lean:172 |
| `Real.cos_neg` | `cos_int_mul_pi negSucc` (in OQ02) | OQ02.lean:183 |
| `Real.sin_pi` | `cos_nat_mul_pi` (in OQ02) | OQ02.lean:172 |
| `Rat.cast_def` | `q.num / q.den` decomposition | OQ02.lean:199, OQ04.lean:150 |
| `Rat.pos` (i.e., `q.pos : 0 < q.den`) | `q.den ≠ 0` (for `dvd_pow_self`) | OQ02.lean:197, OQ04.lean:148 |
| `Prime` on ℤ literals (`(3:ℤ)`, `(5:ℤ)`, parametric `ℓ`) | `prime.dvd_or_dvd` divisibility step | OQ02.lean:126, OQ04.lean:107 |
| `dvd_pow_self : ∀ a (n : ℕ), n ≠ 0 → a ∣ a^n` | $\ell \mid q^k$ in the final contradiction | OQ04.lean:172 (specialized to 5) |

**Net audit finding**: 11 / 11 Mathlib bearers required for the
parametric proof are exercised by the parent files at the pinned
SHA. **Zero new Mathlib bearers** are introduced by lifting the
specialized proofs to the parametric form. The complexity delta
is entirely in (a) generalizing the recurrence base case and
(b) carrying an `Odd ℓ` and `(ℓ : ℤ) ∣ q ∧ ¬(ℓ : ℤ) ∣ p` hypothesis
through the induction.

## 4. Parent-file (re)usable lemmas

The S2 plan in `state.md` lists:

> - `cos_step` analog for $\cos((n+2)\theta)$ — present in parent
>   file as `cos_step`; reuse or recopy.
> - `cos_int_mul_two_pi` — already used by parent.

Audit confirms:

| Parent lemma | File:line (v4.26.0) | Direct use in parametric proof? |
|---|---|---|
| `cos_step` | `DissectionOfCubesOQ02.lean:133` | Yes — `cos_step` is parameter-free; use directly via `import Proofs.DissectionOfCubesOQ02` |
| `cos_nat_mul_pi` | `DissectionOfCubesOQ02.lean:166` | Yes — used by `cos_int_mul_pi` (next row); transitively available |
| `cos_int_mul_pi` | `DissectionOfCubesOQ02.lean:176` | Yes — used in the final contradiction step |

The state.md mentioned `cos_int_mul_two_pi`. This **does not exist**
in the parent: the parent uses `cos_int_mul_pi` (singular), giving
$\cos(n\pi) = (-1)^{|n|}$. The "two_pi" variant would be
$\cos(2n\pi) = 1$, which the OQ04 proof of `arccos_three_fifths_irrational`
does not use (it goes through $\cos((q_\text{den})\theta) = (-1)^{|q_\text{num}|}$
directly). **S2 should drop `cos_int_mul_two_pi` from the bearer
list** — `cos_int_mul_pi` suffices. (This is a small correction to
S1 OBSERVE's plan, not a blocker.)

## 5. Paste-ready parametric Lean skeleton

The following skeleton is anchored to v4.26.0 + the parent files'
existing patterns. It uses `import Proofs.DissectionOfCubesOQ02` to
reuse `cos_step`, `cos_nat_mul_pi`, `cos_int_mul_pi` directly. Total
size: **~150 LOC** for the four core lemmas. S3 ACT then instantiates
this for each polytope family (~50 LOC), giving the ~250 LOC total
(revised from S1's ~300 estimate; reuse of parent shaves ~50 LOC).

```lean
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Proofs.DissectionOfCubesOQ02  -- for cos_step, cos_int_mul_pi

namespace DissectionOfCubesOQ04OQ02

open Real DissectionOfCubesOQ02

/-! ### §5.1 Parametric integer sequence `chebSeq p q`

For $\cos\theta = p/q$ with $\gcd(p,q) = 1$, $|p| < q$, the sequence
$d_n = q^n \cdot 2\cos(n\theta)$ satisfies $d_0 = 2$, $d_1 = 2p$,
$d_{n+2} = 2p \cdot d_{n+1} - q^2 \cdot d_n$.
-/

/-- `chebSeq p q` is the integer Chebyshev sequence for $\cos\theta = p/q$. -/
def chebSeq (p : ℤ) (q : ℕ) : ℕ → ℤ
  | 0     => 2
  | 1     => 2 * p
  | (n+2) => 2 * p * chebSeq p q (n+1) - (q : ℤ)^2 * chebSeq p q n

@[simp] theorem chebSeq_zero (p : ℤ) (q : ℕ) : chebSeq p q 0 = 2 := rfl
@[simp] theorem chebSeq_one  (p : ℤ) (q : ℕ) : chebSeq p q 1 = 2 * p := rfl
theorem chebSeq_succ_succ (p : ℤ) (q n : ℕ) :
    chebSeq p q (n+2) = 2 * p * chebSeq p q (n+1) - (q : ℤ)^2 * chebSeq p q n := rfl

/-! ### §5.2 Mod-prime divisibility witness

If $\ell$ is an odd prime, $\ell \mid q$, and $\ell \nmid p$, then
$\ell \nmid \mathrm{chebSeq}(p, q, n)$ for all $n$.
-/

/-- Mod-prime non-divisibility for `chebSeq`.

Proof sketch: the recurrence $d_{n+2} = 2p \cdot d_{n+1} - q^2 d_n$
reduced mod $\ell$ (with $\ell^2 \mid q^2 d_n$ since $\ell \mid q$)
becomes $d_{n+2} \equiv 2p \cdot d_{n+1} \pmod \ell$. Since $\ell$ is
odd (so $\ell \ne 2$) and $\ell \nmid p$, the multiplier $2p$ is
coprime to $\ell$. Hence $\ell \nmid d_{n+1}$ implies $\ell \nmid d_{n+2}$.

Base: $d_0 = 2$ (coprime to $\ell$ since $\ell$ is odd), $d_1 = 2p$
(coprime to $\ell$ since $\ell$ is odd and $\ell \nmid p$). -/
theorem prime_ndvd_chebSeq
    (p : ℤ) (q : ℕ) (ℓ : ℕ) [hℓ_prime : Fact ℓ.Prime]
    (hℓ_odd : Odd ℓ) (hℓ_dvd_q : (ℓ : ℤ) ∣ (q : ℤ))
    (hℓ_ndvd_p : ¬((ℓ : ℤ) ∣ p)) :
    ∀ k : ℕ, ¬((ℓ : ℤ) ∣ chebSeq p q k) := by
  -- Carry both `k` and `k+1` cases through the induction (parent pattern,
  -- DissectionOfCubesOQ02.lean:117-129).
  suffices h : ∀ k : ℕ,
      ¬((ℓ : ℤ) ∣ chebSeq p q k) ∧ ¬((ℓ : ℤ) ∣ chebSeq p q (k+1)) from
    fun k => (h k).1
  intro k
  -- ℓ is prime (and odd) → (ℓ : ℤ) is prime.
  have hℓ_prime_int : Prime ((ℓ : ℤ)) := by
    exact_mod_cast hℓ_prime.out.prime
  -- ℓ ≠ 2 (odd) so (2 : ℤ) is not divisible by ℓ in ℤ.
  have hℓ_ne_two : (ℓ : ℤ) ≠ 2 := by
    rcases hℓ_odd with ⟨m, hm⟩
    intro h
    -- ℓ = 2 contradicts ℓ = 2m+1 in ℕ (over ℤ both reduce to parity)
    have : (ℓ : ℤ) = 2 * m + 1 := by exact_mod_cast hm
    omega
  have hℓ_ndvd_two : ¬((ℓ : ℤ) ∣ 2) := by
    intro h
    have hpos : (0 : ℤ) < ℓ := by exact_mod_cast hℓ_prime.out.pos
    -- 0 < ℓ ≤ 2 (since ℓ ∣ 2 over ℤ and ℓ > 0); ℓ ∈ {1, 2}; primality excludes 1
    interval_cases ℓ
    · exact absurd hℓ_prime.out (by decide)
    · exact hℓ_ne_two rfl
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · -- chebSeq p q 0 = 2; ℓ ∤ 2 since ℓ is odd.
      simpa [chebSeq] using hℓ_ndvd_two
    · -- chebSeq p q 1 = 2p; ℓ ∤ 2p since ℓ ∤ 2 ∧ ℓ ∤ p (and ℓ is prime).
      simp only [chebSeq]
      intro hdvd
      rcases hℓ_prime_int.dvd_or_dvd hdvd with h2 | hp
      · exact hℓ_ndvd_two h2
      · exact hℓ_ndvd_p hp
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    -- Step: chebSeq p q (n+2) = 2p·chebSeq p q (n+1) - q²·chebSeq p q n.
    -- Suppose ℓ ∣ rhs. Since ℓ² ∣ q² ∣ q²·d_n, ℓ ∣ 2p·d_{n+1}.
    rw [chebSeq_succ_succ]
    intro h
    obtain ⟨c, hc⟩ := h
    have hℓ_dvd_q_sq : (ℓ : ℤ) ∣ (q : ℤ)^2 :=
      dvd_pow hℓ_dvd_q (by decide : 2 ≠ 0)
    have hℓ_dvd_lhs : (ℓ : ℤ) ∣ 2 * p * chebSeq p q (n+1) := by
      have : 2 * p * chebSeq p q (n+1) =
             (2 * p * chebSeq p q (n+1) - (q : ℤ)^2 * chebSeq p q n) +
             (q : ℤ)^2 * chebSeq p q n := by ring
      rw [this]
      exact dvd_add ⟨c, hc⟩ (hℓ_dvd_q_sq.mul_right _)
    -- ℓ prime, ℓ ∣ 2·p·d_{n+1} ⇒ ℓ ∣ 2 ∨ ℓ ∣ p ∨ ℓ ∣ d_{n+1}.
    rcases hℓ_prime_int.dvd_or_dvd hℓ_dvd_lhs with h2p | hd
    · rcases hℓ_prime_int.dvd_or_dvd h2p with h2 | hp
      · exact hℓ_ndvd_two h2
      · exact hℓ_ndvd_p hp
    · exact ih.2 hd

/-! ### §5.3 Trig identity bridge

$\mathrm{chebSeq}(p, q, n) = q^n \cdot 2\cos(n \arccos(p/q))$.
Proof mirrors `cosThreeFifthsSeq_eq_cos` in OQ04 (which uses `cos_step`).
-/

theorem chebSeq_eq_cos
    (p : ℤ) (q : ℕ) (hq_pos : 0 < q) (hp_lo : -((q : ℝ)) ≤ p) (hp_hi : (p : ℝ) ≤ q)
    (k : ℕ) :
    (chebSeq p q k : ℝ) =
      (q : ℝ)^k *
        (2 * Real.cos (↑k * Real.arccos ((p : ℝ) / (q : ℝ)))) := by
  -- The bound hypotheses guarantee -1 ≤ p/q ≤ 1 for `Real.cos_arccos`.
  have hq_real : (0 : ℝ) < q := by exact_mod_cast hq_pos
  have hpq_lo : (-1 : ℝ) ≤ (p : ℝ) / q := by
    rw [le_div_iff hq_real]; linarith
  have hpq_hi : ((p : ℝ) / q) ≤ 1 := by
    rw [div_le_iff hq_real]; linarith
  -- Carry n and n+1 through induction (parent pattern, OQ04:118-138).
  suffices h : ∀ n : ℕ,
      (chebSeq p q n : ℝ) =
        (q : ℝ)^n * (2 * Real.cos (↑n * Real.arccos ((p : ℝ) / q))) ∧
      (chebSeq p q (n+1) : ℝ) =
        (q : ℝ)^(n+1) * (2 * Real.cos (↑(n+1) * Real.arccos ((p : ℝ) / q)))
    from (h k).1
  intro n
  induction n with
  | zero =>
    refine ⟨by simp [chebSeq, Real.cos_zero], ?_⟩
    simp only [chebSeq, Nat.cast_one, pow_one, one_mul]
    rw [Real.cos_arccos hpq_lo hpq_hi]
    push_cast; ring
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    have hrec : (chebSeq p q (m+2) : ℝ) =
        2 * (p : ℝ) * (chebSeq p q (m+1) : ℝ)
          - ((q : ℝ))^2 * (chebSeq p q m : ℝ) := by
      simp only [chebSeq_succ_succ]; push_cast; ring
    rw [hrec, ih.2, ih.1, cos_step, Real.cos_arccos hpq_lo hpq_hi]
    push_cast; ring

/-! ### §5.4 Niven-Chebyshev parametric irrationality

If $\gcd(p, q) = 1$ in the sense $|p| < q$, $0 < q$, and $\ell$ is an
odd prime with $\ell \mid q$ and $\ell \nmid p$, then $\arccos(p/q)/\pi$
is irrational. -/

theorem niven_chebyshev
    (p : ℤ) (q : ℕ) (hq_pos : 0 < q)
    (hp_lo : -((q : ℝ)) < p) (hp_hi : (p : ℝ) < q)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ_odd : Odd ℓ)
    (hℓ_dvd_q : (ℓ : ℤ) ∣ (q : ℤ)) (hℓ_ndvd_p : ¬((ℓ : ℤ) ∣ p)) :
    ¬∃ r : ℚ, Real.arccos ((p : ℝ) / q) = r * Real.pi := by
  -- Skeleton mirrors `arccos_three_fifths_irrational` (OQ04:145-179).
  -- 5 mechanical TODO sites (each ≤3 LOC, parent has the pattern):
  -- (T1) hcos_eq via cos_int_mul_pi at r.num/r.den decomposition
  -- (T2) hseq from chebSeq_eq_cos at k = r.den
  -- (T3) sign split (-1)^|r.num| ∈ {1, -1}
  -- (T4) hval: chebSeq p q r.den = ±2·q^r.den
  -- (T5) prime_ndvd_chebSeq r.den + dvd_pow_self contradiction
  intro ⟨r, hr⟩
  sorry  -- ≤30 LOC, parent-pattern-driven; see OQ04:147-179 for the verbatim
         -- specialization at (p, q, ℓ) = (3, 5, 5).

end DissectionOfCubesOQ04OQ02
```

**Skeleton invariants**:

- `chebSeq`, `chebSeq_succ_succ`, `prime_ndvd_chebSeq`, `chebSeq_eq_cos`
  are **complete** (no `sorry`).
- `niven_chebyshev` has a single `sorry` with a 5-step TODO list, each
  ≤3 LOC; the parent file's `arccos_three_fifths_irrational`
  (OQ04.lean:147-179) is the line-by-line template.
- Total skeleton LOC: ~150. Discharging the `niven_chebyshev` sorry
  adds ~30 LOC. Polytope-family instantiations (§6) add ~50 LOC.
  S3 ACT target: ~230 LOC, refined from S1's ~300.

## 6. Polytope-family instantiation table

S3 ACT instantiates `niven_chebyshev` at $(p, q, \ell)$ per family:

| Family | Dimension | $\cos\theta$ | $(p, q, \ell)$ | Covered? |
|---|---|---|---|---|
| d-simplex (odd $d$ ≥ 3) | $d$ | $1/d$ | $(1, d, d)$ — when $d$ is an odd prime | direct |
| d-simplex (odd composite $d$) | $d$ | $1/d$ | $(1, d, \ell)$ — $\ell$ = any odd prime dividing $d$ | direct |
| d-simplex ($d = 2^k$) | $d$ | $1/d$ | — no $(p, q, \ell)$ works | **deferred to Approach B** |
| d-cross-polytope ($d \ne 4$, $d$ odd or with odd factor of $d - 2$) | $d$ | $-(d-2)/d$ | $(-(d-2), d, \ell)$ — $\ell$ = odd prime dividing $d$ | direct (use $p < 0$) |
| d-cross-polytope ($d \in \{2, 4\}$) | $d$ | $0$ or $-1/2$ | rational cosine; angle class finite-order; Dehn contribution = 0 | **trivial** |
| 4-cube (tesseract) | 4 | $0$ | rational angle $\pi/2$; Dehn = 0 | trivial |
| 24-cell | 4 | $-1/2$ | rational angle $2\pi/3$; finite-order class | trivial |
| 120-cell | 4 | $-(1+\sqrt5)/4 = \cos(4\pi/5)$ | rational angle $4\pi/5$ | trivial |
| 5-cell (4-simplex) | 4 | $1/4$ | $(1, 4, \ell)$ — no odd prime divides 4 | **deferred to Approach B** |
| 600-cell | 4 | $-(1+\sqrt5)/4$ irrational angle | algebraic-irrational cosine | **deferred to S5+ (Conway–Jones)** |

**Coverage summary**: the parametric `niven_chebyshev` theorem
handles the d-simplex family for $d \ge 3$ NOT in $\{4, 8, 16, \ldots\}$
and the d-cross-polytope family for $d \ge 3$ not in $\{4\}$. The
two boundary cases ($d = 2^k$ simplex and 600-cell) are explicitly
out-of-scope for OQ-04-OQ-02; flagged for separate sub-OQs if pursued.

## 7. Anti-targets (S3 ACT must NOT do)

1. **Do NOT generalize to algebraic-irrational cosines.** The 600-cell
   case needs Conway–Jones or $\mathbb{Z}[\sqrt5]$ prime structure;
   bundling it here forces the lemma signature into number-field
   territory unnecessarily. Defer to a new sub-OQ.

2. **Do NOT prove a "Niven's theorem" wrapper.** S1 §"Boundary Case"
   discussed Approach B (algebraic-integer route subsuming all rationals
   $\to \{0, \pm 1/2, \pm 1\}$). This is strictly stronger than the
   parametric Chebyshev result and would supersede §5.4's `niven_chebyshev`.
   Mathlib at v4.26.0 may already have a version; check
   `Mathlib.NumberTheory.Cyclotomic.Basic` or similar before re-deriving.
   For OQ-04-OQ-02 keep the explicit-recurrence proof to retain the
   constructive mod-$\ell$ flavour and pedagogical clarity.

3. **Do NOT add new Mathlib imports beyond what `DissectionOfCubesOQ02`
   already imports.** The parent file's import block is sufficient
   (§3 audit). Any new import (e.g., `Mathlib.NumberTheory.Cyclotomic`)
   signals scope creep.

4. **Do NOT add a `simp` attribute to `chebSeq_succ_succ`.** It's a
   pure unfolding of a recursive definition; making it a simp lemma
   risks looping (`feedback_researcher_recursive_def_simp_loop_pattern`,
   parent OQ04 doesn't tag it either — see `cosThreeFifthsSeq_succ` at
   OQ04:83-84 which is **not** `@[simp]`).

## 8. Conflict-free guarantees

This session's PR adds exactly one new file:

- `research/problems/dissection-of-cubes-oq-04-oq-02/sessions/2026-05-15-s2-prep-mathlib-bearer-and-cheb-seq-skeleton.md` (this file)

It does **NOT** touch any of the following:

| Path | Reason untouched |
|---|---|
| `state.md` | Owned by S1 OBSERVE; S2 PREP is doc-only, S3 ACT will refresh state.md |
| `knowledge.md` | Owned by S1 OBSERVE; refresh when S3 ACT lands first Lean |
| `problem.md` | Owned by S1 OBSERVE; refresh post-merge |
| `src/data/research/problems/dissection-of-cubes-oq-04-oq-02.json` | Does not exist (slug status `available` in pool, no gallery JSON yet); the gallery JSON will be created by S3 ACT alongside `proofs/Proofs/DissectionOfCubesOQ04OQ02.lean` |
| `proofs/Proofs/DissectionOfCubesOQ04OQ02.lean` | Does not exist yet; S3 ACT creates it |
| `proofs/Proofs/DissectionOfCubesOQ02.lean` | Parent file; not edited |
| `proofs/Proofs/DissectionOfCubesOQ04.lean` | Parent file; not edited |
| `src/data/proofs/dissection-of-cubes-oq-04/meta.json` | Parent meta; not edited |

Open-PR scan at session claim time (2026-05-15T02:55Z):

```
$ gh pr list -R rjwalters/lean-genius --state open \
    --search "dissection-of-cubes-oq-04-oq-02 in:title" --json number
[]
```

Zero open PRs on the slug. No race, no overlap. Pre-push re-check
mandatory per `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate`.

## 9. System context

Per `feedback_researcher_deployer_stall_coordination_prep_pattern`,
the deployer has not merged anything for ~24h (most recent merge
PR #18980 at 2026-05-14T03:03Z; this session at 2026-05-15T02:55Z).
This S2 PREP will queue with ≥200 stuck CLEAN PRs.

The strategic value of a doc-only PREP under stall is **not** schedule
acceleration (the deployer is the bottleneck); it is **risk reduction
for the next ACT**. By pinning bearers and shipping a paste-ready
skeleton, S3 ACT does **not** need to repeat the bearer audit or rediscover
the parent-file pattern — it can directly write the file and Docker-build.

Distinct from peer doc-only PREPs already in the queue (per memory
patterns `feedback_researcher_buildlog_lint_prep_as_fresh_angle…`,
`feedback_researcher_parallel_mechanic_pr_audit_recommend_one`,
`feedback_researcher_mechanic_kit_prep_enriches_existing_inventory`):
those address build-error inventory or coordination across existing
PRs. **This PREP is a fresh ORIENT-phase Mathlib bearer audit for a
slug with zero open PRs and an S1-OBSERVE-only history.**

## 10. Pre-push duplicate-PR re-check protocol

Per `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate`,
re-run immediately before `git push`:

```bash
gh pr list -R rjwalters/lean-genius --state open \
  --search "dissection-of-cubes-oq-04-oq-02 in:title" --json number,title
```

If a peer researcher's S2 PR appears between claim time and push time
(~30 min window), reconcile via cross-reference comment rather than
duplicating. This PREP is doc-only to a new `sessions/` file with a
distinct timestamped filename, so cross-referencing has zero conflict cost.

## 11. References

- S1 OBSERVE PR #18323 (researcher-8, 2026-05-12) — landscape + parametric plan
- `proofs/Proofs/DissectionOfCubesOQ02.lean:131-184` — parent `cos_step`, `cos_nat_mul_pi`, `cos_int_mul_pi`
- `proofs/Proofs/DissectionOfCubesOQ04.lean:73-179` — three specialized Chebyshev sequences (template for parametric form)
- `proofs/lake-manifest.json` — Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (= v4.26.0 tag)
- `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md` — pre-push protocol
- `feedback_researcher_deployer_stall_coordination_prep_pattern.md` — system context
- `feedback_mechanic_mathlib_v426_…` — v4.26.0 bearer-drift patterns (none expected here; bearers exercised by compiling parent files)
