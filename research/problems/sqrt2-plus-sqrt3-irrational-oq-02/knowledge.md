# Knowledge: sqrt2-plus-sqrt3-irrational-oq-02

## Established Facts

- **n = 2 concrete case (merged, PR #25630).** `{1, √2, √3, √6}` is ℚ-linearly
  independent, axiom-free, via the elementary regroup-over-ℚ(√2) +
  conjugate-multiplication method. Induction heart: `√3 ∉ ℚ(√2)`.
- **General biquadratic case (this session).** For *any* coprime squarefree
  `a, b > 1`, `{1, √a, √b, √(ab)}` is ℚ-linearly independent, i.e.
  `[ℚ(√a, √b) : ℚ] = 4`. The same `linear_combination` certificate that proves
  the `{2,3}` instance works verbatim with `a, b` symbolic — verified by an
  explicit polynomial-identity check before building (the conjugate identity
  `√b·(r² − a·s²) = (a·q·s − p·r) + (p·s − q·r)·√a` is the same in both).
- Squarefree `n > 1` ⟹ `¬ IsSquare n` (`not_isSquare_of_squarefree`) ⟹
  `Irrational (√n)` via Mathlib `irrational_sqrt_natCast_iff`. This replaces the
  radicand-specific divisor-bound irrationality inputs of the n=2 file.

## Open Questions Within This Problem

- The main open question (general Besicovitch, see `problem.md`).
- n = 3 concrete: `{√d : d ∣ 30 squarefree}` (8 radicands) — needs two nested
  conjugate steps / degree-8 multiquadratic field.
- The general induction heart `sqrt_prime_not_mem_multiquadratic` (arbitrary
  finite prime set) remains `sorry` in the sibling
  `Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ02` — BUILD-class (~250–450 LOC),
  needs the "squares of a multiquadratic field are `r²·∏_{T⊆ps} q`" lemma.

## Failed Approaches

(None this session — the generalization went through as designed.)

## Promising Leads

- The two-radicand degree-doubling lemma (`sqrtb_not_in_Qsqrta`, general `a,b`)
  is the genuine n=2 layer of Besicovitch's induction. The next structural step
  is to make the conjugate-multiplication argument relative: `√c ∉ ℚ(√a, √b)`
  for a third coprime squarefree `c`, using a ℚ(√a,√b)-conjugate. If that
  generalizes uniformly it gives the induction heart elementarily, bypassing the
  powerset-squares characterization route currently sketched in the sibling file.
- `irrational_sqrt_of_squarefree` and `not_isSquare_of_squarefree` are clean,
  reusable, and plausibly Mathlib-contribution candidates.

## Session Log

### 2026-06-18 (REVISIT, FRESH-continuation) — generalize n=2 to coprime squarefree pairs

**Outcome:** progress (added verified, axiom-free general theorem).

- Confirmed PR #25630 (n=2 concrete `{1,√2,√3,√6}`) merged to main.
- Generalized to `linearIndependent_one_sqrt_sqrt_sqrt`: coprime squarefree
  `a,b > 1` ⟹ `{1,√a,√b,√(ab)}` ℚ-independent. Added supporting
  `not_isSquare_of_squarefree`, `irrational_sqrt_of_squarefree`, general heart
  `sqrtb_not_in_Qsqrta`, and a consistency corollary recovering the `{2,3}` case.
- Verified the symbolic transfer of the conjugate identity by hand before
  building (no enumeration; one structural generalization covering infinitely
  many biquadratic fields).
- File: `proofs/Proofs/Sqrt2PlusSqrt3IrrationalOQ02.lean` (already registered).

---

## Session 2026-07-02 (researcher-1): induction heart first relative level, VERIFIED

New file `proofs/Proofs/Sqrt2PlusSqrt3IrrationalOQ02Relative.lean` (177 L, 3 thm,
**0 axioms / 0 sorries**, `#print axioms` = `[propext, Classical.choice,
Quot.sound]`). Proves the `n=2 → n=3` step of Besicovitch's induction — the first
non-trivial instance of the sibling file's `sqrt_prime_not_mem_multiquadratic`
`sorry`:

> **`sqrtc_not_mem_biquadratic`** — for pairwise-coprime squarefree `a,b,c > 1`,
> `√c ∉ ℚ(√a,√b)`: no rationals `p,q,r,s` with `√c = p+q√a+r√b+s√(ab)`.
> Hence `[ℚ(√a,√b,√c) : ℚ] = 8`.

Plus `prod_not_rat_sq` (helper: `t²m = n` impossible for coprime squarefree
`m,n>1`, via `√(mn)` irrational) and the concrete corollary
`sqrt5_not_mem_Qsqrt2_sqrt3` (`√5 ∉ ℚ(√2,√3)`).

**Method (no IntermediateField/Galois API — explicit ℚ-coordinates).** Square the
membership eqn; since `{1,√a,√b,√(ab)}` is ℚ-independent
(`linearIndependent_one_sqrt_sqrt_sqrt`) and `c∈ℚ`, matching the four coordinates
gives `p²+q²a+r²b+s²ab=c`, `pq+rsb=0`, `pr+qsa=0`, `ps+qr=0`. The last two force
`r(p²−aq²)=s(p²−aq²)=0`. Split on `p²−aq²`: either `r=s=0` (→ `√c∈ℚ(√a)`, killed
by `sqrtb_not_in_Qsqrta` on radicands `a,c`) or `p=q=0` (→ `√c=r√b` or `√c=s√(ab)`,
killed by `prod_not_rat_sq` via `√(bc)`/`√(abc)` irrational).

**Reusable Lean tricks.**
- The coordinate-extraction `linear_combination` certificate (the crux): after
  `rw [habmul]; push_cast`, the goal closes with
  `linear_combination -hR2 - (q+s√b)²·hsa2 - (r²+s²a+2rs√a)·hsb2`
  where `hR2 : c = (p+q√a+r√b+s(√a√b))²`, `hsa2:√a²=a`, `hsb2:√b²=b`.
  (Derived by hand: `T = (R²−c) − (√a²−a)(q+s√b)² − (√b²−b)(r²+s²a+2rs√a)`.)
- `r(p²−aq²)=0` from `pr+qsa=0`, `ps+qr=0` via `linear_combination p*eR - a*q*eS`;
  the `s` version via `p*eS - q*eR`.
- `Squarefree 2/3/5`: `decide` STALLS on `Nat.minSqFac`; use `Nat.prime_two.squarefree`
  etc. (`Nat.Prime.squarefree`).
- `(a*b).Coprime c` from two coprimalities: `Nat.coprime_mul_iff_left.mpr ⟨hac,hbc⟩`
  (NOT `Nat.Coprime.mul`, which doesn't exist).
- `Squarefree.ne_zero` gives `b ≠ 0` for the `rsb=0 ⟹ rs=0` step.

**Next.** The same regroup-and-split scales to `√d ∉ ℚ(√a,√b,√c)` (degree 8→16),
but needs the degree-8 linear-independence lemma first (analogue of
`linearIndependent_one_sqrt_sqrt_sqrt` over 8 basis products). That is the natural
follow-up toward the sibling's general `sqrt_prime_not_mem_multiquadratic`.
