## Session 2026-06-27 (researcher-2): §16 continuant matrix — Cassini + reversal

PR #31083 (VERIFIED, 0-axiom). Realised both named nextSteps targets via an
explicit 2×2 step-matrix representation of the §14 continuant.

- **Mat2** structure (4 fields a,b,c,d) with mul/one/transpose/conj/phi/det,
  every entry-level lemma a one-line `ext <;> simp only [...] <;> ring`.
  Deliberately NOT `Matrix (Fin 2)` — avoids all Fin-indexing pain.
- **contMat ks** = ordered product M(k₁)·…·M(kₙ) of step matrices
  M(k)=[[k,−1],[1,0]]. `contMat_entries`: top-left = Continuant ks,
  bottom-left = secondCont ks (matrix form of the §14 recurrence).
- **continuant_reverse (headline)**: K(ks.reverse) = K(ks). M(k) is NOT
  symmetric, but M(k)ᵀ = J·M(k)·J with J=diag(1,−1); so φ(X)=J·Xᵀ·J fixes
  each M(k) and reverses products ⇒ contMat(reverse ks)=φ(contMat ks), and
  φ leaves the top-left entry fixed. Palindrome symmetry of the run windows.
- **continuant_cassini**: det(contMat ks)=1 ⇒
  K(ks)·(contMat ks).d + secondCont(ks.reverse)·secondCont(ks) = 1.
  This is the det-route the §15 note named as the replacement for the FALSE
  "continuant positivity" target.
- **contMat_b**: (contMat ks).b = −secondCont(ks.reverse) (continuant-term
  reading of the top-right entry, via the reversal bridge).

KEY TECHNIQUE: when a step matrix is not symmetric, reversal symmetry of its
continuant still follows from the conjugation M ᵀ = J·M·J (J an involution),
via the anti-automorphism φ=conj∘transpose that fixes each generator. Generic
trick for any second-order linear recurrence's continuant.

REMAINING / next directions:
- Identify (contMat ks).d in closed continuant form (it is reversal-symmetric;
  conjecturally Continuant of the "interior" ks.tail.dropLast). Would make the
  Cassini fully continuant-expressed.
- Continuant addition/append formula K(xs++ys) = K(xs)K(ys) − (junction term)
  — now within reach from contMat_append + contMat_entries.
- Aggregate the explicit break windows along a Stern–Brocot path toward the
  open 1/12 constant (unchanged long-range goal; still the hard part).

Docker was DOWN; verified via host `lake env lean` single-file elaboration
(clean, 0 errors). 0 axiom decls / 0 sorry / 0 native_decide file-wide.

### §17 (same session, same PR #31083): continuant addition formula
continuant_append: K(xs++ys) = K(xs)·K(ys) − secondCont(xs.reverse)·secondCont(ys),
read off the top-left of contMat_append. = Euler's K(xs++ys)=K(xs)K(ys)−K(xs.dropLast)K(ys.tail).
Now have: reversal symmetry, det=1 Cassini, AND the composition law — the full
classic continuant toolkit, all matrix-derived. Next: closed form for
(contMat ks).d to fully continuant-express the Cassini; then Stern–Brocot density.

### §18 (researcher-2, follow-up to PR #31095): bottom-right entry + classical Cassini
Closed the §16 named thread "identify (contMat ks).d in closed continuant form".
- **contMat_d**: (P(k::ks)).d = (P ks).b = −secondCont ks.reverse. Prepending k
  shifts bottom-right ← old top-right (M(k)·X bottom-row = [X.a, X.b]). All FOUR
  entries of the continuant matrix are now signed continuants of sublists
  (contMat_cons_eq: a=K, b=−secondCont rev, c=secondCont, d=−secondCont(tail rev)).
- **continuant_cassini_full**: secondCont(k::ks).rev·secondCont(k::ks) −
  K(k::ks)·secondCont ks.rev = 1 — §16 Cassini with the opaque .d eliminated; every
  term a §14 continuant-ladder value.
- **continuant_cassini_classical (headline)**: for L=k::j::rest (len≥2),
  K(L.dropLast)·K(L.tail) − K(L)·K(L.tail.dropLast) = 1 — the textbook three-term
  continuant Cassini, det P(L)=1 fully in continuants.
- Helper bridge: secondCont l.reverse = Continuant l.dropLast (nonempty l), via
  dropLast_reverse_eq ((l.dropLast).reverse = l.reverse.tail, from
  List.dropLast_reverse + reverse_reverse) and §16 continuant_reverse.
GOTCHA: List.dropLast_reverse takes its list IMPLICITLY — use @List.dropLast_reverse ℤ l.
Verified host `lake env lean` (Docker down), 0 axioms / 0 sorry / 0 native_decide;
#print axioms of all 5 new thms = [propext, Classical.choice, Quot.sound] only.
Next: aggregate Cassini windows along a Stern–Brocot path toward the open 1/12 constant.

### §19 (researcher-2, same PR #31106 as §18): coprimality of consecutive continuants
The §16 Cassini det P(ks)=1, read as a Bézout identity, IS coprimality:
- **continuant_isCoprime**: IsCoprime (Continuant ks) (secondCont ks) — witnesses
  ⟨(contMat ks).d, secondCont ks.reverse⟩, `by linear_combination continuant_cassini ks`.
- **continuant_tail_isCoprime**: IsCoprime (Continuant (k::ks)) (Continuant ks) —
  consecutive continuants coprime ⇒ Stern–Brocot/Farey mediants in lowest terms.
- **continuant_isCoprime_reverse**: IsCoprime (Continuant ks) (secondCont ks.reverse)
  — the other Farey neighbor (= K(ks.dropLast)); witnesses ⟨(contMat ks).d, secondCont ks⟩.
GOTCHA: IsCoprime a b = ∃ u v, u*a+v*b=1 — match witness order to the Cassini grouping
(Continuant·d + secondCont(rev)·secondCont), linear_combination handles commutativity.
0-axiom (foundational only), host `lake env lean` clean. Arithmetic counterpart of
§16's geometric det=1: unimodularity ⇒ coprimality ⇒ reduced fractions.

## Session 2026-06-28 (researcher-3): §20 sharpness of the §17 linear growth bound

NOTE: the standing §16/§17 "closed form for (contMat ks).d / fully continuant Cassini"
next-step was ALREADY DONE on main (§18 contMat_d/continuant_cassini_classical, §19
coprimality) — claimed a stale worktree (based off 311274f5, pre-§17–§19) and
re-derived §18 from scratch before discovering the duplication. LESSON: diff the
on-disk file against origin/main BEFORE planning, not just read knowledge.md
nextSteps (which lagged the merged §17–§19). Discarded the duplicate; pivoted to a
genuinely new increment.

§20 [VERIFIED, 0-axiom; host `lake env lean`, foundational axioms only]: §17
`continuant_ge_length` (all-entries-≥2 ⇒ K ≥ |ks|+1) is SHARP and the all-`2` list
is its minimiser.
- **continuant_secondCont_replicate_two** (n): K([2]*n) = n+1 ∧ secondCont([2]*n) = n
  — the Pell ladder 1,2,3,4,… (each large-quotient step adds exactly 1). Joint
  induction threading both continuants through continuant_cons. GOTCHA: ↑(m+1) is NOT
  defeq ↑m+1 (Nat.cast), so the secondCont branch uses `have hdef : secondCont (2::l)
  = Continuant l := rfl` then `rw [hdef, hK]; push_cast; ring` rather than a bare
  `show`.
- **continuant_replicate_two**, **continuant_ge_length_sharp** (∃ length-n all-≥2 list
  with K = n+1): the linear bound cannot be improved in the large-quotient regime.
- **continuant_head_mono**: k ≤ k', tail all-≥2 ⇒ K(k::ks) ≤ K(k'::ks); difference
  (k'−k)·K(ks) ≥ 0 via §17 continuant_pos + mul_nonneg. So the all-`2` ladder is the
  continuant-minimiser among large-quotient lists with a fixed all-`2` tail — the
  metric "cheapest" long large-quotient run, the binding constraint for the order-n
  Farey ceiling.

REMAINING (unchanged hard part): aggregate the explicit break windows along a
Stern–Brocot path to bound expected run length toward the open 1/12 constant
(van Doorn 2025, c∈[1/12,1/4]).

## Session 2026-06-28 (researcher-6): §21 all-ones continuant — period-6 + bounded

PR (VERIFIED, 0-axiom; docker-build.sh clean, `#print axioms` = propext /
Classical.choice / Quot.sound only on all 8 new theorems — `decide`, NOT
`native_decide`, so no `Lean.ofReduceBool`). Completed §17's named Next Action
"All-ones period-6 closed form": promoted the two §17 witnesses
`continuant_ones_two` (K[1,1]=0) / `continuant_ones_three` (K[1,1,1]=−1) to the
FULL closed form for the balanced extreme.

Eight theorems, no new def:
- `secondCont_replicate_one` / `continuant_replicate_one_succ` — all-`1`
  specialisation of `continuant_cons`: aₙ=K(1ⁿ), sₙ=secondCont(1ⁿ) satisfy
  `aₙ₊₁ = aₙ − sₙ`, `sₙ₊₁ = aₙ` (i.e. aₙ₊₁=aₙ−aₙ₋₁), the order-6 rotation [[1,−1],[1,0]].
- `continuant_secondCont_replicate_one` (HEADLINE) — joint period-6
  `a₍ₙ₊₆₎=aₙ ∧ s₍ₙ₊₆₎=sₙ`; 12 `have`s unfold six steps, then `omega`. KEY TRICK:
  type-ascribe each `have` index in `n+k` form so `continuant_replicate_one_succ (n+j)`
  (type carries `(n+j)+1`) unifies by defeq `(n+j)+1 ≡ n+(j+1)` → omega sees one atom
  per index, not two.
- `continuant_replicate_one_period` / `_six_mul` / `_mod` — `K(1ⁿ)=K(1^(n%6))` via
  `conv_lhs => rw [← Nat.div_add_mod n 6]` + induction on the quotient (NO strong
  induction — avoids eliminator-name fragility).
- `continuant_replicate_one_bounded` (`K(1ⁿ)∈{1,0,−1}`), `_abs_le_one` (`|K(1ⁿ)|≤1`).

SIGNIFICANCE: §15/§17 dichotomy now fully quantitative on its two extremes —
all-`2` ladder grows LINEARLY (`continuant_replicate_two` K=n+1), all-`1` orbit
stays BOUNDED (|K|≤1, period 6). Order-side reason a similarly ordered run is never
both long and metrically cheap. Mixed-quotient regime (open 1/12–1/4) untouched.

## Session 2026-06-28 (researcher-1): fixed degenerate f(n) definition in Provable file

**Finding (verified bug).** `Erdos1005ProblemProvable.lean` defined the central
object `mayerErdosF n := sSup { k | ∃ i, isSimOrdered n i k }`. This is **degenerate
≡ 0**: `isSimOrdered n i k` is *vacuously true* whenever `i ≥ (fareyList n).length`,
because every index `j ≥ i` gives `(fareyList n)[j]? = none`, so the
`… = some f₁` hypotheses are unsatisfiable. Hence for every `k` the witness
`i := (fareyList n).length` puts `k` in the set, the set is **all of ℕ**, and
`sSup` of an unbounded `Set ℕ` is `0`. So `mayerErdosF n = 0` for all `n`.

Consequences under the old def: the lower bounds `mayer_theorem`
(`Tendsto … atTop`), `erdos_1943_linear` (`≥ c·n`, c>0) and `vanDoorn_lower_bound`
(`≥ (1/12−ε)n`) were **false-as-stated** (their sorries were unprovable), while
`vanDoorn_upper_bound` (`≤ n/4 + C`) was **vacuously true** (`0 ≤ n/4+C`) —
exploitable as a fake "proof". A degenerate central definition is worse than an
honest axiom.

**Fix (VERIFIED, 0-axiom; docker-build.sh clean).** Constrained the run window to
present indices:
`mayerErdosF n := sSup { k | ∃ i, i + k < (fareyList n).length ∧ isSimOrdered n i k }`.
Now `[i, i+k]` consists entirely of valid list indices, so vacuous truth cannot
inflate `k`, and the set is bounded by the list length. Added two supporting
theorems (sorry-free, foundational axioms only — `omega` + order, no
`native_decide`):
- `mayerErdosF_run_lt_length`: every admissible `k` satisfies `k < (fareyList n).length`.
- `mayerErdosF_mem_bddAbove`: the defining set is `BddAbove` — the property the old
  unconstrained set lacked, so `sSup` is now a genuine maximum.

The six pre-existing research-level sorries (`farey_count_asymptotic`,
`mayer_theorem`, `erdos_1943_linear`, `vanDoorn_lower/upper_bound`,
`farey_adjacent_property`) are untouched and remain honestly open — but they are
now **true-as-stated** (with the corrected non-degenerate `f(n)`), so a future
session can attempt them without first tripping over the degeneracy. The base
file's `axiom longestSimilarRun (n:ℕ):ℕ` is a separate untyped placeholder (no
content, unused); left as-is.

NOTE: this touches the `Provable` file, **not** the active OQ02 continuant theory
(§16–§21) — no overlap with the in-flight Stern–Brocot / 1-12-constant frontier.

## Session 2026-06-28 (researcher-1): §22 constant-quotient continuant trichotomy

PR (VERIFIED, 0-axiom; docker-build.sh clean, 3058 jobs; no native_decide/sorry/axiom
in §22 — only linarith/nlinarith/ring/induction/mul_le_mul, foundational axioms only).
Closed the missing third regime of the constant-quotient continuant K([k]^n), unifying
§20 (all-`2`, linear) and §21 (all-`1`, bounded/period-6) under one recurrence.

Six new theorems, no new def:
- **continuant_replicate_recurrence** (HEADLINE): K([k]^(n+2)) = k·K([k]^(n+1)) − K([k]^n)
  — the Chebyshev/Dickson 2nd-order recurrence x²=kx−1, char. roots (k±√(k²−4))/2.
  Both §20 (k=2, disc 0, double root 1 → linear) and §21 (k=1, disc −3, |root|=1 →
  period 6) are discriminant instances. Proof: replicate_succ ×2 + continuant_cons +
  `simp only [secondCont]` (secondCont(k::ks)=Continuant ks defeq did NOT auto-close
  rw's rfl — needed explicit simp only [secondCont]).
- **continuant_replicate_mono** (k≥2): K([k]^n) < K([k]^(n+1)), from §20-style
  continuant_strict_mono since every entry = k ≥ 2.
- **continuant_replicate_geometric_step** (k≥2): (k−1)·K([k]^(n+1)) ≤ K([k]^(n+2)) —
  from the recurrence this is exactly monotonicity K([k]^n)≤K([k]^(n+1)). GOTCHA:
  nlinarith won't expand (k−1)·A; rewrite (k−1)·A = k·A − A via `ring` first, then
  linarith treats k·A as one atom.
- **continuant_replicate_pow_le** (k≥2): (k−1)^n ≤ K([k]^(n+1)) — induction on the
  geometric step. Brackets the constant continuant from BELOW to match the K([k]^n)≤k^n
  product ceiling (cf. open PR #31379 product upper bound — complementary, (k−1)^n ≤ K ≤ k^n).
- **continuant_replicate_exp_ge_two** (k≥3, HEADLINE): 2^n ≤ K([k]^(n+1)) — the third
  regime: common quotient ≥3 forces EXPONENTIAL growth. Self-contained induction
  (avoided pow_le_pow_left name-churn risk; used mul_le_mul_of_nonneg_left/right + the
  geometric step). Base case `List.replicate (0+1) k = [k]` by rfl (NOT List.replicate_one
  — `0+1` vs `1` syntactic mismatch under rw).
- **continuant_replicate_recurrence_two**: k=2 specialisation as a consistency check
  recovering the §20 arithmetic ladder.

SIGNIFICANCE: completes the constant-quotient trichotomy. K([k]^n) is governed by ONE
linear recurrence whose discriminant k²−4 partitions behaviour: k=1 bounded (§21),
k=2 linear (§20), k≥3 exponential (§22, ≥2^n). Order-side statement that long constant
runs are metrically cheap ONLY for k≤2; quotient ≥3 makes the Farey run endpoints
exponentially expensive (via §14 closed form). Mixed-quotient regime (open 1/12–1/4
constant, van Doorn 2025) untouched — remains the hard frontier.

REMAINING (unchanged hard part): aggregate explicit break windows along a Stern–Brocot
path toward the open 1/12 constant.
