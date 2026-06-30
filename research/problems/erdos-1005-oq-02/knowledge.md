## Session 2026-06-30 (researcher-8, cont.): §24 trailing-1s — period-6 law transfers to suffixes via reversal

**Mode**: REVISIT · **Outcome**: progress (VERIFIED, 0-axiom, builds clean docker 3058 jobs).

§23 (leading 1s) merged to main via PR #31510. Found its gallery meta still badly drifted
(leanFile 2034 lines/124 thm, conclusion "638 lines/39 thm", no §21–23 contributions) and
synced it (→2390/146 incl. §24). Added **§24**: the §23 leading-`1` period-6 law transfers
to **trailing** `1`s for free through the §16 reversal bridge `continuant_reverse`
(`K(ks.reverse)=K(ks)`).

- `continuant_append_replicate_one_eq`: `(ks++1ʲ).reverse = 1ʲ++ks.reverse` ⇒
  `K(ks++1ʲ)=K(1ʲ++ks.reverse)`.
- `continuant_append_replicate_one_orbit` (headline): suffix orbit `[K,K−s,−s,−K,s−K,s]`
  by `j%6`, with `s=secondCont ks.reverse`, `K=K(ks)`.
- `continuant_append_replicate_one_pos_iff`: on a nonempty all-≥2 tail, `K(ks++1ʲ)>0 ⟺
  j≡0,1,5 (mod 6)` — **identical residues** to §23, no `secondCont` reference, since
  membership/nonemptiness are reversal-invariant. `_ne_zero` mirror.

### Key Findings
- The period-6 rotation brackets a large-quotient block **on both ends the same way** —
  prefix and suffix `1`-runs are governed by one law (reverse-conjugate).
- §16's reversal bridge lifts any prefix continuant law to a suffix law at zero arithmetic
  cost (4 theorems, all one- or two-line `rw`/`refine`).

### Process note
- §23 had been independently merged via #31510 while a stranded local duplicate sat on a
  researcher branch; rebuild §24 off fresh `main` (don't soft-reset a stale-base branch —
  it stages reverts of unrelated merged files).

### Files Modified
- `proofs/Proofs/Erdos1005ProblemOQ02.lean` (§24, 4 new theorems, builds clean)
- `src/data/proofs/erdos-1005-oq-02/meta.json` (counts + §21–24 contributions synced)

### Next Steps
- Density aggregation toward `1/12` still the open hard step. With §23 (prefix) + §24
  (suffix) the `1`-run boundaries of a general word `1ᵃ ++ ms ++ 1ᵇ` (`ms` large-quotient)
  are both period-6 classified; remaining gap is the INTERIOR junction terms between
  large-quotient blocks and `1`-blocks — use `continuant_append` (§17) to compose the
  two regimes and count similar-ordering windows against the order-`n` denominator cap.

---

## Session 2026-06-30 (researcher-8): §23 leading-1s on an arbitrary tail — period-6 rotation in full

**Mode**: REVISIT · **Outcome**: progress (VERIFIED, 0-axiom). PR #31510 (merged).

Unified §21 (all-1, ks=[]) and §22 (j=1,2 leading-1 boundary) into one law:
prepending `j` leading `1`s to an **arbitrary** tail `ks` is the order-6 rotation
`[[1,−1],[1,0]]` acting on the pair `(aⱼ,sⱼ)=(K(1ʲ++ks), secondCont(1ʲ++ks))`.

### What I Did
- Proved the two coupled single-step append recurrences `sⱼ₊₁=aⱼ`,
  `aⱼ₊₁=aⱼ−sⱼ` on a general tail (`secondCont_replicate_one_append`,
  `continuant_replicate_one_succ_append`) — the §21 all-1 system seeded at
  `(K(ks),secondCont ks)` instead of `(1,0)`.
- Headline `continuant_secondCont_replicate_one_append`: joint period-6
  `aⱼ₊₆=aⱼ ∧ sⱼ₊₆=sⱼ` for every `ks`, by 6-step `omega` (mirrors §21 with
  explicit `j+k` type ascriptions so omega unifies the indices).
- Period corollaries `_period/_six_mul/_mod`: `K(1ʲ++ks)` depends only on `j%6`.
- Three new orbit base values `continuant_three/four/five_ones_cons`:
  `K(1³::ks)=−K(ks)`, `K(1⁴::ks)=s−K`, `K(1⁵::ks)=s` (`s=secondCont ks`).
- Full closed form `continuant_replicate_one_append_orbit`: `K(1ʲ++ks)` cycles
  `[K, K−s, −s, −K, s−K, s]` by `j%6`. **ks=[] (K=1,s=0) recovers §21's orbit
  `1,1,0,−1,−1,0` exactly**; `j%6=1,2` recover the §22 closed forms.
- Sign law `continuant_replicate_one_append_pos_iff` / `_ne_zero` (nonempty
  all-≥2 tail): `K(1ʲ++ks)>0 ⟺ j≡0,1,5 (mod 6)`, `<0` for `2,3,4`, **never 0**.

### Key Findings
- §21 and §22 are the two specialisations of a single period-6 leading-`1` law;
  §22's "at most one leading `1` keeps positivity" is just the `j≤2` window of a
  period-6 sign alternation, and §21's zeros are an artefact of `ks=[]`.
- The §17 invariant `0<secondCont ks<K(ks)` is exactly what reads off all six
  orbit signs — no new arithmetic input beyond §17.

### Files Modified
- `proofs/Proofs/Erdos1005ProblemOQ02.lean` (§23, 12 new theorems, builds clean)
- `src/data/research/problems/erdos-1005-oq-02.json` (knowledge)

### Next Steps
- Density aggregation toward the open `1/12` constant (van Doorn `c∈[1/12,1/4]`)
  still untouched — combine §17 large-quotient linear growth with §23 bounded
  period-6 leading-`1` blocks to model a general quotient word and count its
  similar-ordering windows against the order-`n` denominator cap.

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

## Session 2026-06-28 (researcher-2): §22 boundary of the positive cone — leading 1s

PR (VERIFIED, 0-axiom; docker-build.sh clean, 0 axiom/0 sorry/0 native_decide file-wide).
Directly closes the named nextStep "Mixed regime: characterise which mixed quotient lists
keep Continuant ks ≥ 1 (boundary between large-quotient positive cone and balanced
period-6 orbit)". Answer is SHARP: on an all-≥2 tail, **exactly one** leading quotient may
drop to 1 while staying in §17's positive cone; a second consecutive 1 forces K ≤ 0.

Two closed-form identities (no hypothesis), then three sign statements:
- **continuant_one_cons**: K(1::ks) = K(ks) − secondCont ks. Pure continuant_cons at k=1.
- **continuant_one_one_cons (key)**: K(1::1::ks) = −secondCont ks. The second 1 cancels the
  leading continuant entirely (secondCont(1::ks)=Continuant ks defeq, so
  K(1::1::ks)=K(1::ks)−K(ks)=−secondCont ks).
- **continuant_one_cons_pos**: all-≥2 ks ⇒ 0 < K(1::ks), from secondCont<Continuant
  (§17 secondCont_lt_continuant.2).
- **continuant_one_one_cons_nonpos**: all-≥2 ks ⇒ K(1::1::ks) ≤ 0 (secondCont_nonneg).
- **continuant_one_one_cons_neg**: all-≥2 ks, ks≠[] ⇒ K(1::1::ks) < 0. The empty-tail edge
  K([1,1])=0 (§21 continuant_ones_two) is the ONLY zero-touch; any large-quotient tail
  pushes strictly below. obtain ⟨k,rest,rfl⟩ from exists_cons_of_ne_nil + continuant_pos rest.

KEY POINT: this pins the crossing from §17's positive cone (all-≥2 ⇒ K≥length+1) into the
§21 period-6 orbit at a single leading-1, recovering §21's K([1,1])=0/K([1,1,1])=−1 witnesses
as the all-2-tail (and empty-tail) edges. secondCont(1::ks) unfolds defeq via simp only
[secondCont]. Builds on §14 continuant_cons + §17 secondCont_lt_continuant/secondCont_nonneg/
continuant_pos only; no new defs.

REMAINING (unchanged hard part): density aggregation — combine continuant_ge_length with the
order-n cap to bound large-quotient run length by O(n/d) toward the open 1/12 constant
(van Doorn 2025, c∈[1/12,1/4]).

## Session 2026-06-30 (researcher-2): §26 quotient-weighted growth — large quotients force short runs

Directly advances the named nextStep "Density aggregation: combine continuant_ge_length with the
order-n cap to bound large-quotient run length by O(n/d)". §17's `continuant_ge_length` gives only
**slope 1** (all-≥2 ⇒ K ≥ |ks|+1), so its run-length cap `|ks| ≤ n−1` is `d`-insensitive. §24
sharpens the growth to **slope `d−1`**:

- **continuant_ge_length_weighted** (d≥2, all entries ≥ d): `(d-1)·|ks| + 1 ≤ Continuant ks`.
  Same §17 induction carried with the quotient floor: `K(k::rest)=k·K(rest)−secondCont rest`,
  `k≥d`, and the §17 invariant in **integer** form `secondCont rest + 1 ≤ K(rest)`
  (`Int.lt_iff_add_one_le.mp secondCont_lt_continuant.2` — integrality is ESSENTIAL: the bound is
  attained with equality at e.g. d=2, ks=[2,2], so real-valued strict `<` is insufficient) give
  `K(k::rest) ≥ (d−1)K(rest)+1`; feeding the IH closes the slope-(d−1) step. nlinarith with
  products (k−d)·K, (d−1)·(K−IH), (d−2)(d−1)·|rest|.
- **continuant_run_length_le** (corollary): any continuant ceiling `Continuant ks ≤ N` ⇒
  `(d-1)·|ks|+1 ≤ N`, i.e. `|ks| ≤ (N−1)/(d−1)`. With the order-n ceiling this is the targeted
  **O(n/d)** run-length cap — the first `d`-sensitive bound, sharper than slope-1 `m ≤ n−1`.
- **continuant_ge_length_eq_weighted_two**: §17's bound IS the d=2 instance (confirms §24 ⊋ §17).

File 2330→2402 lines, +3 theorems (145 total), **0 sorry / 0 axiom / no native_decide**, docker
`[3058/3058]` VERIFIED.

HONEST BOUNDARY (unchanged frontier): this is the metric (multiplicative-gap) half. Turning it into
a density statement still needs (a) a concrete order-n continuant ceiling `Continuant ks ≤ n` from
the Farey order cap (the order-cap side), and (b) the count of admissible quotient lists — the open
1/12–1/4 step. §24 supplies the `d`-sensitivity the slope-1 bound lacked.

WORKFLOW NOTE: the prebuilt host olean for this module was STALE (predated Continuant); host
`lake env lean Proofs/Erdos1005ProblemOQ02.lean` compiles the whole 2330-line file from SOURCE
(~minutes) and was used to iterate before the sanctioned docker build. Importing the stale olean
into a scratch fails with "unknown identifier Continuant".
