# Knowledge Base: erdos-30-wip-01

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Session 2026-07-22 (researcher-1-3) — Erdős–Turán counting UPPER bound (0-axiom)

**Mode**: FRESH (EMPTY → ACT) · **Outcome**: progress — converted the classical
Erdős–Turán (1941) upper bound from parent-file comments/axioms into 6 axiom-free
theorems in a new companion `proofs/Proofs/Erdos30WIP01.lean` (Docker-verified
v4.31.0; `#print axioms` on all six = `[propext, Classical.choice, Quot.sound]`).

**Mechanism** (difference-map counting, the clean route — avoids the fiddly
sum-over-{2,…,2N} bookkeeping):
- For a Sidon set `A`, the map `diffMap (a,b) = (a:ℤ) − b` is **injective on the
  off-diagonal** (`diffMap_injOn`): `a − b = c − d` rewrites to `a + d = c + b`,
  and `HasDistinctSums` forces `{a,d} = {c,b}`; the branch `a = b` is killed by
  off-diagonality. Uses the parent's `sidon_iff_distinct_sums`.
- The image lands in the `2N` nonzero integers of `Icc (−N) N` (via
  `Int.card_Icc` + `Finset.card_erase_of_mem`), so
  `A.offDiag.card ≤ 2N` (`sidon_offDiag_card_le`), and
  `Finset.offDiag_card : |A.offDiag| = |A|² − |A|` gives `|A|² ≤ 2N + |A|`
  (`sidon_card_sq_le`).
- Squeeze `(|A|−1)² ≤ |A|(|A|−1) ≤ 2N` then `Nat.le_sqrt` ⟹
  `|A| ≤ ⌊√(2N)⌋ + 1` (`sidon_card_le_sqrt`).
- `Finset.sup_le` passes the per-set bound to the supremum:
  `sidonNumber N ≤ ⌊√(2N)⌋ + 1` (`sidonNumber_le_sqrt`), and a `Real.sqrt_sq` /
  `Real.sqrt_le_sqrt` cast gives `(sidonNumber N : ℝ) ≤ √(2N) + 1`
  (`sidonNumber_le_real`) — the `√N` shape of Erdős–Turán.

**Reusable idioms (v4.31)**:
- `obtain ⟨m, rfl⟩ : ∃ m, A.card = m + 1` FAILS (`subst` on a non-variable
  `A.card`); use `obtain ⟨m, hm⟩ … ; rw [hm] at hcard ⊢` instead.
- `Nat.le_sqrt : m ≤ Nat.sqrt n ↔ m * m ≤ n`; `Nat.sqrt_le' n : Nat.sqrt n ^ 2 ≤ n`.
- `Int.card_Icc : #(Icc a b) = (b + 1 − a).toNat` — `omega` closes the `.toNat`
  arithmetic after `Finset.card_erase_of_mem`.
- `(Nat.sqrt n : ℝ) ≤ Real.sqrt n` via `rw [← Real.sqrt_sq (positivity)]` then
  `Real.sqrt_le_sqrt` + `exact_mod_cast (Nat.sqrt_le' n)`.

**Mathlib gap**: no Sidon/B₂-set API, no roots-of-unity/Vandermonde discriminant
product — build the counting bound from `Finset.offDiag_card` / `Int.card_Icc` /
`Nat.le_sqrt`.

**STILL OPEN / out of scope** (untouched, honest): the `N^{1/4}` constant
refinement (Erdős–Turán exact form `√N + N^{1/4} + 1`, and Lindström/BFR/CHO
improvements), Singer's projective-plane LOWER bound `h(N) ≥ (1−o(1))√N` (deep
finite geometry), and the OPEN `$1000` Erdős–Turán conjecture (error `≤ N^ε` for
all `ε > 0`) which stays a `Prop`.

## Session 2026-07-22 (researcher-1-3) — h(10)=4 past the counting wall (perfect-ruler parity)

Added 4 axiom-free theorems to `Erdos30WIP01.lean` (Docker-verified v4.31.0, 8577 jobs;
`#print axioms` = propext/Classical.choice/Quot.sound on all headline results; no
sorry/native_decide/axiom):

- `sidonNumber_ten : sidonNumber 10 = 4` — the **first exact value past the counting wall**.
  For N<=9 the counting bound |A|^2 <= 2N+|A| alone forces |A|<=4; at N=10 it goes slack
  (5*4 = 20 = 2*10), so a genuinely new obstruction is needed.
- `no_sidon_card_five_range_eleven : A ⊆ range 11 → IsSidonSet A → A.card <= 4` — the crux,
  a **perfect-ruler parity argument**. A 5-element Sidon set in {0,...,10} has C(5,2)=10
  distinct positive differences a-b, all in {1,...,10}; being 10 distinct values in a
  10-element set they are EXACTLY {1,...,10} (a perfect difference set / perfect ruler),
  summing to 1+...+10 = 55 (odd). But the sum of ordered positive differences is always
  EVEN: S1-S2 with S1+S2 = sum_{offDiag} p.1 = (|A|-1)*sum A = 4*sum A (each element is a
  first coordinate of |A|-1 ordered pairs), so S1-S2 = 4*sum A - 2*S2 is even. Even != 55.
- `sidonNumber_le_of_card` — general helper: (∀ Sidon A ⊆ {0..N}, |A|<=B) → h(N)<=B.
- `sum_offDiag_fst : sum_{p∈A.offDiag} p.1 = (|A|-1)*sum A` — reusable off-diagonal
  first-coordinate sum (via A×A = diag ⊔ offDiag; sum_product - sum_diag).

### Lean idioms / gotchas (all cost Docker cycles)
- Positive-difference SET = {1..10} WITHOUT computing |P|: take the FULL off-diagonal image
  `A.offDiag.image diffMap = (Icc (-10) 10).erase 0` (eq_of_subset_of_card_le, 20=20 via
  offDiag_card+card_erase_of_mem+Int.card_Icc), then `Finset.filter_image` turns
  `P.image diffMap = (offDiag.image diffMap).filter (0<·) = ((Icc -10 10).erase 0).filter(0<·)
  = Icc 1 10` — closed by `decide` on concrete ℤ finsets. Avoids the swap-bijection card count.
- `Finset.card_nbij'` uses `Set.MapsTo` (coe-membership, painful); `Finset.sum_nbij'` uses
  plain `∀ a ∈ s, i a ∈ t` — MUCH cleaner. Used sum_nbij' with i=j=Prod.swap for the
  swap identity `sum_{offDiag.filter ¬(0<diffMap)} p.1 = sum_P p.2`; left/right_inv =
  `Prod.swap_swap`, value goal = `rfl` (`(swap a).2` defeq `a.1`), membership via
  `show 0 < (a.2:ℤ)-(a.1:ℤ); omega` (defeq reduces `(swap a).1`/`.2`).
- `sum_product` leaves body `((a,y).1:ℤ)` (contains bound var y) so `Finset.sum_const`
  WON'T fire; first fold via `rw [show (∑ y∈A,((a,y).1:ℤ)) = ∑ _y∈A,(a:ℤ) from rfl]`.
- `Finset.sum_image` needs the SUMMAND `f` pinned (`(f := fun d:ℤ => d)`) — Lean can't infer
  it (higher-order); then `rw [← hsi]` to fold `∑_P diffMap → ∑_{image} id`.
- `Finset.sum_filter_add_sum_filter_not s p f` (s,p,f all EXPLICIT) vs
  `Finset.card_filter_add_card_filter_not (s := ...) p` (s IMPLICIT) — inconsistent arg style.
- `Finset.eq_of_subset_of_card_le (h:s⊆t)(h2:#t<=#s) : s=t`.

### Remaining open (unchanged mission)
- h(11)=5 next (witness {0,1,4,9,11}); table continues by case analysis but each new value
  past the wall needs its own exhaustive/parity argument.
- Sharp `-c*sqrt(N)`... (Sidon: polynomial sqrt(N)-order LOWER bound, Singer perfect-difference
  sets) needs modular Sidon infrastructure Mathlib lacks. The $1000 N^{1/4}-error conjecture
  stays a Prop. Elementary two-sided (upper sqrt(2N)+1, lower log via powers-of-two) + exact
  table h(0..10) is the provable envelope.

## Session 2026-07-22b (researcher-1) — table extended: h(11)=h(12)=h(13)=h(14)=5

Added 5 declarations to `Erdos30WIP01.lean` (host-verified v4.31, `lake env lean` exit 0;
`#print axioms` = [propext, Classical.choice, Quot.sound] on all four table entries):
- `isSidonSet_0_1_4_9_11` (private): the 5-element witness — the 5-way `rcases` × omega
  template (625 cases) scales fine on host.
- `sidonNumber_eleven/_twelve/_thirteen/_fourteen`: h(11)..h(14) = 5. Upper bounds are
  pure counting again (`sidonNumber_le_of_sq` + nlinarith with the integrality hint
  `6 ≤ m`): C(6,2)=15 distinct positive differences cannot fit in {1,…,N} for N ≤ 14.
  Lower bounds: the single witness ⊆ range(N+1) by `decide`.

**Next wall (h(15)), precisely characterized:** counting goes slack (6·5 = 30 = 2·15)
AND the h(10) parity argument is silent (a perfect 6-mark ruler of length 15 has
difference sum 1+⋯+15 = 120, even). So h(15) = 5 requires the (true) nonexistence of a
perfect 6-mark ruler — needs a finer obstruction (mod-considerations or bounded case
split), a genuinely new session-sized target.

Build note: parent olean `Proofs.Erdos30Problem` was missing from the shared cache —
build it explicitly first: `lake env lean -o .lake/build/lib/lean/Proofs/Erdos30Problem.olean
Proofs/Erdos30Problem.lean`, then the WIP file elaborates normally.

## Session 2026-07-23 (researcher-1) — table extended: h(22..24)=6, h(25..27)=7

Added 12 declarations to `Erdos30WIP01.lean` (0 sorries, 0 axioms; kernel `decide +kernel`
for the searches):
- `isSidonSet_of_sidonCheck` (private): converse `SidonCheck` bridge — explicit witnesses
  now certify by one `decide` instead of an `|A|⁴`-case `rcases`/`omega` sweep.
- `no_sidon_extension_zero_twentytwo/-three/-four` (private): kernel searches — no
  5-subset of `{1,…,N−1}` extends the pinned endpoints `{0,N}` to a 7-element Sidon set
  (`C(N−1,5)` = 20349 / 26334 / 33649 candidates for N = 22, 23, 24).
- `no_sidon_card_seven_range_twentythree/-four/-five`: no 7-element Sidon set in
  `{0,…,N}` for N = 22, 23, 24 — the h(16) span dichotomy CHAINED: slide down by the
  minimum; reduced span appeals to the obstruction proved just before (anchor: the
  merged h(21) parity theorem `no_sidon_card_seven_range_twentytwo`), span = N pins both
  endpoints and falls to the kernel search.
- `isSidonSet_0_1_4_10_18_23_25` (private): the optimal 7-mark Golomb ruler (span 25,
  differences `{1,…,25} \ {11,12,16,20}`), certified via the bridge.
- `sidonNumber_twentytwo … twentyseven`: h(22)=h(23)=h(24)=6, h(25)=h(26)=h(27)=7.
  Exact table now COMPLETE h(0..27).

**Next wall (h(28..33)):** counting goes slack for eight at N = 28 (8·7 = 56 = 2·28) and
the optimal 8-mark ruler `{0,1,4,9,15,22,32,34}` has span 34 — six values needing
per-N nonexistence of an 8-element set; the dichotomy would need `C(N−1,6)`-scale kernel
searches (~296k at N = 28, growing). DEEP targets unchanged (Singer √N lower bound,
N^{1/4} refinement, $1000 N^ε conjecture).

## Session 2026-07-23b (researcher-1) — h(28)=7 via mod-4 class double count (NO kernel search)

Added 2 declarations to `Erdos30WIP01.lean` (0 sorries, 0 axioms):
- `no_sidon_card_eight_range_twentynine`: no 8-element Sidon set in {0,…,28}.
- `sidonNumber_twentyeight : sidonNumber 28 = 7`. Table now COMPLETE h(0..28).

**Mechanism — the feared ~296k-candidate kernel search was unnecessary.** At N = 28
an 8-element Sidon set has C(8,2) = 28 distinct positive differences in {1,…,28},
so the perfect ruler is FORCED (no span dichotomy: 56 signed differences must
exhaust {±1,…,±28}, the `himageFull` cardinality step from the h(10) template).
Then a **mod-4 double count**: among {±1,…,±28} exactly 14 values are ≡ 0 (mod 4)
and 14 are ≡ 2 (mod 4). With c₀..c₃ the mod-4 class sizes of A:
- same-class ordered pairs: Σ cᵣ(cᵣ−1) = 14 (fiber `T0.filter (p.1%4=r)` =
  `(A.filter (·%4=r)).offDiag`, exactly the h(15) mod-3 fibration);
- cross-class ordered pairs (r vs r+2): Σ cᵣ·c_{(r+2)%4} = 14 (NEW fibration:
  `T2.filter (p.1%4=r) = A_r ×ˢ A_{(r+2)%4}` — off-diagonality is automatic since
  the classes differ; card via `Finset.card_product`).
With Σ cᵣ = 8: first constraint forces multiset {4,2,1,1} or {3,3,2,0}; for every
arrangement c₀c₂+c₁c₃ ∈ {6,9}, never 7. `interval_cases`×4 + omega closes
(hsum8 linearly prunes the nesting to ~165 leaves).

**Lean notes**: general fibration lemma stated as
`∀ r s, s = (r+2)%4 → T2.filter … = A_r ×ˢ A_s` and instantiated with `rfl` inside
the `sum_congr` — avoids `(r+2)%4` literal-normalization headaches; the extraction
step then needs `Nat.reduceAdd, Nat.reduceMod` simprocs to fold `(0+2)%4 → 2`
inside the filter lambdas before `generalize` can abstract the class cards.
Mod-obstruction ladder so far: h(10) parity (sum odd), h(15) mod-3 same-class,
h(21) parity again, h(28) mod-4 same+cross class. Each perfect-ruler wall
N = k(k−1)/2 falls to a residue count so far.

**Next wall (h(29..33)):** perfect ruler NO LONGER forced (28 diffs in {1,…,29}
miss one value); span dichotomy returns: span ≤ 28 slides to the h(28) theorem,
span = N pins {0,N}. Mod-4 alone is INSUFFICIENT at N = 29 (checked: missing
value ≡ 2 (mod 4) with class multiset {4,2,1,1} arranged c₀c₂+c₁c₃ = 6 survives
the double count) — needs either a mod-4+mod-3 combination, endpoint-pinned
sum-collision pruning (a+b = 29 forbidden pairs), or the C(28,6) ≈ 376k kernel
search. DEEP targets unchanged.

## Session 2026-07-24 (researcher-1) — Erdős–Turán construction: polynomial lower bound h(N) ≥ √N/4

Added ~215 lines to `Erdos30WIP01.lean` (0 sorries, 0 axioms; `#print axioms` =
propext/Classical.choice/Quot.sound on all three headline theorems):
- `etMap`/`etSet` (private): the Erdős–Turán (1941) construction — for odd prime p,
  the p numbers `2pi + (i² mod p)` (i < p) form a Sidon set in {0,…,2p²−1}.
- `base_two_p_eq` (private): base-2p digit extraction (quotient/remainder both match).
- `et_quadratic` (private): the crux — i+j = k+l and i²+j² ≡ k²+l² (mod p) with all
  < p forces {i,j} = {k,l}. Over ZMod p: equal power sums + equal e₁ ⟹ equal e₂
  (2 invertible, p odd), so both pairs are root multisets of one monic quadratic;
  (x−k)(x−l) = 0 at x = i via `linear_combination`, split by `mul_eq_zero`.
- `sidonNumber_ge_of_odd_prime`: p ≤ h(2p²−1).
- `sidonNumber_sqrt_lower`: h(N) > ⌊√((N+1)/2)⌋/2 for N ≥ 49 (Bertrand:
  `Nat.exists_prime_lt_and_le_two_mul` on m/2 with m = ⌊√((N+1)/2)⌋; m ≥ 5 makes
  the prime ≥ 3, hence odd).
- `sidonNumber_ge_real_sqrt`: √N/4 ≤ h(N) for N ≥ 49. **With `sidonNumber_le_real`
  (h(N) ≤ √(2N)+1) the file now settles h(N) ≍ √N elementarily** — the former
  DEEP target "Singer √N lower bound" is achieved via Erdős–Turán instead of
  Singer difference sets (no projective planes needed).

**Lean recipe notes:**
- `omega` atomizes `2*p*a` and `2*p*b` as DISTINCT atoms — after extracting a = b
  from the base-2p division, `subst` first so both sides share one atom, then omega.
- Cast to ZMod p via `congrArg (Nat.cast : ℕ → ZMod p)` + `push_cast [ZMod.natCast_mod]`
  (folds `(i² % p : ℕ)` cast to `(i : ZMod p)²` in one pass).
- `(2 : ZMod p) ≠ 0` for odd prime p: via `ZMod.val_cast_of_lt (2 < p)`; needs
  `haveI : NeZero p := ⟨hp.pos.ne'⟩` alongside `Fact p.Prime`.
- Both symmetric-function identities are one-shot `linear_combination`:
  `(x+y+z+w) * h1 - h2` gives 2xy = 2zw; `x * h1 - hq'` gives (x−z)(x−w) = 0.
- `Nat.sub_le_iff_le_add` avoids omega-on-pow when feeding `2*p^2 − 1 ≤ N` to
  `sidonNumber_mono` (omega rejects `^`; linarith with atoms p², (N+1)/2 works).

**h(29) wall CORRECTION (prior note wrong):** the earlier claim "parity ⟹ missing
diff d odd" is FALSE. Mod-2 class count: signed even diffs = 28 − 2[d even] =
o(o−1)+e(e−1) = o²+e²−8 with o+e = 8; d odd needs o²+e² = 36 — impossible
({32,34,40,50,64}) — so **d is EVEN**. Then mod-4: d ≡ 0 (mod 4) gives same-class
12 ⟹ profile {3,3,1,1} but cross-class stays 14 ⟹ c₀c₂+c₁c₃ = 7 ∉ {10,6} —
contradiction. So **d ≡ 2 (mod 4)**, d ∈ {2,6,10,14,18,22,26}. Mod-3: 3∤d ⟹
profile (4,3,1); 3∣d (d ∈ {6,18}) ⟹ profile (4,2,2) — NOT excluded (prior note
also overclaimed "mod-3 forces 3∤d"). Residue invariants alone still don't close
h(29); remaining routes: mod-6/mod-8 cross counts against the narrowed d-list, or
span dichotomy (span 28 dies on the h(28) theorem by translation; span 29 pins
{0,29}, sum-collision kills complementary pairs a+(29−a), C(14,6)·2⁶ ≈ 192k
candidates — still beyond decide+kernel comfort).

**Remaining targets:** h(29..33) per-N nonexistence (above), N^{1/4} refinement
(Erdős–Turán exact form √N + N^{1/4} + 1), $1000 N^ε conjecture (stays a Prop).
The construction side is now DONE at order √N; constant-sharpening (h ≥ (1−o(1))√N
via Singer) would need genuine finite-geometry infra.

## 2026-07-24 h(29) session + evening recovery (researcher-1)

**h(29) = 7 LANDED — verified backtracking search.** The 01:24 session
built the engine, pushed branch `research/erdos30-wip01-h29`, and died
before PR; the evening session recovered it (cherry-pick onto fresh
origin/main, append-conflict vs the ET section resolved, host-verified,
PR'd). New in `Erdos30WIP01.lean` (+199 LOC):

- `searchOK A lo hi k : Bool` — pruned backtracking Sidon-extension
  search: extend the partial set one element at a time in increasing
  order, abandon a branch the moment `SidonCheck` fails. 26,651
  extension tests vs C(28,6) = 376,740 flat candidates (14×), and most
  tests die on an early sum collision.
- `searchOK_complete` — completeness by induction on k: a true extension
  would be rediscovered smallest-element-first (min' of the residual B
  is in the scan range; `SidonCheck` is hereditary via `sidonCheck_mono`;
  `B.erase min'` lives in `{x+1,…,hi}`).
- `search_zero_twentynine_eq_false : searchOK {0,29} 1 28 6 = false` —
  one `decide +kernel`.
- `no_sidon_card_eight_range_thirty` — span dichotomy: slide min to 0;
  span ≤ 28 dies on `no_sidon_card_eight_range_twentynine` (the h(28)
  mod-4 theorem); span 29 pins {0,29} and the six interior elements fall
  to the search via `searchOK_complete` + the `SidonCheck` bridge.
- `sidonNumber_twentynine : sidonNumber 29 = 7` (lower bound: the span-25
  optimal 7-mark ruler still attains 7).

**Counting route CLOSED (evening session, exhaustive check):** for EVERY
modulus m = 2..16 there are class profiles satisfying all symmetric
difference-bucket counts of {1..29}\{d} for some admissible d (48
survivors at m = 8, 42 at m = 6, 144 at m = 12, 330 at m = 15). The
"mod-6/mod-8 cross counts" route suggested by the prior session cannot
work at any single modulus — recorded as a structured blocker.

**Kernel-performance data (evening session, host v4.31):**
- Flat `powersetCard` + quartic `SidonCheck` `decide +kernel`:
  ~105 ms/candidate (2002-candidate slice = 211 s) ⟹ flat C(28,6)
  ≈ 11 CPU-hours — validates the pruned-engine approach.
- ★`Finset.sort` is WF-recursive and does NOT kernel-reduce: any
  `decide +kernel` predicate touching `.sort` gets stuck at
  `instDecidablePairwise`. Keep kernel predicates list-native.
- List-native alternative (`List.sublistsLen` over `List.range'`,
  sublists of a sorted list are sorted — no sort call; explicit
  `diffList` + `Nodup` with early-exit): 2002 candidates ≈ 2 s,
  C(27,5) = 80,730 ≈ 6.5 min (4.8 ms each) — 20–100× faster than the
  Finset formulation. This is the fallback engine if `searchOK` cost
  grows too fast at h(32)/h(33).

**Next:** h(30..33) each = one `searchOK_complete` application + a
constant-bumped span-dichotomy copy; then h(34) = 8 witness
{0,1,4,9,15,22,32,34}. Completes the 8-mark story.
