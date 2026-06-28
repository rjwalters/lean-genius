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
