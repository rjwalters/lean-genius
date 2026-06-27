
## Session (researcher-1, 2026-06-27) — Part 8: congruence-invariance of optimality

State on entry: file complete through Part 7 (PR #30601 merged) — raw count h≡0,
corrected hCong via congruence quotient, hCong non-degenerate *conditional on*
[Finite (Quotient (OptimalSetoid n))]. 0 sorry / 0 axiom, verified.

Identified gap: Parts 1–3 only proved the *translation* subgroup preserves
optimality (translate_optimal), but hCong quotients by the FULL isometry group
(AreCongruent). The well-definedness backbone — optimality constant on congruence
classes — was unproved.

Added Part 8 (PR #30629, draft, BUILD-BLOCKED on host-disk exhaustion):
  - isometry_diameter / isometry_valid / applyIsometry_optimal  (full-group
    generalizations of the translate_* lemmas)
  - optimal_of_congruent  (P optimal ∧ P~Q ⟹ Q optimal)
  - translationIsometry / Ptranslate_eq_applyIsometry / translate_optimal_via_isometry
    (recover Parts 1–3 as the translation special case)
Purely additive +80 lines, 0 sorry / 0 axiom.

Open / next directions (unresolved, hard):
  - The genuine Erdős content is UNCONDITIONAL finiteness of Quotient(OptimalSetoid n).
    All non-degeneracy results still carry the [Finite ...] hypothesis.
  - hCong n ≥ 2 for large n (the actual OQ-02 weak conjecture) remains open.

## Session (researcher-1, 2026-06-27) — Part 9: first UNCONDITIONAL hCong values

Added Part 9 to Erdos103OQ02.lean (same PR #30629, still BUILD-BLOCKED). Removes
the [Finite] hypothesis in the concrete small cases:
  - diameter_lt_two / minDiameter_lt_two / isOptimal_iff_valid_lt_two: for n<2 the
    diameter is identically 0 (else-branch of `diameter`), so optimality ⇔ validity.
  - hCong_eq_one_of_all_congruent: nonempty + all-optimal-configs-congruent ⇒
    hCong n = 1, NO [Finite] hypothesis (nonempty subsingleton quotient ⇒ card 1
    via Nat.card_eq_one_iff_unique). This is the lever that discharges finiteness.
  - hCong_zero (=1, PointConfig 0 is the one-point empty-tuple type) and
    hCong_one (=1, all single points congruent by translation). First
    finiteness-free values; the hCong analogue of the parent's informal h(2)=h(3)=1.
Purely additive +80 lines, 0 sorry / 0 axiom.

Mathlib names HAND-VERIFIED against proofs/.lake/packages/mathlib (build was blocked):
  Nat.card_eq_one_iff_unique (Nat.card α=1 ↔ Subsingleton∧Nonempty), ciInf_const
  ([Nonempty ι], ℝ is only conditionally complete), iInf_congr (lives in the
  [InfSet] section so it DOES apply to ℝ — not CompleteLattice-only), Fin.elim0,
  Fin.instUnique : Unique (Fin 1) ⇒ Subsingleton (Fin 1).

GOTCHAs this session:
  - Docker responds to `docker ps` but CANNOT build: host /System/Volumes/Data at
    100% (5.6 GiB free) → image build dies on containerd meta.db input/output error.
    Same blocker as Part 8; commit + push, keep PR draft, hand-verify lemma names.
  - hCong is a `def`, so `rw [hCong]` fails — use `show Nat.card (...) = 1` (defeq).
  - Next direction (still open & hard): UNCONDITIONAL Finite (Quotient (OptimalSetoid n))
    for general n, and hCong n ≥ 2 for large n.

GOTCHAs this session:
  - Shared session branch (research/researcher-N-sessionM) may already back an OPEN
    PR for unrelated work (here #30620 cayley-hamilton). Do NOT rebase/force-push it.
    Put new work on a dedicated branch off origin/main.
  - Docker host /System/Volumes/Data at 100% → containerd meta.db I/O error, no builds.
