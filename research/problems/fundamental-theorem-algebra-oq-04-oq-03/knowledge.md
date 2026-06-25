# Knowledge Base: fundamental-theorem-algebra-oq-04-oq-03

## Problem Understanding

oq-04-oq-03 = openQuestions[3] of fundamental-theorem-algebra-oq-04:
"Prove the Galois correspondence for ℂ/ℝ: intermediate fields ↔ subgroups of
Gal(ℂ/ℝ) ≅ ℤ/2ℤ, an alternative proof of no-intermediate-fields."

The parent entry proves no-intermediate-fields via the TOWER LAW. This entry
gives the GALOIS route, as requested.

## Deliverables (verified, 0-axiom, original)

`Proofs/FundamentalTheoremAlgebraOQ04OQ03.lean` — 5 thm / 1 def / 3 instances /
0 axioms / 0 sorries / 136 lines.

- `galois_complex_real : IsGalois ℝ ℂ`
- `card_galoisGroup_eq_two : Nat.card (ℂ ≃ₐ[ℝ] ℂ) = 2`
- `galoisGroup_isCyclic : IsCyclic (ℂ ≃ₐ[ℝ] ℂ)` (≅ ℤ/2ℤ)
- `galoisCorrespondence : IntermediateField ℝ ℂ ≃o (Subgroup Gal)ᵒᵈ`
- `card_intermediateField_eq_card_subgroup`
- `subgroup_eq_bot_or_top` (Lagrange)
- `intermediateField_eq_bot_or_top` — every intermediate field is ⊥=ℝ or ⊤=ℂ

## Insights / Gotchas

- `Normal ℝ ℂ` is NOT default; needs `IsAlgClosure ℝ ℂ` in scope (`IsAlgClosure.normal`
  instance). `Algebra.IsSeparable ℝ ℂ` IS automatic (char 0).
- `IsGalois.mk` builds IsGalois from separable + normal.
- `IsGalois.card_aut_eq_finrank` returns `Nat.card`.
- Subgroup count of prime-order group: use Lagrange `Subgroup.card_subgroup_dvd_card`
  + `Nat.dvd_prime` + `Subgroup.eq_bot_of_card_eq`/`eq_top_of_card_eq` (avoids
  needing a CommGroup instance for normality).
- Correspondence lands in `(Subgroup G)ᵒᵈ`; `OrderDual.ofDual/toDual` are defeq;
  `OrderIso.map_top`/`map_bot` flip ⊤↔⊥.

## Dead Ends

- `Subgroup.normal_of_comm H` needs `CommGroup` instance (not auto from IsCyclic).
- `interval_cases` can't use a divisibility hyp for bounds; use `Nat.dvd_prime`.
