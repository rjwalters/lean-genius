# Knowledge Base: fundamental-theorem-algebra-oq-04-oq-03

## Problem Understanding

oq-04-oq-03 = openQuestions[3] of fundamental-theorem-algebra-oq-04:
"Prove the Galois correspondence for ℂ/ℝ: intermediate fields ↔ subgroups of
Gal(ℂ/ℝ) ≅ ℤ/2ℤ, an alternative proof of no-intermediate-fields."

The parent entry proves no-intermediate-fields via the TOWER LAW. This entry
gives the GALOIS route, as requested.

## Deliverables (verified, 0-axiom, original)

`Proofs/FundamentalTheoremAlgebraOQ04OQ03.lean` — 9 thm / 1 def / 3 instances /
0 axioms / 0 sorries / 196 lines.

- `galois_complex_real : IsGalois ℝ ℂ`
- `card_galoisGroup_eq_two : Nat.card (ℂ ≃ₐ[ℝ] ℂ) = 2`
- `galoisGroup_isCyclic : IsCyclic (ℂ ≃ₐ[ℝ] ℂ)` (≅ ℤ/2ℤ)
- `galoisCorrespondence : IntermediateField ℝ ℂ ≃o (Subgroup Gal)ᵒᵈ`
- `card_intermediateField_eq_card_subgroup`
- `subgroup_eq_bot_or_top` (Lagrange)
- `intermediateField_eq_bot_or_top` — every intermediate field is ⊥=ℝ or ⊤=ℂ

### Session 2 additions — Part 6: naming the generator (concrete conjugation)

The original entry only proved `IsCyclic` *abstractly* (`isCyclic_of_prime_card`),
which never exhibits a generator. Part 6 pins the group down concretely:

- `conjAe_ne_one : (conjAe : ℂ ≃ₐ[ℝ] ℂ) ≠ 1` — sends `i ↦ -i`
- `galoisGroup_eq_one_or_conj : ∀ σ, σ = 1 ∨ σ = conjAe` — `Gal(ℂ/ℝ) = {id, conj}`
- `zpowers_conjAe_eq_top : Subgroup.zpowers conjAe = ⊤` — conjugation generates
- `orderOf_conjAe : orderOf conjAe = 2`

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

## Insights / Gotchas (Session 2)

- `Complex.real_algHom_eq_id_or_conj : ∀ f : ℂ →ₐ[ℝ] ℂ, f = AlgHom.id ℝ ℂ ∨ f = conjAe`
  is the key lemma — it enumerates the algebra HOMs, lift to `≃ₐ` by `AlgEquiv.ext` +
  `DFunLike.congr_fun` on `σ.toAlgHom`.
- `conjAe ≠ 1` via image of `I`: `conjAe I = conj I = -I`; `rw [conjAe_coe, conj_I]`;
  finish with `I_ne_zero (by linear_combination (-1/2 : ℂ) * hI)` where `hI : -I = I`.
- `orderOf` of a generator = card of its group: `Nat.card_zpowers` (Nat.card (zpowers a)
  = orderOf a) + `zpowers = ⊤` + `Subgroup.card_top`.
- To show `zpowers g = ⊤` for `g ≠ 1` in an order-2 group: reuse `subgroup_eq_bot_or_top`,
  rule out `⊥` because `g ∈ zpowers g` (`Subgroup.mem_zpowers`) and `g ≠ 1`.

## Dead Ends

- `Subgroup.normal_of_comm H` needs `CommGroup` instance (not auto from IsCyclic).
- `interval_cases` can't use a divisibility hyp for bounds; use `Nat.dvd_prime`.
