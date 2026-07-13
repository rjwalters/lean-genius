## Session 2026-07-09 (researcher-6)
Added `Monster_realizing_field_not_solvable` to InverseGaloisOQ03.lean: the
Monster-realizing field K/ℚ has a non-solvable Galois group (field-side
counterpart of Monster_not_solvable_barrier; concrete 'beyond Shafarevich'
witness). Non-solvability transported across 𝕄 ≃* Gal(K/ℚ) via
solvable_of_solvable_injective. No new axioms. Mirrors verified sibling
Monster_realizing_field_finrank. PR #36895. UNVERIFIED — Docker infra down
(containerd content-store I/O errors); all API checked statically vs local
Mathlib v4.26 pin. Meta leanFile synced 16→17 thm / 303→322 lines.

## Session 2026-07-11 (researcher-8) — REPAIR: file was BROKEN on main, now compiles

`InverseGaloisOQ03.lean` did not compile against the current Mathlib pin (the
`Monster_realizing_field_not_solvable` addition was shipped UNVERIFIED under docker outage;
docker-free `bin/lake env lean` now exposes two real breakages). Both fixed:
1. Line 189: `commutator_eq_bot_iff_center_eq_top.mp h` → `unknown constant …mp`. The lemma
   exists but its `.mp` dot-projection no longer resolves with `G` implicit; fixed by making
   the group explicit — `(commutator_eq_bot_iff_center_eq_top (G := Monster)).mp h`.
2. Lines 280 & 301 (`Monster_realizing_field_finrank`, `Monster_realizing_field_not_solvable`):
   after `obtain ⟨K, fK, aK, fdK, gK, ⟨e⟩⟩`, the `haveI := fK; haveI := aK; …` block left
   `Algebra ℚ K` / `Module ℚ K` unsynthesizable at `IsGalois.card_aut_eq_finrank ℚ K`. Fixed by
   `haveI → letI` (transparent instances) — the obtained axiom-witness instances need to be
   definitionally visible for the finrank/aut synthesis. Minimal repro confirmed haveI fails /
   letI succeeds.

Now compiles clean (exit 0, olean written), **0 sorries, 6 axioms** (unchanged, matching meta:
Monster, Monster_card, Monster_isSimple, Monster_realizable_over_Q + the two Monster instances;
`#print axioms` shows no sorryAx / ofReduceBool). Gallery meta counts (361 lines / 19 theorems /
6 axioms) remain accurate. The p-group / Monster-realizability theme is otherwise saturated.

## Session 2026-07-13 (researcher-3) — perfectness as a universal property + field-side (VERIFIED)

SOLVED-state look-outward on a saturated problem. The file had `Monster_commutator_eq_top`
([𝕄,𝕄]=𝕄, perfect) but only in commutator-subgroup form. Added the two structurally
meaningful consequences absent from the file:

- `Monster_no_nontrivial_abelian_quotient {A}[CommGroup A](φ:𝕄→*A)(surj) : Subsingleton A`
  — the universal-property form of perfectness: 𝕄 has NO nontrivial abelian quotient. Proof:
  `map_commutator_eq Monster φ` sends [𝕄,𝕄]=⊤ (surj⟹range=⊤, map_top_of_surjective) to
  commutator A = ⊤; but A abelian ⟹ commutator A = ⊥ (commutatorElement_eq_one_iff_mul_comm);
  ⊤=⊥ in Subgroup A ⟹ Subsingleton A.
- `Monster_realizing_field_gal_commutator_eq_top` — FIELD-SIDE: for Thompson's realizing K,
  commutator (K≃ₐ[ℚ]K)=⊤ (Gal(K/ℚ) is perfect). Transports perfectness across e:𝕄≃*Gal via
  the same map_commutator_eq mechanism. By Galois correspondence ⟹ K/ℚ has NO nontrivial
  abelian subextension (max abelian subext = fixed field of commutator = ℚ). Field-side
  counterpart of Monster_commutator_eq_top, mirrors Monster_realizing_field_not_solvable.

★Gotcha: `map_commutator_eq` has G EXPLICIT (`variable (G)` at Commutator/Basic.lean:224) →
call `map_commutator_eq Monster φ`, NOT `map_commutator_eq φ` (else "expected Type" mismatch).
★Docker exit-139 SIGSEGV + exit-135 SIGBUS codegen crashes (post-elaboration, no error: line)
— retry built green (`✔ Built (8.0s)`, 7749 jobs). 6 axioms unchanged (all deep Monster
inputs, not eliminable), 0 real sorries, no native_decide. 40→42 theorems, 574→640 lines.
Gallery meta synced (was stale 513/37). Theme remains saturated after this.
