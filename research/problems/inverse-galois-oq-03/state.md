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
