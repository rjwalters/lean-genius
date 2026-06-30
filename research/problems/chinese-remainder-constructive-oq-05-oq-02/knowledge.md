# Knowledge Base: chinese-remainder-constructive-oq-05-oq-02

Inductive CRT certificate for an arbitrary list of pairwise-coprime moduli.

---

## Problem Understanding

Sibling `chinese-remainder-constructive-oq-05-oq-01` has `crt_pair_iff` (2 moduli) and
`crt_triple_iff` (3 moduli) uniqueness certificates. OQ: generalise to an arbitrary list
of pairwise-coprime moduli (inductive certificate), connecting to the oq-04 list thread.

---

## Session 2026-06-27 (researcher-9) — SOLVED (uniqueness) [VERIFIED, 0-axiom]

**Outcome**: BUILD + new gallery entry. The n-modulus uniqueness certificate via an
inductive combination engine.

### Built `Proofs/ChineseRemainderConstructiveOQ05OQ02.lean` (89 LOC, 3 theorems)
- `prod_dvd_of_forall_dvd {d} : ∀ {ms}, ms.Pairwise Coprime → (∀ m ∈ ms, m ∣ d) →
  ms.prod ∣ d`. List induction (`intro ms; induction ms`); cons step: head `a` coprime to
  `t.prod` via `Nat.coprime_list_prod_right_iff.mpr ha` (ha from `List.pairwise_cons`),
  then `Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hda hdt` after `List.prod_cons`. Membership
  via `List.mem_cons.mpr (Or.inl rfl)` / `(Or.inr hm)`.
- `crt_list_unique {ms} (hpw) {a b} (ha : a<ms.prod) (hb) (h : ∀ m∈ms, a%m=b%m) : a=b`.
  `rcases le_total a b`; each branch: `(Nat.modEq_iff_dvd' hab).mp (h m hm)[.symm]` gives
  `m ∣ (b−a)`, `prod_dvd_of_forall_dvd` lifts to `ms.prod ∣ (b−a)`,
  `Nat.eq_zero_of_dvd_of_lt hpd (by omega)` → diff 0 → `omega`.
- `crt_345_unique`: [3,4,5] product 60 instance. `hpw`/`hprod` by `decide`; residue ∀ via
  `fin_cases hm <;> assumption`.

### Verification
`lake env lean` (worktree): EXIT 0, no warnings. `#print axioms` all 3 =
`[propext, Classical.choice, Quot.sound]` (engine: only propext, Quot.sound) — 0
counting-axioms, no native_decide (decide used only on the concrete [3,4,5] facts, kernel
decide not native). Gallery meta+annotations created (verified/original/axiomCount 0).

### GOTCHAs
- `induction ms` needs ms generalized: state as `{d} : ∀ {ms}, ... ` and `intro ms;
  induction ms` so the IH quantifies the tail correctly.
- `Nat.coprime_list_prod_right_iff : Coprime k l.prod ↔ ∀ n ∈ l, Coprime k n` (in
  Mathlib.Data.Nat.GCD.BigOperators) — the head-coprime-to-tail-product fact.
- `Nat.Coprime.mul_dvd_of_dvd_of_dvd (hcop) (h1) (h2) : m*n ∣ d`.
- decide (kernel) is fine for 0-axiom; native_decide would add ofReduceBool.
- Build in WORKTREE proofs dir, not main.

### Files
- `proofs/Proofs/ChineseRemainderConstructiveOQ05OQ02.lean` (new, verified 0-axiom)
- `src/data/proofs/chinese-remainder-constructive-oq-05-oq-02/{meta.json,annotations.json}`

### Next Steps
- Pair with an explicit inductive CONSTRUCTION (fold Nat.chineseRemainder along the list)
  for full existence+uniqueness.
- Finset/Multiset version; non-coprime case via lcm.

## Session 2026-06-28 (researcher-1) — the EXISTENCE half [VERIFIED, 0-axiom]

SOLVED → looked outward. The entry had only uniqueness (crt_list_unique); added the
existence half, completing the n-modulus CRT.

- `crt_list_exists : ∀ {ms}, ms.Pairwise Coprime → ∀ r, ∃ x, ∀ m ∈ ms, x ≡ r m [MOD m]`.
  List induction; cons step: head `a` coprime to `t.prod` (coprime_list_prod_right_iff),
  combine head + tail solution via `Nat.chineseRemainder hcop (r a) y`, then push the
  tail-product congruence down to each tail modulus with `Nat.ModEq.of_dvd (List.dvd_prod hmt)`.
- `crt_345_exists` — worked [3,4,5] instance, mirroring crt_345_unique. Existence + uniqueness
  ⟹ the bijection ℤ/60 ≃ ℤ/3 × ℤ/4 × ℤ/5.

Key Mathlib: `Nat.chineseRemainder (co : Coprime n m) (a b) : {k // k ≡ a [MOD n] ∧ k ≡ b [MOD m]}`
(Mathlib.Data.Nat.ModEq); `Nat.ModEq.of_dvd (d : m ∣ n) (h : a ≡ b [MOD n]) : a ≡ b [MOD m]`;
`List.dvd_prod (ha : a ∈ l) : a ∣ l.prod`.

Verified: lake env lean clean; #print axioms crt_list_exists/crt_345_exists =
[propext, Classical.choice, Quot.sound]. File now 123 lines, 5 theorems, 0 sorry / 0 axiom.
