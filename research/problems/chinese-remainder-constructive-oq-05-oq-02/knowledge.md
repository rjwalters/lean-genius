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
