# Erdős #153 - Knowledge Base

## Problem Statement

Forum
Favourites
Tags
More
 Go
 Go
Dual View
Random Solved
Random Open

Let $A$ be a finite Sidon set and $A+A=\{s_1<\cdots<s_t\}$. Is it true that\[\frac{1}{t}\sum_{1\leq i<t}(s_{i+1}-s_i)^2 \to \infty\]as $\lvert A\rvert\to \infty$?



A similar problem can be asked for infinite Sidon sets.


Back to the problem

## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 5/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #2000
- Problem #83
- Problem #888
- Problem #1998
- Problem #152
- Problem #154
- Problem #2
- Problem #39
- Problem #1

## References

- ESS94

## Sessions

### Session 2026-07-04 (researcher-8) — OQ-03 Section VII: explicit multiset-coefficient count

**Mode**: REVISIT (infrastructure) · **Outcome**: proof written, BUILD-PENDING (dual-tool blackout)

Added Section VII to `proofs/Proofs/Erdos153OQ03.lean` closing the gap between
Section VI's `|hSumset h A| = |A.sym h|` and the docstring's promised closed form
`C(|A|+h−1, h)`.

**Key mathematical finding — a real Mathlib gap.** Mathlib supplies the type-level
stars-and-bars identity `Sym.card_sym_eq_choose : Fintype.card (Sym α k) =
C(Fintype.card α + k − 1, k)` (`Mathlib/Data/Sym/Card.lean`) but has **no**
cardinality lemma for the *finset* operation `Finset.sym` (confirmed absent from
the `Finset/Sym` docs page; the erdos-340 notes flagged the same). New lemma:

```
card_sym (h : ℕ) (A : Finset ℕ) : (A.sym h).card = (A.card + h - 1).choose h
```

Bridge recipe (all names doc-confirmed): the coercion map
`Sym.map (Subtype.val : ↥A → ℕ) : Sym ↥A h → Sym ℕ h` is
- **injective** — `Sym.map_injective Subtype.val_injective`;
- **onto `A.sym h`** — for `t` with all entries in `A` (`Finset.mem_sym_iff`),
  lift via `Sym.attach t : Sym {x // x ∈ t} h`, relabel each element into `↥A`,
  and `Sym.map_map` + `Sym.attach_map_coe` recover `t`; membership of the image
  uses `Sym.mem_map`.
So `A.sym h = univ.image (Sym.map val)`; `Finset.card_image_of_injective` +
`Finset.card_univ` + `Sym.card_sym_eq_choose` + `Fintype.card_coe` give the count.
Companions: `card_sym_eq_multichoose` (`Nat.multichoose_eq`) and the capstone
`card_hSumset_eq_choose : IsBhSet h A → |hSumset h A| = C(|A|+h−1, h)`.

**Verification status.** NOT machine-checked this session: local Docker's
containerd content store is corrupted (blob `input/output error`, disk 97%), and
Aristotle's `prove` backend returns 404. Proof written against Mathlib-doc
signatures; verify with `./proofs/scripts/docker-build.sh Proofs.Erdos153OQ03`
when a tool returns. `card_sym` is standalone and Mathlib-worthy (a candidate
`Finset.card_sym` upstream contribution).

### Session 2026-07-04b (researcher-8) — re-audit; blackout persists

**Mode**: REVISIT · **Outcome**: no build (blackout), confidence raised via audit

Re-verified every Mathlib name/signature used by Section VII against the *current*
mathlib4 docs (independent second pass): `Sym.map_injective`, `Sym.attach`,
`Sym.attach_map_coe`, `Sym.map_map`, `Sym.mem_map`, `Sym.card_sym_eq_choose`
(`{α} [Fintype α] (k) [Fintype (Sym α k)] : Fintype.card (Sym α k) =
(Fintype.card α + k − 1).choose k`), `Nat.multichoose_eq` (`n.multichoose k =
(n+k−1).choose k`) — all confirmed exactly as used. New corroborating signal: the
**already-merged** base file (commit 21997e39c74) builds `Finset.mem_sym_iff`,
`Sym.coe_injective`, `Sym.mem_coe` (lines 436–445), so the `Finset.sym`/`Sym` API
is proven-good in this exact toolchain. Sole residual risk: the defeq at the
`exact Sym.attach_map_coe t` after `rw [Sym.map_map]` (needs
`Subtype.val ∘ (fun x => ⟨x.1,_⟩) ≡ Subtype.val` by β/η) — high confidence, only a
build can settle it.

**Infra update (important):** disk has RECOVERED to 32% (25 Gi free), yet the
containerd content-store corruption *persists* — even `docker run <existing-imageID>`
fails with `blob … input/output error`. So this is NOT a disk-space issue; it needs
a **Docker Desktop restart/factory-reset** (a host action I won't take unilaterally
while two other agents have in-flight `lean-build-*` containers). Two pre-existing
containers still run; no *new* container can start until Docker is reset.
PR #34776 stays gated (`loom:review-requested`) as BUILD-PENDING — correct
conservative posture until a build confirms.

---

*Generated from erdosproblems.com on 2026-01-12*
