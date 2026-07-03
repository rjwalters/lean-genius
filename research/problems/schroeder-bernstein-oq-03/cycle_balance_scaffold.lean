/-
  SCAFFOLD (researcher-4, 2026-07-03) — NOT BUILT. Paste into
  proofs/Proofs/SchroederBernsteinOQ03.lean (Section 4-bis) and verify against
  v4.26.0 in a build-capable session.

  Purpose: replace the `BuiltFrom` hypothesis of `escape_exists` with the
  cons-preserved **cycle-balance** invariant, so an extension-only (cons)
  scheduler discharges every stage's escape obligation. This resolves the
  termination↔stability fork in favour of the short "extend-only" path
  (Rogers §7.4), removing the need for a finite-injury stabilization argument.

  See knowledge.md, session 2026-07-03 (researcher-4), for the mathematics.
  Symbols used below (`fwdOrbit`, `chaseTarget`, `mDom`, `mRan`, `IsMatching`,
  `MatchingCorr`, `escape_exists`, `domain_step_exists`) are all already defined
  in SchroederBernsteinOQ03.lean; this file assumes that context.
-/

namespace MyhillIsomorphism

/-- `a` is periodic under `g ∘ f` (lies on a finite forward-orbit cycle). Under
    injective `g ∘ f` this is the only alternative to an all-distinct infinite
    forward orbit (no ρ-shaped orbits: injectivity forbids tails into cycles). -/
def OnCycle (f g : ℕ → ℕ) (a : ℕ) : Prop := ∃ m, 1 ≤ m ∧ fwdOrbit f g a m = a

/-- **Case (i): infinite forward orbit ⇒ escape, no invariant needed.** If `a` is
    not `g∘f`-periodic then `f (fwdOrbit f g a ·)` is injective, so among
    `(mRan L).length + 1` values one lands outside `mRan L`. This is the EASY half
    (self-contained pigeonhole; do this first). Proof sketch: `¬OnCycle` ⟹
    `fwdOrbit f g a` injective on `Finset.range ((mRan L).length + 1)` ⟹ (f inj)
    `f ∘ fwdOrbit` injective there ⟹ can't map into the smaller `mRan L`. -/
theorem escape_of_infinite_orbit {f g : ℕ → ℕ}
    (hf : Function.Injective f) (hg : Function.Injective g)
    {L : List (ℕ × ℕ)} {a : ℕ} (hac : ¬ OnCycle f g a) :
    ∃ N, N ≤ (mRan L).length ∧ f (fwdOrbit f g a N) ∉ mRan L := by
  sorry

/-- The cons-preserved balance invariant, stated over one cycle. A faithful Lean
    encoding of "cycle `C`" is the open modelling choice (see knowledge.md step 3):
    either a `Finset` cut out by `Nat.find` of the period, or a reformulation that
    avoids naming `C`. The *specification* is: for every `g∘f`-cycle `C`,
    `(C ∩ mDom L).card = (f '' C ∩ mRan L).card`. Placeholder signature below. -/
def Balanced (f g : ℕ → ℕ) (L : List (ℕ × ℕ)) : Prop := sorry

/-- **Case (ii): balanced + periodic ⇒ escape.** If `a` is on a cycle `C` of size
    `m` and `a ∉ mDom L`, then `(C ∩ mDom L).card ≤ m-1`, so balance gives
    `(f '' C ∩ mRan L).card ≤ m-1 < m = |f '' C|`, hence some `f (fwdOrbit f g a k)`
    is fresh. -/
theorem escape_of_balanced {f g : ℕ → ℕ}
    (hf : Function.Injective f) (hg : Function.Injective g)
    {L : List (ℕ × ℕ)} (hbal : Balanced f g L)
    {a : ℕ} (hac : OnCycle f g a) (ha : a ∉ mDom L) :
    ∃ N, N ≤ (mRan L).length ∧ f (fwdOrbit f g a N) ∉ mRan L := by
  sorry

/-- `BuiltFrom`-free escape, by dichotomy on `OnCycle`. Drop-in replacement for the
    `BuiltFrom`-hypothesised `escape_exists`; the scheduler carries `Balanced`
    (cons-preserved, below) instead of `BuiltFrom`. -/
theorem escape_exists' {f g : ℕ → ℕ}
    (hf : Function.Injective f) (hg : Function.Injective g)
    {L : List (ℕ × ℕ)} (hbal : Balanced f g L) {a : ℕ} (ha : a ∉ mDom L) :
    ∃ N, f (fwdOrbit f g a N) ∉ mRan L := by
  by_cases hac : OnCycle f g a
  · obtain ⟨N, _, hN⟩ := escape_of_balanced hf hg hbal hac ha; exact ⟨N, hN⟩
  · obtain ⟨N, _, hN⟩ := escape_of_infinite_orbit hf hg hac (L := L); exact ⟨N, hN⟩

/-- **Claim B, domain half.** A domain cons `(a, f (fwdOrbit f g a N))` with a fresh
    escape target preserves `Balanced`: on `a`'s cycle both `(C ∩ mDom)` and
    `(f '' C ∩ mRan)` gain exactly one element; other cycles are untouched (the
    escape target lies on `a`'s component only, by injectivity/no-tails). -/
theorem balanced_cons_domain {f g : ℕ → ℕ}
    (hf : Function.Injective f) (hg : Function.Injective g)
    {L : List (ℕ × ℕ)} (hbal : Balanced f g L) {a b : ℕ}
    (ha : a ∉ mDom L) (hb : b ∉ mRan L) (hb_orbit : ∃ N, b = f (fwdOrbit f g a N)) :
    Balanced f g ((a, b) :: L) := by
  sorry

/-- **Claim B, range half** (dual under `Prod.swap` / the `(q,p,g,f)` problem). -/
theorem balanced_cons_range {f g : ℕ → ℕ}
    (hf : Function.Injective f) (hg : Function.Injective g)
    {L : List (ℕ × ℕ)} (hbal : Balanced f g L) {c : ℕ}
    (hc : c ∉ mRan L) (hc_dom : g c ∉ mDom L) :
    Balanced f g ((g c, c) :: L) := by
  sorry

/-- Base case: the empty matching is balanced (both sides 0 for every cycle). -/
theorem balanced_nil (f g : ℕ → ℕ) : Balanced f g [] := by
  sorry

end MyhillIsomorphism
