-- L'Hopital's Rule: ∞/∞ Form
--
-- Formalizes L'Hopital's rule for the ∞/∞ indeterminate form.
-- Mathlib (as of v4.26) provides only the 0/0 form
-- (HasDerivAt.lhopital_zero_*). This file states the ∞/∞ form.
--
-- The ∞/∞ form: if g(x) → +∞ and f'(x)/g'(x) → c, then f(x)/g(x) → c.
-- Note: only the DENOMINATOR needs to diverge. The numerator can do
-- anything (the conclusion still holds).
--
-- Status: AXIOMATIZED
-- Related: LHopital.lean (0/0 form, verified)

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

namespace LHopitalInfty

open Set Filter Topology

-- ## The ∞/∞ Form of L'Hopital's Rule

/-- **L'Hopital's Rule — ∞/∞ Form, Right Limit**

If f and g are differentiable on (a, b), g'(x) ≠ 0 on (a, b),
g(x) → +∞ as x → a⁺, and f'(x)/g'(x) → c as x → a⁺,
then f(x)/g(x) → c.

Note: we only require g → +∞ (not f → ∞). The classical textbook
statement assumes both tend to ∞, but the theorem holds under the
weaker hypothesis that only the denominator diverges.

Proof sketch (via CMVT):
Fix x₁ ∈ (a, b). For x ∈ (a, x₁), CMVT gives ξ ∈ (x, x₁) with
(f(x)-f(x₁))/(g(x)-g(x₁)) = f'(ξ)/g'(ξ). Then
f(x)/g(x) = [f'(ξ)/g'(ξ)]·(1 - g(x₁)/g(x)) + f(x₁)/g(x).
As x → a⁺: g(x) → ∞, so g(x₁)/g(x) → 0 and f(x₁)/g(x) → 0.
The CMVT ratio is within ε of c. Hence f(x)/g(x) → c. -/
axiom lhopital_infty_right {f g f' g' : ℝ → ℝ} {a b c : ℝ}
    (hab : a < b)
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Ioo a b, g' x ≠ 0)
    (hga : Tendsto g (𝓝[>] a) atTop)
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[>] a) (𝓝 c)) :
    Tendsto (fun x => f x / g x) (𝓝[>] a) (𝓝 c)

/-- **L'Hopital's Rule — ∞/∞ Form, Left Limit**

Mirror of the right-limit version: g(x) → +∞ as x → b⁻. -/
axiom lhopital_infty_left {f g f' g' : ℝ → ℝ} {a b c : ℝ}
    (hab : a < b)
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Ioo a b, g' x ≠ 0)
    (hgb : Tendsto g (𝓝[<] b) atTop)
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[<] b) (𝓝 c)) :
    Tendsto (fun x => f x / g x) (𝓝[<] b) (𝓝 c)

/-- **L'Hopital's Rule — ∞/∞ Form, at +∞**

If g(x) → +∞ as x → +∞ and f'(x)/g'(x) → c, then f(x)/g(x) → c. -/
axiom lhopital_infty_atTop {f g f' g' : ℝ → ℝ} {a c : ℝ}
    (hff' : ∀ x ∈ Ioi a, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Ioi a, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Ioi a, g' x ≠ 0)
    (hgtop : Tendsto g atTop atTop)
    (hdiv : Tendsto (fun x => f' x / g' x) atTop (𝓝 c)) :
    Tendsto (fun x => f x / g x) atTop (𝓝 c)

-- ## Application: Growth Rate Comparison

/-- If f/g → 0 and g → +∞, then eventually f < g.

This is a direct application of the ∞/∞ L'Hopital philosophy:
comparing growth rates via the ratio limit. -/
theorem growth_slower_implies_eventually_lt {f g : ℝ → ℝ}
    (hg : Tendsto g atTop atTop)
    (hfg : Tendsto (fun x => f x / g x) atTop (𝓝 0)) :
    ∀ᶠ x in atTop, f x < g x := by
  -- f/g → 0 means eventually f/g < 1
  have h1 : ∀ᶠ x in atTop, f x / g x < 1 :=
    (tendsto_order.mp hfg).2 1 one_pos
  -- g → +∞ means eventually g > 0
  have h2 : ∀ᶠ x in atTop, (0 : ℝ) < g x :=
    (Filter.tendsto_atTop.mp hg 1).mono (fun x hx => by linarith)
  -- Combine: f/g < 1 and g > 0 implies f < g
  exact (h1.and h2).mono (fun x ⟨hlt, hpos⟩ => by rwa [div_lt_one hpos] at hlt)

end LHopitalInfty
