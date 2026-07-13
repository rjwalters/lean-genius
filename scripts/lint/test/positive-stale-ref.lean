-- Synthetic positive fixture: declares `namespace Erdos741APN_I` but body
-- still references the pre-rename namespace `Erdos741`.
-- The lint should flag the `delta Erdos741.foo at h` and
-- `simp_all [Erdos741.bar]` references.

namespace Erdos741APN_I

def foo : Nat := 0
def bar : Nat := 1

lemma stale_in_body : 1 = 1 := by
  -- Stale leftover from sed-style rename (should be flagged):
  have h : foo = 0 := rfl
  delta Erdos741.foo at h
  simp_all [Erdos741.bar]
  change Erdos741.foo = Erdos741.foo
  rfl

end Erdos741APN_I
