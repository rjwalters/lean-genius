-- Synthetic negative fixture: declares `namespace Erdos741APN_I` with all
-- in-body references qualified to the renamed namespace (or unqualified).
-- The lint should NOT flag anything here.

namespace Erdos741APN_I

def foo : Nat := 0
def bar : Nat := 1

lemma clean_in_body : 1 = 1 := by
  have h : foo = 0 := rfl
  -- Unqualified references, OK:
  delta foo at h
  simp_all [bar]
  -- Properly renamed references, OK:
  change Erdos741APN_I.foo = Erdos741APN_I.foo
  rfl

-- A comment mentioning Erdos741.foo should not be flagged.
-- The next line is a comment, not code: delta Erdos741.foo at h

end Erdos741APN_I
