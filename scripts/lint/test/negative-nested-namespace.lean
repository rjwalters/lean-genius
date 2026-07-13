-- Synthetic negative fixture: two declared namespaces. References from one
-- to the other are legitimate cross-namespace refs and should not be
-- flagged.

namespace Foo

def x : Nat := 0

end Foo

namespace FooAPN_I

def y : Nat := 1

-- Legitimate cross-namespace reference: Foo IS a declared namespace in
-- this file, so Foo.x should NOT be flagged.
lemma cross_ref : Foo.x = 0 := rfl

end FooAPN_I
