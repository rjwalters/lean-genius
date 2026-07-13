-- Synthetic negative fixture: file with NO `^namespace` declaration.
-- The lint should silently skip and exit 0.

def foo : Nat := 0

lemma trivial_lemma : foo = 0 := rfl
