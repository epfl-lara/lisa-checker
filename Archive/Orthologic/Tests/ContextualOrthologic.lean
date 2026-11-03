import Lisa.Orthologic.ContextualCalculus

namespace Lisa.Tests.ContextualOrthologic

open Orthologic.Contextual

private def p : Term Nat Nat := .atom 0
private def q : Term Nat Nat := .atom 1
private def r : Term Nat Nat := .atom 2

#guard check p p
#guard !check p q
#guard check (.meet p .top) p
#guard check p (.meet p .top)
#guard check (.unary 0 (.meet p .top)) (.unary 0 p)
#guard check (.unary 0 p) (.unary 0 (.meet p .top))
#guard check (.unary 0 (.meet p (.neg p))) (.unary 0 .bot)
#guard check (.unary 0 (.neg (.neg p))) (.unary 0 p)
#guard !check (.unary 0 (.meet p q)) (.unary 0 p)
#guard !check (.unary 0 p) (.unary 0 q)
#guard !check (.unary 0 p) (.unary 1 p)
#guard check (.binary 0 (.meet p .top) (.join q .bot)) (.binary 0 p q)
#guard !check (.binary 0 p q) (.binary 0 q p)
#guard check (.unary 0 (.binary 1 (.unary 2 (.meet p .top)) q))
  (.unary 0 (.binary 1 (.unary 2 p) q))
#guard check (.neg (.unary 0 (.join p .bot))) (.neg (.unary 0 p))
#guard check .top (.join (.unary 0 p) (.neg (.unary 0 p)))
#guard check (.meet (.unary 0 p) (.neg (.unary 0 p))) .bot
#guard !check (.meet p (.join q r)) (.join (.meet p q) (.meet p r))
#guard !check (.unary 0 (.meet p (.join q r)))
  (.unary 0 (.join (.meet p q) (.meet p r)))
#guard decide (Derives (.unary 0 (.meet p .top)) (.unary 0 p))
#guard !decide (Derives (.unary 0 (.meet p q)) (.unary 0 p))

private def nest : Nat → Term Nat Nat → Term Nat Nat
  | 0, p => p
  | n + 1, p => .unary 0 (nest n p)

-- Unequal nested literals must not trigger recursive saturation at every layer.
#guard !check (nest 32 p) (nest 32 q)
#guard !check (nest 32 p) (nest 32 (.neg p))
#guard check (nest 32 (.meet p .top)) (nest 32 p)

-- Hoisting the runtime depth must preserve the original decision exactly.
example [DecidableEq α] [DecidableEq κ] (p q : Term α κ) :
    check p q = if p = q then true else
      Orthologic.Calculus.Free.compare (interpret (max p.depth q.depth) p)
        (interpret (max p.depth q.depth) q) := rfl

#guard check (.binary 3 (nest 16 (.meet p .top)) (nest 8 (.join q .bot)))
  (.binary 3 (nest 16 p) (nest 8 q))
#guard !check (.binary 3 (nest 16 (.meet p .top)) (nest 8 q))
  (.binary 3 (nest 16 p) (nest 8 r))

example (p q : Term α κ) [DecidableEq α] [DecidableEq κ] :
    check p q = true ↔ Derives p q := check_iff p q

example (p q : Term α κ) (n m : Nat)
    (hp : p.depth ≤ n) (hq : q.depth ≤ n)
    (hp' : p.depth ≤ m) (hq' : q.depth ≤ m) :
    interpret n p ≤ interpret n q ↔ interpret m p ≤ interpret m q :=
  interpret_stable p q n m hp hq hp' hq'

#print axioms check_valid
#print axioms check_iff
#print axioms Derives.complete

end Lisa.Tests.ContextualOrthologic
