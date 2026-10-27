import Lisa.Combined

open Lisa Expr

namespace ExpressionNormalizeTests

open ExpressionOrder

def x : SVar := ⟨⟨"x", 0⟩, ind⟩
def y : SVar := ⟨⟨"y", 0⟩, ind⟩
def z : SVar := ⟨⟨"z", 0⟩, ind⟩
def a : Expr := .const (.named "a" ind)
def b : Expr := .const (.named "b" ind)
def p : Expr := .const (.named "p" prop)
def q : Expr := .const (.named "q" prop)
def r : Expr := .const (.named "r" prop)
def g : Expr := .const (.named "g" (ind >> ind))
def h : Expr := .const (.named "h" (ind >> prop))
def pred : Expr := .const (.named "P" ((ind >> ind) >> prop))
def opaqueFn : Expr := .const (.named "opaque" (prop >> prop))

def delayed : Expr := .lam x (.app (.lam z (.var z)) (.app g (.var x)))
def olEta : Expr := .lam x (and (.app h (.var x)) top)

-- Recheck eta after beta contraction and after OL simplification under a binder.
#guard (normalize 12 delayed).expr = g
#guard !(normalize 12 delayed).exhausted
#guard (normalize 12 olEta).expr = h
#guard Combined.Replay.check 12 delayed g
#guard Combined.Replay.check 12 (.app pred delayed) (.app pred g)
#guard Combined.Replay.check 12 olEta h
#guard Combined.Replay.check 12 h olEta
#guard Combined.Replay.check 12 (forall_ x (and (.app h (.var x)) top))
  (.app (.const (.named "forall" ((ind >> prop) >> prop))) h)

-- Do not capture substitution arguments or erase an eta binder occurring in the function.
def captured : Expr := .app (.lam x (.lam y (.var x))) (.var y)
def dependentFunction : Expr := .app (.const (.named "k" (ind >> ind >> ind))) (.var x)
def noEta : Expr := .lam x (.app dependentFunction (.var x))

#guard AlphaEq (normalize 12 captured).expr (.lam z (.var y))
#guard !(AlphaEq (normalize 12 captured).expr (.lam y (.var y)))
#guard (normalize 12 noEta).expr = noEta
#guard !Combined.Replay.check 3 noEta dependentFunction

-- Sort checks cover malformed applications and logical signatures too.
def badBeta : Expr := .app (.lam x (.var x)) p
def badAnd : Expr := and a top

#guard (normalize 12 badBeta).expr = badBeta
#guard (normalize 12 badBeta).expr.sort = none
#guard (normalize 12 badAnd).expr.sort = badAnd.sort
#guard !Combined.Replay.check 3 badBeta p
#guard !Combined.Replay.check 3 (.app (.const (.named "not" (ind >> prop))) a) (neg a)
#guard (normalize 12 (forall_ ⟨x.id, prop⟩ top)).expr.sort = none
#guard (normalize 12 (forall_ ⟨x.id, prop⟩ top)).expr ≠ top
#guard (normalize 12 (.app (.app (.const (.named "eq" (prop >> prop >> prop))) p) p)).expr ≠ top
#guard !Combined.Replay.check 3 (forall_ x p) (forall_ x q)
#guard !Combined.Replay.check 3 (.lam x (.var y)) (.lam y (.var y))

-- Budget exhaustion returns a certified partial result, not a negative theorem.
#guard (normalize 0 delayed).expr = delayed
#guard (normalize 0 delayed).exhausted
#guard Combined.Replay.check 0 delayed g

-- Alpha-equivalent opaque atoms compare through the actual replay backend.
def alphaLeft : Expr := .app pred (.lam x (.var x))
def alphaRight : Expr := .app pred (.lam y (.var y))

#guard Combined.Replay.check 0 alphaLeft alphaRight
#guard hash (reduceLambda alphaLeft) = hash (reduceLambda alphaRight)
#guard !Combined.Replay.check 0 (.var x) (.var y)
#guard !Combined.Replay.check 0 (.var x) (.var ⟨x.id, prop⟩)
#guard !Combined.Replay.check 0 (.lam x (.lam y (.var x))) (.lam x (.lam y (.var y)))

-- Equality recognizes conversion, reflexivity, and unordered operand pairs.
#guard (normalize 12 (eq (.app delayed a) (.app g a))).expr = top
#guard Combined.Replay.check 4 (eq a b) (eq b a)
#guard Combined.Replay.check 4 (eq b a) (eq a b)
#guard Combined.Replay.check 3 (eq a b) top
#guard !Combined.Replay.check 3 top (eq a b)
#guard Combined.Replay.check 6 (eq (.app delayed a) b) (eq b (.app g a))

-- Quantifier monotonicity compares bodies using one shared fresh variable.
#guard (normalize 12 (forall_ x top)).expr = top
#guard (normalize 12 (forall_ x bot)).expr = bot
#guard (normalize 12 (exists_ x top)).expr = top
#guard (normalize 12 (exists_ x bot)).expr = bot
#guard Combined.Replay.check 8 (forall_ x (and p q)) (forall_ y p)
#guard !Combined.Replay.check 4 (forall_ x p) (forall_ y (and p q))
#guard Combined.Replay.check 8 (and (forall_ x (and p q)) r) (and (forall_ y p) r)
#guard Combined.Replay.check 8 (or (forall_ x (and p q)) r) (or (forall_ y p) r)
#guard Combined.Replay.check 8 (neg (forall_ x p)) (neg (forall_ y (and p q)))
#guard Combined.Replay.check 8 (exists_ x (and p q)) (exists_ y p)

-- Contextual atom inequalities must also participate inside OL reasoning.
def narrow : Expr := forall_ x (and p q)
def wide : Expr := forall_ y p

#guard Combined.Replay.check 5 (and narrow (neg wide)) bot
#guard Combined.Replay.check 5 top (or (neg narrow) wide)
#guard Combined.Replay.check 5 (and narrow (neg wide)) (and r (neg r))
#guard !Combined.Replay.check 3 (and wide (neg narrow)) bot
#guard !Combined.Replay.check 3 top (or (neg wide) narrow)
-- The reference calculus proves quantified bounds that replay does not yet recognize.
#guard !Combined.Replay.check 6 (forall_ x (and narrow (neg wide))) bot
example : leq (forall_ x (and narrow (neg wide))) bot :=
  Derives.forall_le_bot rfl (by decide) (Derives.meet_neg_le_bot
    (.trans (.forallMono x rfl (by decide) (by decide) (.meetLeft _ _))
      (.alphaBetaEta (.alpha (by decide)))))
#guard Combined.Replay.check 8 (.app (.const (.named "exists" ((ind >> prop) >> prop))) h)
  (neg (forall_ x (neg (.app h (.var x)))))

-- Arbitrary functions preserve equivalence, not one-way formula order.
#guard Combined.Replay.check 8 (.app opaqueFn (and p top)) (.app opaqueFn p)
#guard !Combined.Replay.check 3 (.app opaqueFn (and p q)) (.app opaqueFn p)
#guard Combined.Replay.check 8 (.lam x (and (.app h (.var x)) p))
  (.lam y (and p (.app h (.var y))))
#guard !Combined.Replay.check 3 (.lam x (and (.app h (.var x)) p))
  (.lam y (.app h (.var y)))

-- Orthologic must not acquire Boolean distributivity during term comparison.
#guard !Combined.Replay.check 3 (and p (or q r)) (or (and p q) (and p r))
#guard Combined.Replay.check 3 (or (and p q) (and p r)) (and p (or q r))

example (fuel : Nat) (e : Expr) :
    isSame ExpressionOrder.leq (normalize fuel e).expr e := normalize_same fuel e

example (fuel : Nat) (p q : Expr) (h : Combined.Replay.check fuel p q = true) :
    ExpressionOrder.leq p q := Combined.Replay.sound ((Combined.Replay.check_iff fuel p q).mp h)

example (fuel : Nat) (e : Expr) :
    letI := ExpressionOrder.reduction fuel
    isSame ExpressionOrder.leq (OrderReduction.reduce (leq := ExpressionOrder.leq) e) e :=
  normalize_same fuel e

#print axioms normalize_same
#print axioms Combined.Replay.sound

end ExpressionNormalizeTests
