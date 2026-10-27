import Lisa.Orthologic.ExpressionModel
import Lisa.AlphaBetaEta
import Lisa.Order
import Lisa.Orthologic.Algebra

/-!
Construct the reference expression order from conversion and ortholattice rules.
The quotient is an actual ortholattice, not an assumed expression-order instance.
Correspondence with a particular comparison algorithm is a separate obligation.
-/

namespace Lisa.ExpressionOrder

open Expr

/-- Generate inequalities from lattice rules and Lisa's expression equations. -/
inductive Derives : Expr → Expr → Prop
  | refl (p) : Derives p p
  | trans {p q r} : Derives p q → Derives q r → Derives p r
  | bot (p) : Derives bot p
  | top (p) : Derives p top
  | meetLeft (p q) : Derives (and p q) p
  | meetRight (p q) : Derives (and p q) q
  | meet {p q r} : Derives p q → Derives p r → Derives p (and q r)
  | joinLeft (p q) : Derives p (or p q)
  | joinRight (p q) : Derives q (or p q)
  | join {p q r} : Derives p r → Derives q r → Derives (or p q) r
  | neg {p q} : Derives p q → Derives (neg q) (neg p)
  | doubleNeg (p) : Derives (neg (neg p)) p
  | doubleNegRev (p) : Derives p (neg (neg p))
  | excludedMiddle (p) : Derives top (or p (neg p))
  | imp (p q) : Derives (imp p q) (or (neg p) q)
  | impRev (p q) : Derives (or (neg p) q) (imp p q)
  | iff (p q) : Derives (iff p q) (and (imp p q) (imp q p))
  | iffRev (p q) : Derives (and (imp p q) (imp q p)) (iff p q)
  | alphaBetaEta {p q} : AlphaBetaEta p q → Derives p q
  | app {f g a b} : Derives f g → Derives g f → Derives a b → Derives b a →
      Derives (.app f a) (.app g b)
  | lam (x : SVar) {p q} : Derives p q → Derives q p →
      Derives (.lam x p) (.lam x q)
  | eqSymm (s t) : isTerm s → isTerm t → Derives (eq s t) (eq t s)
  | eqRefl (s) : isTerm s → Derives top (eq s s)
  | forallMono (x : SVar) {p q} : x.sort = ind → isFormula p → isFormula q →
      Derives p q → Derives (forall_ x p) (forall_ x q)
  | forallTop (x : SVar) : x.sort = ind → Derives top (forall_ x top)
  | forallBot (x : SVar) : x.sort = ind → Derives (forall_ x bot) bot
  | exists (x : SVar) (p) : x.sort = ind → isFormula p →
      Derives (exists_ x p) (neg (forall_ x (neg p)))
  | existsRev (x : SVar) (p) : x.sort = ind → isFormula p →
      Derives (neg (forall_ x (neg p))) (exists_ x p)

abbrev leq : ExprRel := Derives

namespace Derives

theorem meet_mono {p p' q q'} (hp : Derives p p') (hq : Derives q q') :
    Derives (and p q) (and p' q') :=
  .meet (.trans (.meetLeft _ _) hp) (.trans (.meetRight _ _) hq)

theorem join_mono {p p' q q'} (hp : Derives p p') (hq : Derives q q') :
    Derives (or p q) (or p' q') :=
  .join (.trans hp (.joinLeft _ _)) (.trans hq (.joinRight _ _))

end Derives

/-- Identify expressions only when both generated inequalities hold. -/
def equivalence : Setoid Expr where
  r := isSame leq
  iseqv := ⟨fun p => ⟨.refl p, .refl p⟩,
    fun h => ⟨h.2, h.1⟩,
    fun h₁ h₂ => ⟨.trans h₁.1 h₂.1, .trans h₂.2 h₁.2⟩⟩

abbrev Carrier := Quotient equivalence

def value (p : Expr) : Carrier := Quotient.mk equivalence p

@[simp] theorem value_eq {p q : Expr} : value p = value q ↔ isSame leq p q :=
  Quotient.eq

private def liftBinary (op : Expr → Expr → Expr)
    (h : ∀ {p p' q q'}, isSame leq p p' → isSame leq q q' →
      isSame leq (op p q) (op p' q')) : Carrier → Carrier → Carrier :=
  Quotient.lift₂ (fun p q => value (op p q))
    (fun _ _ _ _ hp hq => Quotient.sound (h hp hq))

private def meet : Carrier → Carrier → Carrier := liftBinary and
  (fun hp hq => ⟨Derives.meet_mono hp.1 hq.1, Derives.meet_mono hp.2 hq.2⟩)

private def join : Carrier → Carrier → Carrier := liftBinary or
  (fun hp hq => ⟨Derives.join_mono hp.1 hq.1, Derives.join_mono hp.2 hq.2⟩)

private def complement : Carrier → Carrier :=
  Quotient.lift (fun p => value (neg p))
    (fun _ _ h => Quotient.sound ⟨.neg h.2, .neg h.1⟩)

instance : LE Carrier := ⟨Quotient.lift₂ Derives (by
  intro p q p' q' hp hq
  apply propext
  exact ⟨fun h => .trans hp.2 (.trans h hq.1),
    fun h => .trans hp.1 (.trans h hq.2)⟩)⟩

@[simp] theorem value_le (p q : Expr) : value p ≤ value q ↔ Derives p q := Iff.rfl

instance : PartialOrder Carrier where
  le_refl a := Quotient.inductionOn a Derives.refl
  le_trans a b c := Quotient.inductionOn₃ a b c (fun _ _ _ => Derives.trans)
  le_antisymm a b := Quotient.inductionOn₂ a b (fun _ _ h₁ h₂ =>
    Quotient.sound ⟨h₁, h₂⟩)

instance : Lattice Carrier where
  sup := join
  inf := meet
  le_sup_left a b := Quotient.inductionOn₂ a b Derives.joinLeft
  le_sup_right a b := Quotient.inductionOn₂ a b Derives.joinRight
  sup_le a b c := Quotient.inductionOn₃ a b c (fun _ _ _ => Derives.join)
  inf_le_left a b := Quotient.inductionOn₂ a b Derives.meetLeft
  inf_le_right a b := Quotient.inductionOn₂ a b Derives.meetRight
  le_inf a b c := Quotient.inductionOn₃ a b c (fun _ _ _ => Derives.meet)

instance : BoundedOrder Carrier where
  top := value top
  bot := value bot
  le_top a := Quotient.inductionOn a Derives.top
  bot_le a := Quotient.inductionOn a Derives.bot

instance : Compl Carrier := ⟨complement⟩

/-- Realize the generated order on equivalence classes as an ortholattice. -/
instance : Ortholattice Carrier where
  compl_antitone := by
    intro a b
    exact Quotient.inductionOn₂ a b (fun _ _ h => Derives.neg h)
  compl_involutive a := Quotient.inductionOn a (fun p =>
    Quotient.sound ⟨Derives.doubleNeg p, Derives.doubleNegRev p⟩)
  sup_compl a := Quotient.inductionOn a (fun p => Quotient.sound
    ⟨Derives.top _, Derives.excludedMiddle p⟩)

/-- Interpret raw syntax in the generated ortholattice without assuming its laws. -/
def interpretation : Lisa.Orthologic.Interpretation leq where
  Carrier := Carrier
  algebra := inferInstance
  eval := value
  compare := fun _ _ => Iff.rfl
  top_eq := rfl
  bot_eq := rfl
  and_eq := fun _ _ => rfl
  or_eq := fun _ _ => rfl
  neg_eq := fun _ => rfl
  imp_eq := fun p q => Quotient.sound ⟨.imp p q, .impRev p q⟩
  iff_eq := fun p q => Quotient.sound
    ⟨.trans (.iff p q) (Derives.meet_mono (.imp p q) (.imp q p)),
      .trans (Derives.meet_mono (.impRev p q) (.impRev q p)) (.iffRev p q)⟩

instance : IsPreorder Expr leq := interpretation.preorder
instance : SequentEncoding leq := interpretation.sequentEncoding

/-- Embed alpha, beta, and eta conversion, including conversion inside contexts. -/
theorem same_of_alphaBetaEta {p q : Expr} (h : AlphaBetaEta p q) : isSame leq p q :=
  ⟨.alphaBetaEta h, .alphaBetaEta h.symm⟩

/-- Factor the lattice interpretation through the alpha-beta-eta quotient first. -/
def ofTerm : AlphaBetaEta.Term → Carrier :=
  Quotient.lift value (fun _ _ h => Quotient.sound (same_of_alphaBetaEta h))

@[simp] theorem ofTerm_term (p : Expr) : ofTerm (AlphaBetaEta.term p) = value p := rfl

theorem same_app {f g a b : Expr} (hf : isSame leq f g) (ha : isSame leq a b) :
    isSame leq (.app f a) (.app g b) :=
  ⟨.app hf.1 hf.2 ha.1 ha.2, .app hf.2 hf.1 ha.2 ha.1⟩

theorem same_lam (x : SVar) {p q : Expr} (h : isSame leq p q) :
    isSame leq (.lam x p) (.lam x q) := ⟨.lam x h.1 h.2, .lam x h.2 h.1⟩

instance : RelationCongruence leq where
  imp_congr := interpretation.imp_congr
  eq_congr := by
    intro s s' t t' _ _ _ _ hs ht
    exact same_app (same_app ⟨.refl _, .refl _⟩ hs) ht

namespace Derives

/-- Eliminate a proposition together with the negation of an upper bound. -/
theorem meet_neg_le_bot {p q : Expr} (h : Derives p q) :
    Derives (Expr.and p (Expr.neg q)) Expr.bot := by
  exact interpretation.transitive (interpretation.and_mono h (interpretation.self_le _))
    (interpretation.and_compl q).1

/-- Propagate a false body through universal quantification. -/
theorem forall_le_bot {x : SVar} {p : Expr} (hx : x.sort = ind) (hp : isFormula p)
    (h : Derives p Expr.bot) : Derives (forall_ x p) Expr.bot :=
  .trans (.forallMono (q := Expr.bot) x hx hp rfl h) (.forallBot x hx)

end Derives

end Lisa.ExpressionOrder
