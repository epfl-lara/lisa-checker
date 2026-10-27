import Lisa.Orthologic.Contextual

namespace Lisa.Orthologic.Contextual

/-- Generate OL inequalities and congruence, without assuming constructor monotonicity. -/
inductive Derives : Term α κ → Term α κ → Prop
  | refl (p) : Derives p p
  | trans {p q r} : Derives p q → Derives q r → Derives p r
  | bot (p) : Derives .bot p
  | top (p) : Derives p .top
  | meetLeft (p q) : Derives (.meet p q) p
  | meetRight (p q) : Derives (.meet p q) q
  | meet {p q r} : Derives p q → Derives p r → Derives p (.meet q r)
  | joinLeft (p q) : Derives p (.join p q)
  | joinRight (p q) : Derives q (.join p q)
  | join {p q r} : Derives p r → Derives q r → Derives (.join p q) r
  | neg {p q} : Derives p q → Derives (.neg q) (.neg p)
  | doubleNeg (p) : Derives (.neg (.neg p)) p
  | doubleNegRev (p) : Derives p (.neg (.neg p))
  | excludedMiddle (p) : Derives .top (.join p (.neg p))
  | unary (k) {p q} : Derives p q → Derives q p → Derives (.unary k p) (.unary k q)
  | binary (k) {p p' q q'} : Derives p p' → Derives p' p → Derives q q' → Derives q' q →
      Derives (.binary k p q) (.binary k p' q')

theorem Derives.sound {p q : Term α κ} (h : Derives p q)
    {L : Type} [Ortholattice L] (v : α → L) (u : κ → L → L)
    (b : κ → L → L → L) : p.eval v u b ≤ q.eval v u b := by
  induction h with
  | refl => exact le_rfl
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | bot => exact bot_le
  | top => exact le_top
  | meetLeft => exact inf_le_left
  | meetRight => exact inf_le_right
  | meet _ _ ih₁ ih₂ => exact le_inf ih₁ ih₂
  | joinLeft => exact le_sup_left
  | joinRight => exact le_sup_right
  | join _ _ ih₁ ih₂ => exact sup_le ih₁ ih₂
  | neg _ ih => exact Ortholattice.compl_antitone ih
  | doubleNeg => exact le_of_eq (Ortholattice.compl_compl _)
  | doubleNegRev => exact le_of_eq (Ortholattice.compl_compl _).symm
  | excludedMiddle => exact le_of_eq (Ortholattice.sup_compl _).symm
  | unary k _ _ ih₁ ih₂ => exact le_of_eq (congrArg (u k) (le_antisymm ih₁ ih₂))
  | binary k _ _ _ _ ih₁ ih₂ ih₃ ih₄ =>
      exact le_of_eq (congrArg₂ (b k) (le_antisymm ih₁ ih₂) (le_antisymm ih₃ ih₄))

namespace Derives

theorem meet_mono {p p' q q' : Term α κ} (hp : Derives p p') (hq : Derives q q') :
    Derives (.meet p q) (.meet p' q') :=
  .meet (.trans (.meetLeft _ _) hp) (.trans (.meetRight _ _) hq)

theorem join_mono {p p' q q' : Term α κ} (hp : Derives p p') (hq : Derives q q') :
    Derives (.join p q) (.join p' q') :=
  .join (.trans hp (.joinLeft _ _)) (.trans hq (.joinRight _ _))

end Derives

def equivalence (α κ : Type) : Setoid (Term α κ) where
  r p q := Derives p q ∧ Derives q p
  iseqv := ⟨fun p => ⟨.refl p, .refl p⟩, fun h => ⟨h.2, h.1⟩,
    fun h₁ h₂ => ⟨.trans h₁.1 h₂.1, .trans h₂.2 h₁.2⟩⟩

abbrev TheoryModel (α κ : Type) := Quotient (equivalence α κ)

def value (p : Term α κ) : TheoryModel α κ := Quotient.mk (equivalence α κ) p

@[simp] theorem value_eq (p q : Term α κ) :
    value p = value q ↔ Derives p q ∧ Derives q p := Quotient.eq

instance : LE (TheoryModel α κ) := ⟨Quotient.lift₂ Derives (by
  intro p q p' q' hp hq
  apply propext
  exact ⟨fun h => .trans hp.2 (.trans h hq.1),
    fun h => .trans hp.1 (.trans h hq.2)⟩)⟩

@[simp] theorem value_le (p q : Term α κ) : value p ≤ value q ↔ Derives p q := Iff.rfl

private def liftBinary (op : Term α κ → Term α κ → Term α κ)
    (h : ∀ {p p' q q'}, (Derives p p' ∧ Derives p' p) →
      (Derives q q' ∧ Derives q' q) →
      (Derives (op p q) (op p' q') ∧ Derives (op p' q') (op p q))) :
    TheoryModel α κ → TheoryModel α κ → TheoryModel α κ :=
  Quotient.lift₂ (fun p q => value (op p q))
    (fun _ _ _ _ hp hq => Quotient.sound (h hp hq))

instance : PartialOrder (TheoryModel α κ) where
  le_refl a := Quotient.inductionOn a Derives.refl
  le_trans a b c := Quotient.inductionOn₃ a b c (fun _ _ _ => Derives.trans)
  le_antisymm a b := Quotient.inductionOn₂ a b (fun _ _ h₁ h₂ =>
    Quotient.sound ⟨h₁, h₂⟩)

instance : Lattice (TheoryModel α κ) where
  inf := liftBinary Term.meet (fun hp hq =>
    ⟨Derives.meet_mono hp.1 hq.1, Derives.meet_mono hp.2 hq.2⟩)
  sup := liftBinary Term.join (fun hp hq =>
    ⟨Derives.join_mono hp.1 hq.1, Derives.join_mono hp.2 hq.2⟩)
  le_sup_left a b := Quotient.inductionOn₂ a b Derives.joinLeft
  le_sup_right a b := Quotient.inductionOn₂ a b Derives.joinRight
  sup_le a b c := Quotient.inductionOn₃ a b c (fun _ _ _ => Derives.join)
  inf_le_left a b := Quotient.inductionOn₂ a b Derives.meetLeft
  inf_le_right a b := Quotient.inductionOn₂ a b Derives.meetRight
  le_inf a b c := Quotient.inductionOn₃ a b c (fun _ _ _ => Derives.meet)

instance : BoundedOrder (TheoryModel α κ) where
  bot := value .bot
  top := value .top
  bot_le a := Quotient.inductionOn a Derives.bot
  le_top a := Quotient.inductionOn a Derives.top

instance : Compl (TheoryModel α κ) := ⟨Quotient.lift (fun p => value (.neg p))
  (fun _ _ h => Quotient.sound ⟨.neg h.2, .neg h.1⟩)⟩

instance : Ortholattice (TheoryModel α κ) where
  compl_antitone := by
    intro a b
    exact Quotient.inductionOn₂ a b (fun _ _ h => Derives.neg h)
  compl_involutive a := Quotient.inductionOn a (fun p =>
    Quotient.sound ⟨Derives.doubleNeg p, Derives.doubleNegRev p⟩)
  sup_compl a := Quotient.inductionOn a (fun p =>
    Quotient.sound ⟨Derives.top _, Derives.excludedMiddle p⟩)

private def unaryValue (k : κ) : TheoryModel α κ → TheoryModel α κ :=
  Quotient.lift (fun p => value (.unary k p)) (fun _ _ h =>
    Quotient.sound ⟨.unary k h.1 h.2, .unary k h.2 h.1⟩)

private def binaryValue (k : κ) : TheoryModel α κ → TheoryModel α κ → TheoryModel α κ :=
  liftBinary (.binary k) (fun hp hq =>
    ⟨.binary k hp.1 hp.2 hq.1 hq.2, .binary k hp.2 hp.1 hq.2 hq.1⟩)

private theorem eval_value (p : Term α κ) :
    p.eval (fun a => value (.atom a)) unaryValue binaryValue = value p := by
  induction p <;> simp_all [Term.eval, unaryValue, binaryValue, liftBinary] <;> rfl

/-- Obtain completeness from the generated term model, not an assumed order instance. -/
theorem Derives.complete (p q : Term α κ)
    (h : ∀ (L : Type) [Ortholattice L] (v : α → L)
      (u : κ → L → L) (b : κ → L → L → L), p.eval v u b ≤ q.eval v u b) :
    Derives p q := by
  have hs := h (TheoryModel α κ) (fun a => value (.atom a)) unaryValue binaryValue
  simpa only [eval_value, value_le] using hs

/-- Decide exactly the generated calculus, including equations inside constructors. -/
theorem check_iff [DecidableEq α] [DecidableEq κ] (p q : Term α κ) :
    check p q = true ↔ Derives p q := by
  rw [check_valid]
  exact ⟨Derives.complete p q, fun h _ _ v u b => h.sound v u b⟩

instance [DecidableEq α] [DecidableEq κ] : DecidableRel (@Derives α κ) := fun p q =>
  decidable_of_iff (check p q = true) (check_iff p q)

end Lisa.Orthologic.Contextual
