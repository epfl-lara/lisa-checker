import Lisa.Orthologic.Formula
import Mathlib.Data.Set.Lattice

/-!
Present Guilloud's two-position orthologic calculus on negation normal forms.
An absent position denotes top in the orthogonality interpretation.
Keep cut explicit so semantic completeness and cut elimination are distinct.
-/

namespace Lisa.Orthologic.Calculus

open Nnf

abbrev Position (α : Type) := Option (Nnf α)

/-- Permit cut only in the unfocused source calculus. -/
inductive Proof {α : Type} (cuts : Bool) : Position α → Position α → Type
  | ax (p) : Proof cuts (some p) (some p.compl)
  | bot (d) : Proof cuts (some .bot) d
  | weaken {g d} : Proof cuts g none → Proof cuts g d
  | contract {g} : Proof cuts g g → Proof cuts g none
  | meetLeft {p q d} : Proof cuts (some p) d → Proof cuts (some (.meet p q)) d
  | meetRight {p q d} : Proof cuts (some q) d → Proof cuts (some (.meet p q)) d
  | join {p q d} : Proof cuts (some p) d → Proof cuts (some q) d →
      Proof cuts (some (.join p q)) d
  | swap {g d} : Proof cuts g d → Proof cuts d g
  | cut {g d p} : cuts = true → Proof cuts g (some p) →
      Proof cuts (some p.compl) d → Proof cuts g d

namespace Proof

/-- Count nodes to measure commutations past the last inference. -/
def size {α : Type} {c g d} : @Proof α c g d → Nat
  | .ax _ | .bot _ => 1
  | .weaken h | .contract h | .meetLeft h | .meetRight h | .swap h => h.size + 1
  | .join h k | .cut _ h k => h.size + k.size + 1

/-- Interpret an absent position as top. -/
def evalPosition {α L : Type} [Ortholattice L] (v : α → L) : Position α → L
  | none => ⊤
  | some p => p.eval v

/-- Interpret a sequent as orthogonality, including the cut rule. -/
theorem sound {α L : Type} [Ortholattice L] {c g d}
    (h : @Proof α c g d) (v : α → L) :
    evalPosition v g ≤ (evalPosition v d)ᶜ := by
  induction h with
  | ax p => simp [evalPosition]
  | bot d => exact bot_le
  | weaken h ih =>
      simp only [evalPosition, Ortholattice.compl_top] at ih
      exact le_trans ih bot_le
  | contract h ih =>
      have he := (Ortholattice.self_orth_iff _).mp ih
      simpa only [evalPosition, Ortholattice.compl_top] using le_of_eq he
  | meetLeft h ih => exact le_trans inf_le_left ih
  | meetRight h ih => exact le_trans inf_le_right ih
  | join h k ih ik => exact sup_le ih ik
  | swap h ih => exact (Ortholattice.orth_comm _ _).mp ih
  | cut _ h k ih ik =>
      simp only [evalPosition, Nnf.eval_compl] at ih ik
      exact le_trans ih ik

/-- Embed a cut-free derivation without changing its conclusion. -/
def withCuts {α : Type} {g d} : @Proof α false g d → Proof true g d
  | .ax p => .ax p
  | .bot d => .bot d
  | .weaken h => .weaken h.withCuts
  | .contract h => .contract h.withCuts
  | .meetLeft h => .meetLeft h.withCuts
  | .meetRight h => .meetRight h.withCuts
  | .join h k => .join h.withCuts k.withCuts
  | .swap h => .swap h.withCuts
  | .cut h _ _ => Bool.noConfusion h

end Proof

/-- Derive inequalities in the calculus with cut. -/
def Derives {α : Type} (p q : Nnf α) : Prop :=
  Nonempty (Proof true (some p) (some q.compl))

namespace Derives

variable {α : Type} {p q r : Nnf α}

theorem refl (p : Nnf α) : Derives p p := ⟨.ax p⟩

theorem trans (h : Derives p q) (k : Derives q r) : Derives p r := by
  obtain ⟨h⟩ := h
  obtain ⟨k⟩ := k
  exact ⟨.cut rfl h (by simpa using k)⟩

theorem bot (p : Nnf α) : Derives .bot p := ⟨.bot _⟩

theorem top (p : Nnf α) : Derives p .top := ⟨.swap (.bot _)⟩

theorem meetLeft (p q : Nnf α) : Derives (.meet p q) p := ⟨.meetLeft (.ax p)⟩

theorem meetRight (p q : Nnf α) : Derives (.meet p q) q := ⟨.meetRight (.ax q)⟩

theorem meet (h : Derives p q) (k : Derives p r) : Derives p (.meet q r) := by
  obtain ⟨h⟩ := h
  obtain ⟨k⟩ := k
  exact ⟨.swap (.join (.swap h) (.swap k))⟩

theorem joinLeft (p q : Nnf α) : Derives p (.join p q) :=
  ⟨.swap (.meetLeft (.swap (.ax p)))⟩

theorem joinRight (p q : Nnf α) : Derives q (.join p q) :=
  ⟨.swap (.meetRight (.swap (.ax q)))⟩

theorem join (h : Derives p r) (k : Derives q r) : Derives (.join p q) r := by
  obtain ⟨h⟩ := h
  obtain ⟨k⟩ := k
  exact ⟨.join h k⟩

theorem compl (h : Derives p q) : Derives q.compl p.compl := by
  obtain ⟨h⟩ := h
  exact ⟨by simpa using Proof.swap h⟩

theorem excludedMiddle (p : Nnf α) : Derives .top (.join p p.compl) := by
  refine ⟨.swap (.weaken (.contract ?_))⟩
  exact .meetLeft (.swap (.meetRight (.swap (.ax p.compl))))

theorem sound {L : Type} [Ortholattice L] (h : Derives p q) (v : α → L) :
    p.eval v ≤ q.eval v := by
  obtain ⟨h⟩ := h
  simpa [Proof.evalPosition] using h.sound v

end Derives

/-- Identify syntax by mutual derivability, not by equality of its constructors. -/
def equivalence (α : Type) : Setoid (Nnf α) where
  r p q := Derives p q ∧ Derives q p
  iseqv := ⟨fun p => ⟨.refl p, .refl p⟩, fun h => ⟨h.2, h.1⟩,
    fun h k => ⟨.trans h.1 k.1, .trans k.2 h.2⟩⟩

abbrev Free (α : Type) := Quotient (equivalence α)

def value {α : Type} (p : Nnf α) : Free α := Quotient.mk (equivalence α) p

private def liftBinary {α : Type} (op : Nnf α → Nnf α → Nnf α)
    (h : ∀ {p p' q q'}, Derives p p' → Derives q q' →
      Derives (op p q) (op p' q')) : Free α → Free α → Free α :=
  Quotient.lift₂ (fun p q => value (op p q))
    (fun _ _ _ _ hp hq => Quotient.sound ⟨h hp.1 hq.1, h hp.2 hq.2⟩)

instance {α : Type} : LE (Free α) := ⟨Quotient.lift₂ Derives (by
  intro p q p' q' hp hq
  exact propext ⟨fun h => .trans hp.2 (.trans h hq.1),
    fun h => .trans hp.1 (.trans h hq.2)⟩)⟩

instance {α : Type} : PartialOrder (Free α) where
  le_refl a := Quotient.inductionOn a Derives.refl
  le_trans a b c := Quotient.inductionOn₃ a b c (fun _ _ _ => Derives.trans)
  le_antisymm a b := Quotient.inductionOn₂ a b (fun _ _ h k => Quotient.sound ⟨h, k⟩)

instance {α : Type} : Lattice (Free α) where
  inf := liftBinary .meet (fun h k => .meet
    (.trans (.meetLeft _ _) h) (.trans (.meetRight _ _) k))
  sup := liftBinary .join (fun h k => .join
    (.trans h (.joinLeft _ _)) (.trans k (.joinRight _ _)))
  inf_le_left a b := Quotient.inductionOn₂ a b Derives.meetLeft
  inf_le_right a b := Quotient.inductionOn₂ a b Derives.meetRight
  le_inf a b c := Quotient.inductionOn₃ a b c (fun _ _ _ => Derives.meet)
  le_sup_left a b := Quotient.inductionOn₂ a b Derives.joinLeft
  le_sup_right a b := Quotient.inductionOn₂ a b Derives.joinRight
  sup_le a b c := Quotient.inductionOn₃ a b c (fun _ _ _ => Derives.join)

instance {α : Type} : BoundedOrder (Free α) where
  top := value .top
  bot := value .bot
  le_top a := Quotient.inductionOn a Derives.top
  bot_le a := Quotient.inductionOn a Derives.bot

instance {α : Type} : Compl (Free α) := ⟨Quotient.lift (fun p => value p.compl)
  (fun _ _ h => Quotient.sound ⟨Derives.compl h.2, Derives.compl h.1⟩)⟩

instance {α : Type} : Ortholattice (Free α) where
  compl_antitone := fun a b => Quotient.inductionOn₂ a b (fun _ _ => Derives.compl)
  compl_involutive a := Quotient.inductionOn a (fun p => by
    change value p.compl.compl = value p
    rw [Nnf.compl_compl])
  sup_compl a := Quotient.inductionOn a (fun p =>
    Quotient.sound ⟨Derives.top _, Derives.excludedMiddle p⟩)

@[simp] theorem eval_free {α : Type} (p : Nnf α) :
    p.eval (fun a => value (.lit a false)) = value p := by
  induction p with
  | lit a s => cases s <;> rfl
  | bot | top => rfl
  | meet p q ih ik => change _ ⊓ _ = _; rw [ih, ik]; rfl
  | join p q ih ik => change _ ⊔ _ = _; rw [ih, ik]; rfl

/-- Complete the calculus with cut by interpreting formulas in its own term model. -/
theorem complete {α : Type} (p q : Nnf α)
    (h : ∀ (L : Type) [Ortholattice L] (v : α → L), p.eval v ≤ q.eval v) :
    Derives p q := by
  have hfree := h (Free α) (fun a => value (.lit a false))
  simpa only [eval_free] using hfree

private instance : Ortholattice (Set Unit) where
  compl_antitone := fun _ _ h => compl_le_compl h
  compl_involutive := compl_compl
  sup_compl := fun _ => sup_compl_eq_top

/-- Rule out the empty sequent by a nontrivial Boolean interpretation. -/
theorem no_empty {α : Type} {c} (h : @Proof α c none none) : False := by
  have hf := h.sound (fun _ => (∅ : Set Unit))
  simp [Proof.evalPosition] at hf

end Lisa.Orthologic.Calculus
