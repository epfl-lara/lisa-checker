import Completeness.FoundationSyntax
import Foundation.FirstOrder.Basic.Eq
import Foundation.FirstOrder.Completeness.Completeness

/-! Apply the independent Foundation completeness theorem to Mathlib sentences.

The result here is a Foundation derivation from its equality axioms. Transporting
that derivation into `Pure.ProofTree`, and discharging those equality axioms by
Pure's equality rules, is a further syntactic obligation. Keeping this result
separate prevents a semantic validity claim from being mistaken for a Pure proof.
-/

namespace Lisa.SCLambdaToPure.FoundationBridge

variable {L : FirstOrder.Language.{0, 0}}

instance : (language L).Eq where eq := .equality

universe u
variable {M : Type u} [s : LO.FirstOrder.Structure (language L) M]

/-- Forget the distinguished equality relation when recovering a Mathlib structure. -/
@[reducible] def toStructure : L.Structure M where
  funMap := fun f v => s.func f v
  RelMap := fun r v => s.rel (.symbol r) v

theorem of_toStructure [LO.FirstOrder.Structure.Eq (language L) M] :
    @ofStructure L M toStructure = s := by
  apply LO.FirstOrder.Structure.ext
  · funext n f v
    rfl
  · funext n r v
    cases r with
    | symbol r => rfl
    | equality =>
        have h := LO.FirstOrder.Structure.Eq.eq (L := language L) (v 0) (v 1)
        change s.rel Relation.equality ![v 0, v 1] ↔ v 0 = v 1 at h
        have hv : ![v 0, v 1] = v := by
          funext i
          exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
        rw [hv] at h
        exact propext h.symm

/-- A valid Mathlib sentence has an independently checked first-order derivation
in Foundation. This theorem uses its proved completeness, not a new axiom. -/
theorem complete_sentence (φ : L.Sentence)
    (h : ∀ (M : Type) [Nonempty M] [L.Structure M], φ.Realize (M := M)) :
    LO.Entailment.Provable (LO.FirstOrder.Theory.eqAxiom (L := language L)) (encode φ) := by
  apply LO.FirstOrder.complete
  apply LO.FirstOrder.consequence_iff_eq.mpr
  intro M hM s hs _
  letI : L.Structure M := toStructure
  have he : (default : Empty → M) = Empty.elim := Subsingleton.elim _ _
  have hv := (eval_encode φ (Empty.elim : Empty → M) (default : Fin 0 → M)).mpr
    (by simpa only [FirstOrder.Language.Sentence.Realize,
      FirstOrder.Language.Formula.Realize, he] using h M)
  rw [of_toStructure] at hv
  exact hv

end Lisa.SCLambdaToPure.FoundationBridge
