import Lisa.SCLambdaToPure.Reference.PureSemantics
import Foundation.FirstOrder.Basic.Semantics.Semantics

/-! The syntax and semantics adapter for Foundation's first-order calculus.

Foundation uses negation-normal formulas and innermost-first bound indices;
Mathlib uses implication/falsity and outermost-first levels. Equality is a
distinguished relation in the former and a constructor in the latter.
This file proves preservation of meaning, not transport of derivations.
-/

namespace Lisa.SCLambdaToPure.FoundationBridge

open FirstOrder

variable (L : Language.{0, 0})

inductive Relation : Nat → Type where
  | symbol {n} : L.Relations n → Relation n
  | equality : Relation 2

def language : LO.FirstOrder.Language where
  Func := L.Functions
  Rel := Relation L

variable {L}

def encodeTerm : L.Term (α ⊕ Fin n) → LO.FirstOrder.Semiterm (language L) α n
  | .var (.inl x) => .fvar x
  | .var (.inr i) => .bvar i.rev
  | .func f ts => .func f (fun i => encodeTerm (ts i))

def decodeTerm : LO.FirstOrder.Semiterm (language L) α n → L.Term (α ⊕ Fin n)
  | .fvar x => .var (.inl x)
  | .bvar i => .var (.inr i.rev)
  | .func f ts => .func f (fun i => decodeTerm (ts i))

@[simp] theorem decode_encode_term (t : L.Term (α ⊕ Fin n)) :
    decodeTerm (encodeTerm t) = t := by
  induction t with
  | var x => cases x <;> simp [encodeTerm, decodeTerm]
  | func f ts ih => simp [encodeTerm, decodeTerm, ih]

@[simp] theorem encode_decode_term (t : LO.FirstOrder.Semiterm (language L) α n) :
    encodeTerm (decodeTerm t) = t := by
  induction t with
  | bvar | fvar => simp [encodeTerm, decodeTerm]
  | func f ts ih => simp [encodeTerm, decodeTerm, ih]

def encode : L.BoundedFormula α n → LO.FirstOrder.Semiformula (language L) α n
  | .falsum => .falsum
  | .equal t s => .rel .equality ![encodeTerm t, encodeTerm s]
  | .rel r ts => .rel (.symbol r) (fun i => encodeTerm (ts i))
  | .imp p q => .or (encode p).neg (encode q)
  | .all p => .all (encode p)

def decodeAtom (r : Relation L k) (ts : Fin k → LO.FirstOrder.Semiterm (language L) α n) :
    L.BoundedFormula α n :=
  match r with
  | .symbol r => .rel r (fun i => decodeTerm (ts i))
  | .equality => .equal (decodeTerm (ts 0)) (decodeTerm (ts 1))

def decode : LO.FirstOrder.Semiformula (language L) α n → L.BoundedFormula α n
  | .verum => ⊤
  | .falsum => ⊥
  | .rel r ts => decodeAtom r ts
  | .nrel r ts => (decodeAtom r ts).not
  | .and p q => decode p ⊓ decode q
  | .or p q => decode p ⊔ decode q
  | .all p => (decode p).all
  | .exs p => (decode p).ex

universe u
variable {M : Type u} [L.Structure M]

/-- The equality relation denotes actual equality, without any new model assumption. -/
@[reducible] def ofStructure : LO.FirstOrder.Structure (language L) M where
  func := fun _ f v => Language.Structure.funMap f v
  rel := fun _ r v => match r with
    | .symbol r => Language.Structure.RelMap r v
    | .equality => v 0 = v 1

theorem realize_decodeTerm (t : LO.FirstOrder.Semiterm (language L) α n)
    (v : α → M) (b : Fin n → M) :
    (decodeTerm t).realize (Sum.elim v b) =
      t.val (ofStructure (L := L) (M := M)) (b ∘ Fin.rev) v := by
  induction t with
  | bvar | fvar => rfl
  | func f ts ih =>
      simp only [decodeTerm, Language.Term.realize, LO.FirstOrder.Semiterm.val, ofStructure]
      congr 1
      funext i
      exact ih i

theorem eval_encodeTerm (t : L.Term (α ⊕ Fin n)) (v : α → M) (b : Fin n → M) :
    (encodeTerm t).val (ofStructure (L := L) (M := M)) (b ∘ Fin.rev) v =
      t.realize (Sum.elim v b) := by
  rw [← realize_decodeTerm, decode_encode_term]

private theorem reverse_snoc (b : Fin n → M) (a : M) :
    Fin.snoc b a ∘ Fin.rev = Matrix.vecCons a (b ∘ Fin.rev) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp [Fin.rev_succ]

theorem realize_decode (p : LO.FirstOrder.Semiformula (language L) α n)
    (v : α → M) (b : Fin n → M) :
    (decode p).Realize v b ↔
      p.EvalAux (ofStructure (L := L) (M := M)) v (b ∘ Fin.rev) := by
  induction p with
  | verum | falsum => simp [decode, LO.FirstOrder.Semiformula.EvalAux]
  | rel r ts | nrel r ts =>
      cases r <;>
        simp [decode, decodeAtom, LO.FirstOrder.Semiformula.EvalAux, ofStructure,
          Language.BoundedFormula.Realize, realize_decodeTerm] <;> rfl
  | and p q ihp ihq =>
      simpa [decode, LO.FirstOrder.Semiformula.EvalAux] using and_congr (ihp b) (ihq b)
  | or p q ihp ihq =>
      simpa [decode, LO.FirstOrder.Semiformula.EvalAux] using or_congr (ihp b) (ihq b)
  | all p ih =>
      simpa [decode, LO.FirstOrder.Semiformula.EvalAux, reverse_snoc] using
        forall_congr' (fun a => ih (Fin.snoc b a))
  | exs p ih =>
      simpa [decode, LO.FirstOrder.Semiformula.EvalAux, reverse_snoc] using
        exists_congr (fun a => ih (Fin.snoc b a))

theorem eval_encode (p : L.BoundedFormula α n) (v : α → M) (b : Fin n → M) :
    (encode p).EvalAux (ofStructure (L := L) (M := M)) v (b ∘ Fin.rev) ↔ p.Realize v b := by
  induction p with
  | falsum => rfl
  | equal t s =>
      simp [encode, LO.FirstOrder.Semiformula.EvalAux, ofStructure, eval_encodeTerm,
        Language.BoundedFormula.Realize]
  | rel r ts =>
      simp [encode, LO.FirstOrder.Semiformula.EvalAux, ofStructure, eval_encodeTerm,
        Language.BoundedFormula.Realize]
  | imp p q ihp ihq =>
      simp only [encode, LO.FirstOrder.Semiformula.EvalAux,
        ← LO.FirstOrder.Semiformula.neg_eq, LO.FirstOrder.Semiformula.EvalAux_neg]
      simpa [imp_iff_not_or] using
        or_congr (not_congr (ihp b)) (ihq b)
  | all p ih =>
      simpa [encode, LO.FirstOrder.Semiformula.EvalAux, reverse_snoc] using
        forall_congr' (fun a => ih (Fin.snoc b a))

end Lisa.SCLambdaToPure.FoundationBridge
