import Lisa.Orthologic.Syntax

/-! Translate typed lambda terms into the OL representation. Logical symbols are
recognized by their complete identifier and sort. Other constants, applications
and binders remain available to recursive normalization. -/

namespace Lisa.Orthologic
namespace SimpleExpr

def lowerConst : (s : LSort) → Identifier → SimpleExpr s
  | .prop, ⟨"top", 0⟩ => .top
  | .prop, ⟨"bot", 0⟩ => .neg .top
  | _, c => .const c

/-- Recognize saturated logical applications after translating their children.
Quantifier arguments are lambdas after the entry point's eta-long normalization.
The fallback also makes this function total on arbitrary typed input. -/
def lowerApp : {s t : LSort} → SimpleExpr (s >> t) → SimpleExpr s → SimpleExpr t
  | .prop, .prop, .const ⟨"not", 0⟩, p => .neg p
  | .prop, .prop, .app (s := .prop) (.const ⟨"and", 0⟩) p, q => .conj [p, q]
  | .prop, .prop, .app (s := .prop) (.const ⟨"or", 0⟩) p, q => .neg (.conj [.neg p, .neg q])
  | .prop, .prop, .app (s := .prop) (.const ⟨"imp", 0⟩) p, q => .neg (.conj [p, .neg q])
  | .prop, .prop, .app (s := .prop) (.const ⟨"iff", 0⟩) p, q =>
      .conj [.neg (.conj [p, .neg q]), .neg (.conj [q, .neg p])]
  | .ind, .prop, .app (s := .ind) (.const ⟨"eq", 0⟩) a, b => .equal a b
  | .arrow .ind .prop, .prop, .const ⟨"forall", 0⟩, .lam _ p => .all p
  | .arrow .ind .prop, .prop, .const ⟨"exists", 0⟩, .lam _ p => .neg (.all (.neg p))
  | _, _, f, a => .app f a

/-- Binding indices are unchanged: both representations count per sort. -/
def ofTerm : Lambda.Term s → SimpleExpr s
  | .bound n => .bound n
  | .free x => .free x
  | .const c => lowerConst _ c
  | .app f a => lowerApp (ofTerm f) (ofTerm a)
  | .lam s b => .lam s (ofTerm b)

end SimpleExpr
end Lisa.Orthologic
