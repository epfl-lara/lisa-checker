import Lisa.Lambda.Syntax
import Lisa.Conversion

/-! Relate intrinsically typed terms to the named calculus's alpha keys. -/

namespace Lisa.Lambda.Term

def index : {Γ : List LSort} → {s : LSort} → Var Γ s → Nat
  | _, _, .here => 0
  | _, _, .there v => index v + 1

/-- Erase typing evidence while retaining binder depth and free identifiers. -/
def erase : Term Γ s → NamelessExpr
  | .bound (s := s) v => .bound (index v) s
  | .free (s := s) x => .free ⟨x, s⟩
  | .const (s := s) c => .const ⟨c, s⟩
  | .app f a => .app f.erase a.erase
  | .lam (s := s) b => .lam s b.erase


end Lisa.Lambda.Term
