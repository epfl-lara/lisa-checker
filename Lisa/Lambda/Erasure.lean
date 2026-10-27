import Lisa.Lambda.Syntax

/-! Raw syntax uses exactly the same indices as intrinsically sorted terms. -/
namespace Lisa.Lambda
/-- Untyped applications with the same per-sort indices as typed syntax. -/

inductive RawTerm where
  | bound : Nat → LSort → RawTerm
  | free : SVar → RawTerm
  | const : SConst → RawTerm
  | app : RawTerm → RawTerm → RawTerm
  | lam : LSort → RawTerm → RawTerm
  deriving DecidableEq, Repr

def Term.erase : Term s → RawTerm
  | .bound n => .bound n s
  | .free x => .free ⟨x, s⟩
  | .const c => .const ⟨c, s⟩
  | .app f a => .app f.erase a.erase
  | .lam b e => .lam b e.erase
end Lisa.Lambda
