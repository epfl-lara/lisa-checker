import Lisa.Lambda.NamedDecision
import Lisa.Combined.Reference

namespace Lisa.ExpressionOrder

open Lambda

/-- Normalize well-sorted lambda syntax and leave malformed expressions unchanged. -/
def reduceLambda (p : Expr) : Expr := (normalizeNamed p).getD p

theorem reduceLambda_conversion (p : Expr) : Conversion (reduceLambda p) p := by
  cases h : normalizeNamed p with
  | none => simpa [reduceLambda, h] using Conversion.refl p
  | some q => simpa [reduceLambda, h] using (normalizeNamed_sound h).symm

@[simp] theorem reduceLambda_sort (p : Expr) : (reduceLambda p).sort = p.sort :=
  (reduceLambda_conversion p).preserves_sort

@[simp] theorem reduceLambda_idempotent (p : Expr) : reduceLambda (reduceLambda p) = reduceLambda p := by
  cases h : normalizeNamed p with
  | none => simp [reduceLambda, h]
  | some q => simp [reduceLambda, h, normalizeNamed_idempotent h]

/-- Characterize named conversion by the canonical reducer on sorted inputs. -/
theorem reduceLambda_eq_iff {p q : Expr} (hp : p.hasSort s) :
    reduceLambda p = reduceLambda q ↔ Conversion p q := by
  constructor
  · intro h
    exact (reduceLambda_conversion p).symm.trans (h ▸ reduceLambda_conversion q)
  · intro h
    have hn := (conversion_iff_normalizeNamed_eq hp).mp h
    cases he : normalizeNamed p with
    | none =>
        have hs := (normalizeNamed_none p).mp he
        simp [Expr.hasSort, hs] at hp
    | some r => simp [reduceLambda, he, ← hn]

/-- Supply canonical lambda reduction without changing the current reducer or order. -/
@[reducible] def lambdaReduction : OrderReduction leq where
  reduce := reduceLambda
  preserves p := same_of_conversion (reduceLambda_conversion p)
  preservesSort := reduceLambda_sort

/-- Preserve the full reference order when preprocessing either side by lambda normalization. -/
theorem leq_reduceLambda_iff (p q : Expr) : leq (reduceLambda p) (reduceLambda q) ↔ leq p q := by
  letI := lambdaReduction
  exact OrderReduction.leq_iff (leq := leq) p q

/-- Preserve application contexts, even when their enclosing syntax is malformed. -/
theorem reduceLambda_app (f a : Expr) :
    Conversion (reduceLambda (.app f a)) (.app (reduceLambda f) (reduceLambda a)) :=
  (reduceLambda_conversion _).trans
    (.app (reduceLambda_conversion f).symm (reduceLambda_conversion a).symm)

theorem reduceLambda_lam (x : SVar) (p : Expr) :
    Conversion (reduceLambda (.lam x p)) (.lam x (reduceLambda p)) :=
  (reduceLambda_conversion _).trans (.lam x (reduceLambda_conversion p).symm)

end Lisa.ExpressionOrder
