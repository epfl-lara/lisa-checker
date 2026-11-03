import Lisa.LambdaFol.ToPureFol.SignatureAndVariables
import Lisa.LambdaFol.PureFol
import Lisa.LambdaFol.ToPureFol.FirstOrderShape
import Lisa.LambdaFol.ToPureFol.NormalizationScope

/-! Read canonical LambdaFOL expressions into independent first-order epsilon syntax.
Terms and formulas are read together: epsilon contains a formula, while atomic
formulas contain terms. Unsupported higher-order heads return `none`.
Bound individual indices become last-slot levels.
-/
namespace Lisa.LambdaFol.PureFolTranslation
open AlphaBetaEtaNormalization
abbrev BoundedTerm (n : Nat) := PureFol.BoundedTerm language Identifier n
abbrev BoundedFormula (n : Nat) := PureFol.BoundedFormula language Identifier n
mutual
  /-- Read an individual term. All arguments of a first-order symbol are individuals. -/
  def fromNormalTerm? {n : Nat} (ρ : BoundVarMap n) : Term ind → Option (BoundedTerm n)
    | .bound k => (ρ k).map (fun i => .var (.inr i))
    | .free x => some (.var (.inl x))
    | .const c => some (.func ⟨false, c⟩ Fin.elim0)
    | .app (s := .ind) f a => do
        let (symbol, args) ← symbolAndArguments? ρ f
        let a' ← fromNormalTerm? ρ a
        let args := args ++ [a']
        return .func symbol args.get
    | .app (s := .arrow .ind .prop) (.const ⟨"epsilon", 0⟩) (.lam _ p) =>
        return .epsilon (← fromNormalFormula? (bind ρ) p)
    | .app (s := .prop) _ _ => none
    | .app (s := .arrow _ _) _ _ => none

  /-- Collect the head and individual arguments of a partially applied symbol. -/
  def symbolAndArguments? {n : Nat} (ρ : BoundVarMap n) : Term s → Option (Symbol × List (BoundedTerm n))
    | .free x => some (⟨true, x⟩, [])
    | .const c => some (⟨false, c⟩, [])
    | .app (s := .ind) f a => do
        let (symbol, args) ← symbolAndArguments? ρ f
        let a' ← fromNormalTerm? ρ a
        return (symbol, args ++ [a'])
    | _ => none
  /-- Read a formula after eta-long normalization. Recognition includes sorts and
  the complete identifier, just as it does in the production normalizer. -/
  def fromNormalFormula? {n : Nat} (ρ : BoundVarMap n) : Term prop → Option (BoundedFormula n)
    | .const ⟨"top", 0⟩ => some .top
    | .const ⟨"bot", 0⟩ => some .bot
    | .app (s := .prop) (.const ⟨"not", 0⟩) p => return (← fromNormalFormula? ρ p).not
    | .app (s := .prop) (.app (s := .prop) (.const ⟨"and", 0⟩) p) q =>
        return .and (← fromNormalFormula? ρ p) (← fromNormalFormula? ρ q)
    | .app (s := .prop) (.app (s := .prop) (.const ⟨"or", 0⟩) p) q =>
        return .or (← fromNormalFormula? ρ p) (← fromNormalFormula? ρ q)
    | .app (s := .prop) (.app (s := .prop) (.const ⟨"imp", 0⟩) p) q =>
        return (← fromNormalFormula? ρ p).imp (← fromNormalFormula? ρ q)
    | .app (s := .prop) (.app (s := .prop) (.const ⟨"iff", 0⟩) p) q =>
        return (← fromNormalFormula? ρ p).iff (← fromNormalFormula? ρ q)
    | .app (s := .ind) (.app (s := .ind) (.const ⟨"eq", 0⟩) t) u =>
        return .equal (← fromNormalTerm? ρ t) (← fromNormalTerm? ρ u)
    | .app (s := .arrow .ind .prop) (.const ⟨"forall", 0⟩) (.lam _ p) =>
        return (← fromNormalFormula? (bind ρ) p).all
    | .app (s := .arrow .ind .prop) (.const ⟨"exists", 0⟩) (.lam _ p) =>
        return (← fromNormalFormula? (bind ρ) p).ex
    | .free x => some (.rel ⟨true, x⟩ Fin.elim0)
    | .const c => some (.rel ⟨false, c⟩ Fin.elim0)
    | .app (s := .ind) f a => do
        let (symbol, args) ← symbolAndArguments? ρ f
        let a' ← fromNormalTerm? ρ a
        let args := args ++ [a']
        return .rel symbol args.get
    | _ => none

end

def fromExprFormula? (e : Expr) : Option (BoundedFormula 0) := do
  let ⟨s, t⟩ ← PureFolTranslation.normalizeExpr? e
  match s, t with
  | .prop, t => fromNormalFormula? (fun _ => none) t
  | _, _ => none

def fromExprTerm? (e : Expr) : Option (BoundedTerm 0) := do
  let ⟨s, t⟩ ← PureFolTranslation.normalizeExpr? e
  match s, t with
  | .ind, t => fromNormalTerm? (fun _ => none) t
  | _, _ => none

end Lisa.LambdaFol.PureFolTranslation

/-! Translation to PureFol succeeds on well-scoped first-order shapes. -/

namespace Lisa.LambdaFol.PureFolTranslation

open AlphaBetaEtaNormalization FirstOrderShape

private def ReadsIndividual (ρ : BoundVarMap n) : {s : LSort} → Term s → Prop
  | .ind, e => (fromNormalTerm? ρ e).isSome
  | _, e => (symbolAndArguments? ρ e).isSome

private theorem fromNormalFormula_const_isSome (ρ : BoundVarMap n) (c : Identifier) :
    (fromNormalFormula? ρ (.const c)).isSome := by
  by_cases ht : c = ⟨"top", 0⟩
  · subst c; simp [fromNormalFormula?]
  by_cases hb : c = ⟨"bot", 0⟩
  · subst c; simp [fromNormalFormula?]
  simp [fromNormalFormula?]

private theorem fromNormalFormula_app_isSome (ρ : BoundVarMap n) (f : Term (ind >> prop)) (a : Term ind)
    (hf : (symbolAndArguments? ρ f).isSome) (ha : (fromNormalTerm? ρ a).isSome) :
    (fromNormalFormula? ρ (.app f a)).isSome := by
  by_cases he : ∃ t : Term ind, f = .app (.const ⟨"eq", 0⟩) t
  · obtain ⟨t, rfl⟩ := he
    simp only [symbolAndArguments?] at hf
    cases ht : fromNormalTerm? ρ t <;> simp [ht] at hf
    obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp ha
    simp [fromNormalFormula?, ht, ha']
  · obtain ⟨⟨c, args⟩, hc⟩ := Option.isSome_iff_exists.mp hf
    obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp ha
    simp only [not_exists] at he
    simp [fromNormalFormula?, hc, ha']

private def ReadsFormula (ρ : BoundVarMap n) : {s : LSort} → Term s → Prop
  | .prop, e => (fromNormalFormula? ρ e).isSome
  | _, e => (symbolAndArguments? ρ e).isSome

private theorem bind_isSome {d : Depth} (ρ : BoundVarMap n) (hρ : ∀ k < d ind, (ρ k).isSome) :
    ∀ k < (d.inc ind) ind, (bind ρ k).isSome := by
  intro k hk
  cases k with
  | zero => rfl
  | succ k => simpa [bind] using hρ k (by simpa using hk)

mutual
private theorem individual_reads {s n : _} {d} {e : Term s} (h : IsTermOrFunction e)
    (hs : Scoped d e) (ρ : BoundVarMap n) (hρ : ∀ k < d ind, (ρ k).isSome) :
    ReadsIndividual ρ e := by
  match h with
  | .bound k => simpa [ReadsIndividual, fromNormalTerm?] using hρ k hs
  | .free x => simp [ReadsIndividual, fromNormalTerm?]
  | .symbol k c => cases k <;> simp [ReadsIndividual, fromNormalTerm?, symbolAndArguments?, arity]
  | @IsTermOrFunction.app s f a hf ha =>
      obtain ⟨⟨c, args⟩, hc⟩ := Option.isSome_iff_exists.mp (individual_reads hf hs.1 ρ hρ)
      obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (individual_reads ha hs.2 ρ hρ)
      cases s <;> simp [ReadsIndividual, fromNormalTerm?, symbolAndArguments?, hc, ha']

  | .epsilon hp =>
      obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.mp (fromNormalFormula_reads hp hs.2 (bind ρ) (bind_isSome ρ hρ))
      simp [ReadsIndividual, fromNormalTerm?, hp']
termination_by structural h
private theorem fromNormalFormula_reads {s n : _} {d} {e : Term s} (h : IsFormulaOrPredicate e)
    (hs : Scoped d e) (ρ : BoundVarMap n) (hρ : ∀ k < d ind, (ρ k).isSome) :
    ReadsFormula ρ e := by
  match h with
  | .free x => simp [ReadsFormula, fromNormalFormula?]
  | .symbol k c => cases k with
    | zero => exact fromNormalFormula_const_isSome ρ c
    | succ k => simp [ReadsFormula, symbolAndArguments?, arity]
  | @IsFormulaOrPredicate.app s f a hf ha =>
      have hf' := fromNormalFormula_reads hf hs.1 ρ hρ
      have ha' := individual_reads ha hs.2 ρ hρ
      cases s with
      | prop => exact fromNormalFormula_app_isSome ρ f a hf' ha'
      | ind | arrow _ _ =>
          obtain ⟨⟨c, args⟩, hc⟩ := Option.isSome_iff_exists.mp hf'
          obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp ha'
          simp [ReadsFormula, symbolAndArguments?, hc, ha']
  | .neg hp =>
      obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.mp (fromNormalFormula_reads hp hs.2 ρ hρ)
      simp [ReadsFormula, fromNormalFormula?, hp']
  | .and hp hq | .or hp hq | .imp hp hq | .iff hp hq =>
      obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.mp (fromNormalFormula_reads hp hs.1.2 ρ hρ)
      obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.mp (fromNormalFormula_reads hq hs.2 ρ hρ)
      simp [ReadsFormula, fromNormalFormula?, hp', hq']
  | .all hp | .ex hp =>
      obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.mp (fromNormalFormula_reads hp hs.2 (bind ρ) (bind_isSome ρ hρ))
      simp [ReadsFormula, fromNormalFormula?, hp']

termination_by structural h
end

theorem fromNormalFormula_isSome {e : Term prop} (h : IsFormulaOrPredicate e) (hs : Scoped d e)
    (ρ : BoundVarMap n) (hρ : ∀ k < d ind, (ρ k).isSome) : (fromNormalFormula? ρ e).isSome :=
  fromNormalFormula_reads h hs ρ hρ

theorem fromNormalTerm_isSome {e : Term ind} (h : IsTermOrFunction e) (hs : Scoped d e)
    (ρ : BoundVarMap n) (hρ : ∀ k < d ind, (ρ k).isSome) : (fromNormalTerm? ρ e).isSome :=
  individual_reads h hs ρ hρ

/-- Translation succeeds for well-sorted formulas whose constants and free
variables satisfy the first-order restrictions. -/
theorem fromExprFormula_isSome {p : Expr} (hp : isFormula p)
    (hc : AllowedConstants p)
    (hv : ∀ x ∈ p.freeVars, x.sort = ind ∨ x.sort = prop) :
    (fromExprFormula? p).isSome := by
  obtain ⟨e, he⟩ := interpretNamed_sorted hp Names.free
  have hshape := normalForm_isFirstOrder he hc hv
  have hs := normalize_scoped e (subst_of_interpretNamed he)
  simpa [fromExprFormula?, PureFolTranslation.normalizeExpr?, he] using
    fromNormalFormula_isSome hshape hs (n := 0) (fun _ => none) (by simp [Depth.zero])

end Lisa.LambdaFol.PureFolTranslation
