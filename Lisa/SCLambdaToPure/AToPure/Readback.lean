import Lisa.SCLambdaToPure.AToPure.Syntax
import Lisa.SCLambdaToPure.Pure
import Lisa.SCLambdaToPure.AToPure.FirstOrderShape
import Lisa.SCLambdaToPure.AToPure.Normalization

/-! Read canonical LambdaFOL expressions into independent first-order epsilon syntax.
Terms and formulas are read together: epsilon contains a formula, while atomic
formulas contain terms. Unsupported higher-order heads are rejected, not hidden
inside first-order atoms. Bound individual indices become last-slot levels.
-/
namespace Lisa.SCLambdaToPure.Readback
open Lambda
abbrev BTerm (n : Nat) := Pure.BTerm language Identifier n
abbrev BFormula (n : Nat) := Pure.BFormula language Identifier n
mutual
  /-- Read an individual term. All arguments of a first-order symbol are individuals. -/
  def term {n : Nat} (ρ : Bound n) : Term ind → Option (BTerm n)
    | .bound k => (ρ k).map (fun i => .var (.inr i))
    | .free x => some (.var (.inl x))
    | .const c => some (.func ⟨false, c⟩ Fin.elim0)
    | .app (s := .ind) f a => do
        let (symbol, args) ← spine ρ f
        let a' ← term ρ a
        let args := args ++ [a']
        return .func symbol args.get
    | .app (s := .arrow .ind .prop) (.const ⟨"epsilon", 0⟩) (.lam _ p) =>
        return .epsilon (← formula (bind ρ) p)
    | .app (s := .prop) _ _ => none
    | .app (s := .arrow _ _) _ _ => none

  /-- Collect the head and individual arguments of a partially applied symbol. -/
  def spine {n : Nat} (ρ : Bound n) : Term s → Option (Symbol × List (BTerm n))
    | .free x => some (⟨true, x⟩, [])
    | .const c => some (⟨false, c⟩, [])
    | .app (s := .ind) f a => do
        let (symbol, args) ← spine ρ f
        let a' ← term ρ a
        return (symbol, args ++ [a'])
    | _ => none
  /-- Read a formula after eta-long normalization. Recognition includes sorts and
  the complete identifier, just as it does in the production normalizer. -/
  def formula {n : Nat} (ρ : Bound n) : Term prop → Option (BFormula n)
    | .const ⟨"top", 0⟩ => some .top
    | .const ⟨"bot", 0⟩ => some .bot
    | .app (s := .prop) (.const ⟨"not", 0⟩) p => return (← formula ρ p).not
    | .app (s := .prop) (.app (s := .prop) (.const ⟨"and", 0⟩) p) q =>
        return .and (← formula ρ p) (← formula ρ q)
    | .app (s := .prop) (.app (s := .prop) (.const ⟨"or", 0⟩) p) q =>
        return .or (← formula ρ p) (← formula ρ q)
    | .app (s := .prop) (.app (s := .prop) (.const ⟨"imp", 0⟩) p) q =>
        return (← formula ρ p).imp (← formula ρ q)
    | .app (s := .prop) (.app (s := .prop) (.const ⟨"iff", 0⟩) p) q =>
        return (← formula ρ p).iff (← formula ρ q)
    | .app (s := .ind) (.app (s := .ind) (.const ⟨"eq", 0⟩) t) u =>
        return .equal (← term ρ t) (← term ρ u)
    | .app (s := .arrow .ind .prop) (.const ⟨"forall", 0⟩) (.lam _ p) =>
        return (← formula (bind ρ) p).all
    | .app (s := .arrow .ind .prop) (.const ⟨"exists", 0⟩) (.lam _ p) =>
        return (← formula (bind ρ) p).ex
    | .free x => some (.rel ⟨true, x⟩ Fin.elim0)
    | .const c => some (.rel ⟨false, c⟩ Fin.elim0)
    | .app (s := .ind) f a => do
        let (symbol, args) ← spine ρ f
        let a' ← term ρ a
        let args := args ++ [a']
        return .rel symbol args.get
    | _ => none

end

def readFormula (e : Expr) : Option (BFormula 0) := do
  let ⟨s, t⟩ ← Readback.normalized e
  match s, t with
  | .prop, t => formula (fun _ => none) t
  | _, _ => none

def readTerm (e : Expr) : Option (BTerm 0) := do
  let ⟨s, t⟩ ← Readback.normalized e
  match s, t with
  | .ind, t => term (fun _ => none) t
  | _, _ => none

theorem readFormula_eq {e f : Expr} (h : AlphaBetaEta e f) :
    readFormula e = readFormula f := by simp only [readFormula, Readback.normalized_eq h]

theorem readTerm_eq {e f : Expr} (h : AlphaBetaEta e f) :
    readTerm e = readTerm f := by simp only [readTerm, Readback.normalized_eq h]

end Lisa.SCLambdaToPure.Readback

/-! Readback succeeds on well-scoped first-order shapes. -/

namespace Lisa.SCLambdaToPure.Readback

open Lambda FirstOrderShape

private def ReadsIndividual (ρ : Bound n) : {s : LSort} → Term s → Prop
  | .ind, e => (term ρ e).isSome
  | _, e => (spine ρ e).isSome

private theorem formula_const_isSome (ρ : Bound n) (c : Identifier) :
    (formula ρ (.const c)).isSome := by
  by_cases ht : c = ⟨"top", 0⟩
  · subst c; simp [formula]
  by_cases hb : c = ⟨"bot", 0⟩
  · subst c; simp [formula]
  simp [formula]

private theorem formula_app_isSome (ρ : Bound n) (f : Term (ind >> prop)) (a : Term ind)
    (hf : (spine ρ f).isSome) (ha : (term ρ a).isSome) :
    (formula ρ (.app f a)).isSome := by
  by_cases he : ∃ t : Term ind, f = .app (.const ⟨"eq", 0⟩) t
  · obtain ⟨t, rfl⟩ := he
    simp only [spine] at hf
    cases ht : term ρ t <;> simp [ht] at hf
    obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp ha
    simp [formula, ht, ha']
  · obtain ⟨⟨c, args⟩, hc⟩ := Option.isSome_iff_exists.mp hf
    obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp ha
    simp only [not_exists] at he
    simp [formula, hc, ha']

private def ReadsFormula (ρ : Bound n) : {s : LSort} → Term s → Prop
  | .prop, e => (formula ρ e).isSome
  | _, e => (spine ρ e).isSome

private theorem bind_isSome {d : Depth} (ρ : Bound n) (hρ : ∀ k < d ind, (ρ k).isSome) :
    ∀ k < (d.inc ind) ind, (bind ρ k).isSome := by
  intro k hk
  cases k with
  | zero => rfl
  | succ k => simpa [bind] using hρ k (by simpa using hk)

mutual
private theorem individual_reads {s n : _} {d xs} {e : Term s} (h : Individual e)
    (hs : Supported d xs e) (ρ : Bound n) (hρ : ∀ k < d ind, (ρ k).isSome) :
    ReadsIndividual ρ e := by
  match h with
  | .bound k => simpa [ReadsIndividual, term] using hρ k hs
  | .free x => simp [ReadsIndividual, term]
  | .symbol k c => cases k <;> simp [ReadsIndividual, term, spine, arity]
  | @Individual.app s f a hf ha =>
      obtain ⟨⟨c, args⟩, hc⟩ := Option.isSome_iff_exists.mp (individual_reads hf hs.1 ρ hρ)
      obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (individual_reads ha hs.2 ρ hρ)
      cases s <;> simp [ReadsIndividual, term, spine, hc, ha']

  | .epsilon hp =>
      obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.mp (formula_reads hp hs.2 (bind ρ) (bind_isSome ρ hρ))
      simp [ReadsIndividual, term, hp']
termination_by structural h
private theorem formula_reads {s n : _} {d xs} {e : Term s} (h : Formula e)
    (hs : Supported d xs e) (ρ : Bound n) (hρ : ∀ k < d ind, (ρ k).isSome) :
    ReadsFormula ρ e := by
  match h with
  | .free x => simp [ReadsFormula, formula]
  | .symbol k c => cases k with
    | zero => exact formula_const_isSome ρ c
    | succ k => simp [ReadsFormula, spine, arity]
  | @Formula.app s f a hf ha =>
      have hf' := formula_reads hf hs.1 ρ hρ
      have ha' := individual_reads ha hs.2 ρ hρ
      cases s with
      | prop => exact formula_app_isSome ρ f a hf' ha'
      | ind | arrow _ _ =>
          obtain ⟨⟨c, args⟩, hc⟩ := Option.isSome_iff_exists.mp hf'
          obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp ha'
          simp [ReadsFormula, spine, hc, ha']
  | .top => simp [ReadsFormula, formula]
  | .bot => simp [ReadsFormula, formula]
  | .neg hp =>
      obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.mp (formula_reads hp hs.2 ρ hρ)
      simp [ReadsFormula, formula, hp']
  | .and hp hq | .or hp hq | .imp hp hq | .iff hp hq =>
      obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.mp (formula_reads hp hs.1.2 ρ hρ)
      obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.mp (formula_reads hq hs.2 ρ hρ)
      simp [ReadsFormula, formula, hp', hq']
  | .eq ht hu =>
      obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp (individual_reads ht hs.1.2 ρ hρ)
      obtain ⟨u', hu'⟩ := Option.isSome_iff_exists.mp (individual_reads hu hs.2 ρ hρ)
      simp [ReadsFormula, formula, ht', hu']
  | .all hp | .ex hp =>
      obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.mp (formula_reads hp hs.2 (bind ρ) (bind_isSome ρ hρ))
      simp [ReadsFormula, formula, hp']

termination_by structural h
end

theorem formula_isSome {e : Term prop} (h : Formula e) (hs : Supported d xs e)
    (ρ : Bound n) (hρ : ∀ k < d ind, (ρ k).isSome) : (formula ρ e).isSome :=
  formula_reads h hs ρ hρ

theorem term_isSome {e : Term ind} (h : Individual e) (hs : Supported d xs e)
    (ρ : Bound n) (hρ : ∀ k < d ind, (ρ k).isSome) : (term ρ e).isSome :=
  individual_reads h hs ρ hρ

/-- Every well-sorted formula at the epsilon boundary has first-order readback.
There is no fuel bound, and epsilon formulas remain visible in the result. -/
theorem readFormula_isSome {p : Expr} (hp : isFormula p)
    (hc : ConstantsInLanguage p)
    (hv : ∀ x ∈ p.freeVars, x.sort = ind ∨ x.sort = prop) :
    (readFormula p).isSome := by
  obtain ⟨e, he⟩ := interpretNamed_sorted hp Names.free
  have hshape := normalize_named_formula he (inLanguage_of_interpretNamed he hc hv)
  have hs := normalize_supported e (subst_of_interpretNamed he)
  simpa [readFormula, Readback.normalized, he] using
    formula_isSome hshape hs (n := 0) (fun _ => none) (by simp [Depth.zero])

theorem readTerm_isSome {p : Expr} (hp : isTerm p)
    (hc : ConstantsInLanguage p)
    (hv : ∀ x ∈ p.freeVars, x.sort = ind ∨ x.sort = prop) :
    (readTerm p).isSome := by
  obtain ⟨e, he⟩ := interpretNamed_sorted hp Names.free
  have hshape := normalize_individual (inLanguage_of_interpretNamed he hc hv)
    (subst_of_interpretNamed he)
  have hs := normalize_supported e (subst_of_interpretNamed he)
  simpa [readTerm, Readback.normalized, he] using
    term_isSome hshape hs (n := 0) (fun _ => none) (by simp [Depth.zero])

end Lisa.SCLambdaToPure.Readback
