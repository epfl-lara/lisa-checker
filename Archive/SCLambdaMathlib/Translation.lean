import Lisa.SCLambdaToPure.ReadbackSupport

/-!
# A total translation into pure first-order syntax

Interpret names, replace symbols outside the first-order fragment by closed
defaults, normalize, and read the result. Totality and independence from the
chosen alpha-beta-eta representative are proved, rather than assumed.

The rule-transport obligations (especially substitution and quantifiers) are
separate theorems; totality alone is not a conservativity theorem.
-/

namespace Lisa.SCLambdaToPure.Translation

open FirstOrder Lambda

noncomputable instance : DecidableEq (Pure.Formula Readback.language) := Classical.decEq _

def normalized (e : Expr) : Option Packed.Expr :=
  (interpretNamed e Names.free).map (fun ⟨s, t⟩ => ⟨s, normalize (Grounding.ground t)⟩)

theorem normalized_eq {e f : Expr} (h : AlphaBetaEta e f) :
    normalized e = normalized f := by
  have he := interpretNamed_alphaBetaEta h Names.free
  unfold normalized
  generalize interpretNamed e Names.free = a at he ⊢
  generalize interpretNamed f Names.free = b at he ⊢
  cases he with
  | none => rfl
  | some he =>
      simp only [Option.map_some, normalize_eq_of_equiv (Grounding.ground_equiv he)]

def readFormula (e : Expr) : Option (Pure.Formula Readback.language) := do
  let ⟨s, t⟩ ← normalized e
  match s, t with
  | .prop, t => Readback.formula (fun _ => none) t
  | _, _ => none

def readTerm (e : Expr) : Option (Pure.Term Readback.language) := do
  let ⟨s, t⟩ ← normalized e
  match s, t with
  | .ind, t =>
      (Readback.term (fun _ => none) t).map
        (Language.Term.relabel (Sum.elim id Fin.elim0))
  | _, _ => none

theorem readFormula_eq {e f : Expr} (h : AlphaBetaEta e f) :
    readFormula e = readFormula f := by simp only [readFormula, normalized_eq h]

theorem readTerm_eq {e f : Expr} (h : AlphaBetaEta e f) :
    readTerm e = readTerm f := by simp only [readTerm, normalized_eq h]

theorem readFormula_total {e : Expr} (h : isFormula e) : (readFormula e).isSome := by
  obtain ⟨t, ht⟩ := interpretNamed_sorted h Names.free
  simpa [readFormula, normalized, ht] using
    Readback.ground_formula_isSome (subst_of_interpretNamed ht)

theorem readTerm_total {e : Expr} (h : isTerm e) : (readTerm e).isSome := by
  obtain ⟨t, ht⟩ := interpretNamed_sorted h Names.free
  simpa [readTerm, normalized, ht] using
    Readback.ground_term_isSome (subst_of_interpretNamed ht)

/-- A total translation on the actual formula type used by system A. -/
def formula (p : A.Formula) : Pure.Formula Readback.language :=
  (Quotient.lift readFormula (fun _ _ h => readFormula_eq h) p.val).get (by
    have total (q : AlphaBetaEta.Term) :
        AlphaBetaEta.termSort q = some prop →
        (Quotient.lift readFormula (fun _ _ h => readFormula_eq h) q).isSome := by
      refine Quotient.inductionOn q ?_
      intro e he
      exact readFormula_total he
    exact total p.val p.property)

def term (t : Expr) (h : isTerm t) : Pure.Term Readback.language :=
  (readTerm t).get (readTerm_total h)

@[simp] theorem some_formula (p : Expr) (hp : isFormula p) :
    some (formula (A.ofExpr p hp)) = readFormula p := Option.some_get _

@[simp] theorem some_term (t : Expr) (ht : isTerm t) :
    some (term t ht) = readTerm t := Option.some_get _

theorem formula_eq_of_read {p : Expr} {hp : isFormula p} {q : Pure.Formula Readback.language}
    (h : readFormula p = some q) : formula (A.ofExpr p hp) = q :=
  Option.some.inj ((some_formula p hp).trans h)

theorem term_eq_of_read {t : Expr} {ht : isTerm t} {u : Pure.Term Readback.language}
    (h : readTerm t = some u) : term t ht = u :=
  Option.some.inj ((some_term t ht).trans h)

@[simp] theorem readFormula_bot : readFormula Expr.bot = some ⊥ := by
  simp [readFormula, normalized, Expr.bot, interpretNamed,
    Grounding.ground_const FirstOrderShape.Constant.bot, normalize,
    quote, reflect, readback, Readback.formula, SConst.named]

@[simp] theorem readFormula_top : readFormula Expr.top = some ⊤ := by
  simp [readFormula, normalized, Expr.top, interpretNamed,
    Grounding.ground_const FirstOrderShape.Constant.top, normalize,
    quote, reflect, readback, Readback.formula, SConst.named]

theorem readFormula_neg {p : Expr} (hp : isFormula p) :
    readFormula (Expr.neg p) = (readFormula p).map Language.BoundedFormula.not := by
  obtain ⟨p', hp'⟩ := interpretNamed_sorted hp Names.free
  simp [readFormula, normalized, Expr.neg, interpretNamed, hp', Packed.app,
    Grounding.ground_const FirstOrderShape.Constant.neg,
    normalize, eval, quote, reflect, readback, Readback.formula]
  cases Readback.formula (fun _ => none) (eval (Grounding.ground p') ambient Depth.zero) <;> simp

theorem readFormula_and {p q : Expr} (hp : isFormula p) (hq : isFormula q) :
    readFormula (Expr.and p q) = (do return (← readFormula p) ⊓ (← readFormula q)) := by
  obtain ⟨p', hp'⟩ := interpretNamed_sorted hp Names.free
  obtain ⟨q', hq'⟩ := interpretNamed_sorted hq Names.free
  simp [readFormula, normalized, Expr.and, interpretNamed, hp', hq', Packed.app,
    Grounding.ground_const FirstOrderShape.Constant.and,
    normalize, eval, quote, reflect, readback, Readback.formula]

theorem readFormula_or {p q : Expr} (hp : isFormula p) (hq : isFormula q) :
    readFormula (Expr.or p q) = (do return (← readFormula p) ⊔ (← readFormula q)) := by
  obtain ⟨p', hp'⟩ := interpretNamed_sorted hp Names.free
  obtain ⟨q', hq'⟩ := interpretNamed_sorted hq Names.free
  simp [readFormula, normalized, Expr.or, interpretNamed, hp', hq', Packed.app,
    Grounding.ground_const FirstOrderShape.Constant.or,
    normalize, eval, quote, reflect, readback, Readback.formula]

theorem readFormula_imp {p q : Expr} (hp : isFormula p) (hq : isFormula q) :
    readFormula (Expr.imp p q) = (do return (← readFormula p).imp (← readFormula q)) := by
  obtain ⟨p', hp'⟩ := interpretNamed_sorted hp Names.free
  obtain ⟨q', hq'⟩ := interpretNamed_sorted hq Names.free
  simp [readFormula, normalized, Expr.imp, interpretNamed, hp', hq', Packed.app,
    Grounding.ground_const FirstOrderShape.Constant.imp,
    normalize, eval, quote, reflect, readback, Readback.formula]

theorem readFormula_iff {p q : Expr} (hp : isFormula p) (hq : isFormula q) :
    readFormula (Expr.iff p q) = (do return (← readFormula p).iff (← readFormula q)) := by
  obtain ⟨p', hp'⟩ := interpretNamed_sorted hp Names.free
  obtain ⟨q', hq'⟩ := interpretNamed_sorted hq Names.free
  simp [readFormula, normalized, Expr.iff, interpretNamed, hp', hq', Packed.app,
    Grounding.ground_const FirstOrderShape.Constant.iff,
    normalize, eval, quote, reflect, readback, Readback.formula]

/-- On the intended input fragment, the translation is precisely ordinary
alpha-beta-eta canonicalization followed by the existing first-order reader. -/
theorem readFormula_of_firstOrder {p : Expr} (hp : isFormula p)
    (hc : FirstOrderShape.ConstantsInLanguage p)
    (hv : ∀ x ∈ p.freeVars, x.sort = ind ∨ x.sort = prop) :
    readFormula p = Readback.readFormula p := by
  obtain ⟨t, ht⟩ := interpretNamed_sorted hp Names.free
  have hg := Grounding.ground_eq (FirstOrderShape.inLanguage_of_interpretNamed ht hc hv)
  simp [readFormula, normalized, Readback.readFormula, Readback.normalized, ht, hg]


@[simp] theorem formula_bot : formula (A.ofExpr Expr.bot rfl) = ⊥ :=
  formula_eq_of_read readFormula_bot

@[simp] theorem formula_top : formula (A.ofExpr Expr.top rfl) = ⊤ :=
  formula_eq_of_read readFormula_top

theorem formula_neg (p : Expr) (hp : isFormula p) :
    formula (A.ofExpr (Expr.neg p) (isFormula_neg hp)) =
      (formula (A.ofExpr p hp)).not := by
  apply Option.some.inj
  rw [some_formula, readFormula_neg hp, ← some_formula p hp]
  rfl

theorem formula_and (p q : Expr) (hp : isFormula p) (hq : isFormula q) :
    formula (A.ofExpr (Expr.and p q) (isFormula_and hp hq)) =
      formula (A.ofExpr p hp) ⊓ formula (A.ofExpr q hq) := by
  apply Option.some.inj
  rw [some_formula, readFormula_and hp hq, ← some_formula p hp, ← some_formula q hq]
  rfl

theorem formula_or (p q : Expr) (hp : isFormula p) (hq : isFormula q) :
    formula (A.ofExpr (Expr.or p q) (isFormula_or hp hq)) =
      formula (A.ofExpr p hp) ⊔ formula (A.ofExpr q hq) := by
  apply Option.some.inj
  rw [some_formula, readFormula_or hp hq, ← some_formula p hp, ← some_formula q hq]
  rfl

theorem formula_imp (p q : Expr) (hp : isFormula p) (hq : isFormula q) :
    formula (A.ofExpr (Expr.imp p q) (isFormula_imp hp hq)) =
      (formula (A.ofExpr p hp)).imp (formula (A.ofExpr q hq)) := by
  apply Option.some.inj
  rw [some_formula, readFormula_imp hp hq, ← some_formula p hp, ← some_formula q hq]
  rfl

theorem formula_iff (p q : Expr) (hp : isFormula p) (hq : isFormula q) :
    formula (A.ofExpr (Expr.iff p q) (isFormula_iff hp hq)) =
      (formula (A.ofExpr p hp)).iff (formula (A.ofExpr q hq)) := by
  apply Option.some.inj
  rw [some_formula, readFormula_iff hp hq, ← some_formula p hp, ← some_formula q hq]
  rfl

private theorem relabel_zero (t : Readback.BTerm 0) :
    (t.relabel (Sum.elim id Fin.elim0)).relabel Sum.inl = t := by
  rw [Language.Term.relabel_relabel]
  have h : (Sum.inl ∘ Sum.elim (id : Nat → Nat) (Fin.elim0 : Fin 0 → Nat)) = id := by
    funext x
    cases x with
    | inl => rfl
    | inr i => exact i.elim0
  rw [h, Language.Term.relabel_id]

theorem readFormula_eq_terms {t u : Expr} (ht : isTerm t) (hu : isTerm u) :
    readFormula (Expr.eq t u) =
      (do return (← readTerm t).equal (← readTerm u)) := by
  obtain ⟨t', ht'⟩ := interpretNamed_sorted ht Names.free
  obtain ⟨u', hu'⟩ := interpretNamed_sorted hu Names.free
  simp [readFormula, readTerm, normalized, Expr.eq, interpretNamed, ht', hu', Packed.app,
    Grounding.ground_const FirstOrderShape.Constant.eq,
    normalize, eval, quote, reflect, readback, Readback.formula]
  cases Readback.term (fun _ => none) (eval (Grounding.ground t') ambient Depth.zero) <;>
    cases Readback.term (fun _ => none) (eval (Grounding.ground u') ambient Depth.zero) <;>
    simp only [Option.bind_some, Option.map_some, Option.bind_none, Option.map_none,
      Language.Term.equal, Language.Term.bdEqual, relabel_zero]

theorem formula_eq (t u : Expr) (ht : isTerm t) (hu : isTerm u) :
    formula (A.ofExpr (Expr.eq t u) (isFormula_eq ht hu)) = (term t ht).equal (term u hu) := by
  apply Option.some.inj
  rw [some_formula, readFormula_eq_terms ht hu, ← some_term t ht, ← some_term u hu]
  rfl

theorem formula_freeVars (p : Expr) (hp : isFormula p) :
    (formula (A.ofExpr p hp)).freeVarFinset ⊆ Readback.names p.freeVars := by
  obtain ⟨t, ht⟩ := interpretNamed_sorted hp Names.free
  have hread := (some_formula p hp).symm
  simp only [readFormula, normalized, ht, Option.map_some] at hread
  exact (Readback.formula_support _ _ hread).trans
    (Readback.names_mono (normalize_ground_freeVars ht))

/-- Quotient freshness is enough: choose its fresh representative, then use
conversion invariance and the fact that the translation introduces no names. -/
theorem fresh (x : SVar) (Γ : A.Context) (hx : x.sort = ind) (h : A.Fresh x Γ) :
    Pure.Fresh (Readback.variableCode x.id) (Γ.image formula) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨e, he, hq, hf⟩ := h q hq
  rw [← hq]
  intro hmem
  have hm := (Readback.mem_names_iff x.id e.freeVars).mp (formula_freeVars e he hmem)
  apply hf
  have hxe : SVar.mk x.id ind = x := by cases x; simp_all
  simpa only [hxe] using hm

end Lisa.SCLambdaToPure.Translation

