import Lisa.SCLambdaToPure.AtomicRoundtrip

namespace Lisa.SCLambdaToPure

open Lambda

namespace FirstOrderShape

theorem Individual.inLanguage {e : Term s} (h : Individual e) : InLanguage e := by
  induction h with
  | bound => exact .bound _
  | free => exact .individual _
  | symbol => exact .const (.function _ _)
  | app _ _ ihf iha => exact .app ihf iha

theorem Formula.inLanguage {e : Term s} (h : Formula e) : InLanguage e := by
  induction h with
  | free => exact .proposition _
  | symbol => exact .const (.predicate _ _)
  | app _ ha ih => exact .app ih ha.inLanguage
  | top => exact .const .top
  | bot => exact .const .bot
  | neg _ ih => exact .app (.const .neg) ih
  | and _ _ ihp ihq => exact .app (.app (.const .and) ihp) ihq
  | or _ _ ihp ihq => exact .app (.app (.const .or) ihp) ihq
  | imp _ _ ihp ihq => exact .app (.app (.const .imp) ihp) ihq
  | iff _ _ ihp ihq => exact .app (.app (.const .iff) ihp) ihq
  | eq ht hu => exact .app (.app (.const .eq) ht.inLanguage) hu.inLanguage
  | all _ ih => exact .app (.const .all) (.lam ih)
  | ex _ ih => exact .app (.const .ex) (.lam ih)

end FirstOrderShape

namespace Embedding

open FirstOrderShape

/-- Finite support permits one naming injection for a whole sequent. -/
def Roundtrip (p : A.Formula) : Prop :=
  ∃ xs : Finset Identifier, ∀ η : Nat → Identifier, Function.Injective η →
    (∀ x ∈ xs, η (Readback.variableCode x) = x) → Nonempty (Related η p (Translation.formula p))

theorem class_of_interpret {p : Expr} {e : Term s}
    (he : interpretNamed p Names.free = some ⟨s, e⟩) :
    A.ofExpr p (hasSort_of_interpretNamed he) = ofTyped e := by
  apply (A.ofExpr_eq _ _).mpr
  exact .alpha (alpha_reify_of_interpretNamed he Context.empty)

theorem read_ofTyped {e : Term prop} (he : Formula e) (hc : ∀ σ, e.subst σ = e) :
    Readback.formula (fun _ => none) e = some (Translation.formula (ofTyped e)) := by
  have h := Translation.some_formula (e.reify Context.empty) (e.reify_sort _)
  simpa only [Translation.readFormula, Translation.normalized, interpretNamed_reify_free,
    hc, Option.map_some, Grounding.ground_eq he.inLanguage, normalize_formula_eq he,
    ofTyped] using h.symm

private def Atomic : Term prop → Prop
  | .free _ => True
  | .const _ => True
  | .app (s := .ind) _ _ => True
  | _ => False

private theorem atomic_roundtrip {e : Term prop} (he : Formula e) (ha : Atomic e)
    (hc : ∀ σ, e.subst σ = e) : Roundtrip (ofTyped e) := by
  refine ⟨e.freeVars.image SVar.id, ?_⟩
  intro η hη hnames
  have hn (x : Identifier) (hx : (⟨x, ind⟩ : SVar) ∈ e.freeVars) : η (Readback.variableCode x) = x :=
    hnames x (Finset.mem_image.mpr ⟨⟨x, ind⟩, hx, rfl⟩)
  have hr := read_ofTyped he hc
  cases e with
  | bound => contradiction
  | free x =>
      simp only [Readback.formula, Option.some.injEq] at hr
      rw [← hr]
      exact ⟨related_free η x⟩
  | const c => exact ⟨related_const η c hr⟩
  | @app s f a =>
      cases s with
      | ind => exact ⟨related_app he η hn hr⟩
      | prop => contradiction
      | arrow s t => contradiction

private theorem atomic_reify {e : Term prop} (he : Formula e) (ha : Atomic e) (ρ : Context) :
    Roundtrip (A.ofExpr (e.reify ρ) (e.reify_sort ρ)) := by
  rw [class_of_interpret (interpretNamed_reify_free e ρ)]
  apply atomic_roundtrip (he.subst ρ.toSub (fun _ => .free _))
  · cases e with
    | bound => contradiction
    | free => trivial
    | const => trivial
    | @app s f a => cases s <;> trivial
  · exact subst_of_interpretNamed (interpretNamed_reify_free e ρ)

namespace Roundtrip

variable {p q : Expr} {hp : isFormula p} {hq : isFormula q}

theorem neg (h : Roundtrip (A.ofExpr p hp)) :
    Roundtrip (A.ofExpr (Expr.neg p) (isFormula_neg hp)) := by
  obtain ⟨xs, h⟩ := h
  refine ⟨xs, fun η hη hn => ?_⟩
  obtain ⟨d⟩ := h η hη hn
  rw [Translation.formula_neg p hp]
  exact ⟨d.neg⟩

theorem and (h : Roundtrip (A.ofExpr p hp)) (k : Roundtrip (A.ofExpr q hq)) :
    Roundtrip (A.ofExpr (Expr.and p q) (isFormula_and hp hq)) := by
  obtain ⟨xs, h⟩ := h; obtain ⟨ys, k⟩ := k
  refine ⟨xs ∪ ys, fun η hη hn => ?_⟩
  obtain ⟨d⟩ := h η hη (fun x hx => hn x (Finset.mem_union_left _ hx))
  obtain ⟨e⟩ := k η hη (fun x hx => hn x (Finset.mem_union_right _ hx))
  rw [Translation.formula_and p q hp hq]; exact ⟨d.and e⟩

theorem or (h : Roundtrip (A.ofExpr p hp)) (k : Roundtrip (A.ofExpr q hq)) :
    Roundtrip (A.ofExpr (Expr.or p q) (isFormula_or hp hq)) := by
  obtain ⟨xs, h⟩ := h; obtain ⟨ys, k⟩ := k
  refine ⟨xs ∪ ys, fun η hη hn => ?_⟩
  obtain ⟨d⟩ := h η hη (fun x hx => hn x (Finset.mem_union_left _ hx))
  obtain ⟨e⟩ := k η hη (fun x hx => hn x (Finset.mem_union_right _ hx))
  rw [Translation.formula_or p q hp hq]; exact ⟨d.or e⟩

theorem imp (h : Roundtrip (A.ofExpr p hp)) (k : Roundtrip (A.ofExpr q hq)) :
    Roundtrip (A.ofExpr (Expr.imp p q) (isFormula_imp hp hq)) := by
  obtain ⟨xs, h⟩ := h; obtain ⟨ys, k⟩ := k
  refine ⟨xs ∪ ys, fun η hη hn => ?_⟩
  obtain ⟨d⟩ := h η hη (fun x hx => hn x (Finset.mem_union_left _ hx))
  obtain ⟨e⟩ := k η hη (fun x hx => hn x (Finset.mem_union_right _ hx))
  rw [Translation.formula_imp p q hp hq]; exact ⟨d.imp e⟩

theorem iff (h : Roundtrip (A.ofExpr p hp)) (k : Roundtrip (A.ofExpr q hq)) :
    Roundtrip (A.ofExpr (Expr.iff p q) (isFormula_iff hp hq)) := by
  obtain ⟨xs, h⟩ := h; obtain ⟨ys, k⟩ := k
  refine ⟨xs ∪ ys, fun η hη hn => ?_⟩
  obtain ⟨d⟩ := h η hη (fun x hx => hn x (Finset.mem_union_left _ hx))
  obtain ⟨e⟩ := k η hη (fun x hx => hn x (Finset.mem_union_right _ hx))
  rw [Translation.formula_iff p q hp hq]; exact ⟨d.iff e⟩

theorem all (x : Identifier) (h : Roundtrip (A.ofExpr p hp)) :
    Roundtrip (A.ofExpr (Expr.forall_ ⟨x, ind⟩ p) (isFormula_forall rfl hp)) := by
  obtain ⟨xs, h⟩ := h
  refine ⟨insert x xs, fun η hη hn => ?_⟩
  obtain ⟨d⟩ := h η hη (fun y hy => hn y (Finset.mem_insert_of_mem hy))
  rw [Translation.formula_all ⟨x, ind⟩ p rfl hp]
  exact ⟨d.all hη x (hn x (Finset.mem_insert_self _ _))⟩

theorem ex (x : Identifier) (h : Roundtrip (A.ofExpr p hp)) :
    Roundtrip (A.ofExpr (Expr.exists_ ⟨x, ind⟩ p) (isFormula_exists rfl hp)) := by
  obtain ⟨xs, h⟩ := h
  refine ⟨insert x xs, fun η hη hn => ?_⟩
  obtain ⟨d⟩ := h η hη (fun y hy => hn y (Finset.mem_insert_of_mem hy))
  rw [Translation.formula_ex ⟨x, ind⟩ p rfl hp]
  exact ⟨d.ex hη x (hn x (Finset.mem_insert_self _ _))⟩

end Roundtrip

private def Reifies : {s : LSort} → Term s → Prop
  | .prop, e => ∀ ρ, Roundtrip (A.ofExpr (e.reify ρ) (e.reify_sort ρ))
  | _, _ => True

private theorem reifies {e : Term s} (he : Formula e) : Reifies e := by
  induction he with
  | free x => exact fun ρ => atomic_reify (.free x) trivial ρ
  | symbol n c =>
      cases n with
      | zero => exact fun ρ => atomic_reify (.symbol 0 c) trivial ρ
      | succ n => trivial
  | @app s f a hf ha ih =>
      cases s with
      | prop => exact fun ρ => atomic_reify (.app hf ha) trivial ρ
      | ind => trivial
      | arrow s t => trivial
  | top => exact fun ρ => atomic_reify .top trivial ρ
  | bot => exact fun ρ => atomic_reify .bot trivial ρ
  | neg _ ih => exact fun ρ => (ih ρ).neg
  | and _ _ ihp ihq => exact fun ρ => (ihp ρ).and (ihq ρ)
  | or _ _ ihp ihq => exact fun ρ => (ihp ρ).or (ihq ρ)
  | imp _ _ ihp ihq => exact fun ρ => (ihp ρ).imp (ihq ρ)
  | iff _ _ ihp ihq => exact fun ρ => (ihp ρ).iff (ihq ρ)
  | eq ht hu => exact fun ρ => atomic_reify (.eq ht hu) trivial ρ
  | @all p hp ih =>
      intro ρ
      exact (ih (ρ.extend (ρ.fresh p.freeVars ind))).all (ρ.fresh p.freeVars ind).id
  | @ex p hp ih =>
      intro ρ
      exact (ih (ρ.extend (ρ.fresh p.freeVars ind))).ex (ρ.fresh p.freeVars ind).id

theorem firstOrder_roundtrip {p : Expr} (hp : isFormula p) (hb : FirstOrderBoundary p) :
    Roundtrip (A.ofExpr p hp) := by
  obtain ⟨e, he⟩ := interpretNamed_sorted hp Names.free
  have hf := (FirstOrderShape.canonical_lamfol he hb.1 hb.2).2
  have hn : A.ofExpr p hp = ofTyped (normalize e) := by
    apply (A.ofExpr_eq _ _).mpr
    apply normalizeNamed_sound
    simp [normalizeNamed, he]
  rw [hn]
  exact reifies hf Context.empty

end Embedding
end Lisa.SCLambdaToPure
