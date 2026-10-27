import Lisa.Orthologic.Derivation
import Lisa.SCLambdaToPure.AToPure.Reverse.Reification
import Lisa.SCLambdaToPure.Pure

/-! Derived Ordered rules used by the reverse translation: contextual conversion,
individual substitution, epsilon extensionality, and replacement of whole contexts.
Each construction uses the existing rules of Ordered at alpha-beta-eta equivalence.
-/

namespace Lisa.SCLambdaToPure.OrderedDerivation

open Expr Ordered Orthologic.Derivation

noncomputable section

/-- Change a single succedent formula by conversion, retaining its context. -/
def convertRight {Γ Δ : Finset Expr} {p q : Expr}
    (hΓ : isFSet Γ) (hΔ : isFSet Δ) (hp : isFormula p)
    (h : AlphaBetaEta p q) (d : AlphaBetaEtaProof Γ (insert p Δ)) :
    AlphaBetaEtaProof Γ (insert q Δ) := by
  have hq : isFormula q := h.preserves_sort.symm.trans hp
  have step := convert hp hp (.refl _) h (.hypothesis p hp)
  simpa using ProofTree.cut (Γ := Γ) (Δ := Δ) (Ω := ∅) (Ξ := {q}) p
    hΓ hΔ isFSet_empty (singleton_sorted hq) hp d step

/-- Pointwise equivalence of predicates gives equality of their epsilon terms.
This is a derived rule, using the source's simultaneous substitution primitive.
-/
def epsilonExt {Γ Δ : Finset Expr} (x : SVar) (p q : Expr)
    (hΓ : isFSet Γ) (hΔ : isFSet Δ) (hx : x.sort = ind)
    (hp : isFormula p) (hq : isFormula q)
    (fresh : x ∉ freeVars (Γ ∪ Δ))
    (d : AlphaBetaEtaProof Γ (insert (iff p q) Δ)) :
    AlphaBetaEtaProof Γ (insert (eq (epsilon_ (.lam x p)) (epsilon_ (.lam x q))) Δ) := by
  let a := Expr.lam x p
  let b := Expr.lam x q
  let e := epsilon_ a
  have hps : p.sort = some prop := hp
  have hqs : q.sort = some prop := hq
  have ha : a.hasSort (ind >> prop) := by simp [a, hasSort, hx, hps]
  have hb : b.hasSort (ind >> prop) := by simp [b, hasSort, hx, hqs]
  have he : isTerm e := isTerm_epsilon hx hp
  have params : (SubstPair.mk a b).validParams [x] := by
    refine ⟨⟨?_, ha.trans hb.symm⟩, ?_, by simp, ?_⟩
    · simp [Expr.wellSorted, show a.sort = some (ind >> prop) from ha]
    · simp [SubstPair.sort, show a.sort = some (ind >> prop) from ha, LSort.splitArgs, hx]
    · simp [a, b, Expr.freeVars]
  have compared : AlphaBetaEta ((SubstPair.mk a b).pointwiseEq [x]) (iff p q) := by
    have bp := (AlphaBetaEta.beta x p (.var x) rfl).trans (substOne_self hp x)
    have bq := (AlphaBetaEta.beta x q (.var x) rfl).trans (substOne_self hq x)
    simpa [SubstPair.pointwiseEq, SubstPair.sort,
      LSort.splitArgs, Expr.applied, a, b, hps, hx]
      using AlphaBetaEta.app (.app (.refl _) bp) bq
  let z := Lambda.Context.empty.fresh e.freeVars (ind >> prop)
  have hz : z ∉ e.freeVars := Lambda.Context.empty.fresh_not_mem e.freeVars (ind >> prop)
  let body := eq e (epsilon_ (.var z))
  have hbody : isFormula body := by
    apply isFormula_eq he
    simp [epsilon_, isTerm, hasSort, z]
  let r := replacement z body a b [x]
  have valid : r.valid := replacement_valid hbody ha params
  have cv (f : Expr) : AlphaBetaEta (substOne z f body) (eq e (epsilon_ f)) := by
    simpa [body, eq, epsilon_, substOne, Expr.subst, Subst.subst,
      Lambda.NamedSubst.lookup_insert] using
      AlphaBetaEta.app (.app (.refl _) (substOne_fresh he z f hz)) (.refl (epsilon_ f))
  have start : AlphaBetaEtaProof ∅ {r.source} := by
    exact convertTheorem (isFormula_eq he he) (cv a).symm (.rightRefl e he)
  have comparison : AlphaBetaEtaProof Γ (insert r.equation Δ) :=
    convertRight hΓ hΔ (isFormula_iff hp hq) compared.symm d
  have step : AlphaBetaEtaProof Γ (insert r.target Δ) := by
    simpa using ProofTree.rightSubst (Γ := ∅) (Δ := ∅) (Θ := Γ) (Ξ := Δ)
      r isFSet_empty isFSet_empty hΓ hΔ valid
      (by simpa [r, replacement, SubstRule.fresh] using fresh) start comparison
  exact convertRight hΓ hΔ valid.2.2.2.2 (cv b) step

/-! Contextual conversion and individual substitution derived in Ordered.
The latter is the zero-argument instance of its simultaneous substitution rule. -/

def convertLeft {Γ Δ : Finset Expr} {p q : Expr}
    (hΓ : isFSet Γ) (hΔ : isFSet Δ) (hp : isFormula p)
    (h : AlphaBetaEta p q) (d : AlphaBetaEtaProof (insert p Γ) Δ) :
    AlphaBetaEtaProof (insert q Γ) Δ := by
  have hq : isFormula q := h.preserves_sort.symm.trans hp
  have step := convert hp hp h (.refl _) (.hypothesis p hp)
  simpa using ProofTree.cut (Γ := {q}) (Δ := ∅) (Ω := Γ) (Ξ := Δ) p
    (singleton_sorted hq) isFSet_empty hΓ hΔ hp step d

theorem substOne_congr {a b : Expr} (x : SVar) (p : Expr)
    (ha : a.hasSort x.sort) (hb : b.hasSort x.sort) (h : AlphaBetaEta a b) :
    AlphaBetaEta (substOne x a p) (substOne x b p) :=
  (AlphaBetaEta.beta x p a ha).symm.trans
    ((AlphaBetaEta.app (.refl _) h).trans (AlphaBetaEta.beta x p b hb))

private theorem individualParams {t u : Expr} (ht : isTerm t) (hu : isTerm u) :
    (SubstPair.mk t u).validParams [] := by
  simp [SubstPair.validParams, SubstPair.wellSorted, SubstPair.sort, Expr.wellSorted,
    show t.sort = some ind from ht, show u.sort = some ind from hu, LSort.splitArgs]

def leftSubst {Γ Δ Θ Ξ : Finset Expr} (x : SVar) (p t u : Expr)
    (hΓ : isFSet Γ) (hΔ : isFSet Δ) (hΘ : isFSet Θ) (hΞ : isFSet Ξ)
    (hx : x.sort = ind) (hp : isFormula p) (ht : isTerm t) (hu : isTerm u)
    (d : AlphaBetaEtaProof (insert (substOne x t p) Γ) Δ)
    (e : AlphaBetaEtaProof Θ (insert (eq t u) Ξ)) :
    AlphaBetaEtaProof (insert (substOne x u p) (Γ ∪ Θ)) (Δ ∪ Ξ) := by
  let r := replacement x p t u []
  have hr := replacement_valid hp (show t.hasSort x.sort from by simpa only [hx] using ht)
    (individualParams ht hu)
  have he : AlphaBetaEtaProof Θ (insert r.equation Ξ) := by
    simpa [r, SubstPair.pointwiseEq, SubstPair.sort, show t.sort = some ind from ht,
      LSort.splitArgs, Expr.applied] using e
  exact ProofTree.leftSubst r hΓ hΔ hΘ hΞ hr (by simp [r, replacement, SubstRule.fresh]) d he

def rightSubst {Γ Δ Θ Ξ : Finset Expr} (x : SVar) (p t u : Expr)
    (hΓ : isFSet Γ) (hΔ : isFSet Δ) (hΘ : isFSet Θ) (hΞ : isFSet Ξ)
    (hx : x.sort = ind) (hp : isFormula p) (ht : isTerm t) (hu : isTerm u)
    (d : AlphaBetaEtaProof Γ (insert (substOne x t p) Δ))
    (e : AlphaBetaEtaProof Θ (insert (eq t u) Ξ)) :
    AlphaBetaEtaProof (Γ ∪ Θ) (insert (substOne x u p) (Δ ∪ Ξ)) := by
  let r := replacement x p t u []
  have hr := replacement_valid hp (show t.hasSort x.sort from by simpa only [hx] using ht)
    (individualParams ht hu)
  have he : AlphaBetaEtaProof Θ (insert r.equation Ξ) := by
    simpa [r, SubstPair.pointwiseEq, SubstPair.sort, show t.sort = some ind from ht,
      LSort.splitArgs, Expr.applied] using e
  exact ProofTree.rightSubst r hΓ hΔ hΘ hΞ hr (by simp [r, replacement, SubstRule.fresh]) d he

/-! Replace a finite context by derivations of its members. These are cuts and
ordinary structural weakening; no compatibility assumption on an auxiliary
order, or arbitrary reordering of encoded sequents, is needed. -/

private theorem replaceLeftAux (Γ Γ₀ Δ : Finset Expr)
    (hΓ : isFSet Γ) (hΓ₀ : isFSet Γ₀) (hΔ : isFSet Δ)
    (h : ∀ p ∈ Γ, Nonempty (AlphaBetaEtaProof Γ₀ {p}))
    (d : Nonempty (AlphaBetaEtaProof (Γ ∪ Γ₀) Δ)) : Nonempty (AlphaBetaEtaProof Γ₀ Δ) := by
  induction Γ using Finset.induction_on with
  | empty => simpa using d
  | @insert p Γ hp ih =>
      have hΓ' : isFSet Γ := fun q hq => hΓ q (Finset.mem_insert_of_mem hq)
      have hps := hΓ p (Finset.mem_insert_self _ _)
      obtain ⟨dp⟩ := h p (Finset.mem_insert_self _ _)
      obtain ⟨d⟩ := d
      apply ih hΓ' (fun q hq => h q (Finset.mem_insert_of_mem hq))
      refine ⟨?_⟩
      simpa [Finset.union_assoc, Finset.union_comm, Finset.union_left_comm] using
        ProofTree.cut (Γ := Γ₀) (Δ := ∅) (Ω := Γ ∪ Γ₀) (Ξ := Δ) p
          hΓ₀ isFSet_empty (isFSet_union hΓ' hΓ₀) hΔ hps
          (by simpa using dp) (by simpa using d)

theorem replaceLeft {Γ Γ₀ Δ : Finset Expr}
    (hΓ : isFSet Γ) (hΓ₀ : isFSet Γ₀) (hΔ : isFSet Δ)
    (d : Nonempty (AlphaBetaEtaProof Γ Δ))
    (h : ∀ p ∈ Γ, Nonempty (AlphaBetaEtaProof Γ₀ {p})) : Nonempty (AlphaBetaEtaProof Γ₀ Δ) := by
  obtain ⟨d⟩ := d
  exact replaceLeftAux Γ Γ₀ Δ hΓ hΓ₀ hΔ h
    ⟨d.weakening hΓ hΔ (isFSet_union hΓ hΓ₀) hΔ
      (by intro p hp; exact Finset.mem_union_left _ hp) (by simp)⟩

private theorem replaceRightAux (Δ Δ₀ Γ : Finset Expr)
    (hΔ : isFSet Δ) (hΔ₀ : isFSet Δ₀) (hΓ : isFSet Γ)
    (h : ∀ p ∈ Δ, Nonempty (AlphaBetaEtaProof {p} Δ₀))
    (d : Nonempty (AlphaBetaEtaProof Γ (Δ ∪ Δ₀))) : Nonempty (AlphaBetaEtaProof Γ Δ₀) := by
  induction Δ using Finset.induction_on with
  | empty => simpa using d
  | @insert p Δ hp ih =>
      have hΔ' : isFSet Δ := fun q hq => hΔ q (Finset.mem_insert_of_mem hq)
      have hps := hΔ p (Finset.mem_insert_self _ _)
      obtain ⟨dp⟩ := h p (Finset.mem_insert_self _ _)
      obtain ⟨d⟩ := d
      apply ih hΔ' (fun q hq => h q (Finset.mem_insert_of_mem hq))
      refine ⟨?_⟩
      simpa [Finset.union_assoc, Finset.union_comm, Finset.union_left_comm] using
        ProofTree.cut (Γ := Γ) (Δ := Δ ∪ Δ₀) (Ω := ∅) (Ξ := Δ₀) p
          hΓ (isFSet_union hΔ' hΔ₀) isFSet_empty hΔ₀ hps
          (by simpa using d) (by simpa using dp)

theorem replaceRight {Γ Δ Δ₀ : Finset Expr}
    (hΓ : isFSet Γ) (hΔ : isFSet Δ) (hΔ₀ : isFSet Δ₀)
    (d : Nonempty (AlphaBetaEtaProof Γ Δ))
    (h : ∀ p ∈ Δ, Nonempty (AlphaBetaEtaProof {p} Δ₀)) : Nonempty (AlphaBetaEtaProof Γ Δ₀) := by
  obtain ⟨d⟩ := d
  exact replaceRightAux Δ Δ₀ Γ hΔ hΔ₀ hΓ h
    ⟨d.weakening hΓ hΔ hΓ (isFSet_union hΔ hΔ₀)
      (by simp) (by intro p hp; exact Finset.mem_union_left _ hp)⟩

end
end Lisa.SCLambdaToPure.OrderedDerivation

/-! Every derivation of the independent first-order epsilon calculus can be
embedded in the actual Ordered calculus. Epsilon extensionality is translated
using the derived source rule, not an additional source assumption. -/
namespace Lisa.SCLambdaToPure.PureEmbedding
open Readback (language)
open Ordered
variable [DecidableEq (Pure.Formula language)]
noncomputable section

def context (Γ : Pure.Context language) : Finset Expr :=
  Γ.image reifyFormula

omit [DecidableEq (Pure.Formula language)] in
@[simp] theorem context_empty : context ∅ = ∅ := Finset.image_empty _
@[simp] theorem context_insert (p : Pure.Formula language)
    (Γ : Pure.Context language) :
    context (insert p Γ) = insert (reifyFormula p) (context Γ) := Finset.image_insert _ _ _
@[simp] theorem context_union (Γ Δ : Pure.Context language) :
    context (Γ ∪ Δ) = context Γ ∪ context Δ := Finset.image_union _ _

omit [DecidableEq (Pure.Formula language)] in
theorem context_sorted (Γ : Pure.Context language) :
    isFSet (context Γ) := by
  intro p hp
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hp
  exact reifyFormula_sort p

omit [DecidableEq (Pure.Formula language)] in
theorem context_fresh
    (x : Identifier) (Γ : Pure.Context language) (hx : Pure.Fresh x Γ) :
    SVar.mk x ind ∉ freeVars (context Γ) := by
  intro h
  obtain ⟨p, hp, he⟩ := Finset.mem_biUnion.mp h
  obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hp
  subst p
  exact reifyFormula_fresh q x (hx q hq) he

private theorem context_fresh_union
    {x : Identifier} {Γ Δ : Pure.Context language}
    (hΓ : Pure.Fresh x Γ) (hΔ : Pure.Fresh x Δ) :
    SVar.mk x ind ∉ freeVars (context Γ ∪ context Δ) := by
  rw [← context_union]
  apply context_fresh
  intro p hp
  exact (Finset.mem_union.mp hp).elim (hΓ p) (hΔ p)

omit [DecidableEq (Pure.Formula language)] in
private theorem fresh_insert {Γ Δ : Finset Expr} {x : SVar} {p : Expr}
    (h : x ∉ freeVars (Γ ∪ Δ)) (hp : x ∉ p.freeVars) :
    x ∉ freeVars (insert p Γ ∪ Δ) := by
  intro hx
  obtain ⟨q, hq, hxq⟩ := Finset.mem_biUnion.mp hx
  rcases Finset.mem_union.mp hq with hq | hq
  · rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hp hxq
    · exact h (Finset.mem_biUnion.mpr ⟨q, Finset.mem_union_left _ hq, hxq⟩)
  · exact h (Finset.mem_biUnion.mpr ⟨q, Finset.mem_union_right _ hq, hxq⟩)

/-- Embed every Pure derivation in Ordered, preserving its contexts. -/
def toOrdered
    {Γ Δ : Pure.Context language} (d : Pure.ProofTree Γ Δ) :
    AlphaBetaEtaProof (context Γ) (context Δ) := by
  induction d with
  | hypothesis p => simpa using ProofTree.hypothesis (leq := AlphaBetaEta) _ (reifyFormula_sort p)
  | weakening _ hΓ hΔ ih =>
      exact .weakening (context_sorted _) (context_sorted _) (context_sorted _)
        (context_sorted _) ih (Finset.image_subset_image hΓ) (Finset.image_subset_image hΔ)
  | cut p _ _ ih ih' =>
      simpa using ProofTree.cut _ (context_sorted _) (context_sorted _)
        (context_sorted _) (context_sorted _) (reifyFormula_sort p)
        (by simpa using ih) (by simpa using ih')
  | leftFalse => simpa using (ProofTree.leftFalse (leq := AlphaBetaEta))
  | rightTrue => simpa using (ProofTree.rightTrue (leq := AlphaBetaEta))
  | leftAnd p q _ ih =>
      simpa using ProofTree.leftAnd _ _ (context_sorted _) (context_sorted _)
        (reifyFormula_sort p) (reifyFormula_sort q) (by simpa using ih)
  | rightAnd p q _ _ ih ih' =>
      simpa using ProofTree.rightAnd _ _ (context_sorted _) (context_sorted _)
        (context_sorted _) (context_sorted _) (reifyFormula_sort p) (reifyFormula_sort q)
        (by simpa using ih) (by simpa using ih')
  | leftOr p q _ _ ih ih' =>
      simpa using ProofTree.leftOr _ _ (context_sorted _) (context_sorted _)
        (context_sorted _) (context_sorted _) (reifyFormula_sort p) (reifyFormula_sort q)
        (by simpa using ih) (by simpa using ih')
  | rightOr p q _ ih =>
      simpa using ProofTree.rightOr _ _ (context_sorted _) (context_sorted _)
        (reifyFormula_sort p) (reifyFormula_sort q) (by simpa using ih)
  | leftImp p q _ _ ih ih' =>
      simpa using ProofTree.leftImp _ _ (context_sorted _) (context_sorted _)
        (context_sorted _) (context_sorted _) (reifyFormula_sort p) (reifyFormula_sort q)
        (by simpa using ih) (by simpa using ih')
  | rightImp p q _ ih =>
      simpa using ProofTree.rightImp _ _ (context_sorted _) (context_sorted _)
        (reifyFormula_sort p) (reifyFormula_sort q) (by simpa using ih)
  | leftIff p q _ ih =>
      simpa using ProofTree.leftIff _ _ (context_sorted _) (context_sorted _)
        (reifyFormula_sort p) (reifyFormula_sort q) (by simpa using ih)
  | rightIff p q _ _ ih ih' =>
      simpa using ProofTree.rightIff _ _ (context_sorted _) (context_sorted _)
        (context_sorted _) (context_sorted _) (reifyFormula_sort p) (reifyFormula_sort q)
        (by simpa using ih) (by simpa using ih')
  | leftNot p _ ih =>
      simpa using ProofTree.leftNot _ (context_sorted _) (context_sorted _)
        (reifyFormula_sort p) (by simpa using ih)
  | rightNot p _ ih =>
      simpa using ProofTree.rightNot _ (context_sorted _) (context_sorted _)
        (reifyFormula_sort p) (by simpa using ih)
  | leftForall x p t _ ih =>
      have premise := OrderedDerivation.convertLeft (context_sorted _) (context_sorted _)
        (reifyFormula_sort _) (reifyFormula_subst x t p) (by simpa using ih)
      have result := ProofTree.leftForall ⟨x, ind⟩ _ _ (context_sorted _)
        (context_sorted _) rfl (reifyFormula_sort p) (reifyTerm_sort t) premise
      simpa using OrderedDerivation.convertLeft (context_sorted _) (context_sorted _)
        (isFormula_forall rfl (reifyFormula_sort p)) (reifyFormula_forall x p).symm result
  | rightForall x p _ hΓ hΔ ih =>
      have result := ProofTree.rightForall ⟨x, ind⟩ _ (context_sorted _)
        (context_sorted _) rfl (reifyFormula_sort p) (by simpa using ih)
        (fresh_insert (context_fresh_union hΓ hΔ)
          (by simp [Expr.forall_, Expr.freeVars]))
      simpa using OrderedDerivation.convertRight (context_sorted _) (context_sorted _)
        (isFormula_forall rfl (reifyFormula_sort p)) (reifyFormula_forall x p).symm result
  | leftExists x p _ hΓ hΔ ih =>
      have result := ProofTree.leftExists ⟨x, ind⟩ _ (context_sorted _)
        (context_sorted _) rfl (reifyFormula_sort p) (by simpa using ih)
        (fresh_insert (context_fresh_union hΓ hΔ)
          (by simp [Expr.exists_, Expr.freeVars]))
      simpa using OrderedDerivation.convertLeft (context_sorted _) (context_sorted _)
        (isFormula_exists rfl (reifyFormula_sort p)) (reifyFormula_exists x p).symm result
  | rightExists x p t _ ih =>
      have premise := OrderedDerivation.convertRight (context_sorted _) (context_sorted _)
        (reifyFormula_sort _) (reifyFormula_subst x t p) (by simpa using ih)
      have result := ProofTree.rightExists ⟨x, ind⟩ _ _ (context_sorted _)
        (context_sorted _) rfl (reifyFormula_sort p) (reifyTerm_sort t) premise
      simpa using OrderedDerivation.convertRight (context_sorted _) (context_sorted _)
        (isFormula_exists rfl (reifyFormula_sort p)) (reifyFormula_exists x p).symm result
  | refl t => simpa using ProofTree.rightRefl _ (reifyTerm_sort t)
  | leftSubst x p t u _ _ ih ih' =>
      have premise := OrderedDerivation.convertLeft (context_sorted _) (context_sorted _)
        (reifyFormula_sort _) (reifyFormula_subst x t p) (by simpa using ih)
      have result := OrderedDerivation.leftSubst ⟨x, ind⟩ _ _ _ (context_sorted _) (context_sorted _)
        (context_sorted _) (context_sorted _) rfl (reifyFormula_sort p)
        (reifyTerm_sort t) (reifyTerm_sort u) premise (by simpa using ih')
      simpa using OrderedDerivation.convertLeft (isFSet_union (context_sorted _) (context_sorted _))
        (isFSet_union (context_sorted _) (context_sorted _))
        (isFormula_substOne rfl (reifyTerm_sort u) (reifyFormula_sort p))
        (reifyFormula_subst x u p).symm result
  | rightSubst x p t u _ _ ih ih' =>
      have premise := OrderedDerivation.convertRight (context_sorted _) (context_sorted _)
        (reifyFormula_sort _) (reifyFormula_subst x t p) (by simpa using ih)
      have result := OrderedDerivation.rightSubst ⟨x, ind⟩ _ _ _ (context_sorted _) (context_sorted _)
        (context_sorted _) (context_sorted _) rfl (reifyFormula_sort p)
        (reifyTerm_sort t) (reifyTerm_sort u) premise (by simpa using ih')
      simpa using OrderedDerivation.convertRight (isFSet_union (context_sorted _) (context_sorted _))
        (isFSet_union (context_sorted _) (context_sorted _))
        (isFormula_substOne rfl (reifyTerm_sort u) (reifyFormula_sort p))
        (reifyFormula_subst x u p).symm result
  | epsilonWitness x p t _ ih =>
      have premise := OrderedDerivation.convertRight (context_sorted _) (context_sorted _)
        (reifyFormula_sort _) (reifyFormula_subst x t p) (by simpa using ih)
      have result := ProofTree.rightEpsilon ⟨x, ind⟩ _ _ (context_sorted _)
        (context_sorted _) rfl (reifyFormula_sort p) (reifyTerm_sort t) premise
      have cv := (reifyFormula_subst x (Pure.epsilon_ x p) p).trans
        (OrderedDerivation.substOne_congr ⟨x, ind⟩ (reifyFormula p)
          (reifyTerm_sort _) (isTerm_epsilon rfl (reifyFormula_sort p))
          (reifyTerm_epsilon x p))
      simpa using OrderedDerivation.convertRight (context_sorted _) (context_sorted _)
        (isFormula_substOne rfl (isTerm_epsilon rfl (reifyFormula_sort p))
          (reifyFormula_sort p)) cv.symm result
  | epsilonExt x p q _ hΓ hΔ ih =>
      have result := OrderedDerivation.epsilonExt ⟨x, ind⟩ _ _ (context_sorted _) (context_sorted _)
        rfl (reifyFormula_sort p) (reifyFormula_sort q)
        (context_fresh_union hΓ hΔ)
        (by simpa using ih)
      have cv := AlphaBetaEta.app (.app (.refl (.const ⟨⟨"eq", 0⟩, ind >> ind >> prop⟩))
        (reifyTerm_epsilon x p))
        (reifyTerm_epsilon x q)
      simpa using OrderedDerivation.convertRight (context_sorted _) (context_sorted _)
        (isFormula_eq (isTerm_epsilon rfl (reifyFormula_sort p))
          (isTerm_epsilon rfl (reifyFormula_sort q))) cv.symm result

theorem provable_toOrdered
    {Γ Δ : Pure.Context language} (h : Pure.Provable Γ Δ) :
    Nonempty (AlphaBetaEtaProof (context Γ) (context Δ)) := h.map toOrdered

end
end Lisa.SCLambdaToPure.PureEmbedding
