import Lisa.AlphaBetaEtaOrder
import Lisa.Lambda.NamedReflection

/-! Proof steps used by the LambdaFOL orthologic checker.

The target throughout is `Ordered AlphaBetaEta`, not an order that assumes the
constructor laws we are trying to justify. In particular, replacement below an
arbitrary application uses the two-premise substitution rule.
-/

namespace Lisa.Orthologic
open Expr
open Ordered

noncomputable section

namespace Derivation

abbrev Entails (p q : Expr) := AlphaBetaEtaProof {p} {q}
abbrev Theorem (p : Expr) := AlphaBetaEtaProof ∅ {p}

theorem singleton_sorted (h : isFormula p) : isFSet {p} :=
  isFSet_insert h isFSet_empty

/-- Change the two displayed formulas by alpha-beta-eta conversion. -/
def convert (hp : isFormula p) (hq : isFormula q)
    (hpp : AlphaBetaEta p p') (hqq : AlphaBetaEta q q')
    (d : Entails p q) : Entails p' q' := by
  have hp' : isFormula p' := hpp.preserves_sort.symm.trans hp
  have hq' : isFormula q' := hqq.preserves_sort.symm.trans hq
  apply ProofTree.restateWeaken (singleton_sorted hp) (singleton_sorted hq)
    (singleton_sorted hp') (singleton_sorted hq') d
  simpa [sequentLeq, sequentToFormula, conjunction, disjunction, foldFormulas] using
    AlphaBetaEta.app (.app (.refl _) hpp) hqq

def convertTheorem (hp : isFormula p) (h : AlphaBetaEta p q)
    (d : Theorem p) : Theorem q := by
  apply ProofTree.restateWeaken isFSet_empty (singleton_sorted hp)
    isFSet_empty (singleton_sorted (h.preserves_sort.symm.trans hp)) d
  simpa [sequentLeq, sequentToFormula, disjunction, foldFormulas] using h

/-- A substitution which leaves every free variable alone preserves alpha-equivalence.
The implementation may still rename a binder to avoid capture. -/
theorem subst_alpha (hp : p.hasSort s) (σ : Subst)
    (hσ : ∀ x ∈ p.freeVars, σ.find? x = none ∨ σ.find? x = some (.var x)) :
    AlphaEq (σ.subst p) p := by
  obtain ⟨t, ht⟩ := Lambda.interpretNamed_sorted hp Lambda.Names.free
  apply Lambda.alpha_of_interpretNamed_eq (e := t) _ ht
  rw [Lambda.interpretNamed_namedSubst p σ Lambda.Names.free Lambda.Names.free]
  · exact ht
  · intro x hx
    rcases hσ x hx with h | h <;> simp [h, Lambda.interpretNamed, Lambda.Names.free]

theorem substOne_self (hp : p.hasSort s) (x : SVar) :
    AlphaBetaEta (substOne x (.var x) p) p := by
  apply AlphaBetaEta.alpha (subst_alpha hp _ _)
  intro y _
  simp only [Lambda.NamedSubst.lookup_insert, Lean.AssocList.find?]
  by_cases h : y = x <;> simp [h]

theorem substOne_fresh (hp : p.hasSort s) (x : SVar) (a : Expr)
    (hx : x ∉ p.freeVars) : AlphaBetaEta (substOne x a p) p := by
  apply AlphaBetaEta.alpha (subst_alpha hp _ _)
  intro y hy
  have h : y ≠ x := fun h => hx (h ▸ hy)
  simp [Lambda.NamedSubst.lookup_insert, h, Lean.AssocList.find?]

/-- Quantifier comparison is a derived monotonicity rule, with no order axiom. -/
def forall_mono (x : SVar) (hx : x.sort = ind)
    (hp : isFormula p) (hq : isFormula q) (d : Entails p q) :
    Entails (forall_ x p) (forall_ x q) := by
  have hxp := isFormula_forall hx hp
  have hxq := isFormula_forall hx hq
  have d' : Entails (substOne x (.var x) p) q :=
    convert hp hq (substOne_self hp x).symm (.refl _) d
  have left : Entails (forall_ x p) q :=
    .leftForall (Γ := ∅) x p (.var x) isFSet_empty (singleton_sorted hq)
      hx hp (by simpa [isTerm, hasSort] using hx) d'
  exact .rightForall (Δ := ∅) x q (singleton_sorted hxp) isFSet_empty hx hq left
    (by simp [freeVars, HasFree.freeVars, Expr.forall_, Expr.freeVars])

def exists_mono (x : SVar) (hx : x.sort = ind)
    (hp : isFormula p) (hq : isFormula q) (d : Entails p q) :
    Entails (exists_ x p) (exists_ x q) := by
  have hxp := isFormula_exists hx hp
  have hxq := isFormula_exists hx hq
  have d' : Entails p (substOne x (.var x) q) :=
    convert hp hq (.refl _) (substOne_self hq x).symm d
  have right : Entails p (exists_ x q) :=
    .rightExists (Δ := ∅) x q (.var x) (singleton_sorted hp) isFSet_empty
      hx hq (by simpa [isTerm, hasSort] using hx) d'
  exact .leftExists (Γ := ∅) x p isFSet_empty (singleton_sorted hxq) hx hp right
    (by simp [freeVars, HasFree.freeVars, Expr.exists_, Expr.freeVars])

/-- Reverse implication under negative polarity. -/
def neg_mono (hp : isFormula p) (hq : isFormula q) (d : Entails p q) :
    Entails (neg q) (neg p) := by
  have dn : AlphaBetaEtaProof (insert (neg q) {p}) ∅ :=
    .leftNot (Δ := ∅) q (singleton_sorted hp) isFSet_empty hq d
  exact .rightNot (Δ := ∅) p (singleton_sorted (isFormula_neg hq)) isFSet_empty hp
    (by convert dn using 1; ext e; simp [or_comm])

/-- Any validated simultaneous replacement is usable in an arbitrary formula
context. Comparison parameters are fresh for the empty comparison context;
they need not be fresh for the formula being rewritten. -/
def replace (r : SubstRule) (hr : r.valid) (d : Theorem r.equation) :
    Entails r.source r.target := by
  simpa using ProofTree.rightSubst (Γ := {r.source}) (Δ := ∅) (Θ := ∅) (Ξ := ∅)
    r (singleton_sorted hr.2.2.2.1) isFSet_empty isFSet_empty isFSet_empty hr
    (by simp [SubstRule.fresh, freeVars, HasFree.freeVars])
    (.hypothesis r.source hr.2.2.2.1) d

/-- One replacement, whose parameter may have any simple sort. -/
def replacement (z : SVar) (body a b : Expr) (xs : List SVar) : SubstRule :=
  ⟨[(⟨a, b⟩, xs)], ⟨[z], body⟩⟩

@[simp] theorem replacement_source :
    (replacement z body a b xs).source = substOne z a body := rfl

@[simp] theorem replacement_target :
    (replacement z body a b xs).target = substOne z b body := rfl

@[simp] theorem replacement_equation :
    (replacement z body a b xs).equation = (SubstPair.mk a b).pointwiseEq xs := rfl

theorem replacement_valid (hb : isFormula body) (ha : a.hasSort z.sort)
    (hab : (SubstPair.mk a b).validParams xs) :
    (replacement z body a b xs).valid := by
  have hsorted (e : Expr) (he : e.hasSort z.sort) :
      isFormula (substOne z e body) := by
    apply Subst.subst_preserves_hasSort _ hb
    exact Subst.wellSorted_insert (by simp) he
  exact ⟨hb, by simpa [SubstContext.fits, replacement, SubstPair.sort] using ha,
    by simpa [replacement] using hab, hsorted a ha,
    hsorted b (hab.1.2.symm.trans ha)⟩

/-- Argument congruence at any result sort, observed in a formula context `k`.
Taking `k = λw. body` covers any formula containing the application. The supplied
theorem compares the arguments fully applied to fresh independent variables. -/
def app_argument (z : SVar) (k f a b : Expr) (xs : List SVar) (t : LSort)
    (hk : k.hasSort (t >> prop)) (hf : f.hasSort (z.sort >> t)) (ha : a.hasSort z.sort)
    (hab : (SubstPair.mk a b).validParams xs) (hz : z ∉ k.freeVars ∪ f.freeVars)
    (d : Theorem ((SubstPair.mk a b).pointwiseEq xs)) :
    Entails (.app k (.app f a)) (.app k (.app f b)) := by
  have hs (e : Expr) (he : e.hasSort z.sort) : isFormula (.app k (.app f e)) := by
    change k.sort = some (t >> prop) at hk
    change f.sort = some (z.sort >> t) at hf
    change e.sort = some z.sort at he
    simp [isFormula, hasSort, Expr.sort, hk, hf, he]
  have hv : isFormula (.app k (.app f (.var z))) := hs (.var z) rfl
  have hr := replacement_valid (xs := xs) hv ha hab
  have da := replace (replacement z (.app k (.app f (.var z))) a b xs) hr d
  have conv (e : Expr) :
      AlphaBetaEta (substOne z e (.app k (.app f (.var z)))) (.app k (.app f e)) := by
    simpa [substOne, Expr.subst, Subst.subst, Lambda.NamedSubst.lookup_insert] using
      AlphaBetaEta.app (substOne_fresh hk z e (fun h => hz (Finset.mem_union_left _ h)))
        (.app (substOne_fresh hf z e (fun h => hz (Finset.mem_union_right _ h))) (.refl e))
  exact convert hr.2.2.2.1 hr.2.2.2.2 (conv a) (conv b) da

/-- The function position of an application obeys the same replacement rule. -/
def app_function (z : SVar) (k f g a : Expr) (xs : List SVar) (s t : LSort)
    (hzs : z.sort = s >> t) (hk : k.hasSort (t >> prop))
    (hf : f.hasSort z.sort) (ha : a.hasSort s)
    (hfg : (SubstPair.mk f g).validParams xs) (hz : z ∉ k.freeVars ∪ a.freeVars)
    (d : Theorem ((SubstPair.mk f g).pointwiseEq xs)) :
    Entails (.app k (.app f a)) (.app k (.app g a)) := by
  have hv : isFormula (.app k (.app (.var z) a)) := by
    change a.sort = some s at ha
    change k.sort = some (t >> prop) at hk
    simp [isFormula, hasSort, Expr.sort, hzs, hk, ha]
  have hr := replacement_valid (xs := xs) hv hf hfg
  have dr := replace (replacement z (.app k (.app (.var z) a)) f g xs) hr d
  have conv (e : Expr) :
      AlphaBetaEta (substOne z e (.app k (.app (.var z) a))) (.app k (.app e a)) := by
    simpa [substOne, Expr.subst, Subst.subst, Lambda.NamedSubst.lookup_insert] using
      AlphaBetaEta.app (substOne_fresh hk z e (fun h => hz (Finset.mem_union_left _ h)))
        (.app (.refl e) (substOne_fresh ha z e (fun h => hz (Finset.mem_union_right _ h))))
  exact convert hr.2.2.2.1 hr.2.2.2.2 (conv f) (conv g) dr

def trans (hp : isFormula p) (hq : isFormula q) (hr : isFormula r)
    (d : Entails p q) (e : Entails q r) : Entails p r := by
  simpa using ProofTree.cut (Γ := {p}) (Δ := ∅) (Ω := ∅) (Ξ := {r}) q
    (singleton_sorted hp) isFSet_empty isFSet_empty (singleton_sorted hr) hq d e

/-- Both application components may be replaced. Results can have any sort;
`k` observes them in an arbitrary formula context. Hole names are chosen here,
independently of the fresh arguments used by the two pointwise comparisons. -/
def app_congr (k f g a b : Expr) (s t : LSort) (xs ys : List SVar)
    (hk : k.hasSort (t >> prop)) (hf : f.hasSort (s >> t)) (ha : a.hasSort s)
    (hfg : (SubstPair.mk f g).validParams xs) (hab : (SubstPair.mk a b).validParams ys)
    (df : Theorem ((SubstPair.mk f g).pointwiseEq xs))
    (da : Theorem ((SubstPair.mk a b).pointwiseEq ys)) :
    Entails (.app k (.app f a)) (.app k (.app g b)) := by
  let zf := Lambda.Context.empty.fresh (k.freeVars ∪ a.freeVars) (s >> t)
  let za := Lambda.Context.empty.fresh (k.freeVars ∪ g.freeVars) s
  have hg : g.hasSort (s >> t) := hfg.1.2.symm.trans hf
  have hb : b.hasSort s := hab.1.2.symm.trans ha
  have first := app_function zf k f g a xs s t rfl hk hf ha hfg
    (Lambda.Context.empty.fresh_not_mem _ _) df
  have second := app_argument za k g a b ys t hk hg ha hab
    (Lambda.Context.empty.fresh_not_mem _ _) da
  have sorted (f a : Expr) (hf : f.hasSort (s >> t)) (ha : a.hasSort s) :
      isFormula (.app k (.app f a)) := by
    change k.sort = some (t >> prop) at hk
    change f.sort = some (s >> t) at hf
    change a.sort = some s at ha
    simp [isFormula, hasSort, Expr.sort, hk, hf, ha]
  exact trans (sorted f a hf ha) (sorted g a hg ha) (sorted g b hg hb) first second

def and_left (hp : isFormula p) (hq : isFormula q) : Entails (and p q) p := by
  apply ProofTree.leftAnd (Γ := ∅) p q isFSet_empty (singleton_sorted hp) hp hq
  exact .weakening (singleton_sorted hp) (singleton_sorted hp)
    (isFSet_insert hp (singleton_sorted hq)) (singleton_sorted hp)
    (.hypothesis _ hp) (by simp) (by simp)

def iff_intro (hp : isFormula p) (hq : isFormula q)
    (d : Entails p q) (e : Entails q p) : Theorem (iff p q) := by
  have forward : Theorem (imp p q) :=
    .rightImp (Γ := ∅) (Δ := ∅) p q isFSet_empty isFSet_empty hp hq d
  have backward : Theorem (imp q p) :=
    .rightImp (Γ := ∅) (Δ := ∅) q p isFSet_empty isFSet_empty hq hp e
  simpa using ProofTree.rightIff (Γ := ∅) (Ω := ∅) (Δ := ∅) (Ξ := ∅) p q
    isFSet_empty isFSet_empty isFSet_empty isFSet_empty hp hq forward backward

theorem applied_congr (h : AlphaBetaEta p q) (args : List Expr) :
    AlphaBetaEta (p.applied args) (q.applied args) := by
  induction args generalizing p q with
  | nil => exact h
  | cons a args ih => exact ih (.app h (.refl a))

/-- Closing a common eigenvariable by lambda abstraction preserves the pointwise
comparison. This works for individual, proposition, and function binders alike. -/
def lam_pointwise (x : SVar) (p q : Expr) (s : LSort) (xs : List SVar)
    (hp : p.hasSort s)
    (hparams : (SubstPair.mk p q).validParams xs)
    (d : Theorem ((SubstPair.mk p q).pointwiseEq xs)) :
    Theorem ((SubstPair.mk (.lam x p) (.lam x q)).pointwiseEq (x :: xs)) := by
  have hq : q.hasSort s := hparams.1.2.symm.trans hp
  have bp := applied_congr
    ((AlphaBetaEta.beta x p (.var x) rfl).trans (substOne_self hp x)) (xs.map Expr.var)
  have bq := applied_congr
    ((AlphaBetaEta.beta x q (.var x) rfl).trans (substOne_self hq x)) (xs.map Expr.var)
  have conversion : AlphaBetaEta
      ((SubstPair.mk (.lam x p) (.lam x q)).pointwiseEq (x :: xs))
      ((SubstPair.mk p q).pointwiseEq xs) := by
    change p.sort = some s at hp
    simp only [SubstPair.pointwiseEq, SubstPair.sort, Expr.sort, hp,
      Option.map_some, LSort.splitArgs, List.map_cons, Expr.applied, List.foldl_cons]
    split <;> exact .app (.app (.refl _) bp) bq
  exact convertTheorem (SubstPair.pointwiseEq_isFormula hparams) conversion.symm d

def modusPonens (hp : isFormula p) (hq : isFormula q)
    (d : Theorem p) (e : Entails p q) : Theorem q := by
  simpa using ProofTree.cut (Γ := ∅) (Δ := ∅) (Ω := ∅) (Ξ := {q}) p
    isFSet_empty isFSet_empty isFSet_empty (singleton_sorted hq) hp d e

def replace_reverse (r : SubstRule) (hr : r.valid) (d : Theorem r.equation) :
    Entails r.target r.source := by
  simpa using ProofTree.leftSubst (Γ := ∅) (Δ := {r.source}) (Θ := ∅) (Ξ := ∅)
    r isFSet_empty (singleton_sorted hr.2.2.2.1) isFSet_empty isFSet_empty hr
    (by simp [SubstRule.fresh, freeVars, HasFree.freeVars])
    (.hypothesis r.source hr.2.2.2.1) d

def le_top (hp : isFormula p) : Entails p top :=
  .weakening isFSet_empty (singleton_sorted (show isFormula top from rfl))
    (singleton_sorted hp) (singleton_sorted (show isFormula top from rfl))
    .rightTrue (by simp) (by simp)

def bot_le (hp : isFormula p) : Entails bot p :=
  .weakening (singleton_sorted (show isFormula bot from rfl)) isFSet_empty
    (singleton_sorted (show isFormula bot from rfl)) (singleton_sorted hp)
    .leftFalse (by simp) (by simp)

def and_right (hp : isFormula p) (hq : isFormula q) : Entails (and p q) q := by
  apply ProofTree.leftAnd (Γ := ∅) p q isFSet_empty (singleton_sorted hq) hp hq
  exact .weakening (singleton_sorted hq) (singleton_sorted hq)
    (isFSet_insert hp (singleton_sorted hq)) (singleton_sorted hq)
    (.hypothesis _ hq) (by simp) (by simp)

def le_and (hp : isFormula p) (hq : isFormula q) (hr : isFormula r)
    (d : Entails p q) (e : Entails p r) : Entails p (and q r) := by
  simpa using ProofTree.rightAnd (Γ := {p}) (Ω := {p}) (Δ := ∅) (Ξ := ∅) q r
    (singleton_sorted hp) isFSet_empty (singleton_sorted hp) isFSet_empty hq hr d e

def or_left (hp : isFormula p) (hq : isFormula q) : Entails p (or p q) := by
  apply ProofTree.rightOr (Δ := ∅) p q (singleton_sorted hp) isFSet_empty hp hq
  exact .weakening (singleton_sorted hp) (singleton_sorted hp)
    (singleton_sorted hp) (isFSet_insert hp (singleton_sorted hq))
    (.hypothesis p hp) (by simp) (by simp)

def or_right (hp : isFormula p) (hq : isFormula q) : Entails q (or p q) := by
  apply ProofTree.rightOr (Δ := ∅) p q (singleton_sorted hq) isFSet_empty hp hq
  exact .weakening (singleton_sorted hq) (singleton_sorted hq)
    (singleton_sorted hq) (isFSet_insert hp (singleton_sorted hq))
    (.hypothesis q hq) (by simp) (by simp)

def or_le (hp : isFormula p) (hq : isFormula q) (hr : isFormula r)
    (d : Entails p r) (e : Entails q r) : Entails (or p q) r := by
  simpa using ProofTree.leftOr (Γ := ∅) (Ω := ∅) (Δ := {r}) (Ξ := {r}) p q
    isFSet_empty (singleton_sorted hr) isFSet_empty (singleton_sorted hr) hp hq d e

def doubleNegIntro (hp : isFormula p) : Entails p (neg (neg p)) := by
  have d : AlphaBetaEtaProof (insert (neg p) {p}) ∅ :=
    .leftNot (Δ := ∅) p (singleton_sorted hp) isFSet_empty hp (.hypothesis p hp)
  exact .rightNot (Δ := ∅) (neg p) (singleton_sorted hp) isFSet_empty (isFormula_neg hp) d

def doubleNegElim (hp : isFormula p) : Entails (neg (neg p)) p := by
  have d : AlphaBetaEtaProof ∅ (insert (neg p) {p}) :=
    .rightNot (Γ := ∅) p isFSet_empty (singleton_sorted hp) hp (.hypothesis p hp)
  exact .leftNot (Γ := ∅) (neg p) isFSet_empty (singleton_sorted hp) (isFormula_neg hp) d

def false_of_neg_top : Entails (neg top) bot := by
  have d : AlphaBetaEtaProof {neg top} ∅ :=
    .leftNot (Γ := ∅) (Δ := ∅) top isFSet_empty isFSet_empty rfl .rightTrue
  exact .weakening (singleton_sorted (isFormula_neg (show isFormula top from rfl))) isFSet_empty
    (singleton_sorted (isFormula_neg (show isFormula top from rfl)))
    (singleton_sorted (show isFormula bot from rfl)) d (by simp) (by simp)

def contradiction (hp : isFormula p) (d : Entails p (neg p)) : Entails p bot := by
  have both : AlphaBetaEtaProof (insert (neg p) {p}) ∅ :=
    .leftNot (Δ := ∅) p (singleton_sorted hp) isFSet_empty hp (.hypothesis p hp)
  have empty : AlphaBetaEtaProof {p} ∅ := by
    simpa using ProofTree.cut (Γ := {p}) (Δ := ∅) (Ω := {p}) (Ξ := ∅) (neg p)
      (singleton_sorted hp) isFSet_empty (singleton_sorted hp) isFSet_empty (isFormula_neg hp) d both
  exact .weakening (singleton_sorted hp) isFSet_empty (singleton_sorted hp) (singleton_sorted rfl)
    empty (by simp) (by simp)

def eq_symm (hp : isTerm p) (hq : isTerm q) : Entails (eq p q) (eq q p) := by
  let z := Lambda.Context.empty.fresh p.freeVars ind
  have hz := Lambda.Context.empty.fresh_not_mem p.freeVars ind
  let r := replacement z (eq (.var z) p) p q []
  have hv : (SubstPair.mk p q).validParams [] := by
    simp [SubstPair.validParams, SubstPair.wellSorted, SubstPair.sort, Expr.wellSorted,
      show p.sort = some ind from hp, show q.sort = some ind from hq, LSort.splitArgs]
  have hr : r.valid := replacement_valid (isFormula_eq rfl hp) hp hv
  have cv (a : Expr) : AlphaBetaEta (substOne z a (eq (.var z) p)) (eq a p) := by
    simpa [eq, substOne, Expr.subst, Subst.subst, Lambda.NamedSubst.lookup_insert] using
      AlphaBetaEta.app (.app (.refl _) (.refl a)) (substOne_fresh hp z a hz)
  have hd : Theorem r.source := convertTheorem (isFormula_eq hp hp) (cv p).symm (.rightRefl p hp)
  have he : Entails (eq p q) r.equation := by
    simpa [r, SubstPair.pointwiseEq, SubstPair.sort, show p.sort = some ind from hp,
      LSort.splitArgs, Expr.applied] using ProofTree.hypothesis (leq := AlphaBetaEta) (eq p q) (isFormula_eq hp hq)
  have d : Entails (eq p q) r.target := by
    simpa using ProofTree.rightSubst (Γ := ∅) (Δ := ∅) (Θ := {eq p q}) (Ξ := ∅)
      r isFSet_empty isFSet_empty (singleton_sorted (isFormula_eq hp hq)) isFSet_empty hr
      (by simp [r, replacement, SubstRule.fresh]) hd he
  exact convert (isFormula_eq hp hq) hr.2.2.2.2 (.refl _) (cv q) d

theorem fold_and_sorted {ps : List Expr} (hp : isFormula p) (hs : ∀ q ∈ ps, isFormula q) :
    isFormula (ps.foldl and p) := by
  induction ps generalizing p with
  | nil => exact hp
  | cons q qs ih => exact ih (isFormula_and hp (hs q (by simp))) (fun r hr => hs r (by simp [hr]))

theorem le_fold_and {ps : List Expr} (hr : isFormula r) (hp : isFormula p) (hs : ∀ q ∈ ps, isFormula q)
    (hp' : Nonempty (Entails r p)) (hs' : ∀ q ∈ ps, Nonempty (Entails r q)) :
    Nonempty (Entails r (ps.foldl and p)) := by
  induction ps generalizing p with
  | nil => exact hp'
  | cons q qs ih =>
      obtain ⟨d⟩ := hp'
      obtain ⟨e⟩ := hs' q (by simp)
      exact ih (isFormula_and hp (hs q (by simp))) (fun r hr => hs r (by simp [hr]))
        ⟨le_and hr hp (hs q (by simp)) d e⟩ (fun r hr => hs' r (by simp [hr]))

theorem fold_and_le {ps : List Expr} (hp : isFormula p) (hs : ∀ q ∈ ps, isFormula q) :
    Nonempty (Entails (ps.foldl and p) p) ∧
      ∀ q ∈ ps, Nonempty (Entails (ps.foldl and p) q) := by
  induction ps generalizing p with
  | nil => exact ⟨⟨.hypothesis p hp⟩, by simp⟩
  | cons q qs ih =>
      have hq := hs q (by simp)
      have hs' := fun r hr => hs r (List.mem_cons_of_mem q hr)
      obtain ⟨⟨d⟩, e⟩ := ih (isFormula_and hp hq) hs'
      have hall := fold_and_sorted (isFormula_and hp hq) hs'
      refine ⟨⟨trans hall (isFormula_and hp hq) hp d (and_left hp hq)⟩, ?_⟩
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact ⟨trans hall (isFormula_and hp hq) hq d (and_right hp hq)⟩
      · exact e r hr

def fromTheorem (hp : isFormula p) (hq : isFormula q) (d : Theorem q) : Entails p q :=
  .weakening isFSet_empty (singleton_sorted hq) (singleton_sorted hp) (singleton_sorted hq)
    d (by simp) (by simp)

def forall_elim (x : SVar) (hx : x.sort = ind) (hp : isFormula p) : Entails (forall_ x p) p := by
  have hs := substOne_self hp x
  exact .leftForall (Γ := ∅) x p (.var x) isFSet_empty (singleton_sorted hp)
    hx hp (by simpa [isTerm, hasSort] using hx)
    (convert hp hp hs.symm (.refl _) (.hypothesis p hp))

def forall_theorem (x : SVar) (hx : x.sort = ind) (hp : isFormula p) (d : Theorem p) :
    Theorem (forall_ x p) :=
  .rightForall (Γ := ∅) (Δ := ∅) x p isFSet_empty isFSet_empty hx hp d
    (by simp [freeVars, HasFree.freeVars, Expr.forall_, Expr.freeVars])

end Derivation
end
end Lisa.Orthologic
