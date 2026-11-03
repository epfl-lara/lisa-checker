import Lisa.Imported
import Lisa.OrderSimulation

open Lisa Expr

namespace Imported

variable {leq : ExprRel}

section Translation


/-- Recover the sorting evidence carried by the conclusion of a derivation. -/
theorem wellSorted {Γ Δ ss} (tree : ProofTree leq Γ Δ ss) : isFSet Γ ∧ isFSet Δ := by
  induction tree <;> simp_all [isFSet, Expr.bot]

/-- Every recorded assumption is a well-sorted sequent. -/
theorem assumptionsWellSorted {Γ Δ ss} (tree : ProofTree leq Γ Δ ss) :
    ∀ s ∈ ss, isFSet s.1 ∧ isFSet s.2 := by
  classical
  induction tree with
  | assume hΓ hΔ =>
      simpa only [Finset.mem_singleton, forall_eq] using And.intro hΓ hΔ
  | discharge p q ihp ihq =>
      intro s hs
      rcases Finset.mem_union.mp hs with hs | hs
      · exact ihp s (Finset.mem_filter.mp hs).1
      · exact ihq s hs
  | leftOr _ _ _ _ _ _ _ ih | rightAnd _ _ _ _ _ _ _ ih =>
      intro s hs
      obtain ⟨prem, hp, hs⟩ := (mem_premiseAssumptions s _).mp hs
      exact ih prem hp s hs
  | _ =>
      first
      | assumption
      | simp only [Finset.forall_mem_union]; constructor <;> assumption
      | simp

/-- Transport a Type-valued premise family through a mapped list. -/
private noncomputable def mapFamily {α β : Type} (f : α → β) {xs : List α} {P : β → Type}
    (proofs : ∀ x ∈ xs, P (f x)) : ∀ y ∈ xs.map f, P y := by
  intro y hy
  let found := List.mem_map.mp hy
  let x := Classical.choose found
  have hx := (Classical.choose_spec found).1
  have heq := (Classical.choose_spec found).2
  exact heq ▸ proofs x hx

/-- Resolve source assumptions using target proofs and positive order simulation. -/
noncomputable def resolveWith {target : ExprRel}
    (sim : Subrelation leq target) {Γ Δ ss} (tree : ProofTree leq Γ Δ ss)
    (imports : ∀ s ∈ ss, Weakened.ProofTree target s.1 s.2) :
    Weakened.ProofTree target Γ Δ := by
  induction tree with
  | assume hΓ hΔ => exact imports _ (Finset.mem_singleton_self _)
  | leftFalse => exact .leftFalse
  | @discharge Γ Δ α β ss₁ ss₂ p q ihp ihq =>
    apply ihp
    intro s hs
    classical
    by_cases heq : sameSequent leq s (α, β)
    · have hq := ihq (fun t ht => imports t (Finset.mem_union_right _ ht))
      obtain ⟨hα, hβ⟩ := wellSorted q
      -- Sorting of a discharged assumption is supplied at its assumed leaf.
      have hsSort := assumptionsWellSorted p s hs
      exact .restate hα hβ hsSort.1 hsSort.2 hq (sim.sequent heq.2) (sim.sequent heq.1)
    · exact imports s (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hs, heq⟩))
  | weakening h2 h3 p0 h5 ih0 =>
    obtain ⟨h0, h1⟩ := wellSorted p0
    exact .weakening h0 h1 h2 h3 (ih0 imports) (sim.sequent h5)
  | restateTrue h0 h1 h2 =>
    exact .restateTrue h0 h1 (sim.same h2)
  | hypothesis α h0 h1 h2 h3 h4 =>
    exact .hypothesis α h0 h1 h2 (sim.member h3) (sim.member h4)
  | cut α p0 p1 h6 h7 h8 h9 h10 h11 h12 ih0 ih1 =>
    obtain ⟨h0, h1⟩ := wellSorted p0
    obtain ⟨h3, h4⟩ := wellSorted p1
    exact .cut α h0 h1
      (ih0 (fun s hs => imports s (Finset.mem_union_left _ hs))) h3 h4
      (ih1 (fun s hs => imports s (Finset.mem_union_right _ hs))) h6 h7
      h8 (sim.members h9) (sim.members h10) (sim.except h11) (sim.except h12)
  | leftAnd α β p0 h3 h4 h5 h6 h7 h8 h9 ih0 =>
    obtain ⟨h0, h1⟩ := wellSorted p0
    exact .leftAnd α β h0 h1 (ih0 imports) h3 h4 h5 h6
      (sim.members h7) (sim.exceptEither h8) (sim.member h9)

  | @leftOr prems Ω₁ Ω₂ hne hΩ₁ hΩ₂ hsort trees hcontext hprincipal ih =>
    let forget (p : Premise) : AnnotatedSequent Expr := ⟨p.pre, p.post, p.val.1⟩
    apply Weakened.ProofTree.leftOr (prems := prems.map forget)
    · simpa using hne
    · exact hΩ₁
    · exact hΩ₂
    · intro prem hp
      obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hp
      exact ⟨(wellSorted (trees p hp')).1, (wellSorted (trees p hp')).2, hsort p hp'⟩
    · refine mapFamily forget (P := fun p => Weakened.ProofTree target p.pre p.post) ?_
      intro p hp
      exact ih p hp (fun s hs =>
        imports s ((mem_premiseAssumptions s prems).mpr ⟨p, hp, hs⟩))
    · intro prem hp
      obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hp
      exact ⟨sim.members (hcontext p hp').1, sim.except (hcontext p hp').2⟩
    · simpa [forget, List.map_map] using sim.member hprincipal
  | leftImp α β p0 p1 h6 h7 h8 h9 h10 h11 h12 h13 h14 ih0 ih1 =>
    obtain ⟨h0, h1⟩ := wellSorted p0
    obtain ⟨h3, h4⟩ := wellSorted p1
    exact .leftImp α β h0 h1
      (ih0 (fun s hs => imports s (Finset.mem_union_left _ hs))) h3 h4
      (ih1 (fun s hs => imports s (Finset.mem_union_right _ hs))) h6 h7
      h8 h9 (sim.members h10) (sim.members h11) (sim.except h12) (sim.except h13) (sim.member h14)
  | leftIff α β p0 h3 h4 h5 h6 h7 h8 h9 ih0 =>
    obtain ⟨h0, h1⟩ := wellSorted p0
    exact .leftIff α β h0 h1 (ih0 imports) h3 h4 h5 h6
      (sim.members h7) (sim.exceptEither h8) (sim.member h9)
  | leftNot α p0 h3 h4 h5 h6 h7 h8 ih0 =>
    obtain ⟨h0, h1⟩ := wellSorted p0
    exact .leftNot α h0 h1 (ih0 imports) h3 h4 h5 (sim.members h6) (sim.except h7) (sim.member h8)
  | leftForall x α t p0 h3 h4 h5 h6 h7 h8 h9 h10 ih0 =>
    obtain ⟨h0, h1⟩ := wellSorted p0
    exact .leftForall x α t h0 h1 (ih0 imports) h3 h4 h5 h6 h7
      (sim.members h8) (sim.except h9) (sim.member h10)
  | leftExists x α p0 h3 h4 h5 h6 h7 h8 h9 h10 ih0 =>
    obtain ⟨h0, h1⟩ := wellSorted p0
    exact .leftExists x α h0 h1 (ih0 imports) h3 h4 h5 h6
      (sim.members h7) (sim.except h8) (sim.member h9) h10

  | @rightAnd prems Ω₁ Ω₂ hne hΩ₁ hΩ₂ hsort trees hcontext hprincipal ih =>
    let forget (p : Premise) : AnnotatedSequent Expr := ⟨p.pre, p.post, p.val.1⟩
    apply Weakened.ProofTree.rightAnd (prems := prems.map forget)
    · simpa using hne
    · exact hΩ₁
    · exact hΩ₂
    · intro prem hp
      obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hp
      exact ⟨(wellSorted (trees p hp')).1, (wellSorted (trees p hp')).2, hsort p hp'⟩
    · refine mapFamily forget (P := fun p => Weakened.ProofTree target p.pre p.post) ?_
      intro p hp
      exact ih p hp (fun s hs =>
        imports s ((mem_premiseAssumptions s prems).mpr ⟨p, hp, hs⟩))
    · intro prem hp
      obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hp
      exact ⟨sim.members (hcontext p hp').1, sim.except (hcontext p hp').2⟩
    · simpa [forget, List.map_map] using sim.member hprincipal
  | rightOr α β p0 h3 h4 h5 h6 h7 h8 h9 ih0 =>
    obtain ⟨h0, h1⟩ := wellSorted p0
    exact .rightOr α β h0 h1 (ih0 imports) h3 h4 h5 h6
      (sim.members h7) (sim.exceptEither h8) (sim.member h9)
  | rightImp α β p0 h3 h4 h5 h6 h7 h8 h9 ih0 =>
    obtain ⟨h0, h1⟩ := wellSorted p0
    exact .rightImp α β h0 h1 (ih0 imports) h3 h4 h5 h6 (sim.except h7) (sim.except h8) (sim.member h9)
  | rightIff α β p0 p1 h6 h7 h8 h9 h10 h11 h12 h13 h14 ih0 ih1 =>
    obtain ⟨h0, h1⟩ := wellSorted p0
    obtain ⟨h3, h4⟩ := wellSorted p1
    exact .rightIff α β h0 h1
      (ih0 (fun s hs => imports s (Finset.mem_union_left _ hs))) h3 h4
      (ih1 (fun s hs => imports s (Finset.mem_union_right _ hs))) h6 h7
      h8 h9 (sim.members h10) (sim.members h11) (sim.except h12) (sim.except h13) (sim.member h14)
  | rightNot α p0 h3 h4 h5 h6 h7 h8 ih0 =>
    obtain ⟨h0, h1⟩ := wellSorted p0
    exact .rightNot α h0 h1 (ih0 imports) h3 h4 h5 (sim.members h6) (sim.except h7) (sim.member h8)
  | rightForall x α p0 h3 h4 h5 h6 h7 h8 h9 h10 ih0 =>
    obtain ⟨h0, h1⟩ := wellSorted p0
    exact .rightForall x α h0 h1 (ih0 imports) h3 h4 h5 h6
      (sim.members h7) (sim.except h8) (sim.member h9) h10
  | rightExists x α t p0 h3 h4 h5 h6 h7 h8 h9 h10 ih0 =>
    obtain ⟨h0, h1⟩ := wellSorted p0
    exact .rightExists x α t h0 h1 (ih0 imports) h3 h4 h5 h6 h7
      (sim.members h8) (sim.except h9) (sim.member h10)
  | rightEpsilon x α t p0 h3 h4 h5 h6 h7 h8 h9 h10 ih0 =>
    obtain ⟨h0, h1⟩ := wellSorted p0
    exact .rightEpsilon x α t h0 h1 (ih0 imports) h3 h4 h5 h6 h7
      (sim.members h8) (sim.except h9) (sim.member h10)
  | leftRefl s t p0 h3 h4 h5 h6 h7 h8 h9 ih0 =>
    obtain ⟨h0, h1⟩ := wellSorted p0
    exact .leftRefl s t h0 h1 (ih0 imports) h3 h4 h5 h6 (sim.same h7) (sim.members h8) (sim.except h9)
  | rightRefl s t h0 h1 h2 h3 h4 h5 =>
    exact .rightRefl s t h0 h1 h2 h3 (sim.same h4) (sim.member h5)
  | leftSubst r p q hΩ₁ hΩ₂ hv hf hl hr ha hΘ hΞ ihp ihq =>
    obtain ⟨hΓ₁, hΓ₂⟩ := wellSorted p
    obtain ⟨hΘsort, hΞsort⟩ := wellSorted q
    exact .leftSubst r hΓ₁ hΓ₂
      (ihp (fun s hs => imports s (Finset.mem_union_left _ hs)))
      hΘsort (fun e he => hΞsort e (Finset.mem_insert_of_mem he))
      (ihq (fun s hs => imports s (Finset.mem_union_right _ hs)))
      hΩ₁ hΩ₂ hv hf (sim.except hl) (sim.members hr) (sim.member ha)
      (sim.members hΘ) (sim.members hΞ)
  | rightSubst r p q hΩ₁ hΩ₂ hv hf hl hr ha hΘ hΞ ihp ihq =>
    obtain ⟨hΓ₁, hΓ₂⟩ := wellSorted p
    obtain ⟨hΘsort, hΞsort⟩ := wellSorted q
    exact .rightSubst r hΓ₁ hΓ₂
      (ihp (fun s hs => imports s (Finset.mem_union_left _ hs)))
      hΘsort (fun e he => hΞsort e (Finset.mem_insert_of_mem he))
      (ihq (fun s hs => imports s (Finset.mem_union_right _ hs)))
      hΩ₁ hΩ₂ hv hf (sim.members hl) (sim.except hr) (sim.member ha)
      (sim.members hΘ) (sim.members hΞ)
  | instSchema σ p0 h3 h4 h5 h6 ih0 =>
    obtain ⟨h0, h1⟩ := wellSorted p0
    exact .instSchema σ h0 h1 (ih0 imports) h3 h4 h5 ⟨sim.members h6.1, sim.members h6.2⟩


/-- Replay a derivation using proofs of all its remaining assumed sequents. -/
noncomputable def resolve {Γ Δ ss} (tree : ProofTree leq Γ Δ ss)
    (imports : ∀ s ∈ ss, Weakened.ProofTree leq s.1 s.2) :
    Weakened.ProofTree leq Γ Δ :=
  resolveWith ((fun h => h)) tree imports

/-- Embed an import-free weakened derivation. -/
noncomputable def embed {Γ Δ} (tree : Weakened.ProofTree leq Γ Δ) :
    ProofTree leq Γ Δ ∅ := by
  induction tree with
  | leftFalse => exact .leftFalse
  | restate h0 h1 h2 h3 p0 h5 h6 ih0 =>
    simpa using (ProofTree.weakening h2 h3 ih0 h5)
  | weakening h0 h1 h2 h3 p0 h5 ih0 =>
    simpa using (ProofTree.weakening h2 h3 ih0 h5)
  | restateTrue h0 h1 h2 =>
    simpa using (ProofTree.restateTrue h0 h1 h2)
  | hypothesis α h0 h1 h2 h3 h4 =>
    simpa using (ProofTree.hypothesis α h0 h1 h2 h3 h4)
  | cut α h0 h1 p0 h3 h4 p1 h6 h7 h8 h9 h10 h11 h12 ih0 ih1 =>
    simpa using (ProofTree.cut α ih0 ih1 h6 h7 h8 h9 h10 h11 h12)
  | leftAnd α β h0 h1 p0 h3 h4 h5 h6 h7 h8 h9 ih0 =>
    simpa using (ProofTree.leftAnd α β ih0 h3 h4 h5 h6 h7 h8 h9)
  | @leftOr prems Ω₁ Ω₂ hne hΩ₁ hΩ₂ hsort trees hcontext hprincipal ih =>
    let add (p : AnnotatedSequent Expr) : Premise := ⟨p.pre, p.post, p.val, ∅⟩
    have hempty : ∀ ps : List (AnnotatedSequent Expr), premiseAssumptions (ps.map add) = ∅ := by
      intro ps
      induction ps with
      | nil => rfl
      | cons p ps ihEmpty => simpa [premiseAssumptions, add] using ihEmpty
    rw [← hempty prems]
    apply ProofTree.leftOr (prems := prems.map add)
    · simpa using hne
    · exact hΩ₁
    · exact hΩ₂
    · intro prem hp
      obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hp
      exact (hsort p hp').2.2
    · refine mapFamily add (P := fun p => ProofTree leq p.pre p.post p.val.2) ?_
      exact ih
    · intro prem hp
      obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hp
      exact hcontext p hp'
    · simpa [add, List.map_map] using hprincipal
  | leftImp α β h0 h1 p0 h3 h4 p1 h6 h7 h8 h9 h10 h11 h12 h13 h14 ih0 ih1 =>
    simpa using (ProofTree.leftImp α β ih0 ih1 h6 h7 h8 h9 h10 h11 h12 h13 h14)
  | leftIff α β h0 h1 p0 h3 h4 h5 h6 h7 h8 h9 ih0 =>
    simpa using (ProofTree.leftIff α β ih0 h3 h4 h5 h6 h7 h8 h9)
  | leftNot α h0 h1 p0 h3 h4 h5 h6 h7 h8 ih0 =>
    simpa using (ProofTree.leftNot α ih0 h3 h4 h5 h6 h7 h8)
  | leftForall x α t h0 h1 p0 h3 h4 h5 h6 h7 h8 h9 h10 ih0 =>
    simpa using (ProofTree.leftForall x α t ih0 h3 h4 h5 h6 h7 h8 h9 h10)
  | leftExists x α h0 h1 p0 h3 h4 h5 h6 h7 h8 h9 h10 ih0 =>
    simpa using (ProofTree.leftExists x α ih0 h3 h4 h5 h6 h7 h8 h9 h10)
  | @rightAnd prems Ω₁ Ω₂ hne hΩ₁ hΩ₂ hsort trees hcontext hprincipal ih =>
    let add (p : AnnotatedSequent Expr) : Premise := ⟨p.pre, p.post, p.val, ∅⟩
    have hempty : ∀ ps : List (AnnotatedSequent Expr), premiseAssumptions (ps.map add) = ∅ := by
      intro ps
      induction ps with
      | nil => rfl
      | cons p ps ihEmpty => simpa [premiseAssumptions, add] using ihEmpty
    rw [← hempty prems]
    apply ProofTree.rightAnd (prems := prems.map add)
    · simpa using hne
    · exact hΩ₁
    · exact hΩ₂
    · intro prem hp
      obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hp
      exact (hsort p hp').2.2
    · refine mapFamily add (P := fun p => ProofTree leq p.pre p.post p.val.2) ?_
      exact ih
    · intro prem hp
      obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hp
      exact hcontext p hp'
    · simpa [add, List.map_map] using hprincipal
  | rightOr α β h0 h1 p0 h3 h4 h5 h6 h7 h8 h9 ih0 =>
    simpa using (ProofTree.rightOr α β ih0 h3 h4 h5 h6 h7 h8 h9)
  | rightImp α β h0 h1 p0 h3 h4 h5 h6 h7 h8 h9 ih0 =>
    simpa using (ProofTree.rightImp α β ih0 h3 h4 h5 h6 h7 h8 h9)
  | rightIff α β h0 h1 p0 h3 h4 p1 h6 h7 h8 h9 h10 h11 h12 h13 h14 ih0 ih1 =>
    simpa using (ProofTree.rightIff α β ih0 ih1 h6 h7 h8 h9 h10 h11 h12 h13 h14)
  | rightNot α h0 h1 p0 h3 h4 h5 h6 h7 h8 ih0 =>
    simpa using (ProofTree.rightNot α ih0 h3 h4 h5 h6 h7 h8)
  | rightForall x α h0 h1 p0 h3 h4 h5 h6 h7 h8 h9 h10 ih0 =>
    simpa using (ProofTree.rightForall x α ih0 h3 h4 h5 h6 h7 h8 h9 h10)
  | rightExists x α t h0 h1 p0 h3 h4 h5 h6 h7 h8 h9 h10 ih0 =>
    simpa using (ProofTree.rightExists x α t ih0 h3 h4 h5 h6 h7 h8 h9 h10)
  | rightEpsilon x α t h0 h1 p0 h3 h4 h5 h6 h7 h8 h9 h10 ih0 =>
    simpa using (ProofTree.rightEpsilon x α t ih0 h3 h4 h5 h6 h7 h8 h9 h10)
  | leftRefl s t h0 h1 p0 h3 h4 h5 h6 h7 h8 h9 ih0 =>
    simpa using (ProofTree.leftRefl s t ih0 h3 h4 h5 h6 h7 h8 h9)
  | rightRefl s t h0 h1 h2 h3 h4 h5 =>
    simpa using (ProofTree.rightRefl s t h0 h1 h2 h3 h4 h5)
  | leftSubst r _ _ _ _ _ _ hΩ₁ hΩ₂ hv hf hl hr ha hΘ hΞ ihp ihq =>
    simpa using ProofTree.leftSubst r ihp ihq hΩ₁ hΩ₂ hv hf hl hr ha hΘ hΞ
  | rightSubst r _ _ _ _ _ _ hΩ₁ hΩ₂ hv hf hl hr ha hΘ hΞ ihp ihq =>
    simpa using ProofTree.rightSubst r ihp ihq hΩ₁ hΩ₂ hv hf hl hr ha hΘ hΞ
  | instSchema σ h0 h1 p0 h3 h4 h5 h6 ih0 =>
    simpa using (ProofTree.instSchema σ ih0 h3 h4 h5 h6)

/-- Resolve all holes; no imported derivation gives new closed consequences. -/
theorem empty_iff {Γ Δ} :
    Nonempty (Weakened.ProofTree leq Γ Δ) ↔ Nonempty (ProofTree leq Γ Δ ∅) := by
  constructor
  · rintro ⟨p⟩
    exact ⟨embed p⟩
  · rintro ⟨p⟩
    exact ⟨resolve p (fun s hs => False.elim (Finset.notMem_empty s hs))⟩

/-- Introduce any finite set of well-sorted assumptions without using their content. -/
private theorem assumeAll [Std.Refl leq] (ss : Finset Sequent)
    (sorted : ∀ s ∈ ss, isFSet s.1 ∧ isFSet s.2) :
    Nonempty (ProofTree leq ∅ {top} ss) := by
  classical
  induction ss using Finset.induction_on with
  | empty =>
    refine ⟨.restateTrue (by simp) (by simp [Expr.top]) ?_⟩
    simpa [sequentToFormula, disjunction, foldFormulas] using
      (show isSame leq top top from ⟨OrderLaws.self_le _, OrderLaws.self_le _⟩)
  | @insert s ss hnot ih =>
    have hs := sorted s (Finset.mem_insert_self _ _)
    obtain ⟨p⟩ := ih (fun t ht => sorted t (Finset.mem_insert_of_mem ht))
    let q : ProofTree leq ∅ {top} {s} :=
      by
        have truth : ProofTree leq ∅ {top} ∅ :=
          .restateTrue (by simp) (by simp [Expr.top])
            (by simp [isSame, sequentToFormula, disjunction, foldFormulas, OrderLaws.self_le])
        simpa [discharged] using ProofTree.discharge truth (.assume hs.1 hs.2)
    have hp : ProofTree leq ∅ {top} (ss ∪ {s}) :=
      .cut top p q
        (by simp) (by simp [Expr.top]) (by simp [Expr.top])
        (by simp [setLeq]) (by simp [setLeq, isSame])
        (by simp [containedExcept, isSame]) (by simp [containedExcept])
    exact ⟨by simpa only [Finset.union_singleton] using hp⟩

/-- Retain additional well-sorted imports, whether or not the proof uses them. -/
noncomputable def ProofTree.weakenAssumptions [Std.Refl leq] {Γ Δ ss tt}
    (p : ProofTree leq Γ Δ ss) (hsub : ss ⊆ tt)
    (hsorted : ∀ s ∈ tt, isFSet s.1 ∧ isFSet s.2) : ProofTree leq Γ Δ tt := by
  classical
  let q := Classical.choice (assumeAll (leq := leq) tt hsorted)
  have hp := wellSorted p
  have result := ProofTree.cut top q p hp.1 hp.2 (by simp [Expr.top])
    (by simp [setLeq]) (setLeq_of_subset (Finset.Subset.refl _))
    (by simp [containedExcept, isSame, OrderLaws.self_le])
    (by intro r hr; exact Or.inl ⟨r, hr, OrderLaws.self_le _, OrderLaws.self_le _⟩)
  simpa only [Finset.union_eq_left.mpr hsub] using result

end Translation

/-- Characterize derivability with a fixed set of imports once their proofs are supplied. -/
theorem withAssumptions_iff [Std.Refl leq] {Γ Δ ss}
    (imports : ∀ s ∈ ss, Nonempty (Weakened.ProofTree leq s.1 s.2)) :
    Nonempty (ProofTree leq Γ Δ ss) ↔ Nonempty (Weakened.ProofTree leq Γ Δ) := by
  constructor
  · rintro ⟨p⟩
    exact ⟨resolve p (fun s hs => Classical.choice (imports s hs))⟩
  · rintro ⟨p⟩
    obtain ⟨q⟩ := assumeAll (leq := leq) ss (fun s hs =>
      wellSorted (embed (Classical.choice (imports s hs))))
    have result := ProofTree.discharge (embed p) q
    exact ⟨by simpa [discharged] using result⟩

end Imported
