import Lisa.LambdaFol.ToPureFol.PureFolTranslation
import Lisa.LambdaFol.ToPureFol.PureFolToOrdered.Embedding
import Lisa.AlphaBetaEtaNormalization.Internal.Elaboration

/-! Translation to PureFol followed by embedding preserves canonical syntax exactly.
Working with erased sorted terms avoids casts when collecting application spines;
injectivity of erasure recovers equality of the typed terms. -/
namespace Lisa.LambdaFol.PureFolTranslation
open AlphaBetaEtaNormalization.Algorithm
open FirstOrderShape (IsTermOrFunction IsFormulaOrPredicate)
open PureFolEmbedding (VariableAssignment)
open Embedding (apps head)
open Signature (arity)

private def rawHead (c : Symbol) (s : LSort) : RawTerm :=
  if c.schematic then .free ⟨c.id, s⟩ else .const ⟨c.id, s⟩

private def embedded (v : VariableAssignment Identifier n) (t : BoundedTerm n) : RawTerm :=
  (PureFolEmbedding.term v t).erase

private theorem apps_erase (n : Nat) (f : Term (arity n s)) (ts : Fin n → Term ind) :
    (apps n f ts).erase = (List.ofFn (fun i => (ts i).erase)).foldl RawTerm.app f.erase := by
  induction n with
  | zero => simp [apps]; rfl
  | succ n ih => simp [apps, ih, List.ofFn_succ, Term.erase]; rfl

private theorem head_erase (c : Symbol) (s : LSort) :
    (head c s).erase = rawHead c s := by simp only [head, rawHead]; split <;> rfl

private theorem embedded_func (v : VariableAssignment Identifier n) (c : Symbol) (ts : List (BoundedTerm n)) :
    embedded v (.func c ts.get) =
      (ts.map (embedded v)).foldl RawTerm.app (.const ⟨c.id, arity ts.length ind⟩) := by
  simp only [embedded, PureFolEmbedding.term, apps_erase, Term.erase]
  rw [show List.ofFn (fun i => (PureFolEmbedding.term v (ts.get i)).erase) =
      ts.map (embedded v) by
    simpa only [List.map_ofFn] using congrArg (List.map (embedded v)) (List.ofFn_get ts)]

private theorem embedded_rel (v : VariableAssignment Identifier n) (c : Symbol) (ts : List (BoundedTerm n)) :
    (PureFolEmbedding.formula v (.rel c ts.get)).erase =
      (ts.map (embedded v)).foldl RawTerm.app (rawHead c (arity ts.length prop)) := by
  simp only [PureFolEmbedding.formula, apps_erase, head_erase]
  rw [show List.ofFn (fun i => (PureFolEmbedding.term v (ts.get i)).erase) =
      ts.map (embedded v) by
    simpa only [List.map_ofFn] using congrArg (List.map (embedded v)) (List.ofFn_get ts)]

private theorem arity_succ_right (n : Nat) (s : LSort) :
    arity (n + 1) s = arity n (ind >> s) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [arity, ← ih]

private def SpineReconstructed (v : VariableAssignment Identifier n) (ρ : BoundVarMap n) (e : Term s) : Prop :=
  ∀ c ts, symbolAndArguments? ρ e = some (c, ts) →
    e.erase = (ts.map (embedded v)).foldl RawTerm.app (rawHead c (arity ts.length s))

private def IndividualReconstructed (v : VariableAssignment Identifier n) (ρ : BoundVarMap n) : {s : LSort} → Term s → Prop
  | .ind, e => ∀ t, fromNormalTerm? ρ e = some t → embedded v t = e.erase
  | _, _ => True

private def FormulaReconstructed (v : VariableAssignment Identifier n) (ρ : BoundVarMap n) : {s : LSort} → Term s → Prop
  | .prop, e => ∀ p, fromNormalFormula? ρ e = some p → (PureFolEmbedding.formula v p).erase = e.erase
  | _, _ => True

private theorem symbolAndArguments_app {f : Term (ind >> s)} {a : Term ind}
    (hf : SpineReconstructed v ρ f) (ha : IndividualReconstructed v ρ a) :
    SpineReconstructed v ρ (.app f a) := by
  intro c ts hr
  rcases hfr : symbolAndArguments? ρ f with _ | ⟨d, us⟩ <;>
    simp [symbolAndArguments?, hfr] at hr
  rcases har : fromNormalTerm? ρ a with _ | t <;>
    simp [har] at hr
  obtain ⟨rfl, rfl⟩ := hr
  simp [Term.erase, hf _ _ hfr, ← ha _ har, List.map_append,
    List.foldl_append, arity_succ_right]

private theorem fromNormalFormula_app_roundtrip (v : VariableAssignment Identifier n) (ρ : BoundVarMap n)
    (f : Term (ind >> prop)) (a : Term ind) (he : SpineReconstructed v ρ (.app f a)) :
    FormulaReconstructed v ρ (.app f a) := by
  intro p hr
  by_cases h : ∃ t : Term ind, f = .app (.const ⟨"eq", 0⟩) t
  · obtain ⟨t, rfl⟩ := h
    rcases htr : fromNormalTerm? ρ t with _ | t' <;>
      simp [fromNormalFormula?, htr] at hr
    rcases har : fromNormalTerm? ρ a with _ | a' <;>
      simp [har] at hr
    subst p
    have hs := he ⟨false, ⟨"eq", 0⟩⟩ [t', a'] (by simp [symbolAndArguments?, htr, har])
    simpa [PureFolEmbedding.formula, rawHead, embedded, arity, Term.erase] using hs.symm
  · simp only [not_exists] at h
    rcases hfr : symbolAndArguments? ρ f with _ | ⟨c, ts⟩ <;>
      simp [fromNormalFormula?, hfr] at hr
    rcases har : fromNormalTerm? ρ a with _ | a' <;>
      simp [har] at hr
    subst p
    rw [embedded_rel]
    exact (he _ _ (by simp [symbolAndArguments?, hfr, har])).symm

/-- The individual spine also records that a function head is a constant.
This rules out higher-order free symbols without a second grammar induction. -/
private def IndividualSpine (v : VariableAssignment Identifier n) (ρ : BoundVarMap n) (e : Term s) : Prop :=
  SpineReconstructed v ρ e ∧
    ∀ c ts, symbolAndArguments? ρ e = some (c, ts) → c.schematic = false ∨ s = ind

mutual

private theorem individual_roundtrip {s n : _} {e : Term s} (h : IsTermOrFunction e) :
    IndividualSpine (PureFolEmbedding.environment n) (indexToLevel n) e ∧
      IndividualReconstructed (PureFolEmbedding.environment n) (indexToLevel n) e := by
  match h with
  | .bound k =>
      refine ⟨by simp [IndividualSpine, SpineReconstructed, symbolAndArguments?], ?_⟩
      intro t ht
      simp only [fromNormalTerm?] at ht
      obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp ht
      have hk : k < n := by
        by_contra hk
        simp [indexToLevel, hk] at hi
      simp only [indexToLevel, hk, ↓reduceDIte, Option.some.injEq] at hi
      subst i
      simp only [embedded, PureFolEmbedding.term, PureFolEmbedding.environment, Term.erase]
      congr 2
      omega
  | .free x =>
      constructor
      · exact ⟨by
          intro c ts hr
          simp only [symbolAndArguments?] at hr
          obtain ⟨rfl, rfl⟩ := Option.some.inj hr
          rfl, by intros; exact Or.inr rfl⟩
      · intro t ht
        simp only [fromNormalTerm?] at ht
        cases Option.some.inj ht
        rfl
  | .symbol k c =>
      constructor
      · constructor
        · intro d ts hr
          simp only [symbolAndArguments?] at hr
          obtain ⟨rfl, rfl⟩ := Option.some.inj hr
          rfl
        · intro d ts hr
          simp only [symbolAndArguments?] at hr
          obtain ⟨rfl, rfl⟩ := Option.some.inj hr
          exact Or.inl rfl
      · cases k with
        | zero =>
            intro t ht
            change fromNormalTerm? (indexToLevel n) (.const (s := ind) c) = some t at ht
            simp only [fromNormalTerm?] at ht
            cases Option.some.inj ht
            rfl
        | succ k => trivial
  | @IsTermOrFunction.app s f a hfn ha =>
      have rf := individual_roundtrip (n := n) hfn
      have ra := individual_roundtrip (n := n) ha
      have kind : ∀ c ts, symbolAndArguments? (indexToLevel n) (.app f a) = some (c, ts) → c.schematic = false := by
        intro c ts hr
        rcases hfr : symbolAndArguments? (indexToLevel n) f with _ | ⟨c', us⟩ <;> simp [symbolAndArguments?, hfr] at hr
        rcases har : fromNormalTerm? (indexToLevel n) a with _ | t <;> simp [har] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact (rf.1.2 _ _ hfr).resolve_right (by simp)
      refine ⟨⟨symbolAndArguments_app rf.1.1 ra.2, fun c ts hr => .inl (kind c ts hr)⟩, ?_⟩
      cases s with
      | prop => trivial
      | arrow _ _ => trivial
      | ind =>
          intro t ht
          rcases hfr : symbolAndArguments? (indexToLevel n) f with _ | ⟨c, ts⟩ <;>
            simp [fromNormalTerm?, hfr] at ht
          rcases har : fromNormalTerm? (indexToLevel n) a with _ | a' <;>
            simp [har] at ht
          subst t
          rw [embedded_func]
          have hr : symbolAndArguments? (indexToLevel n) (.app f a) = some (c, ts ++ [a']) := by simp [symbolAndArguments?, hfr, har]
          simpa [rawHead, kind _ _ hr] using (symbolAndArguments_app rf.1.1 ra.2 _ _ hr).symm
  | @IsTermOrFunction.epsilon bp hp =>
      refine ⟨by simp [IndividualSpine, SpineReconstructed, symbolAndArguments?], ?_⟩
      intro t ht
      rcases hpr : fromNormalFormula? (PureFolTranslation.bind (indexToLevel n)) bp with _ | p <;>
        simp [fromNormalTerm?, hpr] at ht
      subst t
      have rp := (fromNormalFormula_roundtrip_aux (n := n + 1) hp).2 p (by simpa [indexToLevel_succ] using hpr)
      simpa [embedded, PureFolEmbedding.term, PureFolEmbedding.environment_lift, Term.erase] using
        congrArg (fun q => RawTerm.app (.const ⟨⟨"epsilon", 0⟩, (ind >> prop) >> ind⟩)
          (.lam ind q)) rp
termination_by structural h

private theorem fromNormalFormula_roundtrip_aux {s n : _} {e : Term s} (h : IsFormulaOrPredicate e) :
    SpineReconstructed (PureFolEmbedding.environment n) (indexToLevel n) e ∧
      FormulaReconstructed (PureFolEmbedding.environment n) (indexToLevel n) e := by
  match h with
  | .free x =>
      constructor
      · intro c ts hr
        simp only [symbolAndArguments?] at hr
        obtain ⟨rfl, rfl⟩ := Option.some.inj hr
        simp [Term.erase, rawHead, arity]
      · intro p hr
        simp only [fromNormalFormula?] at hr
        cases Option.some.inj hr
        rfl
  | .symbol k c =>
      constructor
      · intro d ts hr
        simp only [symbolAndArguments?] at hr
        obtain ⟨rfl, rfl⟩ := Option.some.inj hr
        simp [Term.erase, rawHead, arity]
      · cases k with
        | succ k => trivial
        | zero =>
            intro p hr
            change fromNormalFormula? (indexToLevel n) (.const (s := prop) c) = some p at hr
            by_cases ht : c = ⟨"top", 0⟩
            · subst c; simp only [fromNormalFormula?, Option.some.injEq] at hr; subst p; rfl
            by_cases hb : c = ⟨"bot", 0⟩
            · subst c; simp only [fromNormalFormula?, Option.some.injEq] at hr; subst p; rfl
            have hr : (.rel ⟨false, c⟩ Fin.elim0 : BoundedFormula n) = p := by simpa [fromNormalFormula?] using hr
            subst p
            rfl
  | @IsFormulaOrPredicate.app s f a hfn ha =>
      have rf := fromNormalFormula_roundtrip_aux (n := n) hfn
      have ra := individual_roundtrip (n := n) ha
      have hs := symbolAndArguments_app rf.1 ra.2
      refine ⟨hs, ?_⟩
      cases s with
      | ind => trivial
      | arrow _ _ => trivial
      | prop => exact fromNormalFormula_app_roundtrip (PureFolEmbedding.environment n) (indexToLevel n) f a hs
  | @IsFormulaOrPredicate.neg bp hp =>
      refine ⟨by simp [SpineReconstructed, symbolAndArguments?], ?_⟩
      intro p hr
      rcases hpr : fromNormalFormula? (indexToLevel n) bp with _ | p' <;>
        simp [fromNormalFormula?, hpr] at hr
      subst p
      have rp := (fromNormalFormula_roundtrip_aux (n := n) hp).2 p' hpr
      simpa [PureFolEmbedding.formula, Term.erase] using
        congrArg (RawTerm.app (.const ⟨⟨"not", 0⟩, prop >> prop⟩)) rp
  | @IsFormulaOrPredicate.and bp bq hp hq | @IsFormulaOrPredicate.or bp bq hp hq | @IsFormulaOrPredicate.imp bp bq hp hq | @IsFormulaOrPredicate.iff bp bq hp hq =>
      refine ⟨by simp [SpineReconstructed, symbolAndArguments?], ?_⟩
      intro p hr
      rcases hpr : fromNormalFormula? (indexToLevel n) bp with _ | p' <;>
        simp [fromNormalFormula?, hpr] at hr
      rcases hqr : fromNormalFormula? (indexToLevel n) bq with _ | q' <;>
        simp [hqr] at hr
      subst p
      have rp := (fromNormalFormula_roundtrip_aux (n := n) hp).2 p' hpr
      have rq := (fromNormalFormula_roundtrip_aux (n := n) hq).2 q' hqr
      simp only [PureFolEmbedding.formula, Term.erase, rp, rq]
  | @IsFormulaOrPredicate.all bp hp | @IsFormulaOrPredicate.ex bp hp =>
      refine ⟨by simp [SpineReconstructed, symbolAndArguments?], ?_⟩
      intro p hr
      rcases hpr : fromNormalFormula? (PureFolTranslation.bind (indexToLevel n)) bp with _ | p' <;>
        simp [fromNormalFormula?, hpr] at hr
      subst p
      have rp := (fromNormalFormula_roundtrip_aux (n := n + 1) hp).2 p' (by simpa [indexToLevel_succ] using hpr)
      simp only [PureFolEmbedding.formula, PureFolEmbedding.environment_lift, Term.erase, rp]
termination_by structural h
end

/-- Reading a canonical formula and embedding it recovers the original term.
Both operations use the same `n` surrounding individual binders. -/
theorem fromNormalFormula_roundtrip {n : Nat} {p : BoundedFormula n} {e : Term prop} (he : IsFormulaOrPredicate e)
    (hr : fromNormalFormula? (indexToLevel n) e = some p) : PureFolEmbedding.formula (PureFolEmbedding.environment n) p = e :=
  Term.erase_injective ((fromNormalFormula_roundtrip_aux he).2 _ hr)

end Lisa.LambdaFol.PureFolTranslation
