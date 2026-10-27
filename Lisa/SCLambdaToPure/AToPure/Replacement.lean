import Lisa.Lambda.AlphaBetaEta
import Lisa.Lambda.NamedEnvironment

/-!
# Capture-avoiding replacement in intrinsically sorted expressions

The translation to FOL needs to replace free individual names by terms and to
abstract them into bound indices. Unlike grounding, these replacements can
contain ambient indices, so their images must shift when entering a binder.
The same operation handles all three kinds of leaves; its composition laws
keep the binder and substitution proofs independent of the normalizer.
-/

namespace Lisa.SCLambdaToPure

open Lambda

@[ext] structure Replacement where
  bound : Sub
  free : (s : LSort) → Identifier → Term s
  const : (s : LSort) → Identifier → Term s

namespace Replacement

def rename (R : Replacement) (ρ : Ren) : Replacement where
  bound s n := (R.bound s n).rename ρ
  free s x := (R.free s x).rename ρ
  const s c := (R.const s c).rename ρ

def lift (R : Replacement) (b : LSort) : Replacement where
  bound := R.bound.lift b
  free s x := (R.free s x).shift b
  const s c := (R.const s c).shift b

def apply (R : Replacement) : Term s → Term s
  | .bound n => R.bound s n
  | .free x => R.free s x
  | .const c => R.const s c
  | .app f a => .app (R.apply f) (R.apply a)
  | .lam b e => .lam b ((R.lift b).apply e)

private theorem lift_rename (R : Replacement) (ρ : Ren) :
    (R.lift b).rename (ρ.lift b) = (R.rename ρ).lift b := by
  apply Replacement.ext
  · funext s n
    by_cases h : s = b
    · subst s; cases n <;> simp [rename, lift, Sub.lift, Term.rename, Ren.lift_shift]
    · simp [rename, lift, Sub.lift, h, Ren.lift_shift]
  · funext s x; simp [rename, lift, Ren.lift_shift]
  · funext s c; simp [rename, lift, Ren.lift_shift]

theorem rename_apply (R : Replacement) (e : Term s) (ρ : Ren) :
    (R.apply e).rename ρ = (R.rename ρ).apply e := by
  induction e generalizing R ρ with
  | lam b e ih => simp only [apply, Term.rename, ih, lift_rename]
  | _ => simp_all [apply, Term.rename, rename]

def precompose (R : Replacement) (ρ : Ren) : Replacement :=
  { R with bound := fun s n => R.bound s (ρ s n) }

private theorem lift_precompose (R : Replacement) (ρ : Ren) :
    (R.lift b).precompose (ρ.lift b) = (R.precompose ρ).lift b := by
  apply Replacement.ext
  · funext s n
    by_cases h : s = b
    · subst s; cases n <;> simp [precompose, lift, Sub.lift, Ren.lift]
    · simp [precompose, lift, Sub.lift, Ren.lift, h]
  · rfl
  · rfl

theorem apply_rename (R : Replacement) (e : Term s) (ρ : Ren) :
    R.apply (e.rename ρ) = (R.precompose ρ).apply e := by
  induction e generalizing R ρ with
  | lam b e ih => simp only [Term.rename, apply, ih, lift_precompose]
  | _ => simp_all [apply, Term.rename, precompose]

theorem apply_shift (R : Replacement) (e : Term s) (b : LSort) :
    (R.lift b).apply (e.shift b) = (R.apply e).shift b := by
  simp only [Term.shift, apply_rename, rename_apply]
  congr 1
  apply Replacement.ext
  rotate_left
  · rfl
  · rfl
  funext s n
  by_cases h : s = b <;> simp [precompose, rename, lift, Sub.lift, Ren.shift, h]

/-- Apply `S` first, then `R`. -/
def comp (R S : Replacement) : Replacement where
  bound s n := R.apply (S.bound s n)
  free s x := R.apply (S.free s x)
  const s c := R.apply (S.const s c)

private theorem lift_comp (R S : Replacement) (b : LSort) :
    (R.lift b).comp (S.lift b) = (R.comp S).lift b := by
  apply Replacement.ext
  · funext s n
    change (R.lift b).apply (S.bound.lift b s n) = (R.comp S).bound.lift b s n
    by_cases h : s = b
    · subst s
      cases n with
      | zero => simp [apply, lift]
      | succ n => simpa only [Sub.lift_succ, comp] using apply_shift R (S.bound b n) b
    · simpa only [Sub.lift_other h] using apply_shift R (S.bound s n) b
  · funext s x; exact apply_shift R (S.free s x) b
  · funext s c; exact apply_shift R (S.const s c) b

theorem apply_apply (R S : Replacement) (e : Term s) :
    R.apply (S.apply e) = (R.comp S).apply e := by
  induction e generalizing R S with
  | lam b e ih => simp only [apply, ih, lift_comp]
  | _ => simp_all [apply, comp]

def ofSub (σ : Sub) : Replacement where
  bound := σ
  free _ x := .free x
  const _ c := .const c

@[simp] theorem lift_ofSub (σ : Sub) : (ofSub σ).lift b = ofSub (σ.lift b) := rfl

@[simp] theorem apply_ofSub (σ : Sub) (e : Term s) : (ofSub σ).apply e = e.subst σ := by
  induction e generalizing σ with
  | lam b e ih => simp [apply, Term.subst, ih]
  | _ => simp_all [apply, Term.subst, ofSub]

theorem apply_instantiate (R : Replacement) (e : Term t) (a : Term s) :
    R.apply (e.instantiate a) = ((R.lift s).apply e).instantiate (R.apply a) := by
  simp only [Term.instantiate, ← apply_ofSub, apply_apply]
  congr 1
  apply Replacement.ext
  · funext u n
    change R.apply (Term.single a u n) = (ofSub (Term.single (R.apply a))).apply (R.bound.lift s u n)
    rw [apply_ofSub]
    change R.apply (Term.single a u n) = (R.bound.lift s u n).instantiate (R.apply a)
    by_cases h : u = s
    · subst u
      cases n with
      | zero => simp [Term.single, Term.instantiate, Term.subst]
      | succ n => simp [Term.single, Sub.id, apply]
    · simp [Term.single, Sub.extend_other h, Sub.id, apply, Sub.lift_other h]
  · funext u x
    change R.free u x = (ofSub (Term.single (R.apply a))).apply ((R.free u x).shift s)
    rw [apply_ofSub]
    exact (R.free u x).shift_instantiate (R.apply a) |>.symm
  · funext u c
    change R.const u c = (ofSub (Term.single (R.apply a))).apply ((R.const u c).shift s)
    rw [apply_ofSub]
    exact (R.const u c).shift_instantiate (R.apply a) |>.symm

theorem equiv (R : Replacement) {e f : Term s} (h : Equiv e f) :
    Equiv (R.apply e) (R.apply f) := by
  induction h generalizing R with
  | refl => exact .refl _
  | symm _ ih => exact .symm (ih R)
  | trans _ _ ih ih' => exact .trans (ih R) (ih' R)
  | app _ _ ih ih' => exact .app (ih R) (ih' R)
  | lam _ ih => exact .lam (ih (R.lift _))
  | beta b a =>
      simpa only [apply, apply_instantiate] using Equiv.beta ((R.lift _).apply b) (R.apply a)
  | @eta s t f =>
      change Equiv (.lam s (.app ((R.lift s).apply (f.shift s)) ((R.lift s).bound s 0))) _
      rw [apply_shift]
      simpa [lift] using Equiv.eta (R.apply f)

end Replacement
end Lisa.SCLambdaToPure

/-! Connecting capture-avoiding replacement with Lisa's named boundary. -/

namespace Lisa.SCLambdaToPure.Replacement

open Lambda

def packed (R : Replacement) : Packed.Expr → Packed.Expr
  | ⟨s, e⟩ => ⟨s, R.apply e⟩

def names (R : Replacement) (η : Names) : Names := fun x => R.apply (η x)

theorem names_bind (R : Replacement) (η : Names) (x : SVar) :
    (R.lift x.sort).names (η.bind x) = (R.names η).bind x := by
  funext y
  by_cases h : y = x
  · subst y; simp [names, apply, lift]
  · simp only [names, Names.bind_other _ h, apply_shift]

theorem packed_app (R : Replacement) (f a : Packed.Expr) :
    (Packed.app f a).map R.packed = Packed.app (R.packed f) (R.packed a) := by
  obtain ⟨s, f⟩ := f
  obtain ⟨u, a⟩ := a
  cases s with
  | arrow s t =>
      by_cases h : u = s
      · subst u; simp [Packed.app, packed, apply]
      · simp [Packed.app, packed, h]
  | _ => rfl

theorem interpretNamed_apply (R : Replacement) (hc : ∀ s c, R.const s c = .const c)
    (e : Expr) (η : Names) :
    (interpretNamed e η).map R.packed = interpretNamed e (R.names η) := by
  induction e generalizing R η with
  | var => rfl
  | const c => simp [interpretNamed, packed, apply, hc]
  | app f a ihf iha =>
      simp only [interpretNamed, ← ihf R hc η, ← iha R hc η]
      cases interpretNamed f η <;> cases interpretNamed a η <;> simp [packed_app]
  | lam x b ih =>
      have hc' : ∀ s c, (R.lift x.sort).const s c = .const c := by
        intro s c; simp [lift, hc, Term.rename]
      have hb := ih (R.lift x.sort) hc' (η.bind x)
      rw [names_bind] at hb
      simp only [interpretNamed, ← hb, Option.map_map]
      rfl

/-- Abstract a free name, retaining any existing ambient scope. -/
def abstract (x : SVar) : Replacement where
  bound := Sub.ofRen (Ren.shift x.sort)
  free s y := Names.free.bind x ⟨y, s⟩
  const _ c := .const c

theorem interpretNamed_bind (x : SVar) (e : Expr) :
    interpretNamed e (Names.free.bind x) = (interpretNamed e Names.free).map (abstract x).packed := by
  rw [interpretNamed_apply _ (by intros; rfl)]
  rfl

/-- Replace one free name. Images shift under binders and may contain ambient indices. -/
def single (x : SVar) (a : Term x.sort) : Replacement where
  bound := Sub.id
  free s y := if h : SVar.mk y s = x then cast (congrArg Term (congrArg SVar.sort h).symm) a else .free y
  const _ c := .const c

theorem instantiate_abstract (x : Identifier) (a : Term ind) (e : Term s) :
    ((abstract ⟨x, ind⟩).apply e).instantiate a = (single ⟨x, ind⟩ a).apply e := by
  change (((abstract ⟨x, ind⟩).apply e).subst (Term.single a)) = _
  rw [← apply_ofSub, apply_apply]
  congr 1
  apply Replacement.ext
  · funext s i
    simp only [comp, abstract, ofSub, Sub.ofRen, apply, Term.single]
    by_cases h : s = ind
    · subst s; simp [Ren.shift, single]
    · simp [Ren.shift, h, single, Sub.id]
  · funext s y
    by_cases h : SVar.mk y s = SVar.mk x ind
    · cases h
      simp [comp, abstract, ofSub, single, apply, Term.single]
    · simp only [comp, abstract, single, h, ↓reduceDIte,
        Names.bind_other _ h, Names.free, Term.rename, ofSub, apply]
  · funext s c; rfl

end Lisa.SCLambdaToPure.Replacement
