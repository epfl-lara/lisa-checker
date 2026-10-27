import Lisa.Lambda.Syntax

/-! Ground values delay printing indices. Function values are ordinary functions. -/
namespace Lisa.Lambda

abbrev Depth := LSort → Nat
namespace Depth

def zero : Depth := fun _ => 0

def inc (d : Depth) (b : LSort) : Depth := fun s => if s = b then d s + 1 else d s

@[simp] theorem inc_self : inc d s s = d s + 1 := by simp [inc]

@[simp] theorem inc_other (h : s ≠ b) : inc d b s = d s := by simp [inc, h]
end Depth

abbrev Residual (s : LSort) := Depth → Term s

def Val : LSort → Type
  | .ind => Residual .ind
  | .prop => Residual .prop
  | .arrow s t => Val s → Val t

def fresh (s : LSort) (level : Nat) : Residual s := fun d => .bound (d s - (level + 1))
/-- Mutual readback/reflection is structural recursion on the sort. -/

def readback : (s : LSort) → (Depth → Val s → Term s) × (Residual s → Val s)
  | .ind => (fun d v => v d, fun n => n)
  | .prop => (fun d v => v d, fun n => n)
  | .arrow s t =>
      let (qs, rs) := readback s
      let (qt, rt) := readback t
      (fun d f => .lam s (qt (d.inc s) (f (rs (fresh s (d s))))),
       fun n a => rt (fun d => .app (n d) (qs d a)))

abbrev quote (s : LSort) := (readback s).1

abbrev reflect (s : LSort) := (readback s).2

abbrev Env := (s : LSort) → Nat → Val s
namespace Env

def extend (η : Env) (a : Val b) : Env := fun s n =>
  if h : s = b then match n with
    | 0 => h.symm ▸ a
    | n+1 => η s n
  else η s n

@[simp] theorem extend_zero (η : Env) (a : Val b) : extend η a b 0 = a := by simp [extend]

@[simp] theorem extend_succ (η : Env) (a : Val b) : extend η a b (n+1) = η b n := by simp [extend]

@[simp] theorem extend_other (h : s ≠ b) (η : Env) (a : Val b) : extend η a s n = η s n := by simp [extend, h]
end Env

def eval : Term s → Env → Val s
  | .bound n, η => η s n
  | .free x, _ => reflect s (fun _ => .free x)
  | .const c, _ => reflect s (fun _ => .const c)
  | .app f a, η => eval f η (eval a η)
  | .lam _ b, η => fun a => eval b (η.extend a)

def ambient : Env := fun s n => reflect s (fun d => .bound (d s + n))
/-- Total eta-long normalization, also for ambient indexed variables. -/

def normalize (e : Term s) : Term s := quote s Depth.zero (eval e ambient)
end Lisa.Lambda
