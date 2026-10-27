import Lisa.Orthologic.Syntax

/-! The mutually recursive comparisons used by OL normalization.

`polarLEQ p positive q positive'` compares formulas. False polarity means the
negation of the corresponding formula; this avoids allocating inverted trees
on recursive calls. `latticesEQ` compares formulas in both directions and
compares other sorts through their constructors. Quantifiers use implication;
arbitrary applications require equivalence of both components.

There is no fuel or quantifier-depth limit. The termination measure is twice
the sum of the two tree sizes, plus one for EQ's calls to LEQ at the same size.
The uncached identity shortcut compares erased Lambda terms. `Cached.lean`
reuses those terms and memoizes recursive comparisons with exact-agreement proofs.
-/

namespace Lisa.Orthologic
open SimpleExpr

/-- Interpret the Boolean polarity as a formula, without changing its binding. -/
def polar (p : SimpleExpr prop) (positive : Bool) : SimpleExpr prop :=
  if positive then p else .neg p

mutual

def polarLEQ (p : SimpleExpr prop) (positive : Bool)
    (q : SimpleExpr prop) (positive' : Bool) : Bool :=
  if positive == positive' && decide (p.toTerm = q.toTerm) then true
  else match p, positive, q, positive' with
    | .neg p, s, q, t => polarLEQ p (!s) q t
    | p, s, .neg q, t => polarLEQ p s q (!t)
    | .top, false, _, _ => true
    | _, _, .top, true => true
    | .equal a b, s, .equal c d, t =>
        s == t && ((latticesEQ a c && latticesEQ b d) ||
          (latticesEQ a d && latticesEQ b c))
    | .all p, s, .all q, t =>
        s == t && (if s then polarLEQ p true q true else polarLEQ q true p true)
    | p, s, .conj qs, true => qs.attach.all fun q => polarLEQ p s q.val true
    | .conj ps, false, q, t => ps.attach.all fun p => polarLEQ p.val false q t
    | .conj ps, true, .conj qs, false =>
        (ps.attach.any fun p => polarLEQ p.val true (.conj qs) false) ||
        (qs.attach.any fun q => polarLEQ (.conj ps) true q.val false)
    | p, s, .conj qs, false => qs.attach.any fun q => polarLEQ p s q.val false
    | .conj ps, true, q, t => ps.attach.any fun p => polarLEQ p.val true q t
    | @SimpleExpr.app a _ f x, s, @SimpleExpr.app b _ g y, t =>
        s == t && if h : a = b then latticesEQ (h ▸ f) g && latticesEQ (h ▸ x) y else false
    | _, _, _, _ => false
termination_by 2 * (p.size + q.size)
decreasing_by
  all_goals simp_wf
  all_goals try subst_vars
  all_goals try simp_all only [SimpleExpr.size]
  all_goals try omega
  all_goals first
    | simpa only [SimpleExpr.size] using SimpleExpr.size_lt_conj p.property
    | simpa only [SimpleExpr.size] using SimpleExpr.size_lt_conj q.property

def latticesEQ {s : LSort} (p q : SimpleExpr s) : Bool :=
  if decide (p.toTerm = q.toTerm) then true
  else match s, p, q with
    | .prop, p, q => polarLEQ p true q true && polarLEQ q true p true
    | _, @SimpleExpr.app a _ f x, @SimpleExpr.app b _ g y =>
        if h : a = b then latticesEQ (h ▸ f) g && latticesEQ (h ▸ x) y else false
    | _, .lam _ p, .lam _ q => latticesEQ p q
    | _, _, _ => false
termination_by 2 * (p.size + q.size) + 1
decreasing_by
  all_goals simp_wf
  all_goals try subst_vars
  all_goals try simp_all only [SimpleExpr.size]
  all_goals omega

end

def latticesLEQ (p q : SimpleExpr prop) : Bool := polarLEQ p true q true

end Lisa.Orthologic
