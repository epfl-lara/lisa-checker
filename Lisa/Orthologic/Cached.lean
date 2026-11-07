import Lisa.Orthologic.CacheAlgorithm

/-! Cached entry points and exact agreement with the uncached pipeline.
Use the Memo operations with a retained Cache to share work across queries. -/
namespace Lisa.Orthologic.Cached

/-- Convenience entry points start fresh. Use the `Memo` operations and keep
the returned `Cache` to share work across multiple queries. -/
def normalize (p : Expr) (config : Config := {}) : Option Expr :=
  ((normalizeMemo p).run' {config}).val

def isSame (p q : Expr) (config : Config := {}) : Option Bool :=
  ((isSameMemo p q).run' {config}).val

def isImplying (p q : Expr) (config : Config := {}) : Option Bool :=
  ((isImplyingMemo p q).run' {config}).val

theorem normalize_eq (p : Expr) (config : Config := {}) :
    normalize p config = Orthologic.normalize p := ((normalizeMemo p).run' {config}).property

theorem isSame_eq (p q : Expr) (config : Config := {}) :
    isSame p q config = Orthologic.isSame p q := ((isSameMemo p q).run' {config}).property

theorem isImplying_eq (p q : Expr) (config : Config := {}) :
    isImplying p q config = Orthologic.isImplying p q := ((isImplyingMemo p q).run' {config}).property

-- These results quantify over every cache, not just a cache reachable from empty.
theorem prepareMemo_eq (p : Expr) (cache : Cache) :
    ((prepareMemo p).run' cache).val = Orthologic.prepare p := ((prepareMemo p).run' cache).property

theorem normalizeMemo_eq (p : Expr) (cache : Cache) :
    ((normalizeMemo p).run' cache).val = Orthologic.normalize p := ((normalizeMemo p).run' cache).property

theorem isSameMemo_eq (p q : Expr) (cache : Cache) :
    ((isSameMemo p q).run' cache).val = Orthologic.isSame p q := ((isSameMemo p q).run' cache).property

theorem isImplyingMemo_eq (p q : Expr) (cache : Cache) :
    ((isImplyingMemo p q).run' cache).val = Orthologic.isImplying p q :=
  ((isImplyingMemo p q).run' cache).property

end Lisa.Orthologic.Cached
