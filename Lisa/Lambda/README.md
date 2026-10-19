# The Lisa Lambda package

For the proposed context-free redesign using per-sort de Bruijn indices, see [the rewrite plan](REWRITE_PLAN.md). This guide describes the current implementation.

This guide explains the package in dependency order. Its purpose is to construct a **total, verified decision procedure for alpha-beta-eta conversion on well-sorted Lisa expressions**.

The package has two parts:

1. A normalizer and correctness proof for intrinsically typed, nameless terms.
2. A verified bridge between those terms and Lisa's original named expressions.

The central result is that conversion can be decided by normalizing both expressions and comparing the results.

## Overall pipeline

```text
Lisa.Expr                         original named syntax
    | toNameless
    v
Lisa.NamelessExpr                 syntax with unchecked indices and sorts
    | elaborate
    v
Lisa.Lambda.Term Γ s              typed, scoped syntax
    | eval
    v
Val Γ s                          semantic values
    | Model.quote
    v
Lisa.Lambda.Term Γ s              canonical typed term
    | Term.reify with fresh binder names
    v
Lisa.Expr                         canonical named expression
```

The implementation of `normalizeNamed` uses `interpretNamed` to enter typed syntax directly. The theorem `normalizeNamed_eq` proves that this agrees exactly with the name-erasure-and-elaboration pipeline above.

Three equations summarize the construction:

```text
normalize e = quote (eval e reflectedVariables)

Equiv e f ↔ normalize e = normalize f

compareNamed p q = some true
  ↔ Lisa.Conversion p q ∧ p.wellSorted
```

## Prerequisites: the original syntax and conversion relation

Read [Sort](../Sort.lean), [Syntax](../Syntax.lean), and [Conversion](../Conversion.lean) first.

`Lisa.Expr` has named variables, constants, applications, and lambdas. It permits malformed applications: sorting is computed afterward by `Expr.sort : Expr → Option LSort`.

`Lisa.Conversion : Expr → Expr → Prop` specifies alpha-beta-eta conversion on this syntax. It includes alpha equivalence, beta and eta equations with appropriate side conditions, symmetry, transitivity, and congruence.

`Lisa.NamelessExpr` removes binder names while retaining free identifiers, binder positions, and sort annotations. It does not enforce correct typing or scope by construction.

Be careful about the two conversion files:

| File | Relation | Representation |
|---|---|---|
| `Lisa/Conversion.lean` | `Lisa.Conversion` | Original named expressions |
| `Lisa/Lambda/Conversion.lean` | `Lisa.Lambda.Equiv` | Intrinsically typed de Bruijn terms |

Likewise, `Lisa.Conversion.Term`, a quotient of named expressions, is different from `Lisa.Lambda.Term`, the typed syntax described next.

## 1. Syntax: typing and scope in the datatype

Source: [Syntax.lean](Syntax.lean).

```lean
Term Γ s
```

means a term of sort `s` whose surrounding bound-variable context is `Γ`.

The context lists sorts, with the nearest binder first. `Var Γ s` is a position in that context with evidence that the variable has sort `s`:

```text
.here          nearest variable
.there .here   next variable outward
```

The term constructors enforce typing:

```lean
inductive Term : List LSort → LSort → Type where
  | bound : Var Γ s → Term Γ s
  | free (id : Identifier) : Term Γ s
  | const (id : Identifier) : Term Γ s
  | app : Term Γ (s >> t) → Term Γ s → Term Γ t
  | lam : Term (s :: Γ) t → Term Γ (s >> t)
```

A malformed application cannot be constructed. Its argument must have the function's domain sort.

Bound variables refer into `Γ`. Free variables retain external identifiers and are unaffected by changes to `Γ`. Thus `Term [] s` can still contain free variables: an empty context means no surrounding binders, not necessarily a closed expression.

### Variable maps and substitutions

```lean
Ren Γ Δ := ∀ {s}, Var Γ s → Var Δ s
Sub Γ Δ := ∀ {s}, Var Γ s → Term Δ s
```

`Ren` replaces bound variables with bound variables of the same sort. `Sub` replaces them with terms of the same sort.

Here, “renaming” is the broader terminology used in some de Bruijn formalizations. A `Ren` need not be injective or bijective. It is a sort-preserving variable map, not necessarily an alpha-renaming or a reversible change of names.

For example, a map from `[prop, prop]` to `[prop]` can identify the two source variables. Applying it transforms `f x₁ x₂` into `f x x`; it changes the term as well as its context. This does not assert equivalence of the two terms.

`Term.rename` preserves syntax constructors and changes only bound-variable references. Under a lambda it uses `Ren.lift`:

```text
lift ρ .here      = .here
lift ρ (.there v) = .there (ρ v)
```

The newly introduced binder remains fixed while the surrounding variables follow `ρ`.

An especially important map is `Var.there`, which shifts existing references when adding a context slot. This prevents capture when moving a term beneath a new binder.

Substitution needs the same protection. `Sub.lift` leaves the new variable alone and shifts all older replacement terms underneath it.

`instantiate` substitutes an argument for the newest variable and removes that context slot. It is the substitution used for beta reduction.

The identity and composition lemmas establish the algebra of these operations. They support virtually all later proofs.

## 2. Conversion: specify typed beta-eta equivalence

Source: [Conversion.lean](Conversion.lean).

```lean
Equiv : Term Γ s → Term Γ s → Prop
```

The relation has reflexivity, symmetry, transitivity, application and lambda congruence, beta, and eta constructors.

Conceptually:

```text
(λx. b) a ≈ b[a/x]
λx. f x   ≈ f, when x is fresh for f
```

Alpha equivalence has no constructor because binder names are absent. Alpha-equivalent named expressions have the same de Bruijn structure.

The typed beta constructor needs no extra sorting hypothesis: the types of the body and argument already enforce the required conditions.

The eta constructor is:

```lean
Equiv (.lam (.app (f.rename Var.there) (.bound .here))) f
```

`f` is shifted beneath the new binder, and `.bound .here` supplies the fresh argument. The binder cannot capture references in `f`.

The module proves that existing equivalences survive renaming and substitution. It does not claim that arbitrary renaming leaves a term equivalent to itself.

### Example: shift followed by instantiation

```lean
(e.rename Var.there).instantiate a = e
```

Shifting adds an unused newest slot. Instantiation removes that slot. Because the shifted term never refers to it, the argument `a` is unused and the original term is recovered.

This is literal equality of typed terms, not merely conversion.

## 3. Semantics: normalization by evaluation

Source: [Semantics.lean](Semantics.lean).

This is the computational heart of the package. Instead of repeatedly finding and contracting redexes in syntax, it evaluates terms into semantic values and reads those values back into syntax.

For `(λx. x) a`, evaluation applies a semantic identity function to the value of `a`. The beta redex disappears through function application.

Open terms require more machinery: values must remain usable when evaluation or readback introduces additional binders.

### Family: values indexed by context

```lean
structure Family where
  Obj : List LSort → Type
  map : Ren Γ Δ → Obj Γ → Obj Δ
  map_id : ...
  map_comp : ...
```

A family supplies a type of values for each context, transport along variable maps, and identity/composition laws for that transport.

Despite the comment about larger contexts, the actual interface supports all `Ren Γ Δ`, not only context extensions.

At ground sorts, values are syntax:

```lean
Obj Γ := Term Γ s
map := Term.rename
```

The ground sorts `prop` and `ind` are not interpreted as truth values or a mathematical domain. Their values remain syntax. This is a semantic construction for lambda normalization, not a first-order truth interpretation.

### Family.Fn: functions that work in transported contexts

An ordinary function `A.Obj Γ → B.Obj Γ` would only accept arguments in the current context. Readback of a function introduces a fresh binder and therefore requires a different context.

Instead, a semantic function has:

```lean
run : ∀ {Δ}, Ren Γ Δ → A.Obj Δ → B.Obj Δ
```

It accepts a variable map into a target context and an argument in that context. Its `natural` proof requires compatibility with subsequent transport:

```text
apply, then transport
  =
transport function and argument, then apply
```

`Family.arrow` packages these functions as another family. Transporting a function amounts to composing its incoming variable map with the new transport.

### Model: reflection and readback

```lean
structure Model (s : LSort) where
  values : Family
  quote : values.Obj Γ → Term Γ s
  reflect : Term Γ s → values.Obj Γ
  quote_natural : ...
  reflect_natural : ...
```

`reflect` turns syntax into a semantic value. `quote` reads a semantic value back into typed syntax. Both commute with context transport.

At ground sorts they are identity functions.

At function sorts, quoting introduces a lambda and tests the semantic function on a fresh reflected variable:

```text
quote f = λx. quote (f (reflect x))
```

The implementation is:

```lean
quote f :=
  .lam (B.quote (f.run Var.there (A.reflect (.bound .here))))
```

Reflection of a syntactic function constructs a semantic function that builds applications:

```text
reflect e applied to a
  = reflect (e applied to quote a)
```

An opaque variable or constant of function sort can therefore participate in evaluation without its implementation being known. The actual `reflect` interface accepts arbitrary typed terms; it does not require a separate neutral-term datatype.

`model` builds the appropriate model by recursion on the sort: ground models for `ind` and `prop`, arrow models for function sorts.

### Val and Env

`Val Γ s` is a semantic value of sort `s` in context `Γ`.

```lean
Env Γ Δ := ∀ {s}, Var Γ s → Val Δ s
```

The related interfaces differ in what they assign to a variable:

| Interface | Result |
|---|---|
| `Ren Γ Δ` | A variable in `Δ` |
| `Sub Γ Δ` | A typed term in `Δ` |
| `Env Γ Δ` | A semantic value in `Δ` |

An environment is extended with the argument value when evaluating a lambda body.

### Evaluation

| Term constructor | Evaluation behavior |
|---|---|
| Bound variable | Look up its environment value |
| Free variable | Reflect the variable |
| Constant | Reflect the constant |
| Application | Apply the evaluated function to the evaluated argument |
| Lambda | Construct a semantic function evaluating the body in an extended environment |

`evaluation` returns the evaluator together with a proof that it commutes with transport. `eval` exposes the computational component.

### Normalization

```lean
def normalize (e : Term Γ s) : Term Γ s :=
  (model s).quote
    (eval e (fun v => (model _).reflect (.bound v)))
```

Interpret the context variables as themselves, evaluate, and quote the result.

Readback is eta-long. A variable `f : ind >> ind` reads back as a representation of `λx. f x`. Thus normalization is not an attempt to produce the shortest expression.

The construction is total. It uses structural recursion over sorts and terms rather than a fuel-controlled loop contracting redexes.

## 4. Evaluation: conversion preserves the computed result

Source: [Evaluation.lean](Evaluation.lean).

This module proves that evaluation respects renaming and substitution. In particular, evaluating after substitution agrees with evaluating under an environment containing the replacement terms' values.

Its central result is:

```lean
Equiv.eval_eq : Equiv e f → eval e η = eval f η
```

Every beta-eta conversion is interpreted as equality of semantic values. Quoting those values gives:

```lean
normalize_eq_of_equiv : Equiv e f → normalize e = normalize f
```

This establishes that convertible terms have the same normalization. The reverse direction still needs proof: an algorithm that returned one fixed result for every term would also satisfy this implication.

## 5. Normalization: the output converts to the input

Source: [Normalization.lean](Normalization.lean).

The central soundness result is:

```lean
normalize_sound (e : Term Γ s) : Equiv e (normalize e)
```

The proof uses a logical relation `Related s e v` between syntax and semantic values.

At a ground sort, being related means conversion. At a function sort, it means that applying the syntactic and semantic functions to related arguments produces related results, after any context transport.

Two ingredients do most of the work:

1. `readback_correct`: related values quote to convertible syntax, and reflecting syntax produces a related value.
2. `fundamental`: syntactic substitution and semantic evaluation preserve the relation when their assignments to variables are related.

Apply the fundamental theorem to the identity substitution and reflected-variable environment, then use readback correctness. This yields `normalize_sound`.

Combining it with conversion invariance gives:

```lean
equiv_iff_normalize_eq (e f : Term Γ s) :
  Equiv e f ↔ normalize e = normalize f
```

For the reverse implication, each input converts to its own normalization. If those normalizations are equal, symmetry and transitivity connect the inputs.

The module also proves idempotence:

```lean
normalize (normalize e) = normalize e
```

## 6. Decision and Substitution

Sources: [Decision.lean](Decision.lean), [Substitution.lean](Substitution.lean).

`Decision` derives structural decidable equality for variables and terms, then supplies `DecidableRel Equiv` by comparing normalizations.

This is a decision procedure for terms already known to have the same sort and context.

`Substitution` proves that normalization before substitution or renaming does not change the eventual canonical result:

```text
normalize ((normalize e).subst σ) = normalize (e.subst σ)
normalize ((normalize e).rename ρ) = normalize (e.rename ρ)
```

These are consequences of conversion preservation and normalization correctness, not separate normalizers.

## 7. Erasure and Elaboration: the typed boundary

Sources: [Erasure.lean](Erasure.lean), [Elaboration.lean](Elaboration.lean).

Erasure forgets intrinsic typing evidence while preserving expression structure:

```lean
Term.erase : Term Γ s → NamelessExpr
```

Elaboration checks untrusted nameless syntax:

```lean
elaborate Γ : NamelessExpr → Option (Σ s, Term Γ s)
```

It checks binder indices, their annotated sorts, and application sorts. The dependent pair `Σ s, Term Γ s` packages an inferred sort with a term of that sort.

The round-trip results show that erasing a successfully elaborated term recovers the input, and elaborating erased typed syntax recovers its typed form. Erasure is injective at a fixed context and sort.

This module exposes `normalizeNameless` and `compareNameless`.

| Comparison result | Meaning |
|---|---|
| `some true` | Both inputs elaborate at the same sort and convert |
| `some false` | Both inputs elaborate but do not convert; differing result sorts also give false |
| `none` | At least one input fails elaboration |

Failure is malformed syntax, not exhausted normalization fuel.

## 8. NamedEnvironment: interpret original named expressions

Source: [NamedEnvironment.lean](NamedEnvironment.lean).

```lean
Names Γ := (x : SVar) → Term Γ x.sort
```

This environment assigns a typed term to each named variable. `Names.free` interprets variables as free identifiers.

Binding a name maps that name to the new `.here` and shifts other interpretations beneath the binder. This handles shadowing.

`Packed.Expr Γ := Σ s, Term Γ s` packages dynamically inferred sorts. `Packed.app` checks the sorts before constructing an intrinsically typed application.

`interpretNamed` recursively interprets a `Lisa.Expr` under a naming environment, rejecting ill-sorted applications.

## 9. NamedAlpha: connect binding names to positions

Source: [NamedAlpha.lean](NamedAlpha.lean).

This module proves that direct named interpretation agrees with erasing binder names and interpreting the nameless expression.

`resolve` handles lookup through a stack of binders, choosing the nearest occurrence of a name. The module establishes:

- Alpha equivalence preserves typed interpretation.
- Interpreting under `Names.free` agrees with `toNameless` followed by elaboration.
- Well-sorted named expressions elaborate at their original sort.
- Elaboration fails precisely for ill-sorted named expressions.
- For expressions of the same known sort, alpha equivalence is characterized by equality of their successful typed interpretations.

## 10. NamedSubstitution: align the two substitution algorithms

Source: [NamedSubstitution.lean](NamedSubstitution.lean).

Named substitution in `Lisa.Syntax` must avoid capture by checking free variables and sometimes generating fresh binder names. Typed substitution instead shifts positions under binders.

This module proves that the two implementations agree after interpretation.

`Represents` describes how a named substitution relates two naming environments on relevant variables. The main theorem `interpretNamed_namedSubst` covers capture avoidance, including freshening binders.

`interpretNamed_substOne` specializes the result to the substitution used by the named beta rule, connecting it to typed instantiation.

This bridge is essential: the typed normalizer must implement the original calculus's substitution, not merely a similar-looking operation.

## 11. NamedConversion: named conversion implies typed conversion

Source: [NamedConversion.lean](NamedConversion.lean).

`ResultEquiv` relates interpretation results: failures can be related, and successful results are related when they have the same sort and their typed terms convert.

`interpretNamed_conversion` proves that every constructor of the original `Lisa.Conversion` relation is respected by typed interpretation.

The beta case relies on the substitution bridge. Alpha relies on `NamedAlpha`; eta relies on fresh-variable and binder properties.

For a well-sorted source, named conversion therefore implies successful positive comparison by the typed normalizer.

## 12. Reification: restore fresh binder names

Source: [Reification.lean](Reification.lean).

```lean
Context Γ := ∀ {s}, Var Γ s → Identifier
```

A naming context assigns identifiers to bound-variable positions.

```lean
Term.reify : Term Γ s → Context Γ → Lisa.Expr
```

Reification preserves applications, restores named variables, and generates a fresh name at each lambda. Freshness accounts for both the body's free variables and the surrounding naming context.

The module proves sort preservation, bounds on free variables, and compatibility with typed interpretation.

There are two different readback operations in the package:

| Operation | Direction |
|---|---|
| `Model.quote` | Semantic value → typed syntax |
| `Term.reify` | Typed syntax → original named syntax |

Quoting produces the canonical typed result. Reification restores names without capture.

## 13. NamedReflection: typed conversion implies named conversion

Source: [NamedReflection.lean](NamedReflection.lean).

The important theorem is:

```lean
Equiv.reify :
  Equiv e f → Lisa.Conversion (e.reify ρ) (f.reify ρ)
```

It reconstructs each intrinsic conversion using only the original named conversion rules. The beta case uses the substitution correspondence; eta needs fresh names and the original eta side condition.

The module also connects an original expression to the reification of its successful elaboration by alpha equivalence.

Together with `NamedConversion`, this supplies both directions of the bridge between the two calculi on well-sorted inputs.

## 14. NamedDecision: the final API

Source: [NamedDecision.lean](NamedDecision.lean).

```lean
compareNamed : Lisa.Expr → Lisa.Expr → Option Bool
normalizeNamed : Lisa.Expr → Option Lisa.Expr
```

The exact positive comparison theorem is:

```lean
compareNamed p q = some true ↔
  Lisa.Conversion p q ∧ p.wellSorted
```

Conversion preserves sorts, so the right-hand side also ensures that `q` is well sorted.

The remaining outcomes are characterized too:

```text
some false ↔ both expressions are well sorted and do not convert
none       ↔ at least one expression is ill sorted
```

`SortedExpr s` packages an original expression with a proof of its sort. Conversion on this fragment receives a `DecidableRel` instance.

Named normalization is proved to:

- Return an expression convertible to its input.
- Preserve its sort.
- Fail exactly when the input is ill sorted.
- Be idempotent.
- Characterize conversion by literal equality of named normal forms, assuming the source has a known sort.

The well-sortedness assumption matters: two malformed inputs can both normalize to `none`, and equality of those failures does not establish conversion.

## Role in the proof checker

The combined expression-comparison layer uses named lambda normalization to recognize expressions differing by alpha, beta, or eta conversion.

```text
Check a proof step
  → compare expressions
  → normalize lambda structure
  → use the typed evaluator and readback
  → rely on the conversion correspondence proofs
```

The Lambda package treats logical constants as opaque symbols. It does not prove arbitrary propositional equivalences or quantified implications; the orthologic and combined modules add that reasoning.

Its normalizer requires no fuel. A budget in the combined checker controls other contextual reasoning, rather than this typed lambda normalization procedure.

## Suggested reading order

After the prerequisite files, this is a valid dependency order:

1. [Syntax](Syntax.lean)
2. [Conversion](Conversion.lean)
3. [Semantics](Semantics.lean)
4. [Evaluation](Evaluation.lean)
5. [Normalization](Normalization.lean)
6. [Decision](Decision.lean)
7. [Substitution](Substitution.lean)
8. [Erasure](Erasure.lean)
9. [Elaboration](Elaboration.lean)
10. [NamedEnvironment](NamedEnvironment.lean)
11. [NamedAlpha](NamedAlpha.lean)
12. [NamedSubstitution](NamedSubstitution.lean)
13. [NamedConversion](NamedConversion.lean)
14. [Reification](Reification.lean)
15. [NamedReflection](NamedReflection.lean)
16. [NamedDecision](NamedDecision.lean)

For a first pass, focus on the definitions in `Semantics` and the statements of `normalize_sound` and `equiv_iff_normalize_eq`. Then read `NamedDecision` to see the external guarantee before working through the named-translation proofs.
