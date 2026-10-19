# Plan: a simpler, intrinsically sorted lambda package

## Objective and recommendation

Build an independent alternative in `Lisa.LambdaV2`, preserving the mathematical purpose and project-facing guarantees of the existing package. Internal signatures and representation-specific helpers may change. Success requires **fewer implementation lines and an easier development to understand**, with complete proofs.

**Recommendation:** use intrinsically sorted `Term s`, per-sort numeric variables, ordinary semantic functions, and a matching per-sort untyped format for erasure/elaboration. Interpret named expressions directly. Isolate agreement with Lisa's shared alpha-equivalence in one proof module.

This supersedes the previous plan's requirement to preserve the finite-stack nameless API and build a separate scope-preservation theory. Preserve nameless normalization and decision as capabilities, adapted to the new representation of open terms. Do not require all operations to pass through Lisa's existing nameless format.

This is a design and proof route, not a claim that the size target has already been achieved. Measure the complete core before migrating the whole named bridge. If its new proofs outweigh its savings, revise the design before declaring success.

The plan below has now been implemented in the new submodule and its umbrella. Its Lean sources/tests do not import, alias, invoke, or refer to the existing implementation. Shared production definitions and the existing package remain untouched. Documentation discusses the baseline for auditing purposes; see the implementation result at the end.

## Findings from the current code

These are source observations, rather than assumptions of the proposal:

- `Lisa.NamelessExpr` stores `bound : Nat → LSort → NamelessExpr`. The datatype does not enforce typing or finite scope.
- `Expr.toNameless` finds a complete sorted variable in a single binder list. Its indices count every binder; the produced annotation agrees with the selected binder automatically.
- `AlphaEq` compares these keys together with the inferred source sorts. It performs no further binder-consistency check.
- The existing elaborator and generalized nameless interpreter check arbitrary nameless inputs against a finite binder list.
- The production lambda consumer, `Lisa/Combined/Lambda.lean`, uses the named normalization API and its theorems. `Lisa/Combined/Normalize.lean` uses shared `AlphaEq`, without inspecting its indices.
- Direct uses of nameless elaboration/comparison outside the lambda implementation found in the search are tests. They do not establish a production requirement for the exact finite-stack API.
- The baseline has 16 Lean files and **1,645 nonblank source lines**, including comments/imports and excluding tests/docs. `Normalization.lean` is already only 96 nonblank lines. Simplifying semantics does not automatically shorten its proof.

## Representation options

| Option | Benefit | Cost | Decision |
|---|---|---|---|
| Keep context-indexed terms | Little migration; scope remains intrinsic | Retains the machinery the user wants to remove | Do not pursue |
| `Term s`, indices count every binder | Simple shifts; agrees directly with shared nameless indices | Binder/reference sort agreement requires an invariant, or a defined treatment of inconsistent references | Less suitable for the typed evaluator |
| `Term s`, indices count binders of their own sort | All references have a coherent sorted meaning; total typed substitution/evaluation without `Γ` | Sort cases in lifting; correspondence with shared alpha keys | Recommended |
| Intrinsically sorted named terms | No positional shifting; resembles source expressions | Capture avoidance, alpha reasoning, and fresh names during higher-order readback remain | Viable, but no demonstrated smaller proof route yet |
| Higher-order/parametric abstract syntax | Host functions express binders | Structural equality, induction, executable comparison, and unwanted host functions require a different development | Too large a redesign here |

Intrinsic typing remains: variable sorts, application compatibility, and result sorts are enforced by constructors. Per-sort references select only binders of their own sort. Beyond local binders they denote sorted ambient variables.

With all-binders indices, `λ(_:ind). bound prop 0` can be constructed by context-free, result-sorted constructors, but its binding interpretation is inconsistent. This is harmless for raw syntax produced by a trusted `toNameless`; it complicates an evaluator/substitution theory intended for **every** internal term. A total dependent environment cannot simply return an `ind` argument as a `prop` value. Avoid adding consistency predicates throughout that core.

Named evaluation is possible. However, the choice `Val prop = Term prop`, `Val (s >> t) = Val s → Val t` alone does not give an algorithm for choosing names fresh for an opaque Lean function's captured values. Higher-order reflection quotes arguments too. A disciplined name supply, support/equivariance proof, or equivalent mechanism remains necessary. Do not claim this work disappears merely because the syntax has names. The selected design has a concrete proof route with fewer new ideas.

## Typed syntax and binding

```lean
inductive Term : LSort → Type where
  | bound (s : LSort) (index : Nat) : Term s
  | free (s : LSort) (id : Identifier) : Term s
  | const (s : LSort) (id : Identifier) : Term s
  | app : Term (s >> t) → Term s → Term t
  | lam (domain : LSort) : Term t → Term (domain >> t)
```

Signatures are sketches; sorts may be implicit. Use `Σ s, Term s` only when a computation discovers the sort. There is no `Var Γ s`, `Term Γ s`, or separate internal typing judgment.

```text
λ(_:prop). λ(_:ind). bound prop 0   outer prop binder
λ(_:prop). λ(_:prop). bound prop 1  outer prop binder
λ(_:ind). bound prop 0             ambient prop variable
```

Whole function sorts have their own namespaces too. Lisa already provides sort equality. Start with ordinary functions and equality cases; hash maps are an optional optimization, not a prerequisite.

```text
Ren := LSort → Nat → Nat
Sub := (s : LSort) → Nat → Term s
```

Retain identity, composition, extension, lifting, single substitution, instantiation, and their algebra. Under a binder `b`, renaming protects zero of sort `b`, shifts successors there, and leaves other lookup namespaces unchanged.

Substitution shifts **every replacement term** under that binder, including replacements whose result sort differs from `b`. An `ind` term can contain `prop` references. Isolate sort-equality casts in extension/lifting and expose zero/successor/different-sort equations.

Keep an independent inductive `Equiv` with reflexivity, symmetry, transitivity, application, lambda, beta, and eta. Eta shifts the function in the domain-sort namespace. Do not define conversion as normalization equality.

## Matching untyped syntax

Declare `LambdaV2.RawTerm` with the same five syntactic constructors, but untyped applications. Its bound indices use the same per-sort convention as `Term`.

Use a distinct datatype rather than silently giving `Lisa.NamelessExpr` two meanings. This costs a small constructor declaration and prevents accidental convention mixing.

```text
erase     : Term s → RawTerm
elaborate : RawTerm → Option (Σ s, Term s)
```

Erasure is structural and total. Elaboration accepts sorted indexed variables immediately and checks application sorts. Neither operation needs a binder stack, index conversion, or scope witness.

Prove unconditional typed round trips, successful raw round trips, and erasure injectivity. Retain raw normalization, comparison, differing-sort negative answers, exact positive/failure characterizations, and idempotence using the same proof patterns as the existing package.

The intentional behavior change is explicit: an index beyond local binders is a legitimate ambient variable, not a failure against a finite supplied context. Ill-sorted applications still fail. This adapts the representation of open terms while preserving raw normalization/decision capabilities.

### Relation to the shared `NamelessExpr`

Keep shared `NamelessExpr`, `Expr.toNameless`, and `AlphaEq` unchanged during the isolated implementation. They remain the specification used by Lisa.

Use them only in the proof connecting named interpretation to shared alpha-equivalence. Small helper translations with explicit index environments may be needed. They do not require a second normalizer, finite-stack elaborator, or public bidirectional format-conversion API.

A shared per-sort migration could align the conventions later, but it would also require changing the baseline's consumers/proofs. Do not make this alternative's size target depend on that future change. Count its alpha-correspondence helpers in full.

## Semantics with ordinary functions

```text
Depth := LSort → Nat
Residual s := Depth → Term s
Val ind := Residual ind
Val prop := Residual prop
Val (s >> t) := Val s → Val t
Env := (s : LSort) → Nat → Val s
```

Depth is data used to print variables during reconstruction, not a type index on terms or values. Arrow values are ordinary functions with no renaming argument or naturality field.

Define quote/reflect together by recursion on the sort:

```text
quote_base d v = v d
reflect_base n = n
quote_(s→t) d f =
  lam s (quote_t (d.inc s) (f (reflect_s (fresh_s (d s)))))
reflect_(s→t) n =
  fun a => reflect_t (fun d => app (n d) (quote_s d a))
fresh_s level d = bound s (d s - (level + 1))
```

A recursive pair suffices; no general semantic transport framework is needed. Prove the inequalities justifying subtraction at actual fresh-variable uses.

Evaluation is structural recursion. Application uses function application; lambda returns `fun a => eval body (Env.extend η a)`. Extension inserts the argument at zero of its sort's sequence; other sequences stay unchanged.

```text
ambient s n = reflect_s (fun d => bound s (d s + n))
normalize e = quote_s zero (eval e ambient)
```

Keep eta-long readback. Normalization is total for all typed open terms and needs no fuel or availability checks.

## Normalization proofs

Prove constructor equations, syntactic renaming by environment precomposition, substitution compatibility, and evaluation invariance under all conversion rules. Function cases use ordinary `funext`. This gives normalization invariance.

For soundness, let `W(d,k)` shift ambient indices by `k s - d s` for pointwise `d ≤ k`; prove identity/composition. Use:

```text
RepresentsAt d e n := ∀ k ≥ d, Equiv (e.rename (W(d,k))) (n k)
Related base d e v := RepresentsAt d e v
Related (s→t) d e f :=
  ∀ k ≥ d, ∀ a w,
    Related s k a w →
    Related t k (app (e.rename (W(d,k))) a) (f w)
```

Prove congruence, depth monotonicity, fresh-variable correspondence, simultaneous quote/reflect correctness, and the fundamental evaluation theorem. Derive soundness, canonicality, idempotence, and conversion decidability.

The relation establishes correctness for appropriate evaluator-generated values. It does not claim every arbitrary Lean function is denotable or that reflecting arbitrary residual syntax normalizes it.

### Eliminate the previous separate scope-proof requirement

The named bridge already needs interpretation/substitution compatibility. Specialize it to prove:

```text
interpretNamed p Names.free = some ⟨s, e⟩
    implies e.subst σ = e for every indexed substitution σ.
```

This follows because indexed substitution leaves `Names.free` unchanged. It expresses that complete named inputs have no ambient indexed references without a separate `Scoped` development.

The normalization/substitution theorem then gives:

```text
normalize ((normalize e).subst σ)
  = normalize (e.subst σ)
  = normalize e.
```

This is the equality needed when normalizing reconstructed named output a second time. **It does not assert `(normalize e).subst σ = normalize e` without the outer normalization.** Do not use it as a stronger syntactic scope theorem.

The matching raw interface also needs no scope-preservation proof. Add finite-scope checking or a stronger output-scope theorem only if a real caller needs it. These are not missing intrinsic typing guarantees.

## Named bridge and reconstruction

Keep direct typed interpretation:

```text
Names := (x : SVar) → Term x.sort
interpretNamed : Lisa.Expr → Names → Option (Σ s, Term s)
```

Binding a name assigns its sort's zero variable and shifts the other interpretations. Keep support, sorting, shadowing, renaming/substitution compatibility, and the complete capture-avoiding named substitution correspondence. The shared named substitution and `Conversion` relation remain the specifications.

Prove both directions of agreement with shared alpha-equivalence in `NamedAlpha.lean`. Its helpers may interpret shared keys through index environments. State their domains honestly: a proof helper on all raw keys need not pretend to be a checked finite-stack elaborator. The agreement theorems apply to keys produced from named expressions.

### Small total naming contexts

Use a finite-range assignment of identifiers to indexed variables:

```text
Context.lookup : LSort → Nat → Identifier
Context.used   : LSort → Finset Identifier
Context.lookup_mem : lookup s n ∈ used s
```

This explicitly restricts the naming assignments represented to finite range per sort; it does not claim arbitrary infinite-range functions have finite support. `empty` supplies one reserved default identifier. Extension inserts the fresh name and shifts lookup in that sort's namespace. The per-sort reserved sets also make the reconstructed free-variable bound precise under mixed-sort lambdas. The default has a base name different from `"x"`, so it does not affect the fresh-binder counter policy.

Every assignment on a finite collection of indexed variables extends to this form by using the default elsewhere. Thus finite-context naming is retained. Distinct ambient indices may intentionally receive the same name, just as old naming contexts could assign identical names to different positions. Do not claim injectivity on arbitrary open terms.

Keep `reify : Term s → Context → Expr` total. Avoid body free identifiers and reserved context identifiers when choosing a binder. Prove the exact meaning of reconstruction:

```text
interpretNamed (reify e ρ) Names.free
  = some ⟨s, e.subst ρ.toSub⟩.
```

Reification substitutes names for ambient indexed variables. For named-source interpretations, substitution invariance removes `ρ.toSub` and gives the alpha round trip. Evaluation and normalization themselves never collapse ambient variables.

Prove `Equiv.reify` for any such naming context. Total interpretation allows induction on unrestricted derivations, including intermediate open terms, without assuming they remain finitely scoped. Keep fresh-binder, renaming, weakening, beta, and eta reconstruction lemmas where useful.

### Named API

Preserve:

- `compareNamed : Expr → Expr → Option Bool`, with exact true/false/malformed characterizations;
- decidable shared conversion on sorted source expressions;
- `normalizeNamed : Expr → Option Expr`;
- shared-conversion soundness, sort preservation, and exact ill-sorted failure;
- literal named idempotence;
- conversion iff equal named normalizations for a sorted source.

Compare successful typed normalizations for named decisions. Share a packed-result comparator with raw decisions, rather than duplicating option/sort case analysis or reconstructing names just to compare them. Reconstruct names for `normalizeNamed`.

Prove named idempotence using reification-as-substitution and the displayed normalization/substitution equality. This route does not need a semantic scope-preservation theorem. Kernel-check it before counting that saving as established.

## Module plan

Keep recognizable file boundaries and all mathematical services. No file is removed just to reduce line count.

| File | Role and change |
|---|---|
| `Syntax` | Typed numeric syntax and full binding algebra; remove context membership; no scope framework initially |
| `Conversion` | Independent beta-eta rules and renaming/substitution closure |
| `Semantics` | Direct values/readback/evaluation; remove `Family`, Kripke functions, naturality, and proof-carrying evaluator |
| `Evaluation` | Constructor, renaming, substitution, and conversion invariance equations |
| `Normalization` | Depth logical relation, soundness/canonicality/idempotence; omit separate scope development |
| `Decision` | Typed decidability plus reusable packed comparison/contracts |
| `Substitution` | Keep normalization/substitution and normalization/renaming equations |
| `Erasure` | Matching `RawTerm` and structural erasure with unchanged indices |
| `Elaboration` | Application-sort checks, round trips, raw normalization/comparison and contracts |
| `NamedEnvironment` | Direct typed interpretation and support/sort/substitution laws |
| `NamedAlpha` | Shared alpha correspondence; isolate the two index conventions here |
| `NamedSubstitution` | Complete capture-avoiding named substitution correspondence |
| `NamedConversion` | Interpret every shared conversion rule and derive comparison consequences |
| `Reification` | Finite-range naming, freshness, sorting/free-name properties, substitution characterization |
| `NamedReflection` | Reify conversion; named-source invariance and alpha round trips; reflect comparison |
| `NamedDecision` | Named decisions, canonical output, and all project-facing contracts |

The [declaration audit](DECLARATION_AUDIT.md) maps existing definitions/theorems to these roles. It no longer mandates exact names/signatures or duplicated consequences. Any omitted capability must be explicit. Moving packed helpers to break a dependency cycle is acceptable; count all helpers in the total.

## Implementation phases and gates

1. **Syntax/evaluator prototype:** complete typed binding algebra, conversion, and ordinary-function evaluation. Exercise mixed/same/function-sort binders, capture, ambient variables, and higher-order examples.
2. **Core proof gate:** finish soundness, canonicality, idempotence, and decision. Measure the entire core, including the depth relation. If its new proofs erase the semantic savings, simplify before extending the implementation.
3. **Matching raw interface:** implement erase/elaborate and every normalization/comparison contract. Verify that no stack or scope machinery has reappeared.
4. **Alpha bridge gate:** prove direct named interpretation agrees with shared alpha-equivalence in both directions. Measure this helper cost; do not introduce a second public normalization pipeline to establish the theorem.
5. **Named substitution/conversion:** port the necessary freshening proofs and all conversion constructors while preserving shared definitions.
6. **Reconstruction gate:** prove total finite-range reification, conversion reflection, named-source substitution invariance, and named idempotence. If the proposed route fails, identify the missing lemma before adding a larger framework.
7. **Consumer gate:** finish named decisions and compile an independent consumer against shared reference order: reducer soundness, sorting, idempotence, canonicality, application/lambda congruence, and the order-reduction instance. Do not import the production module selecting the baseline.
8. **Acceptance review:** build all modules/tests, audit axioms/dependencies and declaration roles, compare size/readability, and write the explanatory README from the verified implementation.

## Measuring strict simplification

Compare the complete implementation scope with the baseline's 1,645 nonblank lines. Report raw and nonblank counts, identify comments versus executable definitions/proofs where practical, and count every added helper. Count tests and the extra consumer demonstration separately on both sides. Do not move code elsewhere, compress layout, remove explanations, or weaken guarantees to pass the size check.

| Baseline component | Nonblank lines | What must be measured in the replacement |
|---|---:|---|
| Syntax, conversion, semantics, evaluation, normalization, decision, substitution | 538 | Semantic savings minus additional per-sort algebra and depth-relation proofs |
| Erasure and elaboration | 191 | Structural typed/raw correspondence, including the small new raw datatype |
| All seven named-bridge modules | 916 | Alpha compatibility, capture avoidance, naming, reflection, and final contracts in full |
| Total | 1,645 | All corresponding implementation code, including helpers moved to new files |

This breakdown is why merely shortening `Semantics` is insufficient: over half the baseline is the named bridge. The proposed raw interface and reused substitution/comparison proofs must supply real savings too.

Expected savings: no context membership/parameters; no semantic transport/naturality; direct evaluation; matching typed/raw indices; named-source independence derived from existing substitution laws; shared comparison cases.

Potential increases: sort cases in lifting, the depth-based logical relation, shared-alpha correspondence, and naming-context bookkeeping. Named capture avoidance remains a substantial part of the baseline. A dramatic reduction is not justified in advance; a modest strict reduction is a plausible target that must be measured.

Readability means fewer concepts: typed terms, substitution, semantic values, quote/reflect, the correctness relation, and the named bridge. Avoid a general abstraction framework or opaque tactic compression when direct definitions and lemmas suffice.

If the complete result is not smaller and easier to follow, state that the simplification objective remains unmet and revise it. A shorter evaluator alone is not success.

## Validation

- Build every implementation module/test target; no admitted proofs, added axioms, unsafe code, partial evaluation, or fuel.
- Verify the source/import closure is independent of the baseline implementation.
- Keep syntax/conversion independent of named expressions and evaluation.
- Test same/different/function-sort binders, cross-sort capture in replacements, shadowing, and identifiers shared across sorts.
- Treat ambient indices as meaningful open variables; test application-sort failures separately.
- Check typed/raw round trips, comparator outcomes, and raw normalization idempotence.
- Check named alpha/beta/eta, higher-order cases, sort failures, fresh-name collisions, literal canonicality and idempotence.
- Prove shared alpha correspondence at its stated generality, including malformed applications where applicable.
- Compile the shared conversion/reference-order consumer contracts.
- Report whether fresh binder spellings match the baseline exactly. Canonicality within the alternative is required; exact cross-implementation spelling equality is a separate property.

The isolated alternative must meet its simplicity target without a future change to shared `NamelessExpr`. Such a migration may later remove correspondence helpers, but is not assumed here.

## Implementation result

All 16 module roles are implemented and the three dedicated test targets pass. Normalization soundness/canonicality, raw round trips and decisions, named capture avoidance and alpha/conversion correspondence, named idempotence, and the shared-order reducer contracts are kernel-checked. The named-idempotence proof uses substitution invariance as planned; no separate scope framework was introduced.

| Measure, corresponding 16 modules | Audited baseline | Completed alternative |
|---|---:|---:|
| Physical lines | 1,924 | 1,686 |
| Nonblank lines | 1,645 | 1,412 |
| Nonblank lines excluding comments | 1,555 | 1,363 |

The extra reducer demonstration and umbrella add 50 nonblank lines. Tests add 92 nonblank lines and are reported separately. All helpers are counted within the package; the alternative remains smaller even including the extra reducer/umbrella. No runtime performance claim is made.

The source/import audit confirms independence from the baseline. Inspected theorem axioms are only `propext`, `Quot.sound`, and, for named results, `Classical.choice`. There are no added axioms, admitted proofs, or unsafe/partial evaluator definitions. Naming reserves identifiers per sort, so different sorts may reuse binder spellings; named canonicality and idempotence remain proved.

See [README.md](README.md) for the implemented representation, API, and reading order, and [DECLARATION_AUDIT.md](DECLARATION_AUDIT.md) for completed dispositions of the original declarations.
