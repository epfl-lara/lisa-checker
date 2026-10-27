# Superseded Mathlib-target reduction

These are historical source files from the parallel A/B-to-Mathlib first-order
translation. The active proof now follows Ordered → B → A → PureSyntax, retaining
epsilon and generalized replacement in both intermediate systems.

The files are outside the Lake build. Their old module names and imports are
preserved for reference; this directory is not a standalone compilable package.
`Tests.lean` retains the original regression file, whose relevant cases have been
ported to `Tests/SCLambdaToPure.lean` and `Tests/PureEpsilon.lean`.
`EPSILON_PLAN.md` records the superseded design. The current proof and reading
order are in `Lisa/SCLambdaToPure/EPSILON_PLAN.md`.

The old Mathlib calculus itself remains compiled as
`Lisa/SCLambdaToPure/Reference/MathlibPure.lean`, solely for its optional semantic
regressions. No file in this archive is imported by the active reduction.
