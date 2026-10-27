# Archived completeness experiment

This is the former `Verification` package. It preserves the Foundation syntax
adapter and completeness experiment, including its pinned dependency manifest.
Paths to the parent Lisa project and shared dependency cache were updated after
the move.

The active reduction retains epsilon in its first-order target and translates
syntactically. It does not need Foundation, models, a completeness theorem, or
epsilon elimination. This package is outside the root build and is retained
only for reference.

Foundation uses its own first-order syntax. `FoundationSyntax.lean` adapts the
previous Mathlib target; it does not handle the new epsilon target.
