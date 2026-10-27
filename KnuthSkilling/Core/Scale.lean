/-
# Ordered combination interfaces

`KSSemigroupBase` supplies associative, strictly monotone combination on a
linear order. `KnuthSkillingMonoidBase` adds an identity; `KnuthSkillingAlgebraBase`
requires that identity to be least. The local `toSemigroup` and `toMonoid`
interpretations expose Mathlib laws without installing competing global instances.

Separation hypotheses come in positive, strict and bilateral forms. Their
commutativity, Archimedean and real-representation consequences depend on the
specific hypotheses in `Additive.Axioms`; they are not interchangeable.
-/
import KnuthSkilling.Core.Basic
import KnuthSkilling.Core.Algebra
import KnuthSkilling.Additive.Axioms
