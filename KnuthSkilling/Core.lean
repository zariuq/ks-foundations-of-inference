/-
# Stable algebra entry point

Ordered scales, separation profiles, additive embeddings, tensor representations
and variational functional equations. Probability normalization and entropy are
interpretation layers; Shore--Johnson and countermodels are opt-in.
-/

-- Foundation layer
import KnuthSkilling.Core.Basic
import KnuthSkilling.Core.Algebra
import KnuthSkilling.Core.Interfaces

-- Separation machinery (Alimov/Hölder path)
import KnuthSkilling.Additive.Axioms

-- Main representation theorems
import KnuthSkilling.Additive.Main
import KnuthSkilling.Multiplicative

-- Variational theorem (functional equation → log form)
import KnuthSkilling.Variational.Main
