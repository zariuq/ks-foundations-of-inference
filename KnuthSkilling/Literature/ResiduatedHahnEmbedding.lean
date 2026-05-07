import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Order.Group.Synonym
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Order.PiLex

import KnuthSkilling.Literature.Residuated

/-!
# Jenei (arXiv:1910.01387) — Hahn embedding for (odd involutive) residuated semigroups

This file is the “statement layer” for the representation/embedding results in:

- Sándor Jenei, *The Hahn embedding theorem for a class of residuated semigroups*
  (arXiv:1910.01387v4), local PDF:
  `literature/KS_codex/Jipsen_Tuyt_2019_Hahn_Embedding.pdf`.

Notes:
* The filename in `literature/KS_codex/` is legacy/misleading (“Jipsen_Tuyt”), but the PDF itself is
  Jenei’s paper (see its title page and abstract).
* The full construction uses *partial sublex products* (Definition 4.2, Theorem 11.1).
  Formalizing the construction and theorem proof is substantial.
* What we do here is **not** a proof; we provide precise Lean interfaces (definitions + theorem
  statements-as-`Prop`) that downstream code can depend on without `sorry`.

We also define the “add top and bottom as annihilators” extension used repeatedly in Definition 4.2.
-/

namespace KnuthSkilling.Literature

open Classical

universe u

/-!
## A `WithTopBot` extension with annihilators for `(*)`

Jenei’s Definition 4.2 repeatedly uses “add a new top element `>` as a top element and annihilator,
then add a new bottom element `⊥` as a bottom element and annihilator”.

Mathlib’s `WithTop`/`WithBot` are optimized for *additive* structures and do not provide a generic
multiplication. Here we define a dedicated extension for multiplicative monoids:

* `⊥` is an annihilator (`⊥ * x = ⊥`, `x * ⊥ = ⊥`) and is the least element.
* `⊤` is also an annihilator unless `⊥` is present (so `⊤ * ⊥ = ⊥`), and is the greatest element.
* `↑a` multiplies as `↑(a*b)`.

This matches the “add `>` then add `⊥`” order of construction: `⊥` dominates `⊤` under `(*)`.
-/

inductive WithTopBot (α : Type*) where
  | bot : WithTopBot α
  | some : α → WithTopBot α
  | top : WithTopBot α

namespace WithTopBot

variable {α : Type*}

instance [Inhabited α] : Inhabited (WithTopBot α) := ⟨some default⟩

instance : CoeTC α (WithTopBot α) := ⟨some⟩

@[simp] theorem coe_inj {a b : α} : (a : WithTopBot α) = b ↔ a = b := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    cases h
    rfl

section Order

instance [LE α] : LE (WithTopBot α) where
  le x y :=
    match x, y with
    | bot, _ => True
    | _, top => True
    | some a, some b => a ≤ b
    | top, _ => False
    | _, bot => False

@[simp] theorem bot_le [LE α] (x : WithTopBot α) : bot ≤ x := by
  cases x <;> trivial

@[simp] theorem le_top [LE α] (x : WithTopBot α) : x ≤ top := by
  cases x <;> trivial

@[simp] theorem some_le_some [LE α] {a b : α} : (some a ≤ some b : Prop) ↔ a ≤ b := by rfl

instance [Preorder α] : Preorder (WithTopBot α) where
  le := (· ≤ ·)
  le_refl x := by
    cases x <;> simp [WithTopBot.instLE]
  le_trans a b c hab hbc := by
    cases a <;> cases b <;> cases c <;>
      simp [WithTopBot.instLE] at hab hbc ⊢
    exact le_trans hab hbc

instance [PartialOrder α] : PartialOrder (WithTopBot α) :=
  { (inferInstance : Preorder (WithTopBot α)) with
    le_antisymm := by
      intro a b hab hba
      cases a with
      | bot =>
          cases b with
          | bot => rfl
          | some _ => cases (by simpa [WithTopBot.instLE] using hba)
          | top => cases (by simpa [WithTopBot.instLE] using hba)
      | some a =>
          cases b with
          | bot => cases (by simpa [WithTopBot.instLE] using hab)
          | some b =>
              have hab' : a ≤ b := by simpa [WithTopBot.instLE] using hab
              have hba' : b ≤ a := by simpa [WithTopBot.instLE] using hba
              exact congrArg some (_root_.le_antisymm hab' hba')
          | top => cases (by simpa [WithTopBot.instLE] using hba)
      | top =>
          cases b with
          | bot => cases (by simpa [WithTopBot.instLE] using hab)
          | some _ => cases (by simpa [WithTopBot.instLE] using hab)
          | top => rfl }

end Order

section Mul

instance [Mul α] : Mul (WithTopBot α) where
  mul x y :=
    match x, y with
    | bot, _ => bot
    | _, bot => bot
    | top, _ => top
    | _, top => top
    | some a, some b => some (a * b)

@[simp] theorem bot_mul [Mul α] (x : WithTopBot α) : bot * x = bot := by cases x <;> rfl
@[simp] theorem mul_bot [Mul α] (x : WithTopBot α) : x * bot = bot := by cases x <;> rfl
@[simp] theorem top_mul [Mul α] (x : WithTopBot α) : top * x = (match x with | bot => bot | _ => top) := by
  cases x <;> rfl
@[simp] theorem mul_top [Mul α] (x : WithTopBot α) : x * top = (match x with | bot => bot | _ => top) := by
  cases x <;> rfl

@[simp] theorem some_mul_some [Mul α] (a b : α) : (some a) * (some b) = (some (a * b)) := rfl
@[simp] theorem coe_mul [Mul α] (a b : α) :
    (↑(a * b) : WithTopBot α) = (a : WithTopBot α) * b := rfl

instance [One α] : One (WithTopBot α) := ⟨some 1⟩

@[simp] theorem coe_one [One α] : ((1 : α) : WithTopBot α) = 1 := rfl

instance [CommMonoid α] : CommMonoid (WithTopBot α) where
  mul := (· * ·)
  one := 1
  mul_assoc a b c := by
    cases a <;> cases b <;> cases c <;> try rfl
    · exact congrArg some (mul_assoc _ _ _)
  one_mul a := by
    cases a <;> try rfl
    · exact congrArg some (one_mul _)
  mul_one a := by
    cases a <;> try rfl
    · exact congrArg some (mul_one _)
  mul_comm a b := by
    cases a <;> cases b <;> try rfl
    · exact congrArg some (mul_comm _ _)

end Mul

end WithTopBot

/-!
## FLe-algebras (Definition 1.1)

Jenei’s Definition 1.1 introduces an `FLe`-algebra:

* a lattice `(X, ∧, ∨)` with order `≤`,
* a commutative, residuated monoid `(X, *, 1, ⟿)` satisfying adjointness
  `x * y ≤ z ↔ y ≤ x ⟿ z`,
* a constant `f` (used to define the residual complement `x⁰ := x ⟿ f`),
* involutive means `(x⁰)⁰ = x`,
* odd means `1 = f`.

We package these as Lean typeclasses so other files can talk about “odd involutive FLe-algebras”
without committing to a particular construction.
-/

class FLeAlgebra (α : Type*) extends Lattice α, CommMonoid α where
  /-- Residual operation `x ⟿ z`. -/
  res : α → α → α
  /-- Adjointness: `x*y ≤ z ↔ y ≤ x ⟿ z`. -/
  adj : ∀ x y z : α, x * y ≤ z ↔ y ≤ res x z
  /-- Distinguished constant `f` (Jenei’s `f`). -/
  f : α

namespace FLeAlgebra

variable {α : Type*} [FLeAlgebra α]

infixr:70 " ⟿ " => FLeAlgebra.res

/-- Residual complement `x⁰ := x ⟿ f`. -/
def rcompl (x : α) : α := x ⟿ FLeAlgebra.f

notation:100 x "⁰" => rcompl x

/-- Group part `Xgr = {x | x⁰ is the inverse of x}` (Jenei, p. 6 around (2.4)). In the commutative
setting, this can be expressed by a single equation `x * x⁰ = 1`. -/
def groupPart : Set α := {x : α | x * x⁰ = 1}

def Idempotent (x : α) : Prop := x * x = x

def PositiveIdempotent (x : α) : Prop := Idempotent x ∧ (1 : α) < x

def FiniteIdempotents (α : Type*) [FLeAlgebra α] : Prop := Set.Finite {x : α | Idempotent x}

def FinitePositiveIdempotents (α : Type*) [FLeAlgebra α] : Prop :=
  Set.Finite {x : α | PositiveIdempotent x}

end FLeAlgebra

/-- Involutivity: `(x⁰)⁰ = x`. -/
class InvolutiveFLeAlgebra (α : Type*) [FLeAlgebra α] : Prop where
  rcompl_involutive : ∀ x : α, (x⁰)⁰ = x

/-- Oddness: `1 = f`. -/
class OddFLeAlgebra (α : Type*) [FLeAlgebra α] : Prop where
  one_eq_f : (1 : α) = FLeAlgebra.f

/-- “Chain” hypothesis: the order is total (Jenei: “chain” = linearly ordered). -/
def IsChain (α : Type*) [LE α] : Prop := IsTotal α (· ≤ ·)

/-!
## Statement-only interfaces for Jenei’s main theorems

We record the theorem statements as `Prop` so the K&S development can depend on them without
introducing `sorry`. The intent is that these will be discharged either by:

* a dedicated formalization of Jenei’s partial sublex product machinery, or
* importing an existing Lean development, or
* proving that K&S implies a *stronger* ordered-group representation that subsumes these.

### Theorem 11.1 (informal)

> Every odd involutive `FLe`-chain with finitely many positive idempotents can be represented as a
> finite partial sublex product of linearly ordered abelian groups.

### Corollary 11.6 (informal)

> The monoid reduct of any odd involutive `FLe`-chain with finitely many idempotents embeds into a
> finite lexicographic product of the form `H₁ × G₂^{>⊥} × ... × Gₙ^{>⊥}`.

For Lean purposes, we record a slightly more uniform target: a lexicographic product whose factors
are all extended by `WithTopBot`. This is implied by Corollary 11.6 by composing with the obvious
inclusion `G ↪ WithTopBot G` on the first coordinate.
-/

/-- A convenient “lexicographic target” for Corollary 11.6: lex order on functions, with each
coordinate extended by `WithTopBot`. -/
abbrev JeneiLexTarget (n : ℕ) (G : Fin n → Type u) : Type u :=
  Lex (∀ i : Fin n, WithTopBot (G i))

/-- Jenei Corollary 11.6 as a precise Lean goal (statement only).

This version uses `WithTopBot` for **all** coordinates for uniformity, as explained above. -/
def JeneiCorollary11_6_Spec : Prop :=
  ∀ (X : Type*) [FLeAlgebra X] [InvolutiveFLeAlgebra X] [OddFLeAlgebra X],
    IsChain X →
    FLeAlgebra.FiniteIdempotents X →
      ∃ n : ℕ,
        ∃ (G : Fin n → Type u),
          ∃ instCommGroup : ∀ i, CommGroup (G i),
          ∃ instLinearOrder : ∀ i, LinearOrder (G i),
          ∃ instIsOrderedMonoid : ∀ i, IsOrderedMonoid (G i),
             (letI : ∀ i, CommGroup (G i) := instCommGroup
              letI : ∀ i, LinearOrder (G i) := instLinearOrder
              letI : ∀ i, IsOrderedMonoid (G i) := instIsOrderedMonoid
             letI : ∀ i, PartialOrder (WithTopBot (G i)) := fun _ => inferInstance
             letI : ∀ i, CommMonoid (G i) := fun _ => inferInstance
             letI : ∀ i, CommMonoid (WithTopBot (G i)) := fun _ => inferInstance
             ∃ f : X →*o JeneiLexTarget n G, Function.Injective f)

/-!
## Theorem 11.1 (tracking)

Theorem 11.1 (“partial sublex product group representation”) is substantially stronger than
Corollary 11.6 and depends on Jenei’s Type I / Type II partial sublex product constructions
(Definition 4.2, Theorem 4.4, Definition B).

We intentionally do **not** encode it yet: doing this properly requires first formalizing the
partial sublex product constructors and their induced `FLeAlgebra` structure.

For K&S-facing work, the main reusable consequence is `JeneiCorollary11_6_Spec`.
-/

end KnuthSkilling.Literature
