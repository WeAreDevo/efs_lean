import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Sum.Basic
import Mathlib.Data.Vector.Basic

/-
Elementary Formal Systems. These definitions are based on
Raymond Smullyan's paper 'Elementary formal systems' (1961)
and book 'Theory of Formal Systems' (1961) chapter 1.
-/

/-
An EFS signature consists of the mutually disjoint sets:
  K     : finite alphabet of basic symbols
  V     : finite alphabet of variables
  Pred  : finite alphabet of predicate symbols
  deg   : Pred → Nat, required to be positive on all predicate symbols.
-/
structure EFSSignature where
  K : Type
  V : Type
  Pred : Type

  [K_finite  : Fintype K]
  [V_finite  : Fintype V]
  [P_finite  : Fintype Pred]
  [K_decEq   : DecidableEq K]
  [V_decEq   : DecidableEq V]
  [P_decEq   : DecidableEq Pred]
  deg : Pred → Nat
  deg_pos : ∀ p : Pred, 0 < deg p

attribute [instance] EFSSignature.K_finite EFSSignature.V_finite EFSSignature.P_finite
attribute [instance] EFSSignature.K_decEq  EFSSignature.V_decEq  EFSSignature.P_decEq

/- A `K`-string is just a list of `K` symbols. -/
abbrev KString (S : EFSSignature) : Type := List S.K

/- A nonempty `K`-string. -/
abbrev NonemptyKString (S : EFSSignature) : Type := { u : KString S // u ≠ [] }

/- A term over an EFSSignature is a finite string over the disjoint alphabets K and V. -/
abbrev Term (S : EFSSignature) : Type :=
  List (S.K ⊕ S.V)
/-
Uniform substitution into terms:
Substitute the nonempty `K`-string `u` for all occurrences of variable `x` in a term.
-/
namespace Term
def subst {S : EFSSignature} (x : S.V) (u : NonemptyKString S) : Term S → Term S
  | [] => []
  | (Sum.inl k) :: t =>
      Sum.inl k :: subst x u t
  | (Sum.inr y) :: t =>
      if y = x then -- uses DecidableEq on variables (S.V) to decide y = x.
        -- replace y by the K-string u, embedded into K⊕V as K-symbols
        (List.map Sum.inl u.1) ++ subst x u t
      else
        Sum.inr y :: subst x u t

/- Embedding a K-string into a Term by mapping K-symbols to Sum.inl -/
def ofKstring {S : EFSSignature} : KString S → Term S :=
  List.map Sum.inl
end Term

/-- In Smullyan's presentation, an atomic formula over an EFSSignature is defined as a
string consisting of a predicate symbol P followed by deg P terms seperated by a
comma symbol ',' outside of K,V and P. To avoid parsing, we will jump directly to an abstract
representation, and enforce the well-formedness via the type system.
There are different equivalent ways to encode this abstract syntax in DTT.
Namely, Vector-based (arity enforced by the type) or
List + length proof (arity enforced by a dependent pair).
I chose the vector approach but not sure if it's best. -/
structure AtomicFormula (S : EFSSignature) where
  P : S.Pred
  args : Vector (Term S) (S.deg P)
deriving DecidableEq
/- Lifting substitution to AtomicFormulas -/
namespace AtomicFormula
def subst {S : EFSSignature} (x : S.V) (u : NonemptyKString S) :
  AtomicFormula S → AtomicFormula S
  | ⟨P, args⟩ =>
      ⟨P, Vector.map (Term.subst x u) args⟩

/- helper to construct atomic formulas from K-strings -/
def ofKStrings
  {S : EFSSignature} (P : S.Pred)
  (xs : Vector (KString S) (S.deg P)) :
  AtomicFormula S :=
⟨ P, Vector.map Term.ofKstring xs⟩

end AtomicFormula

/- Intuitively, Smullyan's formulas can be seen as Horn-clauses (think Prolog) with
a finite sequence of premises and a single conclusion.
A direct formulation of Smullyan's definition of
well formed formulas might look something like: -/
-- inductive Formula (S : EFSSignature) where
--   | concl : AtomicFormula S → Formula S
--   | imp : AtomicFormula S → Formula S → Formula S
/- Note we in effect do not allow the possibilty of non-atomic premises.
 Intuition why expressive power is not lost:
 Any implication in a premise can be compiled away by introducing a fresh predicate symbol.

Instead of a direct formulation, we use the following isomorphic list form that keeps explicit track
of the premises and single conclusion. Not sure if this is best in long run...-/
structure Formula (S : EFSSignature) where
  premises : List (AtomicFormula S)
  concl    : AtomicFormula S
deriving DecidableEq
/- In this formulation, Atomic formulas are embeded into Formula as those with empty premises:
   A  ≅  ⟨[], A⟩
-/
/- Extending substitution to general Formulas -/
namespace Formula
def subst {S : EFSSignature} (x : S.V) (u : NonemptyKString S) :
  Formula S → Formula S
  | ⟨premises, concl⟩ =>
      ⟨List.map (AtomicFormula.subst x u) premises,
       AtomicFormula.subst x u concl⟩
end Formula

/-
An Elementary Formal System (EFS) over a signature `S`
is a finite set of formulas (over `S`) called axioms.
-/
structure EFS (S : EFSSignature) where
  axioms : Finset (Formula S)

inductive Provable {S : EFSSignature} (E : EFS S) : Formula S → Prop where
  | ax {X : Formula S} :
  -- Any axiom is provable.
      X ∈ E.axioms →
      ---------------
      Provable E X
--
  | rule1 {X : Formula S} (x : S.V) (u : NonemptyKString S) :
  -- Substitution of words in K for variables.
      Provable E X →
      ----------------------------------
      Provable E (Formula.subst x u X)
--
  /--
  Rule of Detachment or Modus Ponens.
  If we have `A` and `A → X`, infer `X`.
  In our list representation:
   `A` is `⟨[], A⟩` and `A → X` is `⟨A :: ps, C⟩` (with X represented by ⟨ ps, C ⟩ ),
  so the result is `⟨ps, C⟩`.
  -/
  | rule2 {A C : AtomicFormula S} {ps : List (AtomicFormula S)} :
      Provable E ⟨[], A⟩ →
      Provable E ⟨A :: ps, C⟩ →
      -----------------------------
      Provable E ⟨ps, C⟩


/--
Smullyan introduces the term 'attribute':
'for any set S, an attribute over S is either a subset of S or a set of n-tuples of elements of S'
We represent this as the type former Attribute
which for a type `α` denotes the n-ary relation on `α`.
Perhaps there is a more idiomatic way to represent this in Lean?
-/
-- structure Attribute (α : Type) where
--   arity : Nat
--   arity_pos : 0 < arity
--   set : Set (Vector α arity)
abbrev Attribute (α : Type) (n : Nat) : Type :=
  Set (Vector α n)

namespace Attribute
-- Helper to transport attributes along equalities of their arities.
def cast {α : Type} {m n : Nat} (h : m = n) (W : Attribute α m) : Attribute α n :=
  match h with
  | rfl => W
end Attribute

/--
A predicate P of degree n is said to represent the set of
all n-tuples (X1, ••• , Xn) (of strings in K) such that PX1, ••• , Xn is provable in (E).
-/
def PredicateRepresents
  {S : EFSSignature} (E : EFS S)
  (P : S.Pred)
  (W : Attribute (KString S) (S.deg P)) : Prop :=
  ∀ xs : Vector (KString S) (S.deg P),
    xs ∈ W ↔
      Provable E ⟨[], AtomicFormula.ofKStrings P xs⟩

/--
An attribute over `K` is formally representable
if there exists some EFS and predicate that represent it.
-/
def FormallyRepresentable {n : Nat} (S : EFSSignature) (W : Attribute (KString S) n) : Prop :=
  ∃ (E : EFS S) (P : S.Pred) (h : n = S.deg P),
    PredicateRepresents E P (Attribute.cast h W)

/-
Syntax definitions for convenient notation.
-/
namespace EFSNotation

/-- Turnstile notation for derivability: `E ⊢ X` -/
scoped notation:51 E " ⊢ " X:50 => Provable E X

/-- Substitution notation: `X[u/x]` -/
scoped notation:90 t "[" u "/" x "]" => Term.substVar _ x u t
scoped notation:90 A "[" u "/" x "]" => AtomicFormula.subst x u A
scoped notation:90 X "[" u "/" x "]" => Formula.subst x u X

end EFSNotation
