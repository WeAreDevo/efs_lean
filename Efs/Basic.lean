import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Sum.Basic
import Mathlib.Data.Vector.Basic

/-
Elementary Formal Systems (Smullyan)

An EFS signature consists of:
  K     : finite alphabet of basic symbols
  V     : finite alphabet of variables
  Pred  : finite alphabet of predicate symbols
  deg   : Pred → Nat, required to be positive (a "unique positive integer").
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

/-- A term over an EFSSignature is a finite string over the disjoint alphabets K and V. -/
abbrev Term (S : EFSSignature) : Type :=
  List (S.K ⊕ S.V)

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

/- A direct formulation of Smullyan's definition of
well formed formulas might look something like: -/
-- inductive Formula (S : EFSSignature) where
--   | atom : AtomicFormula S → Formula S
--   | imp : AtomicFormula S → Formula S → Formula S
/- But in anticipation of later proofs we instead use the following isomorphic form-/
structure Formula (S : EFSSignature) where
  premises : List (AtomicFormula S)
  concl    : AtomicFormula S
deriving DecidableEq

/--
An Elementary Formal System (EFS) over a signature `S`
is a finite set of formulas (over `S`) called axioms.
-/
structure EFS (S : EFSSignature) where
  axioms : Finset (Formula S)
