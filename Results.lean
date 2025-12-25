import Efs.Defs
open scoped EFSNotation

namespace Example1
-- K has exactly one symbol: l
inductive K : Type
  | l
deriving DecidableEq
instance : Fintype K where
  elems := {K.l}
  complete := by
    intro a
    cases a
    simp

-- One variable x (enough for this example).
inductive V : Type
  | x
deriving DecidableEq
instance : Fintype V where
  elems := {V.x}
  complete := by
    intro a
    cases a
    simp

-- One unary predicate Even (intended: "is even").
inductive Pred : Type
  | Even
deriving DecidableEq
instance : Fintype Pred where
  elems := {Pred.Even}
  complete := by
    intro a
    cases a
    simp

def S : EFSSignature :=
{
  K := K
  V := V
  Pred := Pred
  deg := fun _ => 1
  deg_pos := by
    intro p
    simp
}

-- We identify a string of "l"s of length n with the positive integer n.
def encoding (n : Nat) : KString S :=
  List.replicate n K.l

-- helper to construct atomic formula "Even(s)" from a Term s.
def EvenAtom (s : Term S) : AtomicFormula S :=
  ⟨Pred.Even, Vector.ofFn (fun _ => s)⟩

-- Axiom 1: "Even(ll)".
def ax1 : Formula S :=
  ⟨[] , EvenAtom (Term.ofKstring (encoding 2))⟩

-- Axiom 2: "E(x) -> E(xll)".
def ax2 : Formula S :=
  ⟨[ EvenAtom ([Sum.inr V.x]) ],
  EvenAtom ([Sum.inr V.x] ++ (Term.ofKstring (encoding 2)))⟩

def E : EFS S :=
  {
    axioms := {ax1, ax2}
  }

-- Meta-theoretic predicate: n is an even natural number and nonzero.
def MetaEven (n : Nat) : Prop :=
  ∃ k : Nat, n = 2 * (k + 1)

/- helper to get the only component out of a 1-vector
(which are the elements of the attribute we now go on to define).
-/
def vget0 {α : Type} (xs : Vector α 1) : α :=
  xs.get ⟨0, by simp⟩

-- Attribute of unary strings encoding our meta positive even naturals.
def EvenAttr : Attribute (KString S) 1 :=
  { xs | MetaEven ((vget0 xs).length) }

/-
Finally, we can state the main theorem of this example, which says that the
set of positive nonzero even naturals is formally representable over the unary signature.
Namely, for the above system E, the predicate ”Even" provides the desired representation.
-/
theorem MetaEven_formally_representable :
  FormallyRepresentable S EvenAttr := by
    sorry

end Example1
