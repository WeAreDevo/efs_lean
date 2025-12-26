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
def encode (n : Nat) : KString S :=
  List.replicate n K.l
def unencode (u : KString S) : Nat :=
  u.length
-- useful lemmas about encodings
@[simp] lemma encode_add (m n : Nat) : encode (m + n) = encode m ++ encode n := by
  simp [encode]
lemma encode_ne_nil_of_pos {n : Nat} (hn : 0 < n) : encode n ≠ [] := by
  cases n with
  | zero => cases hn
  | succ n => simp [encode]

-- The following lemma will be useful in the completeness proof.
lemma encode_two_step (k : Nat) :
  encode (2 * (k + 1 + 1)) = encode (2 * (k + 1)) ++ encode 2 := by
  calc
    encode (2 * (k + 1 + 1))
        = encode (2 * (k + 1) + 2) := by
            have two_mul_succ : ∀ m : Nat, 2 * (m + 1) = 2 * m + 2 := by
              intro m
              omega
            simp [two_mul_succ]
    _   = encode (2 * (k + 1)) ++ encode 2 := by
            simp

-- helper to construct atomic formula "Even(s)" from a Term s.
def EvenAtom (s : Term S) : AtomicFormula S :=
  ⟨Pred.Even, Vector.ofFn (fun _ => s)⟩

-- useful simp lemma for vectors
@[simp] lemma Vector.map_ofFn {α β : Type} {n : Nat}
    (f : α → β) (g : Fin n → α) :
    Vector.map f (Vector.ofFn g) = Vector.ofFn (fun i => f (g i)) := by
  ext i
  simp [Vector.ofFn, Vector.map]

-- Axiom 1: "Even(ll)".
def ax1 : Formula S :=
  ⟨[] , EvenAtom (Term.ofKstring (encode 2))⟩

-- Axiom 2: "Even(x) -> Even(xll)".
def ax2 : Formula S :=
  ⟨[ EvenAtom ([Sum.inr V.x]) ],
  EvenAtom ([Sum.inr V.x] ++ (Term.ofKstring (encode 2)))⟩

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
  { xs | MetaEven (unencode (vget0 xs)) }

/-
Finally, we can state the main theorem of this example, which says that the
set of positive nonzero even naturals is formally representable over the unary signature.
Namely, for the above system E, the predicate ”Even" provides the desired representation.

This requires us to show the two lemmas:
(i) ('Completeness') for any even number X, "Even(X)" is provable in the system;
(ii) ('Soundness') if "Even(X)" is provable in the system, then X is even.
-/
lemma completeness : ∀ n : Nat,
  MetaEven n → E ⊢ ⟨ [], (EvenAtom (Term.ofKstring (encode n))) ⟩ :=
    by
      intro n hn
      rcases hn with ⟨k, rfl⟩
      -- Perform induction on the sequence nonzero even naturals
      induction k with
      -- base case
        | zero =>
          -- goal: E ⊢ ⟨[], EvenAtom (Term.ofKstring (encode 2))⟩
          have hmem : ax1 ∈ E.axioms := by
            simp [E]
          -- use the axiom rule, then rewrite goal to ax1
          have : Provable E ax1 := Provable.ax hmem
          simpa [ax1] using this
      -- inductive case
        | succ k ih =>
          -- goal: E ⊢ ⟨[], EvenAtom (Term.ofKstring (encode (2 * (k.succ + 1))))⟩
          -- which is E ⊢ ⟨[], EvenAtom (Term.ofKstring (encode (2 * (k + 2))))⟩

          /- First, we use the subtitution rule (with u := encode (2 * (k + 1)))
          and the second axiom to get "E ⊢ Even(2 * (k + 1)) -> Even((2 * (k + 1)) + 2)"-/
          -- Let u be the string encoding of 2*(k+1), and package it as NonemptyKString for rule1.
          have hu_ne : encode (2 * (k + 1)) ≠ [] := by
            apply encode_ne_nil_of_pos
            -- 2*(k+1) > 0
            have : 0 < 2 * (k + 1) := by
              simp
            exact this
          let u : NonemptyKString S := ⟨encode (2 * (k + 1)), hu_ne⟩
          -- ax2 is provable (because it is an axiom)
          have hax2 : E ⊢ ax2 :=
            Provable.ax (by simp [E])
          -- Substitute u for x in ax2 to get "E ⊢ Even(2 * (k + 1)) -> Even((2 * (k + 1)) + 2)"
          have hsub : E ⊢ (Formula.subst V.x u ax2) :=
            Provable.rule1 V.x u hax2
            -- Put the substituted ax2 into a usable “implication” shape and simplify it.
        -- After substitution it should read: Even(u) -> Even(u ++ encode 2)
          have himp :
            E ⊢ ⟨[EvenAtom (Term.ofKstring (encode (2 * (k + 1))))],
                  EvenAtom (Term.ofKstring (encode (2 * (k + 1)) ++ encode 2))⟩ := by
                    simpa [ax2, EvenAtom, u] using hsub
        -- Detach himp using ih to obtain the successor evenness
          have hnext :
            E ⊢ ⟨[], EvenAtom (Term.ofKstring (encode (2 * (k + 1)) ++ encode 2))⟩ :=
            Provable.rule2 ih himp
        -- Finally, rewrite the goal using the previous lemma encode_two_step
          simpa [encode_two_step] using hnext


theorem MetaEven_formally_representable :
  FormallyRepresentable S EvenAttr := by
    use E
    use Pred.Even
    use rfl
    sorry

end Example1
