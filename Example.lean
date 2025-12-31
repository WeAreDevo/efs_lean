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
  -- Even is a unary predicate:
  deg := fun _ => 1
  deg_pos := by
    simp
}

-- We identify a string of "l"s of length n with the positive integer n.
def encode (n : Nat) : KString S :=
  List.replicate n K.l
def decode (u : KString S) : Nat :=
  u.length
-- useful lemmas about encodings and decodings
-- mutual inverses
@[simp] lemma encode_decode (u : KString S) : encode (decode u) = u := by
-- This holds since K contains only the one symbol l
    -- unfold encode/decode
  simp [encode, decode]
  -- goal is now: replicate (length u) K.l = u
  induction u with
  | nil =>
      simp
  | cons k t ih =>
      cases k  -- only case is K.l
      -- now goal is replicate (length (K.l :: t)) K.l = K.l :: t
      simp [List.replicate_succ, ih]
@[simp] lemma decode_encode (n : Nat) : decode (encode n) = n := by
  simp [decode, encode]
@[simp] lemma decode_append (s t : KString S) :
  decode (s ++ t) = decode s + decode t := by
  simp [decode]
@[simp] lemma encode_add (m n : Nat) : encode (m + n) = encode m ++ encode n := by
  simp [encode]
lemma encode_of_pos_ne_nil {n : Nat} (hn : 0 < n) : encode n ≠ [] := by
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

-- useful simp lemmas for vectors
@[simp] lemma map_ofFn {α β : Type} {n : Nat}
    (f : α → β) (g : Fin n → α) :
    Vector.map f (Vector.ofFn g) = Vector.ofFn (fun i => f (g i)) := by
  ext i
  simp [Vector.ofFn, Vector.map]
lemma eq_ofFn_head {α : Type} (X : Vector α 1) :
  X = Vector.ofFn (fun _ : Fin 1 => X.head) := by
  ext i hi
  have : i = 0 := (Nat.lt_one_iff).1 hi
  subst this
  simp [Vector.head]
@[simp] lemma head_map {α β : Type} {n : Nat} (f : α → β) (v : Vector α (n + 1)) :
  (v.map f).head = f v.head := by
    simp [Vector.head, Vector.map]


-- Axiom 1: "Even(ll)".
def ax1 : Formula S :=
  ⟨[] , EvenAtom (Term.ofKstring (encode 2))⟩

-- Axiom 2: "Even(x) -> Even(xll)".
def ax2 : Formula S :=
  ⟨[ EvenAtom ([Sum.inr V.x]) ],
  EvenAtom ([Sum.inr V.x] ++ (Term.ofKstring (encode 2)))⟩

-- The EFS consisting of the above two axioms.
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
  xs.head
-- additional equality lemmas about vget0 and vectors of length 1
@[simp] lemma vget0_ofFn {α : Type} (t : α) :
  vget0 (Vector.ofFn (fun _ : Fin 1 => t)) = t := by
    rfl
@[simp] lemma head_ofFn {α : Type} (f : Fin 1 → α) :
  (Vector.ofFn f).head = f ⟨0, by simp⟩ := by
  simp [Vector.head]
lemma map_eq_ofFn_head {α β : Type} (f : α → β) (X : Vector α 1) :
  Vector.map f X = Vector.ofFn (fun _ : Fin 1 => f X.head) := by
    rw [eq_ofFn_head X]
    simp [map_ofFn]


-- Attribute of unary strings encoding our meta object.
def EvenAttr : Attribute (KString S) 1 :=
  { xs | MetaEven (decode (vget0 xs)) }

/-
Finally, we can state the main theorem of this example, which says that the
set of positive nonzero even naturals is formally representable over a unary signature.
Namely, with the above system E, the predicate ”Even" provides the desired representation.

This requires us to show the two lemmas:
(i) ('Completeness') for any even number X, "Even(X)" is provable in the system;
(ii) ('Soundness') if "Even(X)" is provable in the system, then X is even.
-/
lemma completeness : ∀ n : Nat,
  MetaEven n → E ⊢ ⟨ [], (EvenAtom (Term.ofKstring (encode n))) ⟩ :=
    by
      intro n hn
      rcases hn with ⟨k, rfl⟩
      -- Perform induction on the sequence of nonzero even naturals
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
            apply encode_of_pos_ne_nil
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

/- Towards proving (ii), we define an interpretation mapping formulas to MetaEven propositions-/

-- We first define evaluations, which ground terms containing variables into K-strings.
def eval {S : EFSSignature}
    (σ : S.V → NonemptyKString S) : Term S → KString S
  | [] => []
  | (Sum.inl k) :: t => k :: eval σ t
  | (Sum.inr x) :: t => (σ x).1 ++ eval σ t

@[simp] lemma eval_concat
  (σ : S.V → NonemptyKString S) (t1 t2 : Term S) :
  eval σ (t1 ++ t2) = eval σ t1 ++ eval σ t2 := by
  induction t1 with
    | nil =>
        simp [eval]
    | cons hd tl ih =>
      cases hd with
        | inl k =>
            simp [eval, ih]
        | inr x =>
            simp [eval, ih]


/-- Evaluating an embedded K-string term just returns that K-string. -/
@[simp] lemma eval_ofKstring
  (σ : S.V → NonemptyKString S) (s : KString S) :
  eval σ (Term.ofKstring s) = s := by
    induction s with
    | nil =>
        simp [Term.ofKstring, eval]
    | cons k ks ih =>
        simpa [Term.ofKstring, eval] using ih

lemma decode_eval_xll (σ : S.V → NonemptyKString S) :
  decode (eval σ (Sum.inr V.x :: Term.ofKstring (encode 2)))
    = decode ((σ V.x).1) + 2 := by
  simp [eval]


/- Interpret an atomic expression of the form EvenX
(where X is a string of l's ) to be true iff [decode] X is even' (i.e. X ∈ EvenAttr) -/
def AtomTrue (A : AtomicFormula S) (σ : S.V → NonemptyKString S) : Prop :=
  match A with
  | ⟨Pred.Even, args⟩ =>
      let t := vget0 args
      MetaEven (decode (eval σ t))

/-'for any expression of the form EvenX1 -> EvenX2,
interpret it to be true iff EvenX1 is true implies EvenX2 is true.'
Here we generalize this to arbitrary formulas (which may have more than one premise).-/
def FormulaTrue (X : Formula S) (σ : S.V → NonemptyKString S) : Prop :=
  match X with
  | ⟨premises, concl⟩ =>
      (∀ A ∈ premises, AtomTrue A σ) → AtomTrue concl σ

/- We first prove that the axioms are always true under this interpretation for any assignment. -/
lemma axioms_true : ∀ ax ∈ E.axioms, ∀ σ, FormulaTrue ax σ := by
  intro ax hax σ
  have h : ax = ax1 ∨ ax = ax2 := by
    -- membership in E.axioms = {ax1, ax2}
    simpa [E] using hax
  cases h with
    | inl h1 =>
      -- h1 : ax = ax1
      rw [h1]
      -- need to show EvenAtom (Term.ofKstring (encode 2)) is true
      simp [FormulaTrue]
      -- There are no premises to ax1, so we just need to show the conclusion is true
      intro _
      simp [ax1, EvenAtom, AtomTrue, MetaEven, decode, vget0, encode]
      -- ⊢ ∃ k, 2 = 2 * (k + 1)
      use 0
    | inr h2 =>
      -- h2 : ax = ax2
      rw [h2]
      /- need to show ⟨[ EvenAtom ([Sum.inr V.x]) ],
       EvenAtom ([Sum.inr V.x] ++ (Term.ofKstring (encode 2)))⟩ is true
      -/
      simp [FormulaTrue]
      -- assume premise is true, show conclusion is true
      intro hprem
      simp [ax2] at hprem ⊢
      rcases hprem with ⟨k, hk⟩
      use k + 1
      -- show decode (eval σ ([Sum.inr V.x] ++ Term.ofKstring (encode 2))) = 2 * (k + 1 + 1)
      -- simplify away vget0/ofFn wrappers
      simp [vget0] at hk ⊢
      rw [decode_eval_xll σ]
      simp [eval] at hk
      -- use assumption from premise to finish
      rw [hk]
      omega


/- Next, we show that provability preserves truth under arbitrary assignments.
This requires some lemmas about assignments and substitutions -/
def variant (σ : S.V → NonemptyKString S) (x : S.V) (u : NonemptyKString S) :
 S.V → NonemptyKString S := fun
                            y => if y = x then u
                            else σ y

lemma eval_subst_eq_eval_update
  (σ : S.V → NonemptyKString S) (x : S.V) (u : NonemptyKString S) (t : Term S) :
  eval σ (Term.subst x u t) = eval (variant σ x u) t := by
  induction t with
    | nil =>
        simp [Term.subst, eval]
    | cons hd tl ih =>
        cases hd with
          | inl k =>
              simp [Term.subst, eval, ih]
          | inr y =>
              simp [eval]
              by_cases hxy : y = x
              · -- case hxy: y = x
                rw [hxy]
                simp [variant]
                rw [← ih]
                simp [Term.subst]
                simpa [Term.ofKstring] using (eval_ofKstring (σ := σ) (s := (u : KString S)))
              · -- case hxy : y ≠ x
                simp [Term.subst]
                simp [variant, hxy]
                rw [← ih]
                simp [eval]

lemma AtomTrue_subst
  (A : AtomicFormula S) (σ : S.V → NonemptyKString S) (x : S.V) (u : NonemptyKString S) :
  AtomTrue (AtomicFormula.subst x u A) σ ↔ AtomTrue A (variant σ x u) := by
    apply Iff.intro
    · intro htrue
      simp [AtomicFormula.subst, AtomTrue] at htrue ⊢
      rcases A with ⟨p, args⟩
      -- in our current signature, there is
      -- only one predicate constructor Pred.Even, so p = Pred.Even.
      cases p; simp at htrue ⊢
      rw [← (eval_subst_eq_eval_update σ x u (vget0 args))]
      simp [vget0] at htrue ⊢
      exact htrue
    · intro htrue
      simp [AtomicFormula.subst, AtomTrue] at htrue ⊢
      rcases A with ⟨p, args⟩
      cases p ; simp at htrue ⊢
      rw [← eval_subst_eq_eval_update σ x u (vget0 args)] at htrue
      simp [vget0] at htrue ⊢
      exact htrue


lemma FormulaTrue_subst
  (X : Formula S) (σ : S.V → NonemptyKString S) (x : S.V) (u : NonemptyKString S) :
  FormulaTrue (Formula.subst x u X) σ ↔ FormulaTrue X (variant σ x u) := by
    simp [Formula.subst, FormulaTrue, AtomTrue_subst]

lemma provable_sound : ∀ {X : Formula S}, (E ⊢ X) → ∀ σ, FormulaTrue X σ := by
  intro X hX
  induction hX with
  -- We show that each proof rule preserves truth.
  | ax hmem =>
      rename_i X
      intro σ
      exact axioms_true X hmem σ
  | rule1 x u h ih =>
      rename_i X
      intro σ
      rw [FormulaTrue_subst]
      exact ih (variant σ x u)
  | rule2 h1 h2 ih1 ih2 =>
      rename_i A C ps
      intro σ
      simp [FormulaTrue] at ih1 ih2 ⊢
      intro hprem
      apply ih2 σ
      · exact ih1 σ
      · exact hprem

lemma soundness : ∀ n : Nat,
  E ⊢ ⟨ [], EvenAtom (Term.ofKstring (encode n)) ⟩ → MetaEven n := by
  intro n hn
  -- pick any valuation; it won’t matter since the term is ground
  let σ0 : S.V → NonemptyKString S := fun _ => ⟨encode 1, by simp [encode]⟩
  -- use provable_sound to get that the formula is true under the assignment
  have htrue := provable_sound hn σ0
  simp [FormulaTrue, EvenAtom, AtomTrue, vget0] at htrue
  exact htrue

theorem MetaEven_formally_representable :
  FormallyRepresentable S EvenAttr := by
    use E
    use Pred.Even
    use rfl
    simp [PredicateRepresents]
    intro X
    -- X : Vector (KString S) 1 (because Even is unary, so Xs a subset of words over K)
    simp [EvenAttr]
    apply Iff.intro
    -- (→) direction: if X ∈ EvenAttr, then Even(Xs) is provable.
    · intro hmem
      simp [Attribute.cast] at hmem
      -- hmem : X ∈ {xs | MetaEven (decode (vget0 xs))}
      -- The result follows from completeness
      have hprov := completeness (decode (vget0 X)) hmem
      simp [EvenAtom, vget0] at hprov
      simp [AtomicFormula.ofKStrings, map_eq_ofFn_head]
      exact hprov
    -- (←) direction: if Even(X) is provable, then X ∈ EvenAttr.
    · intro hprov
      simp [AtomicFormula.ofKStrings] at hprov
      have : MetaEven (decode (vget0 X)) := by
      -- rewrite hprov into the form soundness expects
        have hprov' :
          E ⊢ ⟨[], EvenAtom (Term.ofKstring (encode (decode (vget0 X))))⟩ := by
            simpa [map_eq_ofFn_head] using hprov
        exact soundness (decode (vget0 X)) hprov'
      simp [Attribute.cast]
      exact this

end Example1
