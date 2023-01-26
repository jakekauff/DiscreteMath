import data.set

/-
Exercise: Prove that for any set, L, L ∩ L = L.
-/


example: ∀ {α : Type} (L : set α), L ∩ L = L :=
begin
  intros α L,
  
  apply set.ext _ ,
  assume a,
  split,
  --forward
  assume a,
  cases a,
  exact a_left,
  --backward
  assume ainL,
  exact and.intro ainL ainL,
end

/-
Exercise: Give a formal statement and proof, then an 
English language proof, that the union operator on 
sets is commutative.
-/

-- Formal Statement:
-- The union operator on sets is commutative such that,
-- given two sets X and Y of an arbitrary type, the value
-- a is in set X ∪ Y and in set Y ∪ X. 

-- Formal Proof:
example: ∀ {α :Type} (X Y : set α), X ∪ Y = Y ∪ X :=
begin
  intros α X Y,
  apply set.ext _,
  assume a,
  split,
  -- forward
  assume K,
  cases K with j l,
    apply or.intro_right,
    exact j,
      apply or.intro_left,
      exact l,
  -- backward,
  assume K,
  cases K with j l,
    apply or.intro_right,
    exact j,
      apply or.intro_left,
      exact l,
end

-- English Language Proof:
-- Given an arbitrary type α and sets X and Y of type set α, 
-- a proof that the union operator is commutative is shown. We first
-- assume that α is of an arbitrary type and that sets X and Y are of type
-- set α. Then we prove under these assumptions that for all values a of type 
-- α, a ∈ X ∪ Y ↔ a ∈ Y ∪ X. In the forward direction, we assume 
-- a ∈ X ∪ Y. We can deduce from this that a ∈ X ∨ a ∈ Y. Both cases imply
-- a ∈ Y ∪ X. Next, in the backward direction, we assume a ∈ Y ∪ X. We deduce
-- from case analysis that a ∈ Y ∨ a ∈ X. Both cases imply a ∈ Y ∪ X. QED.

/-
Exercise: Prove that ⊆ is reflexive and transitive.
Give a formal statement, a formal proof, and an English
language (informal) proof of this fact.
-/

-- Formal Statement:
-- The subset or equal operator ⊆  is reflexive and transitive,
-- such that, for set X of arbitrary type α, X ⊆ X.
-- Further, for three sets X, Y, and Z, X ⊆ Y → Y ⊆ Z → X ⊆ Z.

-- Formal Proof:

example: ∀ {α : Type} ( X : set α ), X ⊆ X ∧ ∀ {α : Type} ( X Y Z : set α ), X ⊆ Y → Y ⊆ Z → X ⊆ Z :=
begin
  -- reflexive
  assume α X,
  split,
  assume x,
  assume xinX,
  exact xinX,
  -- transitive
  assume α X Y Z xsubY ysubZ,
  assume x,
  assume xinX,
  have xinY := xsubY xinX,
  have xinZ := ysubZ xinY,
  exact xinZ,
end


-- English Language Proofs:
-- We first prove that ⊆ is reflexive. We assume a set X of an arbitrary type.
-- Next, we apply the theorem of subset reflexivity, which states that a set
-- is a subset of itself. QED.
-- Next, we prove that ⊆ is transitive. We assume sets X Y and Z of an arbitrary
-- type, and that X ⊆ Y and Y ⊆ Z. We then prove X ⊆ Z by assuming an arbitrary
-- value that is in X and showing that a value in X is in Y and thus in Z. QED.
/-
Exercise: Prove that ∪ and ∩ are associative.
Give a formal statement, a formal proof, and an 
English language (informal) proof of this fact.
-/
-- Formal statement
-- The ∪ and ∩ operators are associative, such that for any three sets 
-- X Y and Z of an arbitrary type, (X ∩ Y) ∩ Z = X ∩ (Y ∩ Z) & 
-- (X ∪ Y) ∪ Z = X ∪ (Y ∪ Z)

-- Formal proof

example: ∀ {α : Type} (X Y Z : set α), ((X ∩ Y) ∩ Z) = X ∩ (Y ∩ Z) :=
begin
  assume α X Y Z,
  apply set.ext _,
  assume x,
  split,
  --forward
  assume h,
  cases h with XnY z,
  apply and.intro,
  apply and.elim_left XnY,
    exact and.intro (and.elim_right XnY) z,
  --backward
  assume h,
  cases h with x ynz,
  apply and.intro,
  exact and.intro x (and.elim_left ynz),
    exact and.elim_right ynz,
end

example: ∀ {α : Type} (X Y Z : set α), (X ∪ Y) ∪ Z = X ∪ (Y ∪ Z) :=
begin
  assume α X Y Z,
  apply set.ext _,
  assume x,
  split,
  --forward
  assume h,
  cases h with XuY z,
  cases XuY,
  apply or.intro_left,
  exact XuY,
    apply or.intro_right,
    apply or.intro_left,
    exact XuY,
      apply or.intro_right,
      apply or.intro_right,
      exact z,
  --backward
  assume h,
  cases h,
  apply or.intro_left,
  apply or.intro_left,
  exact h,
    cases h,
    apply or.intro_left,
    apply or.intro_right,
    exact h,
      apply or.intro_right,
      exact h,
end

-- English Language Proofs
-- For an arbitrary type α and sets X Y and Z of the type set α, ∩ is
-- associative (meaning (X ∩ Y) ∩ Z = X ∩ (Y ∩ Z) ) by the theorem of 
-- and associativity. Further, ∪ is associative (meaning 
-- (X ∪ Y) ∪ Z = X ∪ (Y ∪ Z) ) by the theorem of or associativity. QED.
/-
Assignment: read (at least skim) the Sections 1 and 2 of 
the Wikipedia page on set identities: 
https://en.wikipedia.org/wiki/List_of_set_identities_and_relations 
There, , among *many* other facts, you will find definitions 
of left and right distributivity. To complete the remainder
of this assignment, you need to understand what it means for 
one operator to be left- (or right-) distributive over another. 
-/


/-
Exercise: Formally state and prove both formally and 
informally that ∩ is left-distributive over ∩.
-/

-- ∩ is left-distributive over ∩ such that for any three sets
-- X Y and Z of the same arbitrary type, X ∩ (Y ∩ Z) = (X ∩ Y) ∩ (X ∩ Z).

example : ∀ {α : Type} (X Y Z : set α), X ∩ (Y ∩ Z) = (X ∩ Y) ∩ (X ∩ Z) :=
begin
  assume α X Y Z,

  apply set.ext _,
  assume x,
  --apply distrib.cases_on,
  split,
  --forward
  assume h, 
  cases h with w e,
  cases e with g f,
  apply and.intro,
  show x ∈ X ∧ x ∈ Y,
  exact and.intro w g,
    show x ∈ X ∧ x ∈ Z,
    exact and.intro w f,
  
  --backward
  assume h,
  cases h with j a,
  cases a with b o,
  cases j with y t,
  show x ∈ X ∧ x ∈ Y ∧ x ∈ Z,
  exact and.intro b (and.intro t o),
end

-- Informal English Proof
-- We show that ∩ is left-distributive over ∩ such that for three sets
-- X Y and Z of an arbitrary type X ∩ (Y ∩ Z) = (X ∩ Y) ∩ (X ∩ Z). First,
-- we convert the equation to x ∈ X ∩ (Y ∩ Z) ↔ x ∈  (X ∩ Y) ∩ (X ∩ Z).
-- Next, we perform case analysis of the left side to have proofs that x 
-- is in all three sets. Then we apply the and introduction rule to prove that
-- x ∈ X ∧ x ∈ Y ∧ x ∈ Z. In the backward direction, we similarly perform case
-- analysis to come to the same derivation. QED.

/-
Exercise: Formally state and prove both formally 
and informally that ∪ is left-distributive over ∩.
-/

-- ∪ is left-distributive over ∩ such that for any three sets X Y and Z
-- of an arbitrary type, X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z).

example : ∀ {α : Type} (X Y Z : set α), X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z) :=
begin
  assume α X Y Z,
  apply set.ext _,
  assume x,
  
  apply iff.intro _ _,
  -- forward
  assume h,
  cases h,
  apply and.intro,
  show x ∈ X ∨ x ∈ Y,
  apply or.intro_left,
  exact h,
    show x ∈ X ∨ x ∈ Z,
    apply or.intro_left,
    exact h,
      cases h with y z,
      apply and.intro,
      show x ∈ X ∨ x ∈ Y,
      apply or.intro_right,
      exact y,
        show x ∈ X ∨ x ∈ Z,
        apply or.intro_right,
        exact z,

  -- backward
  assume h,
  have XuY := and.elim_left h,
  have XuZ := and.elim_right h,
  cases XuY,
  cases XuZ,
  apply or.intro_left,
  exact XuY,
    apply or.intro_left,
    exact XuY,
    cases XuZ,
      apply or.intro_left,
      exact XuZ,
        apply or.intro_right,
        exact and.intro XuY XuZ,
end

-- English Language:
-- We show that ∪ is left-distributive over ∩, such that for any three sets
-- of the same arbitrary type, X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z). By case analysis,
-- we can see that if x ∈ X ∨ x ∈ Y ∧ x ∈ Z, the following must hold: x ∈ Y ∨ X ∈ Z
-- ∧ x ∈ X ∨ x ∈ Z. In the reverse direction, we similarly perform case analysis. QED.
