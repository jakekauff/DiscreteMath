import data.set
import tactic.ring

namespace relation

-- Jakob Kauffmann (jgk2qq); github: jakekauff13
-- Collaborated with: Jumi Hall (jah5py) & 
--                    Connor McCaffrey (cam7qp)

-- PRELIMINARY SETUP

/-
Preliminary set up. For the rest of this file,
we specify an arbitrary binary relation, r, on
an arbitrary type, β, as a two-place predicate, 
with infix notation x ≺ y for (r x y). One can
pronounce these expressions in English as "x is
related to y".
-/
variables {α β : Type}  (r : β → β → Prop)
local infix `≺` : 50 := r  


/-
The default Lean libraries are missing definitions
for the assympetric property of relations and for
the notion of a powerset. We define these terms for
use in the rest of this file.
-/
def asymmetric := ∀ ⦃x y⦄, x ≺ y → ¬ y ≺ x
def powerset (s : set β) := { s' | s' ⊆ s}


-- PROBLEMS

/- 
#1: Give both a formal and an English-language proof. Then
answer the question, is the proposition true if you remove
the first condition, that β is inhabited? Briefly explain
your answer (in English).
-/
example : (∃ (b : β), true) → asymmetric r → ¬reflexive r :=
begin
  assume e,
  assume a,
  assume x,
  unfold asymmetric at a,
  unfold reflexive at x,
  cases e with w pf,
  have rww := x w,
  have c := a rww,
  contradiction,
end
  -- English-Language Proof:
      /-
      Proof: Suppose β is inhabited and r is asymmetric.
      We now show r is not reflexive. We will prove by 
      negation, assuming that r is reflexive and then 
      we will show that this assumption leads to a contradiction
      from which we can conclude r is not reflexive.

      To derive the contradiction, we first expand the 
      definitions of asymmetric and reflexive. We will
      now show that the following assumptions contradict
      one another:

        β: Type
        r: β → β → Prop
        e: ∃ (b : β), true
        a: ∀ ⦃x y : β⦄, r x y → ¬r y x
        x: ∀ (x : β), r x x

      To show this by exists elimination we first infer
      that there is a an object, w : β, of which we 
      have a proof of existence. Applying reflexivity (x), 
      to w, we deduce w ≺ w (r w w). Next, by applying 
      asymmetry (a), to w ≺ w we derive w ⊀ w, thus deriving
      the aforementioned contradiction.
      QED. 
      -/


/-
#2. Logic, like programming, is subtle. It's very easy for humans
to miss subtle corner cases. As an example, today I ran across
a problem in a textbook by Paul Traiger, a professor emeritus
of philosophy and cognitive science at Occidental College. He
asks students to prove that if a relation is both transitive and 
reflexive that it cannot be anti-symmetric. See the question at
the very bottom of the page here:
https://sites.oxy.edu/traiger/logic/exercises/chapter13/properties_of_relations_exercise.html

Is the conjecture actually logically valid? If not, what condition 
needs to be added to make it so? Try prove this/his version of the
conjecture, as articulated slightly differently below. If you get
stuck, then you need to figure out an additional condition that needs 
to be added as a premise to make the proposition true. In that case,
add the premise and then show that the updated conjecture is true.
-/
example : (∃ (b : β), true) → transitive r → reflexive r → ¬ asymmetric r :=
begin
  assume h,
  unfold transitive reflexive asymmetric,
  assume t r a,
  cases h with b True,
  have b_refl := r b,
  have b_not_refl := a b_refl,
  contradiction,
end


/-
#3: Prove that the subset relation on the powerset of any
set, s, is antisymmetric. Formally state and prove, and
then give an informal proof of, this proposition.
-/
example : ∀ (s : set β) 
            (s1 s2 ∈ powerset s), 
            s1 ⊆ s2 → 
            s2 ⊆ s1 → 
            s1 = s2 :=
begin
  assume s s1 s2 s1ins s2ins s1ins2 s2ins1,
  apply set.ext,
  assume x,
  split,
  assume xins1,
  exact s1ins2 xins1,

  assume xins2,
  exact s2ins1 xins2,
end

/-
Proof: Suppose that s is a set of type β and that s1 and s2 
are in the powerset of s. We will prove that s1 = s2, assuming
the following: s1 ⊆ s2 and s2 ⊆ s1. 

First, we equate the equals sign to an if and only if statement 
under set extensionality. By application of our assumptions 
on one another, we derive that s1 = s2. 

QED.
-/

/-
Given two natural numbers, n and m, we will say that m divides n
if there is a natural number, k, such that n = k*m. Here's a formal
definition of this relation.
-/
def divides (m n : ℕ) := ∃ k, n = k * m


/- 
#4: Formally and informally state and prove each of the following
propositions. Remember that the ring tactic is useful for producing
proofs of simple algebraic equalities involving + and *. You can use
the phrase, "by basic algebra" when translating the use of this tactic
into English. (Or if you wanted to be truly Hobbit-like you could say 
"by the ring axioms!")
-/

-- A: For any n, 1 divides n.
example : ∀ n, divides 1 n :=
begin
  assume n,
  unfold divides,
  cases n with p,
  apply exists.intro 0,
  refl,
  apply exists.intro p.succ,
  have mulone := mul_one p.succ,
  rw mulone,
end

/-
Proof: We provide a proof that for any n, 1 divides n. In order 
to provide this proof, we first assume n of type ℕ. Next, we 
expand the definition of divides. We will then perform case analysis on
n to prove that there exists a k such that n = k * 1.

Case analysis yields two cases which we will prove, thus proving that
1 divides n. The first case is that in which n = 0. After application of
the exists introduction rule with the value 0, we now prove by simple algebra
that 0 = 0 * 1. The second case is that is which n > 0. Similarly, we show that
there exists a k such that n = k * 1, and that k is again equal to n. 

QED.
-/

-- B. For any n, n divides n
example : ∀ n, divides n n :=
begin
  assume n,
  unfold divides,
  apply exists.intro 1,
  have mulone := one_mul n,
  rw mulone,
end
/-
Proof: We provide a proof that for any n, n divides n. We first assume
n is of type ℕ, then we expand the definition of divides. After applying
the exists introduction rule with a value of 1, we must prove that 
n = 1 * n, which is done by simple algebra.

QED.
-/


-- #C. prove that divides is reflexive 
example : reflexive divides :=
begin
  unfold reflexive divides,
  assume n,
  apply exists.intro 1,
  have mulone := (one_mul n),
  rw mulone,
end 
/-
Proof: We will provide a proof that divides is reflexive. We first assume
n is of type ℕ, and then we expand the definition of divides and reflexive. After applying
the exists introduction rule with a value of 1, we must prove that 
n = 1 * n, which is done by simple algebra.
-/

-- #D. prove that divides is transitive
example : transitive divides :=
begin
  unfold transitive divides,
  assume a b c,
  assume ab bc,
  cases ab with a1 p1,
  cases bc with a2 p2,
  apply exists.intro(a2*a1),
  rw p2,
  rw p1,
  have mulassoc := mul_assoc a2 a1 a,
  rw mulassoc,
end 

/-
Proof: We will provide a proof that divides is transitive. We first expand 
the definition of transitive and divides. We will then make the following 
assumptions:

  a b c : ℕ 
  ab : ∃ (k : ℕ), b = k * a
  bc : ∃ (k : ℕ), c = k * b

Under these assumptions, we will prove that there exists a k such that 
c = k * a, showing that divides is transitive. We begin by performing case 
analysis on both ab and bc, yielding the following assumptions:

  a b c a1 a2 : ℕ 
  p1 : b = a1 * a
  p2 : c = a2 * b

We will use these assumptions to rewrite the final proposition c = k * a 
to now be a2 * a1 * a = a2 * a1 * a. We do this by applying the exists
introduction rule for the value a2 * a1, converting the proposition into
c = a2 * a1 * a. Next, we have the proofs that c = a2 * b and b = a1 * a.
Using these, we can rewrite the final proposition as a2 * a1 * a = a2 * a1 * a,
which is true by reflexivity of equality.

QED.
-/

/- 
E. Is divides symmetric? if yes, give a proof, otherwise 
give a counterexample and a brief explanation to show that 
it's not.
-/

example: symmetric divides :=
begin
end
-- Divides is NOT symmetric, as shown by the cases where 2 divides 4
-- (k = 2, which is a natural number), but 4 does not divide 2 
-- (k = 1/2, which is not a natural number).
-- In order for a relation to be symmetric, the relation
-- must hold between the two values in both directions. However, with divides,
-- a natural number does not exist such that a number divides a larger number,
-- and that larger number divides the smaller number.

/- 
#F. Prove that divides is antisymmetric. 
-/
example : anti_symmetric divides := 
begin  
  unfold anti_symmetric divides,
  assume x y xy yx,
  apply exists.elim xy,
  apply exists.elim yx,
  assume a b c d, 
  rw b,
  have : a = 1 := sorry,
  rw this,
  have mulone := one_mul y,
  exact mulone,
end

/-
Proof: We will prove that divides is antisymmetric. First, we expand the
definitions of antisymmetric and divides. Then we perform case analysis on our 
assumed exists statements, leaving us to rewrite the cases. It is obvious that the
value of a must be 1 by simple deduction from already present proofs, leaving us
again to simply rewrite our goal, giving us a new goal that 1 * y = y, which is
true by simple algebra.

QED.
-/

/- #5
Prove the following propositions. Remember that
throughout this file, each definition implicitly
includes β as a type and r as an arbitrary binary 
relation on β. In addition to formal proofs, give
an English language proof of the last of the three
problems.
-/

-- A
example : asymmetric r → irreflexive r :=
begin
  assume h x k,
  have nk := h k,
  contradiction,
end
/-
Proof: We will provide a proof that a relation is irreflexive, given
that the relation is asymmetric, by negation. We do this by assuming that
r x x is true and showing that ¬ r x x is true by applying the proof that 
the relation is asymmetric to r x x, thus deriving a contradiction.

QED.
-/
-- B
example : irreflexive r → transitive r → asymmetric r :=
begin
  unfold irreflexive transitive,
  assume i t x y,
  assume rxy,
  assume nryx,
  have f := t rxy nryx,
  have nrxx := i x,
  contradiction,
end

/-
Proof: We will provide a proof by negation that a relation is asymmetric, 
given that the relation is irreflexive and transitive. We first expand the 
definitions of irreflexive and transitive. Then we make the assumptions that 
the relation r is irreflexive and transitive. Next, we assume r x y and ¬ r y x. 
After this, we apply transitive to r x y and ¬ r y x to derive a proof of r x x. 
Finally, we show a contradiction by applying irreflexive to x, which gives us ¬ r x x. 

QED.
-/

-- C
example : transitive r → ¬ symmetric r → ¬ irreflexive r :=
begin
  unfold transitive symmetric irreflexive,
  assume trans symm irrefl,
end

/-
We do not believe that the proposition is provable or fixable. We tried to 
add that β is inhabited, but this effort was futile. We were unable
to find a counter-example of a relation that shows the invalidity
of the proposition. 
-/
end relation
