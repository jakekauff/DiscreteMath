import .lecture_26
import data.set

namespace relations

section functions

variables {α β γ : Type} (r : α → β → Prop)
local infix `≺`:50 := r

/-
SINGLE-VALUED BINARY RELATION
-/

def single_valued := 
  ∀ {x : α} {y z : β}, r x y → r x z → y = z 

#check @single_valued   -- property of a relation


/-
Exercises: Which of the following are single-valued?
- r = {(0,1), (0,2)}
- r = {(1,0), (2,0)}
- the unit circle on ℝ 
- r = {(-1,0), (0,-1), (1,0), (0,1)}
- y = x^2
- x = y^2
- y = + / - square root x
- f(x) = 3x+1
- y = sin x
- x = sin y
-/

/- FUNCTION

A single-valued binary relation is also called a 
function (sometimes a functional binary relation).
-/
def function := single_valued r

/-
One possible property of a relation, r, is the 
property of being a function, i.e., of r being
single-valued. Single-valuedness is a predicate
on relations. (This idea is isn't definable in
first order predicate logic.)
-/
#check @function  

/-
The same vocabulary applies to functions as to
relations, as functions are just special cases
(single-valued) of otherwise arbitrary binary 
relations.

As with any relation, for example, a function 
has a domain, α, a domain of definition, and a
co-domain, β. As with any relation, the set of 
pairs of a function (that we're specifying) is
is some subset of α × β; or equivalently it is
in the powerset of α × β. 

When you want to express the idea that you have 
an arbitrary relation (possible a function) from
α to β, you may write either of the following:

  - let r ⊆ α × β be any relation from α → β  
  - let r ∈ 𝒫 (α × β) be any relation, α → β 
  - let r : α → β be any binary relation

Be sure you see that these are equivalent 
statements! A key point is that in addition 
to a set of pairs a function (or relation) 
has a domain of definition and a co-domain.
Keeping track of exactly how a set of pairs
relates to its domain and codomain sets is
essential.
-/

/- FOR A RELATION TO BE "DEFINED" FOR A VALUE

Property: We say that a function is "defined" for some
value, (a : α), if there is some (b : β), such that the
pair, (a,b) is "in" r, i.e., (r a b) is true.
-/

def defined (a : α) := ∃ (b : β), r a b

/-
Examples: Which is partial, which is total?

- the positive square root function for x ∈ ℝ (dom def)
- the positive square root function for x ∈ ℝ, x ≥ 0 
-/


/- THE TOTAL vs PARTIAL FUNCTION DICHOTOMY

Property: We say that a function is "total" if it is
defined for every value in its domain. Note that this
usage of the word "total" is completely distinct from
what we learned earlier for relations in general. It's
thus better to use "strongly connected" for relations
to mean every object is related to another in at least
one direction, and to use total to refer to a function 
that is defined on every element of its domain. 
-/

def total_function := function r ∧ ∀ (a : α), defined r a

/-
At this point we expect that for  a total function, r, 
dom_of_def r = domain r. At one key juncture you use
the axiom of set extensionality to convert the goal 
as an equality into that goal as a bi-implication.
After that it's basic predicate logical reasoning,
rather than more reasoning in set theory terms. 
-/

example : total_function r → dom_of_def r = dom r :=
begin
  assume total_r,
  cases total_r with func_r defall,
  unfold dom_of_def,
  unfold dom,
  apply set.ext,
  assume x,
  split,

  -- forwards
  assume h,
  unfold defined at defall,
  unfold defined at defall,
  -- goal completed
  
  -- backwards
  assume h,
  exact defall x,

end

/-
With that proof down as an example, we return to complete
our list of properties of functions: 
  - total
  - partial
  - strictly partial
Here are the definitions for the remaning two.
-/

def strictly_partial_fun := function r ∧ ¬total_function r
def partial_function := function r -- includes total funs

/-
Mathematicians generally consider the set of partial
functions to include the total functions. We will use
the term "strictly partial" function to mean a function,
f, that is not total, where dom_of_def f ⊊ dom f. (Be
sure you see that the subset symbol here means subset
but not equal. That's what the slash through the bottom
line in the symbol means: strict subset.)
-/

/- SURJECTIVE FUNCTIONS

A function that "covers" its codomain (where every value in 
the codomain is an "output" for some value in its domain) 
is said to map its domain *onto* its entire codomain. 
Mathematicians will say that such a function is "onto," 
or "surjective." 
-/

def surjective := 
  total_function r ∧  
  ∀ (b : β), ∃ a : α, r a b

/-
Should this be true?
-/

example : 
  surjective r → 
  image_set r (dom r) = { b : β | true } :=
begin
-- homework (on your own ungraded but please do it!)
end

/-
Which of the following functions are surjective?

- y = log x, viewed as a function from ℝ → ℝ⁺

As written, the question is, um, tricky. Let's 
analyze it. Then we'll give simpler questions.

First a little background on logarithmic and
exponential functions. Simply put, exponentiation
raises a base to an exponent to produce an output,
while the logarithm takes and converts it into 
the exponent to which the base is raised to give
the input. 

From basic algebra, the log (base 10) function,
y = log(x), is defined for any positive real, x,
and is equal to the exponent to which the base
(here 10) must be raised to produce x. Therefore
as usually defined its domain of definition is
the *positive reals* and its co-domain is (*all
of*) the reals.

Now consider the question again. The domain of
definition of log is the positive reals, so if
we expand the domain to all the reals, then the
resulting function becomes partial. On the other
side, if we restrict the range to the positive
reals, then we are excluding from the function
all those values in the interval (0,1) from the
input side in order to restrict the output to
values greater than 0. 

Self homework: Graph this function. 

- λ x, log x : ℝ+ → ℝ, bijective? 
- y = x^2, viewed as a function from ℝ → ℝ 
- y = x, viewed as a function from ℝ → ℝ
- y = sin x, viewed as a function from ℝ → ℝ
- y = sin x, as a function from ℝ to [-1,1] ∈ ℝ

-/

/- INJECTIVE FUNCTION

We have seen that for a relation to be a function, it 
cannot be "one-to-many" (some x value is associated
with more than one y value). On the other hand, it is
possible for a function to associate many x values 
with a single y value. There can be no fan-out from 
x/domain values to y/codomain values, but there can
be fan-in from x to y values.

Which is the following functions exhibits "fan-in",
with different x values associated with the same y
values?

y = x
y = sin x
x = 1 (trick question)
y = 1
y = x^2 on ℝ 
y = x^2 on ℝ⁺ (the positive reals)
-/

def injective := 
  total_function r ∧ 
  ∀ {x y : α} {z : β}, 
    r x z → r y z → x = y
/-
We will often want to know that a function does not
map multiple x values to the same y value. Example:
in a company, we will very like want a function that 
maps each employee to an employee ID number *unique*
to that employee. Rather than being "many to one" we
call such a function "one-to-one." We also say that
such a function has the property of being *injective*.
-/

/-
We will often want to know that a function does not
map multiple x values to the same y value. Example:
in a company, we will very like want a function that 
maps each employee to an employee ID number *unique*
to that employee. Rather than being "many to one" we
call such a function "one-to-one." We also say that
such a function has the property of being *injective*.
There is yet another way to understand the concept.
-/


/- BIJECTIVE FUNCTIONS
-/

/-
Finally, a function is called one-to-one and onto, or
*bijective* if it is both surjective and injective. In
this case, it has to map every element of its domain
-/

def bijective := surjective r ∧ injective r

/-
An essential property of any bijective relation is that 
it puts the elements of the domain and codomain into a
one-to-one correspondence. 

That we've assumed that a function is total is important
here. Here's a counterexample: consider the relation from
dom = {1,2,3} to codom = {A, B} with r = {(1,A), (2,B)}.
This function is injective and surjective but it clearly
does not establish a 1-1 correspondence. 

We can define what it means for a strictly partial function
to be surjective or injective (we don't do it formally here).
We say that a partial function is surjective or injective if
its domain restriction to its domain of definition (making it
total) meets the definitions given above. 

Note that our use of the term, one-to-one, here is
completely distinct from its use in the definition of 
an injective function. An injective function is said
to be "one-to-one" in the sense that it's not many to
one: you can't have f(x) = k and f(y)=k where x ≠ y. 
A one-to-one correspondence *between two sets*, on the 
other hand, is a pairing of elements that associates
each element of one set with a unique single element
of the other set, and vice versa.
-/

/-
Question: Is the inverse of a function always a function.
Think about the function, y = x^2. What is its inverse?
Is it's inverse a function? There's your answer.

A critical property of a bijective function, on the other
hand, is that its inverse is also a bijective function. It
is easy to see: just reverse the "arrows" in a one-to-one
correspondence between two sets. A function who inverse 
is a function is said to be invertible (as a function, as 
every relation has and inverse that is again a relation). 
-/

/-
EXERCISE #1: Prove that the inverse of a 
bijective function is a function. Ok, yes, 
we will work this one out for you! But you
should really read and understand it. Then
the rest shouldn't be too bad.
-/

example : bijective r → function (inverse r) :=
begin
  /-
    Assume hypothesis
  -/
  assume r_bij,

  /-
  Unfold definitions and, from definitions,
  deduce all the basic facts we'll have to
  work with.
  -/
  cases r_bij with r_sur r_inj,
  cases r_inj with r_tot r_one_to_one,
  cases r_sur with r_tot r_onto,
  unfold total_function at r_tot, 
  cases r_tot with r_fun alldef,
  unfold function at r_fun,
  unfold single_valued at r_fun,
  unfold defined at alldef,

  /-
  What remains to be shown is that the
  inverse of r is function. Expanding 
  the definition of function, that means
  r inverse is single-valued. Let's see. 
  -/
  unfold function,
  unfold single_valued,
  /-
  To show that r inverse (mapping β values
  back to α values) r is single-valued, 
  assume that b is some value of type β 
  (in the codomain of r) and show that if 
  r inverse maps b is mapped to both a1 and 
  a2 then a1 = a2.
  -/
  assume b a1 a2 irba1 irba2,
  /-
  Key insight: (inverse r) b a means r a b. 
  In other words, r b a is in r inverse (it
  contains the pair (b, a)) if and only if 
  (a, b) is in r, i.e., r a b.
  -/
  unfold inverse at irba1 irba2,
  /-
  With those pairs now turned around, by the 
  injectivity of r, we're there!
  -/
  apply r_one_to_one irba1 irba2,
end 

/-
Just to set expectations: The reality is that
I explored numerous ways of writing this proof.
Often a first proof will be confusing, messy,
etc. Most proofs of theorems you see in most
mathematics books are gems, polished in their
presentations by generations of mathematicians.
It took me a little while to get to this proof
script and the sequence of reasoning steps and
intermediate proof states it traverses. 
-/


/- INJECTIVE AND SURJECTIVE *PARTIAL* FUNCTIONS

Okay, we actually are now able to to define just
what is means for a *partial* function to be
injective, surjective, bijective, which is that 
it is so when its domain is restricted to its 
domain of definition, rendering it total (at 
which point the preceding definition applies). 
-/

def injectivep := function r ∧ injective (dom_res r (dom_of_def r))
def surjectivep := function r ∧ surjective (dom_res r (dom_of_def r))
def bijectivep := function r ∧ bijective (dom_res r (dom_of_def r))




-- EXERCISE #2: Prove that the inverse of a bijective function is bijective.
example : bijective r → bijective (inverse r) :=
begin
  assume bij_r,
  unfold bijective,
  unfold bijective at bij_r,
  cases bij_r with surj_r inj_r,
  unfold surjective at surj_r,
  unfold injective at inj_r,
  cases surj_r with r_tot r_onto,
  cases inj_r with r_tot r_one_to_one,
  cases r_tot with r_fun alldef,
  unfold function at r_fun,
  unfold single_valued at r_fun,

  apply and.intro _ _,

  unfold surjective,
  unfold total_function,
  split,
  split,
  unfold function,
  unfold single_valued,
  unfold inverse,
  assume b a x rab rxb,
  apply r_one_to_one rab,
  exact rxb,

  assume b,
  apply r_onto b,
  unfold inverse,
  unfold defined at alldef,
  exact alldef,

  unfold injective inverse,
  split, 
  unfold total_function,
  split,
  unfold function,
  unfold single_valued,
  assume b a z rab rzb,
  apply r_one_to_one rab rzb,

  assume b,
  unfold defined at alldef,
  apply r_onto b,

  assume c b a rac rab,
  apply r_fun rac rab,
end


/-
EXERCISE #3: Prove that the inverse of the inverse of a bijective
function is that function.
-/
example : bijective r → (r = inverse (inverse r)) :=
begin
  assume bijr,
  unfold inverse,
end

/-
EXERCISE  #4: Formally state and prove that every injective function 
has a *function* as an inverse.
-/
example : injective r → function (inverse r) :=
  begin
  assume injr,-- hint: remember recent work
  unfold function,
  unfold single_valued,
  cases injr with r_tot r_one_to_one,
  unfold total_function at r_tot,
  unfold function at r_tot,
  unfold single_valued at r_tot,
  unfold defined at r_tot,
  cases r_tot with r_fun alldef,
  assume x y z rxy rxz,
  unfold inverse at rxy,
  unfold inverse at rxz,
  apply r_one_to_one rxy rxz,
  end

/-
EXERCISE #5. Is bijectivity transitive? In other words, if the
relations, s and r, are both bijective, then is the
composition, s after r, also always bijective? Now
we'll see.
-/

open relations    -- for definition of composition

/-
Check the following proposition. True? prove it for all.
False? Present a counterexample.
-/
def bij_trans (s : β → γ → Prop)  (r : α → β → Prop) :
  bijective r → bijective s → bijective (composition s r) := 
  begin
    assume bijr bijs,
    unfold bijective,

    apply and.intro _ _,
    unfold bijective at bijr bijs,
    cases bijr with r_sur r_inj,
    cases bijs with s_sur s_inj,

    unfold surjective,
    unfold total_function,
    unfold function,
    unfold single_valued,
    
    unfold surjective at r_sur s_sur,
    unfold total_function at r_sur s_sur,
    cases r_sur with r_tot r_onto,
    cases s_sur with s_tot s_onto,
    unfold function at r_tot s_tot,
    unfold single_valued at r_tot s_tot,
    cases r_tot with r_fun r_alldef,
    cases s_tot with s_fun s_alldef,

    unfold injective at r_inj s_inj,
    cases r_inj with r_tot r_one_to_one,
    cases s_inj with s_tot s_one_to_one,

    unfold total_function at r_tot s_tot,
    unfold function at r_tot s_tot,
    unfold single_valued at r_tot s_tot,
    unfold defined at r_tot s_tot r_alldef s_alldef,
  
    cases r_tot with r_fun alldef_r,
    cases s_tot with s_fun alldef_s,

    split,
    split,
    
    unfold composition,
    assume x y z,
    assume h i,
    apply exists.elim h,
    apply exists.elim i,

    assume b sbz_rxb,
    assume t sty_rxt,

    have rxb := sbz_rxb.right,
    have rxt := sty_rxt.right,

    have bt := r_fun rxb rxt,

    have sbz := sbz_rxb.left,
    have sty := sty_rxt.left,
    have stz : s t z := eq.subst bt sbz,
    apply s_fun sty stz,

    assume i,
    unfold defined,
    have sr := composition s r,
    have idd := sr i,
    have idd2 := alldef_r i,
    
    unfold composition,
    cases idd2 with beta ribeta,
    have idd3 := alldef_s beta,
    cases idd3 with g sbetag,
    apply exists.intro,
    apply exists.intro,
    apply and.intro sbetag ribeta,

    assume g,
    unfold composition,
    have sr := composition s r,
    have idd := s_onto g,
    cases idd with b sbg,
    have idd2:= r_onto b,
    cases idd2 with a rab,
    apply exists.intro,
    apply exists.intro,
    apply and.intro sbg rab,

    unfold bijective at bijr bijs,
    cases bijr with r_sur r_inj,
    cases bijs with s_sur s_inj,

    unfold injective,
    unfold total_function,
    unfold function,
    unfold single_valued,
    
    unfold surjective at r_sur s_sur,
    unfold total_function at r_sur s_sur,
    cases r_sur with r_tot r_onto,
    cases s_sur with s_tot s_onto,
    unfold function at r_tot s_tot,
    unfold single_valued at r_tot s_tot,
    cases r_tot with r_fun r_alldef,
    cases s_tot with s_fun s_alldef,

    unfold injective at r_inj s_inj,
    cases r_inj with r_tot r_one_to_one,
    cases s_inj with s_tot s_one_to_one,

    unfold total_function at r_tot s_tot,
    unfold function at r_tot s_tot,
    unfold single_valued at r_tot s_tot,
    unfold defined at r_tot s_tot r_alldef s_alldef,

    cases r_tot with r_fun alldef_r,
    cases s_tot with s_fun alldef_s,

    split,
    split,

    unfold composition,
    assume x y z,
    assume h i,
    apply exists.elim h,
    apply exists.elim i,
    assume b sbz_rxb,
    assume t sty_rxt,

    have sbz := sbz_rxb.left,
    have sty := sty_rxt.left,
    
    have rxb := sbz_rxb.right,
    have rxt := sty_rxt.right,

    have bt := r_fun rxb rxt,

    have stz : s t z := eq.subst bt sbz,
    apply s_fun sty stz,

    assume i,
    unfold defined,
    have sr := composition s r,
    have idd := sr i,
    have idd2 := alldef_r i,
    
    unfold composition,
    cases idd2 with beta ribeta,
    have idd3 := alldef_s beta,
    cases idd3 with g sbetag,
    apply exists.intro,
    apply exists.intro,
    apply and.intro sbetag ribeta,

    assume i,
    unfold composition,
    have sr := composition s r,
    assume a g,
    assume e_sbg_rib e_sbg_rab,
    cases e_sbg_rib with b sbg_rib,
    cases e_sbg_rab with t stg_rat,

    have sbg := sbg_rib.left,
    have stg := stg_rat.left,
    
    have rib := sbg_rib.right,
    have rat := stg_rat.right,

    have bt := s_one_to_one sbg stg,

    have rit : r i t := eq.subst bt rib,
    apply r_one_to_one rit rat,
  end

/-
In general, an operation (such as inverse, here) that, 
when applied twice, is the identity, is said to be an
involution. Relational inverse on bijective functions
is involutive in this sense.

A visualization: each green ball here goes to a red
ball there and the inverse takes each red ball right
back to the green ball from which it came, leaving
the original green ball as the end result, as well.
An identity function.
-/

end functions
end relations
