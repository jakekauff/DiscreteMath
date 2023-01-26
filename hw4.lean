-- 1
example : 0 ≠ 1 :=
begin
  -- ¬ (0 = 1)
  -- (0 = 1) → false
  assume h,
  cases h,
end


-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have f : false := h (eq.refl 0),
  exact false.elim (f),
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume (p : P),
  -- ¬¬P
  -- ¬P → false
  -- (P → false) → false
  assume h,
  have f := h p,
  exact f,
end 

-- We might need classical (vs constructive) reasoning 
#check classical.em
open classical
#check em

/-
axiom em : ∀ (p : Prop), p ∨ ¬p

This is the famous and historically controversial
"law" (now axiom) of the excluded middle. It's is
a key to proving many intuitive theorems in logic
and mathematics. But it also leads to giving up on
having evidence *why* something is either true or
not true, in that you no longer need a proof of 
either P or of ¬P to have a proof of P ∨ ¬P.
-/

-- 4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume h,
  have pornp := classical.em P,
  cases pornp with p pn,
  assumption,
  contradiction,
end
#check not.intro 
-- 5

theorem demorgan_1 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  assume P Q,
  apply iff.intro _ _,
  --forward
    intro h,
    by_cases p : P,
    right,
    intro q,
    have pnq : P ∧ Q := and.intro p q,
    apply h pnq,
    left,
    exact p,

  --backward
  assume npornq,
  by_cases p : P,
  by_cases q : Q,
  apply not.intro,
  assume pnq,
  apply or.elim npornq,
    assume np,
    apply np p,
      assume nq,
      apply nq q,
        apply not.intro,
        assume pnq,
        have q1 : Q := and.elim_right pnq,
        apply q q1,
          apply not.intro,
          assume pnq,
          have p1 : P := and.elim_left pnq,
          apply p p1,
end

-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
begin
  assume P Q,
  intro h,
  have pornp := classical.em P,
  have qornq := classical.em Q,
  cases pornp with p np,
    -- p
    have falso := h (or.intro_left _ p),
    exact false.elim falso,
    -- np
    cases qornq with q nq,
      -- q
      have falso := h (or.intro_right _ q),
      exact false.elim falso,
      -- nq
      exact and.intro np nq,
end


-- 7
theorem disappearing_opposite : 
  ∀ (P Q : Prop), P ∨ ¬P ∧ Q ↔ P ∨ Q := 
begin
  --forward
  assume P Q,
  apply iff.intro _ _,
  assume p_or_npandq, 
  apply or.elim p_or_npandq,
  assume p,
  apply or.intro_left,
  exact p,
  assume npandq,
  have q := and.elim_right npandq,
  apply or.intro_right,
  exact q,
  --backward
  assume porq,
  apply or.elim porq,
  assume p,

  apply or.intro_left,
  exact p,
  /-assume q,
  apply or.intro_right,
  apply and.intro,-/
  assume q,
  have pornp := classical.em P,
  apply or.elim pornp,
  assume p,
  apply or.intro_left,
  exact p,
  assume np,
  apply or.intro_right,
  apply and.intro np q,
  

end


-- 8
theorem distrib_and_or : 
  ∀ (P Q R: Prop), (P ∨ Q) ∧ (P ∨ R) ↔
                    P ∨ (Q ∧ R) :=
begin
  intros P Q R,
  apply iff.intro _ _,
  assume h,
  have porq := h.left,
  have porr := h.right,
  cases porq with p q,
    exact or.intro_left _ p,
      cases porr with p r,
        exact or.intro_left _ p,
          exact or.intro_right _ (and.intro q r),
  
  assume h,
  cases h with p qnr, 
    -- p
    exact and.intro (or.intro_left _ p) (or.intro_left _ p),
    -- qnr
    have r := and.elim_right qnr,
    have q := and.elim_left qnr,
    exact and.intro (or.intro_right _ q) (or.intro_right _ r),
end

-- remember or is right associative
-- you need this to know what the lefts and rights are
-- 9
theorem distrib_and_or_foil : 
  ∀ (P Q R S : Prop),
  (P ∨ Q) ∧ (R ∨ S) ↔
  (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) :=
begin
  intros P Q R S,
  apply iff.intro _ _,
    --forward
    assume h,
    have rors := h.right,
    have porq := h.left,
    cases porq with p q,
      -- p
      cases rors with r s,
        -- r within p
        have j := and.intro p r,
        exact or.intro_left _ j,
        -- s within p
        have pands := and.intro p s,
        exact or.intro_right _ (or.intro_left _ pands),
      -- q
      cases rors with r s,
        -- r within q
        have qandr := and.intro q r,
        exact or.intro_right _ (or.intro_right _ (or.intro_left _ qandr)),
        -- s within q
        have qands := and.intro q s,
        have qandr_or_qands := or.intro_right _ qands,
        exact or.intro_right _ (or.intro_right _ qandr_or_qands),
    --backward
    assume h,
    cases h with i j,
      -- case i (P ∧ R)
      have p := and.elim_left i,
      have r := and.elim_right i,
      have porq := or.intro_left _ p,
      have rors := or.intro_left _ r,
      exact and.intro porq rors,
      -- case j ( P ∧ S ∨ Q ∧ R ∨ Q ∧ S)
      cases j with m n,
      -- case m (P ∧ S)
        have p:= and.elim_left m,
        have s := and.elim_right m,
        have rors := or.intro_right _ s,
        have porq := or.intro_left _ p,
        exact and.intro porq rors,
      -- case n (Q ∧ R ∨ Q ∧ S)
        cases n with a b,
        -- case a (Q ∧ R)
          have q := and.elim_left a,
          have r := and.elim_right a,
          have porq := or.intro_right _ q,
          have rors := or.intro_left _ r,
          exact and.intro porq rors,
        -- case b ( Q ∧ S)
          have q := and.elim_left b,
          have s := and.elim_right b,
          have porq := or.intro_right _ q,
          have rors := or.intro_right _ s,
          exact and.intro porq rors,

end


/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
lemma not_all_nats_are_zero : ∀(n : ℕ), (n=0) ∨ (n≠0):=
begin
  assume n,
  apply classical.em,
end 

-- 11. equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) :=
begin
  intros P Q,
  apply iff.intro,
  --forward
    assume h,
    have pornp := classical.em P,
    cases pornp with p np,
    --case p
      have q := h p,
      exact or.intro_right _ q,
    -- case np
      exact or.intro_left _ np,
  --backward
    assume h,
    assume p,
    cases h with np q,
      -- case np
      exact false.elim(np p),
      --case q
      exact q,
end

-- 12
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
  intros P Q,
  assume pimpq,
  assume nq,
  apply not.intro,
  assume p,
  have q := pimpq p,
  exact (nq q),
end

-- 13
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
  intros P Q,
  assume npimpnq,
  assume q,
  have pornp := classical.em P,
  cases pornp with p np,
  -- p
    exact p,
  -- np
    have nq := npimpnq np,
    have falso := nq q,
    exact false.elim falso,
end
