import .assertion
import .imp
import .var_test

/-
Tests after completion of cmd syntax including if and while
-/

def p1 : cmd :=
IF (bool_expr.eq_expr [X] [0]) -- provide concrete syntax
THEN X = [1]
ELSE X = [2]

/-
Tests before completion of cmd syntax including if and while
-/


-- a little program: X gets overwritten
def program : cmd := 
  X = [7];
  Y = [8];
  Z = [9];
  X = [10]

-- verify that post state is as expected
def post_env := c_eval program init_env 
example : post_env.nat_var_interp X = 10 := rfl
example : post_env.nat_var_interp Y = 8 := rfl
example : post_env.nat_var_interp Z = 9 := rfl

open cmd

def p2 : cmd := IF [tt] THEN (program) ELSE (X=[2]) 
def p3 : cmd := IF [ff] THEN (X=[1]) ELSE (X=[2]) 

example : (c_eval p2 init_env).nat_var_interp X = 10 := rfl
example : (c_eval p3 init_env).nat_var_interp X = 2 := rfl

/-
Claim and prove logically that in "program" 
post state, X = 10.
-/
  theorem t1 : 
    ∀ (post : env), 
    c_sem program init_env post → 
    post.nat_var_interp X = 10 := 
  begin
    assume post,
    assume h,
    cases h,
    cases h_ᾰ_1,
    rw <- h_ᾰ_1_ᾰ,
    cases h_is,
    apply rfl,
  end

-- Exam: fix this proof
  example : 
    ∀ (post : env), c_sem program init_env post → post.nat_var_interp Z = 9 := 
  begin
    assume post,
    assume h,
    unfold program at h,
    cases h,
    cases h_ᾰ,
    cases h_ᾰ_ᾰ_1,
    cases h_ᾰ_1,
    rw <- h_ᾰ_1_ᾰ,
    rw <- h_ᾰ_ᾰ_1_ᾰ,
    unfold Z,
    apply rfl,      -- YOU FIX
  end


-- computational testing
example : (c_eval p2 init_env).nat_var_interp X = 1 := rfl  -- no
example : (c_eval p3 init_env).nat_var_interp X = 2 := rfl  -- yes

-- logical verification

example : 
  ∀ (e e' : env), c_sem p2 e e' → e'.nat_var_interp X = 1 :=
begin
  unfold p2,
  intros,
  cases ᾰ,
  cases ᾰ_ᾰ,  -- impossible case
  cases ᾰ_ᾰ_1,
  rw <- ᾰ_ᾰ_1_ᾰ,
  cases e,
  exact rfl,
end

