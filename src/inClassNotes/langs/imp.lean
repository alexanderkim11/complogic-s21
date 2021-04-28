import .arith_expr
import .bool_expr

/-
A little PL in which we have mutable
state and an update (assignment) operation.
-/

/-
We don't have mutable state in a pure functional language
-/
def x := 1
-- def x := 2


-- structure avar : Type := (idx : nat)

def X := avar.mk 0
def Y := avar.mk 1
def Z := avar.mk 2

def init : a_state := λ (v : avar), 0

/-
{ (X,0), (Y,0), (Z,0), ... }  st
X = 7;
{ (X,7), (Y,0), (Z,0), ... } st'
Y = 8
{ (X,7), (Y,8), (Z,0), ... } st'' 
Z = 9
{ (X,7), (Y,8), (Z,9), ... } st'''
X = 10
{ (X,10), (Y,8), (Z,9), ... } st'''


Π (v : avar), if v = X then st' v = 7 else st' v = st v
-/

def var_eq : avar → avar → bool 
| (avar.mk n1) (avar.mk n2) := n1 = n2 


def override : a_state → avar → aexp → a_state 
| st v exp := 
    λ (v' : avar), 
      if (var_eq v v') 
      then (aeval exp st) 
      else (st v')


def st' := override init X [7]

#eval st' X
#eval st' Y
#eval st' Z

def st'' := override st' Y [8]

#eval st'' X
#eval st'' Y
#eval st'' Z

def st''' := override st'' Z [9]

#eval st''' X
#eval st''' Y
#eval st''' Z
 

 def st'''' := override st''' X [10]

#eval st'''' X
#eval st'''' Y
#eval st'''' Z


inductive cmd : Type
| skip 
| assn (v : avar) (e : aexp) 
| seq (c1 c2 : cmd) : cmd
-- | cond (b : bool_expr) (c1 c2 : cmd) : cmd
-- | while (b : bool_expr) (c : cmd) : cmd

open cmd

notation v = a := assn v a 
notation c1 ; c2  := seq c1 c2 


def a1 : cmd := X = [7]
def a2 := Y = [8]
def a3 := Z = [9]
def a4 := X = [10]

def program : cmd := -- a1; a2; a3; a4
  X = [7];
  Y = [8];
  Z = [9];
  X = [10];
  skip



def c_eval : cmd → a_state → a_state
| skip st := st
| (v = e) st  := override st v e
| (c1 ; c2)st  := c_eval c2 (c_eval c1 st) 

/-
We implement assignment using function override,
converting a given (initial) state into a new state
by binding a given variable to the value of a given
arithmetic expression.

We implement sequential composition of c1 and c2 by 
evaluating c2 in the state obtained by evaluating
c1 in the given (initial) state. Note that c1 and
c2 can each themselves be complex programs (in our
little language).
-/


def res := c_eval program init

#reduce res X
#reduce res Y
#reduce res Z

-- Yay!


inductive c_sem : cmd → a_state → a_state → Prop
| c_sem_skip : ∀ (st : a_state), 
    c_sem skip st st

| c_sem_assm :
  ∀ (pre post : a_state) (v : avar) (e : aexp),
    (override pre v e = post) → 
    c_sem (v = e) pre post

| c_sem_seq :
  ∀ (pre is post : a_state) (c1 c2 : cmd),
  c_sem c1 pre is → 
  c_sem c2 is post →
  c_sem (c1 ; c2) pre post

  /-
  {pre}
  (c1
  {is}
  c2) 
  {post}
  -/


-- proof broken because we added skip at end of "program"
  theorem t1 : 
    ∀ (post : a_state), c_sem program init post → post X = 10 := 
  begin
    assume post,
    assume h,
    unfold program at h,
    cases h,
    cases h_ᾰ_1,
    rw <- h_ᾰ_1_ᾰ,
    apply rfl,
  end

-- here we fix it
  theorem t2 : 
    ∀ (post : a_state), c_sem program init post → post X = 10 := 
  begin
    assume post,
    assume h,
    unfold program at h,
    cases h,
    cases h_ᾰ_1,
    cases h_ᾰ,
    cases h_ᾰ_ᾰ_1,
    rw <- h_ᾰ_ᾰ_1_ᾰ,
    apply rfl,
  end

-- program broken because we added skip at end of "program"
-- homework: you fix it
  example : 
    ∀ (post : a_state), c_sem program init post → post Z = 9 := 
  begin
    assume post,
    assume h,
    unfold program at h,
    cases h,
  _
  end