import .var 

-- some arithmetic variables
def X : var nat := var.mk 0
def Y : var nat := var.mk 1
def Z : var nat := var.mk 2

-- some Boolean variables
def P : var bool := var.mk 0
def Q : var bool := var.mk 1
def R : var bool := var.mk 2

-- test our var_eq function
example : var_eq X X = tt := rfl
example : var_eq X Y = ff := rfl