import tactic 
import linear_algebra.finite_dimensional
import algebra.ring.basic
import data.fin.tuple

-- First have integer N

-- Define NxN Cartan Matrix

-- 
-- variables (n : ℕ)
universes u u' v w


variables (n: ℕ) 

def geq1 : Prop := (n > 1)

constant greaterThan0 : geq1 n

-- have n > 1
def finN : Type := fin n
-- Cartan n: ℕ should be ℕ → matrix n n ℤ 
/-- `matrix m n` is the type of matrices whose rows are indexed by `m`
and whose columns are indexed by `n`. -/
-- def matrix (m : Type u) (n : Type u') (α : Type v) : Type (max u u' v) :=
-- m → n → α

-- cartan is like (n : ℕ) (i : n) (j : n) → int
-- variables (Cartan : ℕ ) 
-- def Cartan(n : ℕ) := (n) → (n) → ℤ 

-- type Cartan[n] = n → n → ℤ 
-- def Cartan (n : Type u) : Type (max u )
variables {m: Type*} [fintype m]

def Cartan : Type := (fin n) → (fin n) → ℤ

-- how to prove that `fin n ⊂ ℕ` so `(fin n) → K ⊂ ℕ → K` 

-- instance eq_decidable_fin_n(i : fin n)(k : ℕ) : decidable (i == k) := sorry

def Cartan_C : Cartan(n) 
  := λ i : fin n, λ j :  fin n, 
    if i=j then 2
    else if i.val= 2 then 2
    else if (i.val=0) ∧ (j.val=1) then 2
    -- it cant figure out whether you are allowed to compare `i ∈ fin n` to `0 ∈ ℕ`
    -- the proof should follow from `fin n ⊂ ℕ` but I don't know how to do that
    else if (i.val-j.val= 1) then -1
    else 0



variables {pX : Type*} [comm_ring pX]

def Op (x : Type*) := x → x

 
variable D : fin n → Op pX


variable x : fin n → pX
variable α : fin n → pX
variable s : fin n → Op pX

def y : fin n → pX := λ i, (s i) (x i)

-- define the K_i's first and work backwards?


-- ∀ i, j ∈ (fin n), D i (x j) = δ_i^j
variables {i j : fin n}



def partial_x : Prop := D i (x j) = if (i=j) then 1 else 0 

def switchOnX(h0 : has_zero (fin n))(h1 : has_one (fin n))
  := (s i) (x i) = 
    if (i.val=0) then - x 0 + 2*x 1
    else if (i.val = n-1) then x (n-2) - x (n-1)
    else x (i-1) - x i + x (i+1)


-- def chainer(h0 : has_zero (fin n))(h1 : has_one (fin n)) : fin n → Op pX
-- | zero := D 0
-- | (x+1) := D 0

open nat 

variables {A : Type*} {ops : ℕ  → A → A}
def chain : ℕ → Op A
| zero := ops 0
| (x+1) := ops (x+1) ∘ chain x


open nat

def chainFin : Π {n : ℕ} (ops : fin n → (A → A)), (A → A)
| 0 ops := id
| (n+1) ops := chainFin (fin.init ops) ∘ ops ⟨n, lt_add_one n⟩

-- variables {B : Type*} {opsFin : (fin n)  → B → B}
-- def chainFin(finZero : has_zero (fin n)): (fin n) → Op B
-- | finZero := opsFin finZero
-- | x := opsFin (x-1) ∘ chainFin x



-- need to show that n > 2 and so 0 and 1 are in `fin n`

-- def ree : ℤ → ℤ := λ i, if i=0 then 2 else 4

-- variable Cartan : (n: ℕ) → matrix 
-- def Cartan (n: ℕ) : matrix (fin n) (fin n) int 

-- variables (C : matrix (fin n) (fin n) int)
-- fin n