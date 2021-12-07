import tactic 
import linear_algebra.finite_dimensional
import analysis.convex.basic
import analysis.inner_product_space.basic
import analysis.normed_space.is_R_or_C

noncomputable theory
open_locale classical
universes u v

variables (K : Type*) (V : Type*) [is_R_or_C K] [inner_product_space K V]

local notation `⟪`x`, `y`⟫` := @inner K V _ x y
local notation `absR` := has_abs.abs
#print notation

set_option pp.coercions true
set_option pp.notation true
set_option pp.generalized_field_notation true

variables (v w : V)

def switch: V -> V -> V := fun v : V, fun w : V, w - (2*⟪v, w⟫/⟪v,v⟫)•v

#check  ⟪v,w⟫
include K
def double: V -> V := fun v, 2 • v

example (v : V) : double K V v = v + v :=
begin
intros,
rw double,

simp,

have h₁ : 2 • v = v + v := calc
  2 • v = (1 + 1) • v : by triv
  ... = 1•v + 1•v : by rw add_smul
  ... = v + v : by rw one_smul,

rw h₁
end

local notation `s` := switch K V
example (v w u : V) : s (s w v) u = s w (s v u):=
begin
  intros,
  rw switch,
  simp,
  -- rw [switch],
end


theorem mul_zeroree (a : ℝ) : a * 0 = 0 :=
begin
  have h : a * 0 + a * 0 = a * 0 + 0,
  { rw [<-mul_add, add_zero, add_zero] },
  rw add_left_cancel h
end

example (a b c : V) (h1 : a +b = a + c) : b= c:=
begin
intros, 
rw add_left_cancel

end

-- section 


-- def ident {α : Type*} : α → α := fun x, x


-- example {x: ℕ}: ident x = x
-- def maybe := s v u = s u v

-- s_(s_i a_j) = s_i s_j





