-- https://dl.acm.org/doi/pdf/10.1145/3519935.3519958

import Mathlib

variable (k l : ℕ)
axiom one_lt_k: 1 < k
axiom k_lt_l:  k < l
axiom l_g_indpendent: (ZNum.gcd k l) = 1


noncomputable def Gfun (x y :ℝ) :=
  if 1 ≤ x*y ∧ x*y ≤ k then x*y
  else x*y/k

def GroupK: Type := {x : ℝ // 1 ≤  x ∧ x < k}

@[ext] lemma group_k.ext (x y : GroupK k) (h : x.1 = y.1) : x = y := Subtype.ext h

lemma abgeschlossenheit (x y : GroupK k): 1 ≤ Gfun k x.1 y.1 ∧ Gfun k x.1 y.1 < k := sorry

lemma showGroup_of_GroupK : Group (GroupK k) := by
  refine{
    mul := λ x y => ⟨(Gfun k x.1 y.1 ), (by apply abgeschlossenheit k )⟩
    mul_assoc := sorry
    one := ⟨(1: ℝ), sorry⟩
    one_mul := sorry
    mul_one := sorry
    inv := λ x => ⟨k/x.1, sorry⟩
    mul_left_inv := sorry
  }

--(k l:ℕ)(h₁:1 < k)(h₂ : k < l)(h₃ : (ZNum.gcd k l) = 1)
lemma Ba (R:ℕ): ∃ N > R, ∀ n ≥ N, ∀ r < R, ∃ s>n, ∃ t>0,
  Set.Ico  (l^(-(t:ℤ)) *k^s:ℝ) (l^(-(t:ℤ)) *k^s+k^R) ⊆ Set.Ioc (k^n + k^r:ℝ) (k^n+k^(r+1)) ∧
  ∀ (u v :ℕ) , 1 ≤ v →  v ≤ (t-1) →
  Set.Ioc (l^(-(t:ℤ)) * k^s:ℝ) (l^(-(t:ℤ)) * k^s+k^R) ∩ Set.Ioc (l^(-(v:ℤ))* k^u:ℝ) (l^(-(v:ℤ))* k^u+k^R) = ∅  := by
  sorry
/-   let he: ∃ (E:ℕ), k ^ (-(E:ℤ)) ≤ (1/4:ℚ)
  . sorry
  let hm: ∃ (M:ℕ), l^M > k^(R+E)
  . sorry
  use E  -/
