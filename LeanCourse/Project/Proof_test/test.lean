import Mathlib

set_option autoImplicit true
open Polynomial
open FiniteDimensional Polynomial
open scoped Classical Polynomial

--! This is a test whit use using ℂs and instead Complex numbers

def G (z₁ z₂ : ℂ): Set ℂ := {z : ℂ | ∃ r : ℝ, z = ((r : ℂ) * z₁ + 1 - r * z₂)}
def C (z₁ : ℂ) (r : ℝ): Set ℂ := {z : ℂ | (z.re - z₁.re) ^ 2 + ( z.im -  z₁.im) ^ 2 = r}

def Z_one_M (M : Set ℂ) : Set ℂ := {z : ℂ| ∃ z₁ z₂ z₃ z₄ : ℂ,  z ∈ (G z₁ z₂ ∩ G z₃ z₄) ∧ z₁ ≠ z₃ ∧ z₁ ≠ z₄ ∧ z₁ ∈ M ∧ z₂ ∈ M ∧ z₃ ∈ M ∧ z₄ ∈ M}
def Z_two_M (M : Set ℂ) : Set ℂ := {z : ℂ| ∃ z₁ z₂ z₃ z₄ z₅ : ℂ,  z ∈ (G z₁ z₂ ∩ C z₃ (Complex.normSq (z₄ -  z₅))) ∧ z₄ ≠ z₅ ∧  z₁ ∈ M ∧ z₂ ∈ M ∧ z₃ ∈ M ∧ z₄ ∈ M ∧ z₅ ∈ M}
def Z_three_M (M : Set ℂ) : Set ℂ := {z : ℂ| ∃ z₁ z₂ z₃ z₄ z₅ z₆ : ℂ,  z ∈ (C z₁ (Complex.normSq (z₂ -  z₃)) ∩ C z₄ (Complex.normSq (z₅ -  z₆))) ∧ z₁ ≠ z₄ ∧ z₂ ≠ z₃ ∧ z₅ ≠ z₆ ∧ z₁ ∈ M ∧ z₂ ∈ M ∧ z₃ ∈ M ∧ z₄ ∈ M ∧ z₅ ∈ M ∧ z₆ ∈ M}

def Z_M (M : Set ℂ) : Set ℂ := M ∪ Z_one_M M ∪ Z_two_M M ∪ Z_three_M M

def M_I (M : Set ℂ) : ℕ → Set ℂ
  | 0 => M
  | (Nat.succ n) => Z_M (M_I M n)

def M_inf (M : Set ℂ) : Set ℂ := ⋃ n : ℕ, M_I M n

noncomputable def K_zero (M : Set ℂ) : IntermediateField ℚ  ℂ := IntermediateField.adjoin ℚ ({(z : ℂ)  | z ∈ M} ∪ {(starRingEnd ℂ) z  | z ∈ M})

theorem Classfication_z_in_M_inf (M : Set ℂ) (z : ℂ) :
z ∈ M_inf M ↔
  ∃ (n : ℕ) (L : ℕ →  (IntermediateField ℚ ℂ)) (H : ∀ i,  Module (L i) (L (i + 1))),
  z ∈ L n ∧  K_zero M = L 0 ∧ (∀ i < n, FiniteDimensional.finrank (L i) (L (i + 1)) = 2) := by
  constructor
  case mp =>
    intro h
    sorry
  case mpr => sorry


lemma Classfication_z_in_M_inf_2m (M : Set ℂ) (z : ℂ) :
  z ∈ M_inf M →  ∃ (m : ℕ) ,((2  : ℕ) ^ m : WithBot ℕ) = Polynomial.degree (minpoly (K_zero M) z)  := by
    intro h
    rw [Classfication_z_in_M_inf] at h
    sorry

lemma short (M : Set ℂ) (z : ℂ) :
  ¬ (∃ (m : ℕ) ,((2  : ℕ) ^ m : WithBot ℕ) = Polynomial.degree (minpoly (K_zero M) z)) → z ∉ M_inf M := by
    apply Not.imp_symm
    simp
    apply Classfication_z_in_M_inf_2m

def is_complex_rational (z : ℂ) : Prop :=
  ∃ (q : ℚ), z.re = q ∧ z.im = 0

-- Complex.ofReal_rat_cast (h : ∀ x : M, Complex.ofReal_rat_cast x)
lemma K_zero_eq_rational_if_M_sub_Q (M : Set ℂ) (h : M ⊆ Set.range ((↑): ℚ → ℂ)) : K_zero M = ⊥ := by
  apply le_antisymm
  . apply IntermediateField.adjoin_le_iff.mpr
    simp
    constructor
    exact h
    have h': ∀ z ∈ M ,  (starRingEnd ℂ) z = z := by
      intro m hm; rw[Complex.conj_eq_iff_im]
      apply h at hm; simp at hm
      obtain ⟨q, hq⟩ := hm
      rw[←hq]
      simp
    intro y hy
    simp at hy
    obtain ⟨q, hq₁, hq₂⟩ := hy
    rw[←hq₂, h']
    exact h hq₁
    exact hq₁
  . simp

 #check  IntermediateField.adjoin_le_iff.mpr
  --Todo ask how to use this: apply IntermediateField.adjoin_le_subfield or IntermediateField.adjoin_le_iff
--#check IntermediateField.adjoin_le_subfield

lemma mini_polynom_dergree_eq_iff (L: Type)[Field L](L₁ L₂: Subfield L)(α : L): (L₁  = L₂) → degree (minpoly L₁ α) = degree (minpoly L₂ α) := by
sorry

#check IntermediateField.adjoin_le_iff

--! This is are helper lemmas to show irreducibility of polynomials: https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Polynomial.20irreducible/near/412616130

section constructionDoubleCube
noncomputable def P : (Polynomial ℚ) := monomial 3 1 - 2 -- x^3 - 2
noncomputable def P' : (Polynomial ℚ) := X ^ 3 - 2 -- x^3 - 2

lemma P_eqq : P = P' := by simp[P, P']; symm; apply Polynomial.X_pow_eq_monomial


lemma P_irreducible : Irreducible P := by -- X_pow_sub_C_irreducible_of_prime
  sorry

lemma degree_third_root_of_two : Polynomial.degree (minpoly ℚ ((2:ℂ ) ^ (1/3:ℂ))) = 3 := by
  have h: minpoly ℚ ((2:ℂ ) ^ (1/3:ℂ)) = P := by
    symm
    apply minpoly.eq_of_irreducible_of_monic
    case hp1 => exact P_irreducible
    case hp2 =>
      simp[P]
    case hp3 =>
      rw[P_eqq, Polynomial.Monic.def]
      apply monic_X_pow_sub_C
      simp
  rw[h, P_eqq]
  simp[P']
  apply Polynomial.degree_X_pow_sub_C
  linarith


lemma not_mod_eq_imp_not_eq (a b n : ℕ ) (h : ¬ a % n = b % n) : ¬ a = b := by
  intro h'
  rw[h'] at h
  simp at h

lemma third_root_of_two_not_in_M_inf (M := {(0:ℂ),(1:ℂ)}): (2 : ℂ) ^ (1/3: ℂ) ∉ M_inf M := by
  apply short
  simp
  intro x
  have h: ¬ 2 ^ x =  Polynomial.degree (minpoly ℚ ((2:ℂ ) ^ (1/3:ℂ))) := by
    rw[degree_third_root_of_two]
    cases x with
      | zero => simp
      | succ x => norm_cast; rw[pow_succ]; apply not_mod_eq_imp_not_eq (n:= 2); norm_num
  convert h
  simp
  sorry
end constructionDoubleCube


section constructionAngleTrisection
noncomputable def H_monic : Polynomial ℚ := monomial 3 1 - monomial 1 6/8 - 1/8 -- x^3 - 6/8 x - 1/8
noncomputable def H_monic' : Polynomial ℚ := X ^ 3 - 6/8 * X - 1/8 -- x^3 - 6/8 x - 1/8


lemma H_irreducible : Irreducible H_monic := sorry --! Use den_dvd_of_is_root as Rational root theorem

lemma exp_pi_ninth : Polynomial.degree (minpoly ℚ (Complex.exp ((Real.pi/3)/3) : ℂ)) = 3:= by
  have h: minpoly ℚ (Complex.exp ((Real.pi/3)/3) : ℂ) = H_monic := by
    symm
    apply minpoly.eq_of_irreducible_of_monic
    case hp1 => exact H_irreducible
    case hp2 =>
      simp[H_monic]
      sorry
    case hp3 =>
      sorry
  rw[h]
  sorry


lemma pi_third_not_in_M_inf (M := {⟨0,0⟩ ,⟨1,0⟩,  Complex.exp (Real.pi/3) }) :
  (Complex.exp ((Real.pi/3)/3) : ℂ) ∉ M_inf M := by
  apply short
  simp
  intro x
  have h: ¬ 2 ^ x =  Polynomial.degree (minpoly ℚ (Complex.exp (↑Real.pi / 3 / 3))) := by
    rw[exp_pi_ninth]
    sorry
  convert h
  have h': ↥(K_zero M) =  ℚ := by rw[K_zero_eq_rational_if_M_sub_Q M]; sorry; sorry -- optParam is wired
  sorry

lemma Angle_not_Trisectable(M := {⟨0,0⟩ ,⟨1,0⟩, Complex.exp (α)}) :
  ∃ (α : ℂ), (Complex.exp (α/3) : ℂ) ∉ M_inf M := by
  use (Real.pi/3)
  exact pi_third_not_in_M_inf M

end constructionAngleTrisection
