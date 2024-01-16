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

noncomputable def K_zero (M : Set ℂ) : IntermediateField ℚ  ℂ := IntermediateField.adjoin ℚ ({(z : ℂ)  | z ∈ M} ∪ {(z.re - z.im : ℂ)  | z ∈ M})

lemma r_in_M_inf_sprt_r_in_M (M : Set ℂ) (r : ℂ) (h : r ∈ M_inf M) : (r^(1/2)) ∈ M_inf M := by
  sorry

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
  z ∈ M_inf M ↔ ∃ (m : ℕ) ,((2  : ℕ) ^ m : WithBot ℕ) = Polynomial.degree (minpoly (K_zero M) z) := by
  constructor
  case mp =>
    intro h
    rw [Classfication_z_in_M_inf] at h
    sorry
  case mpr => sorry

def is_complex_rational (z : ℂ) : Prop :=
  ∃ (q : ℚ), z.re = q ∧ z.im = 0

lemma K_zero_eq_rational_if_M_sub_Q (M : Set ℂ) (h : M ⊆ {z : ℂ | is_complex_rational z}) : K_zero M = ℚ := by
  sorry
  --Todo ask how to use this: apply IntermediateField.adjoin_le_subfield or IntermediateField.adjoin_le_iff
--#check IntermediateField.adjoin_le_subfield

/- --! This is are helper lemmas to show irreducibility of polynomials: https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Polynomial.20irreducible/near/412616130
theorem irreducible_iff_lt_natDegree_lt {R} [CommSemiring R] [NoZeroDivisors R]
    {p : R[X]} (hp : p.Monic) (hp1 : p ≠ 1) :
    Irreducible p ↔ ∀ q, Monic q → natDegree q ∈ Finset.Ioc 0 (natDegree p / 2) → ¬ q ∣ p := by
  rw [hp.irreducible_iff_natDegree', and_iff_right hp1]
  constructor
  · rintro h g hg hdg ⟨f, rfl⟩
    exact h f g (hg.of_mul_monic_left hp) hg (mul_comm f g) hdg
  · rintro h f g - hg rfl hdg
    exact h g hg hdg (dvd_mul_left g f)

theorem irreducible_iff_roots_eq_zero_of_degree_le_three {R} [CommRing R] [IsDomain R]
    {p : R[X]} (hp : p.Monic)
    (hp2 : 2 ≤ p.natDegree) (hp3 : p.natDegree ≤ 3) : Irreducible p ↔ p.roots = 0 := by
  rw [irreducible_iff_lt_natDegree_lt hp]; swap
  · rintro rfl; rw [natDegree_one] at hp2; cases hp2
  have hp0 : p ≠ 0 := by rintro rfl; rw [natDegree_zero] at hp2; cases hp2
  simp_rw [show p.natDegree / 2 = 1 from (Nat.div_le_div_right hp3).antisymm
    (by apply Nat.div_le_div_right (c := 2) hp2), show Finset.Ioc 0 1 = {1} from rfl,
    Finset.mem_singleton, Multiset.eq_zero_iff_forall_not_mem, mem_roots hp0, ← dvd_iff_isRoot]
  refine ⟨fun h r ↦ h _ (monic_X_sub_C r) (natDegree_X_sub_C r), fun h q hq hq1 ↦ ?_⟩
  rw [hq.eq_X_add_C hq1, ← sub_neg_eq_add, ← C_neg]; apply h
 -/

section constructionDoubleCube
noncomputable def P : (Polynomial ℚ) := monomial 3 1 - 2 -- x^3 - 2
noncomputable def P' : (Polynomial ℚ) := X ^ 3 - 2 -- x^3 - 2

lemma P_eqq : P = P' := by simp[P, P']; symm; apply Polynomial.X_pow_eq_monomial


/- lemma P_irreducible : Irreducible P := by -- Uses X_pow_sub_C_irreducible_of_prime with is to new
  rw[P_eqq]
  apply X_pow_sub_C_irreducible_of_prime
  . apply Nat.prime_three
  by_contra h
  simp at h
  obtain ⟨x,h⟩  := h
  apply irrational_nrt_of_notint_nrt (x := x) (n := 3) (m := 2)
  . norm_cast
  . norm_num
    intro y
    have hx: (x:ℝ) = (2:ℚ) ^ (1/3:ℝ):= by
      calc (x:ℝ) = x ^ (3:ℝ) ^ (1/3:ℝ):= by simp; sorry --!apply Real.pow_nat_rpow_nat_inv
        _ = (2:ℚ) ^ (1/3:ℝ) := by sorry -- cast_real at h; rw[h]
    rw[hx]
    sorry
  . norm_num
  . simp -/


lemma second_P_irreducible : Irreducible P := by -- X_pow_sub_C_irreducible_of_prime
  rw[Polynomial.Monic.irreducible_iff_natDegree']
  . simp
    constructor
    case left => sorry
    case right =>
      intro f g hf hg hfg hdeg
      by_contra h
      have hp : natDegree P = 3 := by sorry
      simp[hp] at h
      have h1 : Polynomial.degree g = 1 := by sorry
      have hnr : ¬ ∃ (x : ℚ), Polynomial.IsRoot P x := by
        rw[←hfg]
        --use x
        --rw[Polynomial.root_mul] --Polynomial.exists_root_of_degree_eq_one
        sorry
      have hr : ∃ (x : ℚ) , Polynomial.IsRoot P x := by
        rw[←hfg]
        sorry
        --exact Polynomial.root_mul (Polynomial.exists_root_of_degree_eq_one  h1)
      sorry
  rw[P_eqq]; rw[Polynomial.Monic.def]; apply monic_X_pow_sub_C; simp

lemma degree_third_root_of_two : Polynomial.degree (minpoly ℚ ((2 : ℝ) ^ (1/3))) = 3 := by
  have h: minpoly ℚ ((2 : ℝ) ^ (1/3)) = P := by
    symm
    apply minpoly.eq_of_irreducible_of_monic
    case hp1 => exact second_P_irreducible
    case hp2 =>
      simp[P]
      have h: ((2:ℝ) ^ (1/3:ℝ)) ^ 3 = 2 := by
        rw [one_div]
        change ((2:ℝ)  ^ (Nat.cast 3)⁻¹) ^ (3:ℝ) = _
        --rw [Real.rpow_nat_inv_pow_nat (show 2 ≥ 0 by norm_num) (show 3 ≠ 0 by decide)] --TODO: Needs Mathlib update
        sorry
      --rw[← one_div, h] --TODO: Needs Mathlib update
      sorry
    case hp3 => rw[P_eqq]; rw[Polynomial.Monic.def]; apply monic_X_pow_sub_C; simp
  rw[h, P_eqq]
  simp[P']
  apply Polynomial.degree_X_pow_sub_C
  linarith


lemma third_root_of_two_not_in_M_inf (M := {⟨0,0⟩ ,⟨1,0⟩}) :
  (⟨(2 : ℝ) ^ (1/3), 0⟩ : ℂ) ∉ M_inf M := by
  rw[Classfication_z_in_M_inf_2m M ⟨(2 : ℝ) ^ (1/3), 0⟩]
  by_contra h
  sorry

end constructionDoubleCube


section constructionAngleTrisection
/- noncomputable def H : Polynomial ℚ := monomial 3 8 - monomial 1 6 - 1 -- 8x^3 - 6x - 1
noncomputable def H' : Polynomial ℚ := 8 * X ^ 3 - 6 * X - 1 -- 8x^3 - 6x - 1 -/
noncomputable def H_monic : Polynomial ℚ := monomial 3 1 - monomial 1 6/8 - 1/8 -- x^3 - 6/8 x - 1/8
noncomputable def H_monic' : Polynomial ℚ := X ^ 3 - 6/8 * X - 1/8 -- x^3 - 6/8 x - 1/8

lemma H_monic_eqq : H_monic = H_monic' := by simp[H_monic, H_monic']; sorry-- apply div_eqq_iff apply Polynomial.X_pow_eq_monomial

lemma H_irreducible : Irreducible H_monic := sorry --! Use den_dvd_of_is_root as Rational root theorem

lemma exp_pi_ninth : Polynomial.degree (minpoly ℚ (Complex.exp ((Real.pi/3)/3) : ℂ)) = 3:=
  have h: minpoly ℚ ((2 : ℝ) ^ (1/3)) = H_monic := by
    symm
    apply minpoly.eq_of_irreducible_of_monic
    case hp1 => exact H_irreducible
    case hp2 =>
      simp[P]
      have h: ((2:ℝ) ^ (1/3:ℝ)) ^ 3 = 2 := by
        rw [one_div]
        change ((2:ℝ)  ^ (Nat.cast 3)⁻¹) ^ (3:ℝ) = _
        --rw [Real.rpow_nat_inv_pow_nat (show 2 ≥ 0 by norm_num) (show 3 ≠ 0 by decide)] --TODO: Needs Mathlib update
        sorry
      --rw[← one_div, h] --TODO: Needs Mathlib update
      sorry
    case hp3 => rw[H_monic_eqq]; rw[Polynomial.Monic.def]; sorry -- apply monic_X_pow_sub_C; simp
  sorry
/-   rw[h, H_monic_eqq]
  simp[H_monic']
  apply Polynomial.degree_X_pow_sub_C
  linarith -/

lemma pi_third_not_in_M_inf (M := {⟨0,0⟩ ,⟨1,0⟩,  Complex.exp (Real.pi/3) }) :
  (Complex.exp ((Real.pi/3)/3) : ℂ) ∉ M_inf M := sorry

lemma Angle_not_Trisectable(M := {⟨0,0⟩ ,⟨1,0⟩, Complex.exp (α)}) :
  ∃ (α : ℂ), (Complex.exp (α/3) : ℂ) ∉ M_inf M := by
  use (Real.pi/3)
  exact pi_third_not_in_M_inf M

end constructionAngleTrisection
