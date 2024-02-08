import Mathlib

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
    obtain ⟨n, L, H, h₁, h₂, h₃⟩ := h
    sorry

lemma short (M : Set ℂ) (z : ℂ) :
  ¬ (∃ (m : ℕ) ,((2  : ℕ) ^ m : WithBot ℕ) = Polynomial.degree (minpoly (K_zero M) z)) → z ∉ M_inf M := by
    apply Not.imp_symm
    simp
    apply Classfication_z_in_M_inf_2m


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

lemma mini_polynom_dergree_eq_iff (L: Type)[Field L](L₁ L₂: Subfield L)(α : L): (L₁  = L₂) → degree (minpoly L₁ α) = degree (minpoly L₂ α) := by
sorry
--#check IntermediateField.adjoin_le_iff

--! This is are helper lemmas to show irreducibility of polynomials: https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Polynomial.20irreducible/near/412616130
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


--section constructionDoubleCube
noncomputable def P : (Polynomial ℚ) := X ^ 3 - Polynomial.C 2 -- x^3 - 2

lemma P_monic: Monic P := by
  refine monic_of_natDegree_le_of_coeff_eq_one ?n ?pn ?p1
  . use 3
  . apply Eq.le
    apply Polynomial.natDegree_X_pow_sub_C
  . rw[P]
    simp

theorem Z.le_of_succ_le_succ {n m : Int}: LE.le (Int.succ n) (Int.succ m) → LE.le n m := by
  unfold Int.succ
  simp

theorem Z.le_of_lt_succ {m n : Int}: LT.lt m (Int.succ n) → LE.le m n := by
  apply Z.le_of_succ_le_succ

lemma irrational_thirdroot_two: Irrational (2 ^ (1/3:ℝ)) := by
  apply irrational_nrt_of_notint_nrt 3 2
  . simp
    apply Real.rpow_inv_natCast_pow (n:= 3) (x := 2)
    . norm_num
    . simp
  . simp
    intro X
    by_contra h'
    have h'': 2 ^ (1/3:ℝ) < (2:ℝ)  := by
      nth_rewrite 2[←Real.rpow_one 2]
      rw[Real.rpow_lt_rpow_left_iff (x:=2) (y:=(1/3:ℝ)) (z:=(1:ℝ)) (by exact one_lt_two)]
      norm_num
    have h''': (1:ℝ)  < 2 ^ (1/3:ℝ)  := by
      rw[Real.one_lt_rpow_iff (x:=2) (y:=1/3)]
      norm_num
      norm_num
    norm_num at h'
    rw[h'] at h'''
    rw[h'] at h''
    have : (0:ℝ)  < X := by
      apply lt_trans (b:= (1:ℝ) )
      norm_num
      exact h'''
    simp at this
    have g : X ≤ (1:ℕ)  := by
      apply Z.le_of_lt_succ
      simp
      unfold Int.succ
      rw[one_add_one_eq_two]
      norm_cast at h''
    have g' : (1:ℕ)  < X := by norm_cast at h'''
    apply not_lt_of_le g g'
  simp

lemma if_cube_eq_two_irrat(x:ℝ): x ^ 3 = 2 → Irrational x := by
  intro h
  have h₁: 0 ≤ x := by
    rw[←Odd.pow_nonneg_iff (n:=3)]
    rw [h]
    norm_num
    rw[Nat.odd_iff]
    norm_num
  have h₂: x = 2 ^ (3⁻¹:ℝ):= by
    symm; rw[Real.rpow_inv_eq]
    rw[←h]
    norm_cast
    norm_num
    exact h₁
    norm_num
  rw[h₂]
  rw[inv_eq_one_div]
  convert irrational_thirdroot_two

lemma P_roots: roots P = 0 := by
  refine Multiset.eq_zero_of_forall_not_mem ?_
  simp[P]
  intro a _
  by_contra h
  have h': (a:ℝ)^3 = 2 := by
    rw[sub_eq_zero] at h
    norm_cast
  apply if_cube_eq_two_irrat a h'
  simp

lemma P_irreducible : Irreducible P := by
  rw[irreducible_iff_roots_eq_zero_of_degree_le_three P_monic]
  . exact P_roots
  . apply le_trans (b:=3)
    linarith
    apply Eq.le
    symm
    apply Polynomial.natDegree_X_pow_sub_C
  . apply Eq.le
    apply Polynomial.natDegree_X_pow_sub_C

lemma degree_third_root_of_two : Polynomial.degree (minpoly ℚ ((2:ℂ ) ^ (1/3:ℂ))) = 3 := by
  have h: minpoly ℚ ((2:ℂ ) ^ (1/3:ℂ)) = P := by
    symm
    apply minpoly.eq_of_irreducible_of_monic
    case hp1 => exact P_irreducible
    case hp2 =>
      simp[P]
    case hp3 =>
      exact P_monic
  rw[h, P, Polynomial.degree_eq_natDegree]
  norm_cast
  apply natDegree_X_pow_sub_C
  apply Polynomial.X_pow_sub_C_ne_zero
  simp

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
--end constructionDoubleCube


--section constructionAngleTrisection
noncomputable def H : Polynomial ℚ := X ^ 3 - (Polynomial.C (6/8) * X) - Polynomial.C (1/8)  -- x^3 - 6/8 x - 1/8
noncomputable def H' : Polynomial ℚ := Polynomial.C 8 *X ^ 3 - (Polynomial.C 6 * X) - Polynomial.C 1 -- 8x^3 - 6 x - 1

lemma H_degree : natDegree H = 3 := by
  have h: H = Polynomial.C 1 * X ^ 3 + Polynomial.C 0 * X ^ 2 + Polynomial.C ((- 1) * (6/8)) * X + Polynomial.C ((- 1) * (1/8)) := by rw[H, Polynomial.C_mul (a:= -(1:ℚ)) (b:= (6/8:ℚ)), Polynomial.C_mul (a:= -(1:ℚ)) (b:= (1/8:ℚ))]; simp[Mathlib.Tactic.RingNF.add_neg]
  apply LE.le.antisymm'
  . rw[H]
    simp
    rw[Polynomial.natDegree_sub (p:= (X ^ 3)) (q:= ((Polynomial.C (6/8) * X)))]
    apply Eq.le
    simp[Polynomial.natDegree_sub_eq_right_of_natDegree_lt (p:= (Polynomial.C (6/8) * X)) (q:= (X^3 :ℚ[X])), Polynomial.natDegree_X_pow, Polynomial.natDegree_C]
  . simp_rw[h]
    apply Polynomial.natDegree_cubic_le

lemma HM: Monic H := by
  refine monic_of_natDegree_le_of_coeff_eq_one ?n ?pn ?p1
  . use 3
  . apply Eq.le
    apply H_degree
  . rw[H]; simp

lemma H_eq_mul_H' : H = Polynomial.C (1/8) * H' := by
  rw[H, H', mul_sub, mul_sub, ←mul_assoc, ←mul_assoc, one_div, ←Polynomial.C_mul, ←Polynomial.C_mul ]
  norm_num

lemma H'_eq_mul_H : H' = Polynomial.C 8 * H := by
  rw[H_eq_mul_H', ←mul_assoc, ←Polynomial.C_mul]
  simp

lemma H_roots: roots H = 0:= by sorry

lemma H_irreducible : Irreducible H := by
  rw[irreducible_iff_roots_eq_zero_of_degree_le_three HM]
  . exact H_roots
  . apply le_trans (b:=3)
    linarith
    apply Eq.le
    symm
    apply H_degree
  . apply Eq.le
    apply H_degree

lemma exp_pi_ninth : Polynomial.degree (minpoly ℚ (Complex.exp ((Real.pi/3)/3) : ℂ)) = 3:= by
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

variable (α : ℂ)
lemma Angle_not_Trisectable(M := {⟨0,0⟩ ,⟨1,0⟩, Complex.exp (α)}) :
  ∃ (α : ℂ), (Complex.exp (α/3) : ℂ) ∉ M_inf M := by
  use (Real.pi/3)
  exact pi_third_not_in_M_inf M

--end constructionAngleTrisection
