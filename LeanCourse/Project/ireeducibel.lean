import Mathlib
--import Mathlib.LinearAlgebra.FiniteDimensional
--import Mathlib.Data.Polynomial.RingDivision
--import Mathlib.Analysis.SpecialFunctions.Pow --! Warum wird das nicht gefunden https://github.com/leanprover-community/mathlib4/blob/8666bd82efec40b8b3a5abca02dc9b24bbdf2652/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean#L328-L330

open Polynomial


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


open FiniteDimensional Polynomial
open scoped Classical Polynomial
noncomputable def H : Polynomial ℚ := X ^ 3 - (C (6/8) * X) - C (1/8)  -- x^3 - 6/8 x - 1/8

lemma H_degree : natDegree H = 3 := by
  --have h : H = X ^ 3 - ((C (6/8) * X) + C (1/8) ) := by simp_rw[H]; exact sub_sub (X ^ 3) (C (6 / 8) * X) (C (1/8))
  --have h'' : max (natDegree (C (6/8) * X :ℚ[X])) (natDegree (C (1/8))) ≤ 3 := by rw[max_le_iff];  constructor; apply le_trans (b:= 1); apply Eq.le; apply Polynomial.natDegree_C_mul_X (a:= (6/8:ℚ)); simp; norm_num; apply le_trans (b:= 0); apply Eq.le; apply Polynomial.natDegree_C; simp
  --have h' : max (natDegree (X ^ 3:ℚ[X])) (natDegree ((C (6/8) * X) + C (1/8))) ≤ 3 := by rw[max_le_iff]; constructor;  apply Eq.le; apply Polynomial.natDegree_X_pow; sorry --!apply le_trans (Polynomial.natDegree_add_le (p:= ((C (6/8) * X):ℚ[X])) (q:= (C (1/8)))) h''
  --have h₁ : Polynomial.natDegree (p := (C (6/8) * X: ℚ[X])) < Polynomial.natDegree (p:= (X^3 :ℚ[X])) := by simp_rw[Polynomial.natDegree_X_pow]; apply LT.lt.trans_le' (b:= 1); simp; apply Eq.le; apply Polynomial.natDegree_C_mul_X (a:= (6/8:ℚ)); simp
  have h: H = C 1 * X ^ 3 + C 0 * X ^ 2 + C ((- 1) * (6/8)) * X + C ((- 1) * (1/8)) := by rw[H, Polynomial.C_mul (a:= -(1:ℚ)) (b:= (6/8:ℚ)), Polynomial.C_mul (a:= -(1:ℚ)) (b:= (1/8:ℚ))]; simp[Mathlib.Tactic.RingNF.add_neg]
  apply LE.le.antisymm'
  . rw[H]
    simp
    rw[Polynomial.natDegree_sub (p:= (X^3 :ℚ[X])) (q:= ((C (6/8) * X)))]
    apply Eq.le
    simp[Polynomial.natDegree_sub_eq_right_of_natDegree_lt (p:= (C (6/8) * X)) (q:= (X^3 :ℚ[X])), Polynomial.natDegree_X_pow, Polynomial.natDegree_C]
  . simp_rw[h]; apply Polynomial.natDegree_cubic_le  --apply le_trans (Polynomial.natDegree_sub_le (p:= (X^3 :ℚ[X])) (q:= ((C (6/8) * X) + C (1/8)))) h'

lemma HM: Monic H := by
  refine monic_of_natDegree_le_of_coeff_eq_one ?n ?pn ?p1
  . use 3
  . apply Eq.le; apply H_degree
  . rw[H]; simp

lemma H_roots: roots H = 0:= by
  sorry

lemma H_irreducible : Irreducible H := by
  rw[irreducible_iff_roots_eq_zero_of_degree_le_three HM]
  . exact H_roots
  . apply le_trans (b:=3); linarith; apply Eq.le; symm; apply H_degree
  . apply Eq.le; apply H_degree


noncomputable def P : (Polynomial ℚ) := X ^ 3 - C 2 -- x^3 - 2

lemma P_monic: Monic P := by
  refine monic_of_natDegree_le_of_coeff_eq_one ?n ?pn ?p1
  . use 3
  . apply Eq.le; apply Polynomial.natDegree_X_pow_sub_C
  . rw[P]; simp

lemma P_roots: roots P = 0 := by
  refine Multiset.eq_zero_of_forall_not_mem ?_
  simp[P]
  intro a not_zero
  by_contra h
  have f (x:ℝ): x^3 - 2 = 0 ↔ x = 2 ^ (1/3) := by
    calc x^3 - 2 = 0 ↔ x^3 = 2 := by sorry
    _ ↔ (x^3)^ (1/3)  = 2 ^ (1/3):= by sorry
    _ ↔ x = 2 ^(1/3) := by sorry -- apply NNReal.rpow_nat_inv_pow_nat
  have f': Irrational (2 ^ (1/3:ℝ))  := by
    apply irrational_nrt_of_notint_nrt 3 2;
    . simp
      -- apply NNReal.rpow_nat_inv_pow_nat --TODO: Warum wird das nicht gefunden Link Oben
      sorry
    . simp
      intro X
      by_contra kzdtdtdt
      sorry
    simp-- simp[NNReal.rpow_nat_inv_pow_nat]
  have h': a^3 - 2 ≠ 0 := by
    by_contra h'_contra
    rw[f (a:ℝ)] at h'_contra

  contradiction


lemma P_irreducible : Irreducible P := by
  rw[irreducible_iff_roots_eq_zero_of_degree_le_three P_monic]
  . exact P_roots
  . apply le_trans (b:=3); linarith; apply Eq.le; symm; apply Polynomial.natDegree_X_pow_sub_C
  . apply Eq.le; apply Polynomial.natDegree_X_pow_sub_C
