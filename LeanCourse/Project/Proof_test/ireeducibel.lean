import Mathlib
--import Mathlib.LinearAlgebra.FiniteDimensional
--import Mathlib.Data.Polynomial.RingDivision
--import Mathlib.Analysis.SpecialFunctions.Pow

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
noncomputable def H' : Polynomial ℚ := C 8 *X ^ 3 - (C 6 * X) - C 1 -- 8x^3 - 6 x - 1

lemma H_degree : natDegree H = 3 := by
  have h: H = C 1 * X ^ 3 + C 0 * X ^ 2 + C ((- 1) * (6/8)) * X + C ((- 1) * (1/8)) := by rw[H, Polynomial.C_mul (a:= -(1:ℚ)) (b:= (6/8:ℚ)), Polynomial.C_mul (a:= -(1:ℚ)) (b:= (1/8:ℚ))]; simp[Mathlib.Tactic.RingNF.add_neg]
  apply LE.le.antisymm'
  . rw[H]
    simp
    rw[Polynomial.natDegree_sub (p:= (X^3 :ℚ[X])) (q:= ((C (6/8) * X)))]
    apply Eq.le
    simp[Polynomial.natDegree_sub_eq_right_of_natDegree_lt (p:= (C (6/8) * X)) (q:= (X^3 :ℚ[X])), Polynomial.natDegree_X_pow, Polynomial.natDegree_C]
  . simp_rw[h]
    apply Polynomial.natDegree_cubic_le

lemma HM: Monic H := by
  refine monic_of_natDegree_le_of_coeff_eq_one ?n ?pn ?p1
  . use 3
  . apply Eq.le
    apply H_degree
  . rw[H]; simp

lemma H_eq_mul_H' : H = C (1/8) * H' := by
  rw[H, H', mul_sub, mul_sub, ←mul_assoc, ←mul_assoc, one_div, ←Polynomial.C_mul, ←Polynomial.C_mul ]
  norm_num

lemma H'_eq_mul_H : H' = C 8 * H := by
  rw[H_eq_mul_H', ←mul_assoc, ←Polynomial.C_mul]
  simp

--!lemma Rational_root_therom_degree3 (a b c d :ℤ)(x:ℚ): a * x^3 + b * x^2 + c * x + d = 0 → ∃ y z : ℤ , divides y d ∧ divides z a ∧ x = y/z := by sorry

lemma H_roots: roots H = 0:= by
  have h: roots H = roots H' := by
    rw[H_eq_mul_H']
    apply Polynomial.roots_C_mul
    norm_num
  rw[h]
  refine Multiset.eq_zero_of_forall_not_mem ?_
  /- simp[H']
  intro a _ -/
  by_contra h
  simp at h
  obtain ⟨a, h, h'⟩ := h
  have h₀: ↑(IsFractionRing.den ℚ h) ∣ Polynomial.leadingCoeff H' := by
    apply den_dvd_of_is_root h'
  have h₁': Polynomial.leadingCoeff H' = 8 := by
    apply Mathlib.Tactic.ComputeDegree.coeff_congr_lhs (m:=3)
    . rw[H']
      norm_num
      rw[Polynomial.coeff_X_of_ne_one (n:=3)]
      norm_num
      apply Polynomial.coeff_C_ne_zero
      norm_num
      norm_num
    . rw[H'_eq_mul_H, mul_comm, Polynomial.natDegree_mul_C]
      symm
      exact H_degree
      simp
  /- have h₁ (h₈: NoZeroDivisors 8): (IsFractionRing.den ℚ h) ∣ 8 := by
    rw[h₁'] at h₀
    apply h₀ -/
 /-  have h₁: (IsFractionRing.den ℚ h) ∣ 8 := by
    rw[h₁'] at h₀
    exact h₀ -/

  /- rw[sub_eq_neg_add, sub_eq_neg_add, ←add_assoc, add_comm, ←add_assoc] at h
  nth_rewrite 1 [add_comm] at h
  rw[←add_assoc, add_comm (-(6 * a)), ←add_zero (8 * a ^3), ← zero_mul (a^2), neg_mul_eq_neg_mul] at h
  nth_rewrite 2 [zero_mul] at h -/

  sorry
/-   rw[Rational_root_therom_degree3 (a:= 8) (b:= 0) (c:= -6) (d:= -1) a ] at h
  simp at h
  have h': 8 * ((-1) ^ 3 / 8 ^ 3:ℚ) + -(6 * (-1 / 8)) + -1 = - 17/64 := by sorry
  rw[h'] at h
  have h'' : (-17:ℚ) / 64 ≠  0 := by norm_num
  contradiction
  exact h
 -/

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


noncomputable def P : (Polynomial ℚ) := X ^ 3 - C 2 -- x^3 - 2

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



  --have g: a = 2 ^(1/3:ℝ) := by sorry
  /-  apply NNReal.rpow_one_div_eq_iff (z:= 3) (x:= 2)
    rw[sub_eq_zero] at h
    exact h -/
  /- symm at h
  rw[eq_sub_iff_add_eq] at h
  simp at h
  have h₁ : (2 ^ (1/3:ℝ)) ^ 3 = 2 := by
    simp
    norm_cast
    apply Real.rpow_nat_inv_pow_nat (n:= 3) (x := 2); norm_num; simp
  norm_cast at h
  norm_cast at h₁
  rw[←h₁] at h
  sorry -/
/-   by_contra h
  have f (x:ℝ): x^3 - 2 = 0 ↔ x = 2 ^ (1/3) := by
    calc x^3 - 2 = 0 ↔ x^3 = 2 := by {
      constructor
      . intro h'
        rw[← sub_eq_zero] at h'
        rw[← sub_eq_zero]
        simp at h'
        exact h'
      . intro h'
        rw[h']
        simp
        }
    _ ↔ (x^3)^ (1/3)  = 2 ^ (1/3):= by
      constructor
      . intro h'
        rw[← h']
      . intro h'
/-         rw[← zpow_left_inj (n:= 3)] at h'
        . simp at h'
          have g: ((X ^ 3) ^ (@Nat.cast ℝ Real.natCast 3 : ℝ)⁻¹) ^ 3  = ((2:ℝ) ^ (@Nat.cast ℝ Real.natCast 3 : ℝ)⁻¹) ^ 3  := by norm_cast; norm_cast at h'; sorry--exact h'
          rw[Real.rpow_nat_inv_pow_nat  (n:= 3) (x := 2)] at g
          exact g
          sorry
        . norm_num
        . apply Multiplicative.linearOrderedCommGroup -/
        sorry
    _ ↔ x = 2 ^(1/3) := by
      simp
      constructor
      . intro h'
        rw[← h']
        symm
        have g: (@HPow.hPow ℝ ℕ ℝ instHPow x 3) ^ (@Nat.cast ℝ Real.natCast 3 : ℝ)⁻¹ = x := by apply Real.pow_nat_rpow_nat_inv (n:= 3) (x := x); sorry; simp
        nth_rewrite 2 [←g]
        norm_cast
      . intro h'
        have g: (@HPow.hPow ℝ ℕ ℝ instHPow x 3) ^ (@Nat.cast ℝ Real.natCast 3 : ℝ)⁻¹ = x := by apply Real.pow_nat_rpow_nat_inv (n:= 3) (x := x); sorry; simp
        norm_cast at g
        norm_cast
        nth_rewrite 1 [g]
        exact h'
  have f': Irrational (2 ^ (1/3:ℝ))  := by
    apply irrational_nrt_of_notint_nrt 3 2;
    . simp
      apply Real.rpow_nat_inv_pow_nat (n:= 3) (x := 2) --TODO: Warum wird das nicht gefunden Link Oben
      . norm_num
      . simp
    . simp
      intro X
      by_contra h'
      have h'': 2 ^ (1/3) < 2 := by norm_num
      have h''': 1 < 2 ^ (1/3:ℝ)  := by
        rw[Real.one_lt_rpow_iff (x:=2) (y:=1/3)]
        norm_num
        norm_num
      sorry
    simp
  have h': a^3 - 2 ≠ 0 := by
    by_contra h'_contra
    --rw[f (a:ℝ)] at h'_contra
    --exact f' h'_contra
    sorry
  contradiction -/

--! X_pow_sub_C_irreducible_of_odd

/- apply X_pow_sub_C_irreducible_of_odd
  . apply Nat.Prime.odd_of_ne_two; exact Nat.prime_three; norm_num
  . intro p p_prime p_div_3 b
    have p_is_three: p = 3 := sorry
    rw[p_is_three]
    simp
    by_contra h
    sorry -/


/- lemma P_irreducible' : Irreducible P := by
  apply X_pow_sub_C_irreducible_of_odd
  . apply Nat.Prime.odd_of_ne_two; exact Nat.prime_three; norm_num
  . intro p p_prime p_div_3 b
    have p_is_three: p = 3 := sorry
    rw[p_is_three]
    simp
    by_contra h
    have h': (b:ℝ)^3 = 2 := by norm_cast
    apply if_cube_eq_two_irrat b h'
    simp
 -/

--lemma H_degree : natDegree H = 3 := by
  --have h : H = X ^ 3 - ((C (6/8) * X) + C (1/8) ) := by simp_rw[H]; exact sub_sub (X ^ 3) (C (6 / 8) * X) (C (1/8))
  --have h'' : max (natDegree (C (6/8) * X :ℚ[X])) (natDegree (C (1/8))) ≤ 3 := by rw[max_le_iff];  constructor; apply le_trans (b:= 1); apply Eq.le; apply Polynomial.natDegree_C_mul_X (a:= (6/8:ℚ)); simp; norm_num; apply le_trans (b:= 0); apply Eq.le; apply Polynomial.natDegree_C; simp
  --have h' : max (natDegree (X ^ 3:ℚ[X])) (natDegree ((C (6/8) * X) + C (1/8))) ≤ 3 := by rw[max_le_iff]; constructor;  apply Eq.le; apply Polynomial.natDegree_X_pow; sorry --!apply le_trans (Polynomial.natDegree_add_le (p:= ((C (6/8) * X):ℚ[X])) (q:= (C (1/8)))) h''
  --have h₁ : Polynomial.natDegree (p := (C (6/8) * X: ℚ[X])) < Polynomial.natDegree (p:= (X^3 :ℚ[X])) := by simp_rw[Polynomial.natDegree_X_pow]; apply LT.lt.trans_le' (b:= 1); simp; apply Eq.le; apply Polynomial.natDegree_C_mul_X (a:= (6/8:ℚ)); simp
