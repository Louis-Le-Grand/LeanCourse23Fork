--Zulip: https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Degree.20polynomial.20Q.5BX.5D.20.3D.20K.5BX.5D/near/420593608

import Mathlib

noncomputable def K_zero (M: Set ℂ): IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (M ∪ {(starRingEnd ℂ) z  | z ∈ M})
noncomputable def K_zero_P : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {(0:ℂ),(1:ℂ)}

-- What if have showed and want to use
lemma K_zero_eq_rational_if_M_sub_Q (M : Set ℂ) (h : M ⊆ Set.range ((↑): ℚ → ℂ)) : K_zero M = ⊥ := by sorry

lemma K_zero_P_eq_bot : K_zero_P = ⊥ := by
  rw [← K_zero_eq_rational_if_M_sub_Q {0,1}]
  · rw [K_zero_P, K_zero]; congr
    convert (Set.union_self _).symm using 2
    ext; simp [eq_comm]
  rintro _ (rfl|rfl)
  exacts [⟨0, by simp⟩, ⟨1, by simp⟩]

section
variable {M N F} [Monoid M] [Monoid N] [EquivLike F M N] [MulEquivClass F M N] (f : F) {m : M}

theorem map_isUnit_iff : IsUnit (f m) ↔ IsUnit m :=
  ⟨by convert ← IsUnit.map (MulEquivClass.toMulEquiv f).symm; apply EquivLike.left_inv, IsUnit.map f⟩

theorem map_irreducible_iff : Irreducible (f m) ↔ Irreducible m := by
  simp_rw [irreducible_iff, (EquivLike.surjective f).forall, ← map_mul, (EquivLike.injective f).eq_iff, map_isUnit_iff]

end

-- `IsDomain R` can probably be removed using docs#minpoly.unique
theorem minpoly.map_of_isScalarTower (A K) {R} [Field A] [Field K] [Ring R] [IsDomain R] [Algebra A K]
    [Algebra A R] [Algebra K R] [IsScalarTower A K R] (h : Function.Bijective (algebraMap A K)) (x : R) :
    minpoly K x = (minpoly A x).map (algebraMap A K) := by
  by_cases h0 : IsIntegral A x
  · symm; apply minpoly.eq_of_irreducible_of_monic
    · rw [show algebraMap A K = RingEquiv.ofBijective _ h from rfl, ← Polynomial.mapEquiv_apply, map_irreducible_iff]
      exact minpoly.irreducible h0
    · simp
    · exact (minpoly.monic h0).map _
  · rw [minpoly.eq_zero h0, Polynomial.map_zero]
    exact minpoly.eq_zero (mt (isIntegral_trans (Algebra.isIntegral_of_surjective h.surjective) _ ·) h0)

lemma H : Polynomial.degree ((minpoly ↑K_zero_P) (2 ^ (3:ℂ)⁻¹ :ℂ)) = Polynomial.degree (minpoly ℚ (2 ^ (3:ℂ)⁻¹ :ℂ)) := by
  rw [minpoly.map_of_isScalarTower ℚ K_zero_P, Polynomial.degree_map]
  rw [K_zero_P_eq_bot]
  exact (IntermediateField.botEquiv ℚ ℂ).symm.bijective
