import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators
noncomputable section

theorem exercise_2_3_2 {G : Type*} [Group G] (a b : G) :
  ∃ g : G, b* a = g * a * b * g⁻¹  := by
use b
simp


theorem exercise_3_2_7 {F : Type*} [Field F] {G : Type*} [Field G]
  (φ : F →+* G) : Injective φ  := by
exact φ.injective


theorem exercise_10_1_13 {R : Type*} [Ring R] {x : R}
  (hx : IsNilpotent x) : IsUnit (1 + x)  := by
apply IsNilpotent.isUnit_one_add
assumption


theorem exercise_10_4_6 {R : Type*} [CommRing R]
  [NoZeroDivisors R] (I J : Ideal R) (x : ↑(I ⊓ J)) :
  IsNilpotent ((Ideal.Quotient.mk (I*J)) x)  := by
have hxI : (↑x : R) ∈ I
· exact x.2.left
· have hxJ : (↑x : R) ∈ J
  · exact x.2.right
  · have hx2 : (↑x : R) * (↑x : R) ∈ I * J
    · exact ?sorry_0
      exact Ideal.mul_mem_mul hxI hxJ
    · have hquot : (Ideal.Quotient.mk (I * J)) ((↑x : R) * (↑x : R)) = 0
      · exact ?sorry_1
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hx2
      · use 2
        rw [pow_two]
        exact hquot


theorem exercise_11_2_13 (a b : ℤ) :
  (ofInt a : GaussianInt) ∣ ofInt b → a ∣ b  := by
rw [← intCast_dvd_intCast ]
rw [← Ideal.mem_span_singleton ]
apply Ideal.mem_span_singleton.1

