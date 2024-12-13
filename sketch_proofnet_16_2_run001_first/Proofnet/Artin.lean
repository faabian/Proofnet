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
unfold Injective
intro a₁ a₂ h
simpa only [map_sub, sub_eq_zero] using φ.injective h


theorem exercise_10_1_13 {R : Type*} [Ring R] {x : R}
  (hx : IsNilpotent x) : IsUnit (1 + x)  := by
apply IsNilpotent.isUnit_one_add
exact hx


theorem exercise_10_4_6 {R : Type*} [CommRing R]
  [NoZeroDivisors R] (I J : Ideal R) (x : ↑(I ⊓ J)) :
  IsNilpotent ((Ideal.Quotient.mk (I*J)) x)  := by
have hxI : (x : R) ∈ I
· exact x.2.left
· have hxJ : (x : R) ∈ J
  · exact x.2.right
  · have hx2 : (x : R) * (x : R) ∈ I * J
    · exact ?sorry_0
      exact Ideal.mul_mem_mul hxI hxJ
    · have hresidue : (Ideal.Quotient.mk (I * J)) ((x : R) * (x : R)) = 0
      · exact ?sorry_1
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hx2
      · use 2
        rw [pow_two]
        exact hresidue


theorem exercise_11_2_13 (a b : ℤ) :
  (ofInt a : GaussianInt) ∣ ofInt b → a ∣ b  := by
rw [← Ideal.mem_span_singleton ]
rw [← Ideal.mem_span_singleton ]
rw [Ideal.mem_span_singleton ]
rw [← Ideal.mem_span_singleton ]
rw [Ideal.mem_span_singleton ]
rw [← Ideal.mem_span_singleton ]
rw [Ideal.mem_span_singleton ]
rw [← Ideal.mem_span_singleton ]
rw [Ideal.mem_span_singleton ]
rw [Ideal.mem_span_singleton ]
rw [Int.dvd_iff_emod_eq_zero, ← @Int.cast_inj ℝ _ _ ]
simp

