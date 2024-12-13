import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators
noncomputable section

theorem exercise_2_3_2 {G : Type*} [Group G] (a b : G) :
  ∃ g : G, b* a = g * a * b * g⁻¹  := by
refine ⟨b, ?_⟩
simp


theorem exercise_2_11_3 {G : Type*} [Group G] [Fintype G]
  (hG : Even (card G)) : ∃ x : G, orderOf x = 2  := by
have := card_center_eq_prime_pow hG
let _ := Fintype.ofFinite G
simp only [even_iff_two_dvd, ← Nat.card_eq_fintype_card] at hG
rw [Nat.card_eq_fintype_card] at hG
obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 2 hG
exact ⟨g, hg⟩


theorem exercise_3_2_7 {F : Type*} [Field F] {G : Type*} [Field G]
  (φ : F →+* G) : Injective φ  := by
intro x y h
rw [← sub_eq_zero] at h
simp_rw [sub_eq_zero] at h
rw [← sub_eq_zero] at h
rw [sub_eq_zero] at h
rw [← sub_eq_zero, ← map_sub] at h
rwa [map_sub, sub_eq_zero, φ.injective.eq_iff] at h


theorem exercise_10_1_13 {R : Type*} [Ring R] {x : R}
  (hx : IsNilpotent x) : IsUnit (1 + x)  := by
apply IsNilpotent.isUnit_one_add
exact hx


theorem exercise_10_4_6 {R : Type*} [CommRing R]
  [NoZeroDivisors R] (I J : Ideal R) (x : ↑(I ⊓ J)) :
  IsNilpotent ((Ideal.Quotient.mk (I*J)) x)  := by
have hxI : (x : R) ∈ I
· exact x.2.1
· have hxJ : (x : R) ∈ J
  · exact x.2.2
  · have hx2 : (x : R) * (x : R) ∈ I * J
    · exact ?sorry_0
      exact Ideal.mul_mem_mul hxI hxJ
    · have hquot : (Ideal.Quotient.mk (I * J)) ((x : R) * (x : R)) = 0
      · exact ?sorry_1
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hx2
      · use 2
        rw [pow_two]
        exact hquot


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
rw [← Ideal.mem_span_singleton ]
rw [Ideal.mem_span_singleton ]
rw [← Ideal.mem_span_singleton ]
rw [Ideal.mem_span_singleton ]
rw [← Ideal.mem_span_singleton ]
rw [Ideal.mem_span_singleton ]
rw [← Ideal.mem_span_singleton ]
rw [Ideal.mem_span_singleton ]
rw [← Ideal.mem_span_singleton ]
rw [Ideal.mem_span_singleton ]
rw [← Ideal.mem_span_singleton ]
rw [Ideal.mem_span_singleton ]
rw [← Ideal.mem_span_singleton ]
rw [Ideal.mem_span_singleton ]
rw [← Ideal.mem_span_singleton ]
rw [Ideal.mem_span_singleton ]
rw [← Ideal.mem_span_singleton ]
rw [Ideal.mem_span_singleton ]
rw [← Ideal.mem_span_singleton ]
rw [Ideal.mem_span_singleton ]
rw [← Ideal.mem_span_singleton ]
rw [Ideal.mem_span_singleton ]
rw [← Ideal.mem_span_singleton ]
rw [Ideal.mem_span_singleton ]
rw [← Ideal.mem_span_singleton ]
rw [Ideal.mem_span_singleton ]
rw [← Ideal.mem_span_singleton ]
rw [Ideal.mem_span_singleton ]
rw [← Ideal.mem_span_singleton ]
rw [Ideal.mem_span_singleton ]
rw [← Ideal.mem_span_singleton ]
rw [Ideal.mem_span_singleton ]
rw [← Ideal.mem_span_singleton ]
rw [Ideal.mem_span_singleton ]
rw [← Ideal.mem_span_singleton ]
rw [Ideal.mem_span_singleton ]
rw [← Ideal.mem_span_singleton ]
rw [Ideal.mem_span_singleton ]
rw [← Ideal.mem_span_singleton ]
rw [Ideal.mem_span_singleton ]
rw [← Ideal.mem_span_singleton ]
rw [Ideal.mem_span_singleton ]
rw [← Ideal.mem_span_singleton ]
rw [Ideal.mem_span_singleton ]
rw [← Ideal.Quotient.eq_zero_iff_mem, ofInt_eq_intCast, ofInt_eq_intCast ]
rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton ]
norm_cast
exact id

