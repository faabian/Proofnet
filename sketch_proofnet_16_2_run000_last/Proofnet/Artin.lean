import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators
noncomputable section

theorem exercise_2_3_2 {G : Type*} [Group G] (a b : G) :
  ∃ g : G, b* a = g * a * b * g⁻¹  := by
use b
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
exact φ.injective


theorem exercise_10_1_13 {R : Type*} [Ring R] {x : R}
  (hx : IsNilpotent x) : IsUnit (1 + x)  := by
rw [← add_sub_cancel_right 1 x ]
simp
have := exercise_3 1 x hx
rw [← add_comm ]
rw [← add_comm ]
rw [← add_sub_cancel_right 1 x ]
simp
rw [← sub_sub_cancel (1 : R) x ]
rw [sub_sub_cancel ]
rw [← add_comm ]
rw [← add_comm ]
rw [← sub_sub_cancel (1 : R) x ]
field_simp
apply IsNilpotent.isUnit_one_add
assumption


theorem exercise_10_4_6 {R : Type*} [CommRing R]
  [NoZeroDivisors R] (I J : Ideal R) (x : ↑(I ⊓ J)) :
  IsNilpotent ((Ideal.Quotient.mk (I*J)) x)  := by
have hxI : (x : R) ∈ I
· exact x.prop.left
· have hxJ : (x : R) ∈ J
  · exact x.prop.right
  · have hx2 : (x : R) * (x : R) ∈ I * J
    · exact ?sorry_0
      exact Ideal.mul_mem_mul hxI hxJ
    · have hquot : (Ideal.Quotient.mk (I * J)) ((x : R) * (x : R)) = 0
      · exact ?sorry_1
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hx2
      · use 2
        calc
  ((Ideal.Quotient.mk (I * J)) x) ^ 2
    = (Ideal.Quotient.mk (I * J)) ((x : R) * (x : R)) := ?sorry_2
  _ = 0 := hquot
        rw [pow_two, ← RingHom.map_mul ]


theorem exercise_11_2_13 (a b : ℤ) :
  (ofInt a : GaussianInt) ∣ ofInt b → a ∣ b  := by
simpa using exercise_12_3_11 a b

