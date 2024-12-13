import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators
noncomputable section

theorem exercise_2_1_26 {G : Type*} [Group G]
  [Fintype G] (a : G) : ∃ (n : ℕ), a ^ n = 1  := by
use (Finset.univ : Finset G).card
exact pow_card_eq_one


theorem exercise_2_1_27 {G : Type*} [Group G]
  [Fintype G] : ∃ (m : ℕ), ∀ (a : G), a ^ m = 1  := by
classical
  refine ⟨Fintype.card G, fun a => ?_⟩
  simpa using pow_card_eq_one a


theorem exercise_2_5_23 {G : Type*} [Group G]
  (hG : ∀ (H : Subgroup G), H.Normal) (a b : G) :
  ∃ (j : ℤ) , b*a = a^j * b := by
let H := Subgroup.closure ({a} : Set G)
have hH : H.Normal
· exact hG H
· have hConjugate : b * a * b⁻¹ ∈ H
  · exact hH.conj_mem a (Subgroup.subset_closure (Set.mem_singleton a)) b
  · have hExists : ∃ (j : ℤ), b * a * b⁻¹ = a^j
    · exact ?sorry_0
      revert hConjugate
      intro h
      rw [Subgroup.mem_closure_singleton] at h
      obtain ⟨n, hn⟩ := h
      exact ⟨_, hn.symm⟩
    · have hRearrange : ∃ (j : ℤ), b * a = a^j * b
      · exact ?sorry_1
        obtain ⟨j, h⟩ := hExists
        refine ⟨j, ?_⟩
        rw [← h, inv_mul_cancel_right ]
      · exact hRearrange


theorem exercise_2_6_15 {G : Type*} [CommGroup G] {m n : ℕ}
  (hm : ∃ (g : G), orderOf g = m)
  (hn : ∃ (g : G), orderOf g = n)
  (hmn : m.Coprime n) :
  ∃ (g : G), orderOf g = m * n  := by
obtain ⟨g, rfl⟩ := hm
obtain ⟨m, rfl⟩ := hn
exact ⟨g * m, (Commute.all g m).orderOf_mul_eq_mul_orderOf_of_coprime hmn⟩


theorem exercise_4_2_9 {p : ℕ} (hp : Nat.Prime p) (hp1 : Odd p) :
  ∃ (a b : ℤ), (a / b : ℚ) = ∑ i in Finset.range p, 1 / (i + 1) → ↑p ∣ a  := by
use 0, 1
simp


theorem exercise_5_1_8 {p m n: ℕ} {F : Type*} [Field F]
  (hp : Nat.Prime p) (hF : CharP F p) (a b : F) (hm : m = p ^ n) :
  (a + b) ^ m = a^m + b^m  := by
subst hm
haveI := hp.charP F
haveI := hp.charP F
have hm := pow_mul a p n p
haveI := hp.charP F
haveI := hp.charP F
have := exercise_5_1_4 hp hF a b
haveI := hp.charP F
have := exercise_5_1_4 hp hF a b
haveI := hp.charP F
haveI := hp.charP F
haveI := hp.charP F
haveI := hp.charP F
haveI : Fact p.Prime := ⟨hp⟩
simpa only [map_add, add_pow_char_pow] using exercise_5_1_7 hp hF a b


theorem exercise_5_3_7 {K : Type*} [Field K] {F : Subfield K}
  {a : K} (ha : IsAlgebraic F (a ^ 2)) : IsAlgebraic F a  := by
rw [← neg_sq] at ha
rw [neg_pow] at ha
simp [neg_mul, one_mul, _pow_two] at ha
rw [← pow_one 2] at ha
rw [pow_one] at ha
simpa [isAlgebraic_iff, ← not_and_or, ← Classical.not_imp, Classical.em,
  and_self_right, isAlgebraic_iff_isIntegral] using ha

