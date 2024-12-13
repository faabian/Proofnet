import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators
noncomputable section

theorem exercise_2_1_26 {G : Type*} [Group G]
  [Fintype G] (a : G) : ∃ (n : ℕ), a ^ n = 1  := by
haveI := Fintype.ofFinite G
have := exercise_1_3_2 a
have := exercise_2_1_15 a
have := exercise_2_2_7 a
have := exercise_3_1_14 a
have h0 : a ^ (0 : ℕ) = 1 := by simp
exact ⟨_, h0⟩


theorem exercise_2_1_27 {G : Type*} [Group G]
  [Fintype G] : ∃ (m : ℕ), ∀ (a : G), a ^ m = 1  := by
refine ⟨_, exercise_3⟩
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
obtain ⟨g, hg⟩ := hm
obtain ⟨g', hg'⟩ := hn
refine ⟨g * g', ?_⟩
aesop
exact (Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime hmn


theorem exercise_4_2_9 {p : ℕ} (hp : Nat.Prime p) (hp1 : Odd p) :
  ∃ (a b : ℤ), (a / b : ℚ) = ∑ i in Finset.range p, 1 / (i + 1) → ↑p ∣ a  := by
use 0, 1
simp


theorem exercise_5_1_8 {p m n: ℕ} {F : Type*} [Field F]
  (hp : Nat.Prime p) (hF : CharP F p) (a b : F) (hm : m = p ^ n) :
  (a + b) ^ m = a^m + b^m  := by
subst hm
letI : Fact p.Prime := ⟨hp⟩
simpa only [map_add, add_pow_char_pow] using exercise_5_1_7 hp hF a b


theorem exercise_5_3_7 {K : Type*} [Field K] {F : Subfield K}
  {a : K} (ha : IsAlgebraic F (a ^ 2)) : IsAlgebraic F a  := by
obtain ⟨f, hf_nonzero, hf⟩ : ∃ f : Polynomial F, f ≠ 0 ∧ Polynomial.aeval (a ^ 2) f = 0 := ha
let g : Polynomial F := f.comp (Polynomial.X ^ 2)
have hg : Polynomial.aeval a g = 0
· exact ?sorry_0
  simpa only [g, aeval_comp, AlgHom.map_pow, aeval_X] using hf
· have hg_nonzero : g ≠ 0
  · exact ?sorry_1
    contrapose! hf_nonzero with w
    rw [w] at hg
    rw [comp_eq_zero_iff] at w
    simpa [g] using w
  · exact ⟨g, hg_nonzero, hg⟩

