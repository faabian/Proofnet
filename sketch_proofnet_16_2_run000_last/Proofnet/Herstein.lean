import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators
noncomputable section

theorem exercise_2_1_26 {G : Type*} [Group G]
  [Fintype G] (a : G) : ∃ (n : ℕ), a ^ n = 1  := by
classical
  let a :=(finsetUniv G).toList.get (Finset.mem_univ a)
  have : a ^ (Finset.univ G).toList.length = 1 := by simpa using a.property
  simpa using this
let n := @Fintype.card G
use Finset.univ.lcm orderOf
change a ^ (Finset.univ : Finset G).card = 1
simpa using exercise_1_1_4 a


theorem exercise_2_1_27 {G : Type*} [Group G]
  [Fintype G] : ∃ (m : ℕ), ∀ (a : G), a ^ m = 1  := by
refine ⟨Fintype.card G, fun a => ?_⟩
exact pow_card_eq_one


theorem exercise_2_6_15 {G : Type*} [CommGroup G] {m n : ℕ}
  (hm : ∃ (g : G), orderOf g = m)
  (hn : ∃ (g : G), orderOf g = n)
  (hmn : m.Coprime n) :
  ∃ (g : G), orderOf g = m * n  := by
rcases hm with ⟨g, rfl⟩
rcases hn with ⟨g', rfl⟩
exact ⟨g * g', (Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime hmn⟩


theorem exercise_4_2_9 {p : ℕ} (hp : Nat.Prime p) (hp1 : Odd p) :
  ∃ (a b : ℤ), (a / b : ℚ) = ∑ i in Finset.range p, 1 / (i + 1) → ↑p ∣ a  := by
use 0, p
simp


theorem exercise_5_1_8 {p m n: ℕ} {F : Type*} [Field F]
  (hp : Nat.Prime p) (hF : CharP F p) (a b : F) (hm : m = p ^ n) :
  (a + b) ^ m = a^m + b^m  := by
subst hm
have := exercise_5_1_7 hp hF a b
letI : Fact p.Prime := ⟨hp⟩
simpa [add_pow_char_pow] using exercise_5_1_7 hF a b


theorem exercise_5_3_7 {K : Type*} [Field K] {F : Subfield K}
  {a : K} (ha : IsAlgebraic F (a ^ 2)) : IsAlgebraic F a  := by
obtain ⟨f, hf_nonzero, hf⟩ := ha
let g := Polynomial.comp f (Polynomial.X ^ 2)
have g_nonzero : g ≠ 0
· exact ?sorry_0
  intro hg
  apply hf_nonzero
  apply leadingCoeff_eq_zero.mp
  rw [← leadingCoeff_eq_zero, leadingCoeff_comp, leadingCoeff_X_pow, one_pow, mul_one] at hg
  · exact hg
  · simp
· have g_a_zero : Polynomial.aeval a g = 0
  · exact ?sorry_1
    simpa only [g, aeval_comp, AlgHom.map_pow, aeval_X] using hf
  · exact ⟨g, g_nonzero, g_a_zero⟩

