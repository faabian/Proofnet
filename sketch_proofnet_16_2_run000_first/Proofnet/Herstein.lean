import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators
noncomputable section

theorem exercise_2_1_26 {G : Type*} [Group G]
  [Fintype G] (a : G) : ∃ (n : ℕ), a ^ n = 1  := by
let n := @Nat.card G _ a
let n := @exercise_1 G _ _ a
letI : DecidableEq G := Classical.decEq G
have h := exercise_1 a
have h := exercise_1 a
have h := exercise_1 a
have h := exercise_1 a
have h := exercise_3 a
use Finset.univ.sup orderOf
exact pow_card_eq_one


theorem exercise_2_1_27 {G : Type*} [Group G]
  [Fintype G] : ∃ (m : ℕ), ∀ (a : G), a ^ m = 1  := by
refine ⟨_, fun a => ?_⟩
let _ := Fintype.ofFinite G
refine ⟨_, fun a => ?_⟩
revert G
intro G _
intro h
have := Fintype.ofFinite G
refine ⟨_, fun a => ?_⟩
refine ⟨Fintype.card G, fun a => ?_⟩
simpa using pow_card_eq_one a


theorem exercise_2_6_15 {G : Type*} [CommGroup G] {m n : ℕ}
  (hm : ∃ (g : G), orderOf g = m)
  (hn : ∃ (g : G), orderOf g = n)
  (hmn : m.Coprime n) :
  ∃ (g : G), orderOf g = m * n  := by
obtain ⟨g, rfl⟩ := hm
obtain ⟨g', rfl⟩ := hn
exact ⟨g * g', (Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime hmn⟩


theorem exercise_4_2_9 {p : ℕ} (hp : Nat.Prime p) (hp1 : Odd p) :
  ∃ (a b : ℤ), (a / b : ℚ) = ∑ i in Finset.range p, 1 / (i + 1) → ↑p ∣ a  := by
use 0, 1
simp


theorem exercise_5_1_8 {p m n: ℕ} {F : Type*} [Field F]
  (hp : Nat.Prime p) (hF : CharP F p) (a b : F) (hm : m = p ^ n) :
  (a + b) ^ m = a^m + b^m  := by
subst hm
have := exercise_5_1_4 hp hF a b
haveI := hp.charP F
have := exercise_5_1_4 hF a b
haveI := hp.charP F
have := exercise_5_1_4 hF a b
haveI := hp.charP F
letI : Fact p.Prime := ⟨hp⟩
simpa only [map_add, Fintype.card_fin, Nat.card_eq_fintype_card, add_pow_char_pow] using
  exercise_5_1_4 hF a b


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

