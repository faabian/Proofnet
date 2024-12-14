import Mathlib

open Filter Set

theorem exercise_2022_IA_4_I_2D_a : Irrational (2^((1:ℝ)/3) + 3^((1:ℝ)/3))  := by
by_contra h
obtain ⟨a, b, hab⟩ : ∃ (a b : ℤ), ((2:ℝ)^(1/3) + (3:ℝ)^(1/3)) = a / b := ?sorry_0
have h_cube : (a^3 : ℝ) / (b^3 : ℝ) = 2 + 3 * ((2:ℝ)^(1/3) * (3:ℝ)^(1/3)) + 3 * (3:ℝ)^(2/3) + 3
  exact ?sorry_1
obtain ⟨c, d, hcd⟩ : ∃ (c d : ℤ), ((2:ℝ)^(1/3) * (3:ℝ)^(1/3)) = c / d := ?sorry_2
have h_cube_cd : (c^3 : ℝ) / (d^3 : ℝ) = 81000 * Real.sqrt 3
  exact ?sorry_3
have h_contradiction : False
  exact ?sorry_4
exact h_contradiction
