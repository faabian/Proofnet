import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem exercise_3_14 {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf_inj : Function.Injective f) :
    ∃ (a b : ℂ), f = (λ z => a * z + b) ∧ a ≠ 0  := by
let g : ℂ → ℂ := λ z => f (1 / z)
have hg_diff : Differentiable ℂ g
  exact ?sorry_0
by_contra h_ess
let z₀ : ℂ := ?sorry_1
have hz₀_ne : z₀ ≠ 0
  exact ?sorry_2
have h_dense : ∀ ε > 0, ∃ z, Complex.abs z < ε ∧ f z ∈ ball (f z₀) ε
  exact ?sorry_3
have h_ball : ∃ δ > 0, ball z₀ δ ⊆ f ⁻¹' ball (f z₀) δ
  exact ?sorry_4
have h_contradiction : ∃ z₁ z₂, z₁ ≠ z₂ ∧ f z₁ = f z₂
  exact ?sorry_5
rcases h_contradiction with ⟨z₁, z₂, hz₁z₂_ne, hf_eq⟩
have : z₁ = z₂
  exact hf_inj hf_eq
contradiction


theorem exercise_1_13a {f : ℂ → ℂ} (Ω : Set ℂ) (a b : Ω) (h : IsOpen Ω)
  (hf : DifferentiableOn ℂ f Ω) (hc : ∃ (c : ℝ), ∀ z ∈ Ω, (f z).re = c) :
  f a = f b  := by
rcases hc with ⟨c, hc_const⟩
let u := fun z : ℂ => (f z).re
let v := fun z : ℂ => (f z).im
have hdu_zero : ∀ z ∈ Ω, fderiv ℝ u z = 0
  exact ?sorry_0
have hdv_zero : ∀ z ∈ Ω, fderiv ℝ v z = 0
  exact ?sorry_1
have hf_prime_zero : ∀ z ∈ Ω, fderiv ℂ f z = 0
  exact ?sorry_2
have h_const : ∀ z₁ ∈ Ω, ∀ z₂ ∈ Ω, f z₁ = f z₂
  exact ?sorry_3
exact h_const a a.2 b b.2


theorem exercise_1_13b {f : ℂ → ℂ} (Ω : Set ℂ) (a b : Ω) (h : IsOpen Ω)
  (hf : DifferentiableOn ℂ f Ω) (hc : ∃ (c : ℝ), ∀ z ∈ Ω, (f z).im = c) :
  f a = f b  := by
let u := fun z : ℂ => (f z).re
let v := fun z : ℂ => (f z).im
obtain ⟨c, hc⟩ := hc
have hvx : ∀ z ∈ Ω, fderiv ℝ v z = 0
  exact ?sorry_0
have hvy : ∀ z ∈ Ω, fderiv ℝ v z = 0
  exact ?sorry_1
have hux : ∀ z ∈ Ω, fderiv ℝ u z = 0
  exact ?sorry_2
have h_deriv_zero : ∀ z ∈ Ω, fderiv ℂ f z = 0
  exact ?sorry_3
have h_const : ∀ z₁ ∈ Ω, ∀ z₂ ∈ Ω, f z₁ = f z₂
  exact ?sorry_4
exact h_const a.1 a.2 b.1 b.2
