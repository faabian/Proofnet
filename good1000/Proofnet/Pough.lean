import Mathlib

open Filter Real Function
open scoped Topology
noncomputable section

theorem exercise_2_46 {M : Type*} [MetricSpace M]
  {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
  (hAB : Disjoint A B) (hA₀ : A ≠ ∅) (hB₀ : B ≠ ∅) :
  ∃ a₀ b₀, a₀ ∈ A ∧ b₀ ∈ B ∧ ∀ (a : M) (b : M),
  a ∈ A → b ∈ B → dist a₀ b₀ ≤ dist a b  := by
let d : M × M → ℝ := fun p => dist p.1 p.2
have hAB_compact : IsCompact (A ×ˢ B)
  exact ?sorry_0
have h_continuous : Continuous d
  exact ?sorry_1
have h_min : ∃ p₀ ∈ A ×ˢ B, ∀ p ∈ A ×ˢ B, d p₀ ≤ d p
  exact ?sorry_2
rcases h_min with ⟨⟨a₀, b₀⟩, h₀, h_min_dist⟩
have ha₀ : a₀ ∈ A
  exact ?sorry_3
have hb₀ : b₀ ∈ B
  exact ?sorry_4
use a₀, b₀
constructor
· exact ha₀
constructor
· exact hb₀
· intros a b ha hb
  exact h_min_dist ⟨a, b⟩ exact ?sorry_5


theorem exercise_2_41 (m : ℕ) {X : Type*} [NormedSpace ℝ ((Fin m) → ℝ)] :
  IsCompact (Metric.closedBall 0 1)  := by
let norm_E := fun (x : (Fin m) → ℝ) => Real.sqrt (∑ i, (x i) ^ 2)
have h1 : ∃ C1 C2, 0 < C1 ∧ 0 < C2 ∧ ∀ x : (Fin m) → ℝ, C1 * norm_E x ≤ ‖x‖ ∧ ‖x‖ ≤ C2 * norm_E x
  exact ?sorry_0
obtain ⟨C1, C2, hC1, hC2, h_norm⟩ := h1
have h2 : ∀ x ∈ Metric.closedBall (0 : (Fin m) → ℝ) 1, norm_E x ≤ 1 / C1
  exact ?sorry_1
have h3 : ∀ (x : (Fin m) → ℝ), (∀ n, x n ∈ Metric.closedBall 0 1) → x ∈ Metric.closedBall 0 1
  exact ?sorry_2
have h4 : IsCompact (Metric.closedBall 0 1)
  exact ?sorry_3
have h5 : Continuous (id : ((Fin m) → ℝ) → ((Fin m) → ℝ))
  exact ?sorry_4
have h6 : Continuous (id⁻¹ : ((Fin m) → ℝ) → ((Fin m) → ℝ))
  exact ?sorry_5
exact h4


theorem exercise_2_32a (A : Set ℕ) : IsClopen A  := by
have one_point_open : ∀ n : ℕ, IsOpen ({n} : Set ℕ)
  intro n
  exact ?sorry_0
have subset_open : IsOpen A
  exact ?sorry_1
have subset_closed : IsClosed A
  exact ?sorry_2
apply And.intro
exact subset_closed
exact subset_open
