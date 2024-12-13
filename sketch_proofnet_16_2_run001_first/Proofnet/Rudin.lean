import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators
noncomputable section

theorem exercise_1_1a
  (x : ℝ) (y : ℚ) :
  ( Irrational x ) -> Irrational ( x + y )  := by
simpa using exercise_1_add x y


theorem exercise_1_1b
(x : ℝ)
(y : ℚ)
(h : y ≠ 0)
: ( Irrational x ) -> Irrational ( x * y )  := by
intro exercise_1
exact exercise_1.mul_rat h


theorem exercise_1_4
(α : Type*) [PartialOrder α]
(s : Set α)
(x y : α)
(h₀ : Set.Nonempty s)
(h₁ : x ∈ lowerBounds s)
(h₂ : y ∈ upperBounds s)
: x ≤ y  := by
obtain ⟨z, hz⟩ := h₀
have hxz : x ≤ z
· exact h₁ hz
· have hzy : z ≤ y
  · exact h₂ hz
  · calc
  x ≤ z := hxz
  _ ≤ y := hzy


theorem exercise_1_12 (n : ℕ) (f : ℕ → ℂ) :
  abs (∑ i in range n, f i) ≤ ∑ i in range n, abs (f i)  := by
induction' n with n ih
· simp
· rw [sum_range_succ, sum_range_succ ]
  trans
  apply Complex.abs.add_le
  exact add_le_add ih le_rfl


theorem exercise_1_17
  (n : ℕ)
  (x y : EuclideanSpace ℝ (Fin n)) -- R^n
  : ‖x + y‖^2 + ‖x - y‖^2 = 2*‖x‖^2 + 2*‖y‖^2  := by
rw [norm_add_sq_real, norm_sub_sq_real ]
ring


theorem exercise_1_18b
  : ¬ ∀ (x : ℝ), ∃ (y : ℝ), y ≠ 0 ∧ x * y = 0  := by
intro h
exact one_ne_zero <| h 1
simp only [mul_eq_zero, Ne, not_exists, not_and] at h
simpa [not_or, sub_self, sub_eq_zero] using h 1


theorem exercise_2_25 {K : Type*} [MetricSpace K] [CompactSpace K] :
  ∃ (B : Set (Set K)), Set.Countable B ∧ IsTopologicalBasis B  := by
rcases exists_countable_basis K with ⟨s, hsc, hsU⟩
exact ⟨s, hsc, hsU.2⟩


theorem exercise_3_1a
  (f : ℕ → ℝ)
  (h : ∃ (a : ℝ), Tendsto (λ (n : ℕ) => f n) atTop (𝓝 a))
  : ∃ (a : ℝ), Tendsto (λ (n : ℕ) => |f n|) atTop (𝓝 a)  := by
rcases h with ⟨a, ha⟩
exact ⟨|a|, ha.abs⟩


theorem exercise_4_2a
  {α : Type} [MetricSpace α]
  {β : Type} [MetricSpace β]
  (f : α → β)
  (h₁ : Continuous f)
  : ∀ (x : Set α), f '' (closure x) ⊆ closure (f '' x)  := by
intro x
rw [← closure_image_closure ]
· exact subset_closure
· fun_prop


theorem exercise_4_3
  {α : Type} [MetricSpace α]
  (f : α → ℝ) (h : Continuous f) (z : Set α) (g : z = f⁻¹' {0})
  : IsClosed z  := by
rw [g]
have h_closed_set : IsClosed ({0} : Set ℝ)
· exact ?sorry_0
  exact isClosed_singleton
· have h_preimage_closed : IsClosed (f⁻¹' {0})
  · exact ?sorry_1
    exact h_closed_set.preimage h
  · exact h_preimage_closed


theorem exercise_4_4a
  {α : Type} [MetricSpace α]
  {β : Type} [MetricSpace β]
  (f : α → β)
  (s : Set α)
  (h₁ : Continuous f)
  (h₂ : Dense s)
  : f '' Set.univ ⊆ closure (f '' s)  := by
have h₃ : f '' closure s ⊆ closure (f '' s)
· exact ?sorry_0
  exact image_closure_subset_closure_image h₁
· have h₄ : closure s = Set.univ
  · exact ?sorry_1
    exact h₂.closure_eq
  · have h₅ : f '' Set.univ = f '' closure s
    · exact ?sorry_2
      rw [h₄ ]
    · calc
  f '' Set.univ = f '' closure s := h₅
  _ ⊆ closure (f '' s) := h₃


theorem exercise_4_4b
  {α : Type} [MetricSpace α]
  {β : Type} [MetricSpace β]
  (f g : α → β)
  (s : Set α)
  (h₁ : Continuous f)
  (h₂ : Continuous g)
  (h₃ : Dense s)
  (h₄ : ∀ x ∈ s, f x = g x)
  : f = g  := by
rw [Continuous.ext_on h₃ h₁ h₂ ]
exact fun x hx => h₄ x hx


theorem exercise_4_11a
  {X : Type*} [MetricSpace X]
  {Y : Type*} [MetricSpace Y]
  (f : X → Y) (hf : UniformContinuous f)
  (x : ℕ → X) (hx : CauchySeq x) :
  CauchySeq (λ n => f (x n))  := by
rw [cauchySeq_iff] at hx ⊢
intro U hU
obtain ⟨V, hV, hVsymm, hVU⟩ := comp_symm_mem_uniformity_sets hU
rw [uniformity_eq_symm] at hV
rcases hx _ (mem_map.1 <| hf hU) with ⟨N, hN⟩
exact ⟨N, fun k hk l hl => hN k hk l hl⟩


theorem exercise_4_12
  {α β γ : Type*} [UniformSpace α] [UniformSpace β] [UniformSpace γ]
  {f : α → β} {g : β → γ}
  (hf : UniformContinuous f) (hg : UniformContinuous g) :
  UniformContinuous (g ∘ f)  := by
have := hg.comp hf
exact this

