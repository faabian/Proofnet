import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators
noncomputable section

theorem exercise_1_1a
  (x : ℝ) (y : ℚ) :
  ( Irrational x ) -> Irrational ( x + y )  := by
intro h
simpa using h.add_rat y


theorem exercise_1_1b
(x : ℝ)
(y : ℚ)
(h : y ≠ 0)
: ( Irrational x ) -> Irrational ( x * y )  := by
delta Irrational
intro h1
contrapose! h1
rw [Set.mem_range] at h1 ⊢
obtain ⟨z, hz⟩ := h1
exact ⟨z * y⁻¹, by field_simp [hz]⟩


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
· exact ?sorry_0
  exact h₁ hz
· have hzy : z ≤ y
  · exact ?sorry_1
    exact h₂ hz
  · calc
  x ≤ z := hxz
  _ ≤ y := hzy


theorem exercise_1_14
  (z : ℂ) (h : abs z = 1)
  : (abs (1 + z)) ^ 2 + (abs (1 - z)) ^ 2 = 4  := by
rw [← abs_sq] <;> positivity
rw [← Complex.ofReal_inj] <;> norm_num
norm_cast
rw [← Complex.norm_eq_abs, ← Complex.norm_eq_abs, norm_add_sq_real, norm_sub_sq_real,
  ← Complex.ofReal_inj ]
simp
rw [h ]
ring
norm_num


theorem exercise_1_18b
  : ¬ ∀ (x : ℝ), ∃ (y : ℝ), y ≠ 0 ∧ x * y = 0  := by
simp
by_contra! h
exact one_ne_zero <| h 1
simpa using h 1


theorem exercise_2_25 {K : Type*} [MetricSpace K] [CompactSpace K] :
  ∃ (B : Set (Set K)), Set.Countable B ∧ IsTopologicalBasis B  := by
letI := upgradePolishSpace K
obtain ⟨B, hBc, hB, hB'⟩ := exists_countable_basis K
exact ⟨B, hBc, hB'⟩


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
rw [continuous_iff_continuousAt] at h₁
intro x a ha
obtain ⟨x, hx, rfl⟩ := ha
exact (h₁ x).continuousWithinAt.mem_closure_image hx


theorem exercise_4_3
  {α : Type} [MetricSpace α]
  (f : α → ℝ) (h : Continuous f) (z : Set α) (g : z = f⁻¹' {0})
  : IsClosed z  := by
have hZ : z = f⁻¹' {0}
· exact g
· have hClosedSet : IsClosed ({0} : Set ℝ)
  · exact ?sorry_0
    exact isClosed_singleton
  · have hPreimageClosed : IsClosed (f⁻¹' {0})
    · apply continuous_iff_isClosed.mp h
      exact hClosedSet
    · rw [hZ]
      exact hPreimageClosed


theorem exercise_4_4a
  {α : Type} [MetricSpace α]
  {β : Type} [MetricSpace β]
  (f : α → β)
  (s : Set α)
  (h₁ : Continuous f)
  (h₂ : Dense s)
  : f '' Set.univ ⊆ closure (f '' s)  := by
rw [Set.image_univ ]
simpa only [range_subset_iff, image_univ] using h₁.range_subset_closure_image_dense h₂


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
rw [cauchySeq_iff ]
rw [cauchySeq_iff] at hx
exact fun V hV => hx _ <| hf hV


theorem exercise_4_12
  {α β γ : Type*} [UniformSpace α] [UniformSpace β] [UniformSpace γ]
  {f : α → β} {g : β → γ}
  (hf : UniformContinuous f) (hg : UniformContinuous g) :
  UniformContinuous (g ∘ f)  := by
apply Tendsto.comp hg hf

