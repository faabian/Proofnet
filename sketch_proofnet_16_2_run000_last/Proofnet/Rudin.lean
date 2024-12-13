import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators
noncomputable section

theorem exercise_1_1a
  (x : ℝ) (y : ℚ) :
  ( Irrational x ) -> Irrational ( x + y )  := by
simpa using exercise_1_9x


theorem exercise_1_1b
(x : ℝ)
(y : ℚ)
(h : y ≠ 0)
: ( Irrational x ) -> Irrational ( x * y )  := by
contrapose
norm_cast
delta Irrational
simp_all
rintro a ha
exact ⟨a * y⁻¹, by simp_all [mul_assoc]⟩


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
  · exact le_trans hxz hzy


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
simp only [upgradePolishSpace, displayText_eq_coe] at this
obtain ⟨B, hBc, hB⟩ := exists_countable_basis K
exact ⟨B, hBc, hB.2⟩


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
simpa only [image_eq_range] using fun x => image_closure_subset_closure_image h₁


theorem exercise_4_3
  {α : Type} [MetricSpace α]
  (f : α → ℝ) (h : Continuous f) (z : Set α) (g : z = f⁻¹' {0})
  : IsClosed z  := by
simpa only [g] using isClosed_singleton.preimage h


theorem exercise_4_4a
  {α : Type} [MetricSpace α]
  {β : Type} [MetricSpace β]
  (f : α → β)
  (s : Set α)
  (h₁ : Continuous f)
  (h₂ : Dense s)
  : f '' Set.univ ⊆ closure (f '' s)  := by
have h_closure : closure s = Set.univ
· exact ?sorry_0
  rw [dense_iff_closure_eq] at h₂
  exact h₂
· have h_continuity : f '' closure s ⊆ closure (f '' s)
  · exact ?sorry_1
    apply image_closure_subset_closure_image h₁
  · have h_image_univ : f '' Set.univ = f '' closure s
    · exact ?sorry_2
      rw [h_closure ]
    · have h_final : f '' Set.univ ⊆ closure (f '' s)
      · rw [h_image_univ]
        exact h_continuity
      · exact h_final


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
haveI := h₃.false
rw [Continuous.ext_on h₃ h₁ h₂ ]
exact fun x hx => h₄ x hx


theorem exercise_4_11a
  {X : Type*} [MetricSpace X]
  {Y : Type*} [MetricSpace Y]
  (f : X → Y) (hf : UniformContinuous f)
  (x : ℕ → X) (hx : CauchySeq x) :
  CauchySeq (λ n => f (x n))  := by
simpa only [CauchySeq, Metric.cauchy_iff] using hx.map hf


theorem exercise_4_12
  {α β γ : Type*} [UniformSpace α] [UniformSpace β] [UniformSpace γ]
  {f : α → β} {g : β → γ}
  (hf : UniformContinuous f) (hg : UniformContinuous g) :
  UniformContinuous (g ∘ f)  := by
apply Tendsto.comp hg hf

