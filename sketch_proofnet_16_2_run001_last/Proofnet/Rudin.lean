import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators
noncomputable section

theorem exercise_1_1a
  (x : ℝ) (y : ℚ) :
  ( Irrational x ) -> Irrational ( x + y )  := by
simpa [← cast_add] using exercise_1_add x y


theorem exercise_1_1b
(x : ℝ)
(y : ℚ)
(h : y ≠ 0)
: ( Irrational x ) -> Irrational ( x * y )  := by
intros
aesop


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
rw [EuclideanSpace.norm_eq ]
rw [EuclideanSpace.norm_eq ]
rw [EuclideanSpace.norm_eq,EuclideanSpace.norm_eq ]
rw [← rpow_natCast, ← rpow_natCast ]
rw [← EuclideanSpace.norm_eq ]
rw [EuclideanSpace.norm_eq ]
rw [← rpow_natCast, ← rpow_natCast ]
rw [← EuclideanSpace.norm_eq, ← EuclideanSpace.norm_eq, ← EuclideanSpace.norm_eq ]
norm_cast
norm_cast
rw [norm_add_sq_real, norm_sub_sq_real, ← mul_self_sqrt <| sum_nonneg fun _ _ => sq_nonneg _ ]
ring_nf
rw [EuclideanSpace.norm_eq ]
rw [← Real.sqrt_sq <| norm_nonneg y ]
rw [sq_sqrt ]
· rw [EuclideanSpace.norm_eq ]
· positivity


theorem exercise_1_18b
  : ¬ ∀ (x : ℝ), ∃ (y : ℝ), y ≠ 0 ∧ x * y = 0  := by
simp
push_neg
by_contra! h
simpa using h 1


theorem exercise_2_25 {K : Type*} [MetricSpace K] [CompactSpace K] :
  ∃ (B : Set (Set K)), Set.Countable B ∧ IsTopologicalBasis B  := by
let s : Set K
clear_value s
· letI := upgradePolishSpace K
  obtain ⟨B, hBc, -, hB⟩ := exists_countable_basis K
  exact ⟨B, hBc, hB⟩
· exact Set.univ


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
intros
simpa using image_closure_subset_closure_image h₁


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
have h₃ : closure s = Set.univ
· exact ?sorry_0
  exact h₂.closure_eq
· have h₄ : f '' closure s = f '' Set.univ
  · exact ?sorry_1
    rw [h₃ ]
  · have h₅ : f '' closure s ⊆ closure (f '' s)
    · exact ?sorry_2
      exact image_closure_subset_closure_image h₁
    · calc
  f '' Set.univ = f '' closure s := by rw [h₄]
  _ ⊆ closure (f '' s) := by exact h₅


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
exact fun x hx ↦ h₄ x hx


theorem exercise_4_11a
  {X : Type*} [MetricSpace X]
  {Y : Type*} [MetricSpace Y]
  (f : X → Y) (hf : UniformContinuous f)
  (x : ℕ → X) (hx : CauchySeq x) :
  CauchySeq (λ n => f (x n))  := by
simpa [cauchySeq_iff] using hf.comp_cauchySeq hx


theorem exercise_4_12
  {α β γ : Type*} [UniformSpace α] [UniformSpace β] [UniformSpace γ]
  {f : α → β} {g : β → γ}
  (hf : UniformContinuous f) (hg : UniformContinuous g) :
  UniformContinuous (g ∘ f)  := by
exact hg.comp hf

