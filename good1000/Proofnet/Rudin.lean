import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators
noncomputable section

theorem exercise_1_12 (n : ℕ) (f : ℕ → ℂ) :
  abs (∑ i in range n, f i) ≤ ∑ i in range n, abs (f i)  := by
induction n with
  | zero =>
    have h_base : abs (∑ i in range 0, f i) = 0
      exact ?sorry_0
    have h_sum_zero : ∑ i in range 0, abs (f i) = 0
      exact ?sorry_1
    rw [h_base, h_sum_zero]
  | succ n ih =>
    have h_inductive : abs (∑ i in range n, f i) ≤ ∑ i in range n, abs (f i)
      exact ih
    have h_succ : abs (∑ i in range (n + 1), f i) = abs ((∑ i in range n, f i) + f n)
      exact ?sorry_2
    calc
  abs (∑ i in range (n + 1), f i)
    = abs ((∑ i in range n, f i) + f n) := by rw [h_succ]
  _ ≤ abs (∑ i in range n, f i) + abs (f n) := ?sorry_3
  _ ≤ (∑ i in range n, abs (f i)) + abs (f n) := ?sorry_4
  _ = ∑ i in range (n + 1), abs (f i) := ?sorry_5


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
  exact ?sorry_0
have hzy : z ≤ y
  exact ?sorry_1
calc
  x ≤ z := hxz
  _ ≤ y := hzy


theorem exercise_5_17
  {f : ℝ → ℝ}
  (hf' : DifferentiableOn ℝ f (Set.Icc (-1) 1))
  (hf'' : DifferentiableOn ℝ (deriv f) (Set.Icc 1 1))
  (hf''' : DifferentiableOn ℝ (deriv (deriv f)) (Set.Icc 1 1))
  (hf0 : f (-1) = 0)
  (hf1 : f 0 = 0)
  (hf2 : f 1 = 1)
  (hf3 : deriv f 0 = 0) :
  ∃ x, x ∈ Set.Ioo (-1 : ℝ) 1 ∧ deriv (deriv (deriv f)) x ≥ 3  := by
have hs : ∃ s ∈ Set.Ioo 0 1, f 1 = f 0 + deriv f 0 + (1 / 2) * deriv (deriv f) 0 + (1 / 6) * deriv (deriv (deriv f)) s
  exact ?sorry_0
have ht : ∃ t ∈ Set.Ioo (-1) 0, f (-1) = f 0 - deriv f 0 + (1 / 2) * deriv (deriv f) 0 - (1 / 6) * deriv (deriv (deriv f)) t
  exact ?sorry_1
obtain ⟨s, hs_mem, hs_eq⟩ := hs
obtain ⟨t, ht_mem, ht_eq⟩ := ht
have h_subtract : 1 = (1 / 6) * (deriv (deriv (deriv f)) s + deriv (deriv (deriv f)) t)
  exact ?sorry_2
have h_conclusion : ∃ x, x ∈ Set.Ioo (-1 : ℝ) 1 ∧ deriv (deriv (deriv f)) x ≥ 3
  exact ?sorry_3
exact h_conclusion


theorem exercise_4_12
  {α β γ : Type*} [UniformSpace α] [UniformSpace β] [UniformSpace γ]
  {f : α → β} {g : β → γ}
  (hf : UniformContinuous f) (hg : UniformContinuous g) :
  UniformContinuous (g ∘ f)  := by
rw [UniformContinuous] at hf hg ⊢
apply Tendsto.comp hg hf


theorem exercise_1_19
  (n : ℕ)
  (a b c x : EuclideanSpace ℝ (Fin n))
  (r : ℝ)
  (h₁ : r > 0)
  (h₂ : 3 • c = 4 • b - a)
  (h₃ : 3 * r = 2 * ‖x - b‖)
  : ‖x - a‖ = 2 * ‖x - b‖ ↔ ‖x - c‖ = r  := by
have h_sq₁ : ‖x - a‖^2 = (2 * ‖x - b‖)^2
  exact ?sorry_0
have h_eq₁ : ‖x‖^2 - 2 * (inner a x) + ‖a‖^2 = 4 * (‖x‖^2 - 2 * (inner b x) + ‖b‖^2)
  exact ?sorry_1
have h_simplified₁ : 3 * ‖x‖^2 + 2 * (inner a x) - 8 * (inner b x) - ‖a‖^2 + 4 * ‖b‖^2 = 0
  exact ?sorry_2
have h_sq₂ : ‖x - c‖^2 = r^2
  exact ?sorry_3
have h_subst : ‖x - ((4 / 3 : ℝ) • b - (1 / 3 : ℝ) • a)‖^2 = ((2 / 3 : ℝ) * ‖b - a‖)^2
  exact ?sorry_4
have h_eq₂ : ‖x‖^2 - 2 * (inner ((4 / 3 : ℝ) • b - (1 / 3 : ℝ) • a) x) + ‖(4 / 3 : ℝ) • b - (1 / 3 : ℝ) • a‖^2 = (4 / 9 : ℝ) * ‖b - a‖^2
  exact ?sorry_5
have h_equiv : (3 * ‖x‖^2 + 2 * (inner a x) - 8 * (inner b x) - ‖a‖^2 + 4 * ‖b‖^2) = 3 * (‖x‖^2 - 2 * (inner ((4 / 3 : ℝ) • b - (1 / 3 : ℝ) • a) x) + ‖(4 / 3 : ℝ) • b - (1 / 3 : ℝ) • a‖^2)
  exact ?sorry_6
exact ?sorry_7


theorem exercise_2_25 {K : Type*} [MetricSpace K] [CompactSpace K] :
  ∃ (B : Set (Set K)), Set.Countable B ∧ IsTopologicalBasis B  := by
have finite_cover : ∀ n : ℕ, ∃ (U : Finset K), Set.univ ⊆ ⋃ x ∈ U, Metric.ball x (1 / (n : ℝ))
  exact ?sorry_0
let B := ⋃ n, { U : Set K | ∃ x : K, Metric.ball x (1 / (n : ℝ)) = U }
have countable_B : Set.Countable B
  exact ?sorry_1
have is_basis_B : IsTopologicalBasis B
  exact ?sorry_2
exact ⟨B, countable_B, is_basis_B⟩


theorem exercise_4_4a
  {α : Type} [MetricSpace α]
  {β : Type} [MetricSpace β]
  (f : α → β)
  (s : Set α)
  (h₁ : Continuous f)
  (h₂ : Dense s)
  : f '' Set.univ ⊆ closure (f '' s)  := by
have h_f_univ : f '' Set.univ = f '' closure s
  exact ?sorry_0
have h_continuous : f '' closure s ⊆ closure (f '' s)
  exact ?sorry_1
calc
  f '' Set.univ = f '' closure s := h_f_univ
  _ ⊆ closure (f '' s) := h_continuous


theorem exercise_1_17
  (n : ℕ)
  (x y : EuclideanSpace ℝ (Fin n)) -- R^n
  : ‖x + y‖^2 + ‖x - y‖^2 = 2*‖x‖^2 + 2*‖y‖^2  := by
have h1 : ‖x + y‖^2 = ‖x‖^2 + 2 * ⟪x, y⟫_ℝ + ‖y‖^2
  exact ?sorry_0
have h2 : ‖x - y‖^2 = ‖x‖^2 - 2 * ⟪x, y⟫_ℝ + ‖y‖^2
  exact ?sorry_1
calc
  ‖x + y‖^2 + ‖x - y‖^2
    = (‖x‖^2 + 2 * ⟪x, y⟫_ℝ + ‖y‖^2) + (‖x‖^2 - 2 * ⟪x, y⟫_ℝ + ‖y‖^2) := by rw [h1, h2]
  _   = 2 * ‖x‖^2 + 2 * ‖y‖^2 := ?sorry_2


theorem exercise_4_19
  {f : ℝ → ℝ} (hf : ∀ a b c, a < b → f a < c → c < f b → ∃ x, a < x ∧ x < b ∧ f x = c)
  (hg : ∀ r : ℚ, IsClosed {x | f x = r}) : Continuous f  := by
by_contra h
obtain ⟨x₀, ε, hε, h_discont⟩ : ∃ x₀ ε, ε > 0 ∧ ∀ δ > 0, ∃ x, |x - x₀| < δ ∧ |f x - f x₀| ≥ ε := ?sorry_0
obtain ⟨r, hr₂⟩ : ∃ r : ℚ, f x₀ ≠ r ∧ ∀ δ > 0, ∃ t, t ≠ x₀ ∧ |t - x₀| < δ ∧ f t = r := ?sorry_1
have h_closed : x₀ ∈ {x | f x = r}
  exact ?sorry_2
have h_contradiction : f x₀ = r
  exact ?sorry_3
exact hr₂.1 h_contradiction


theorem exercise_4_8b
  (E : Set ℝ) :
  ∃ f : ℝ → ℝ, UniformContinuousOn f E ∧ ¬ Bornology.IsBounded (Set.image f E)  := by
let f : ℝ → ℝ := fun x => x
have h_uniform_continuous : UniformContinuous f
  exact ?sorry_0
have h_uniform_continuous_on_E : UniformContinuousOn f E
  exact ?sorry_1
have h_not_bounded : ¬ Bornology.IsBounded (Set.image f E)
  exact ?sorry_2
exact ⟨f, h_uniform_continuous_on_E, h_not_bounded⟩


theorem exercise_4_15 {f : ℝ → ℝ}
  (hf : Continuous f) (hof : IsOpenMap f) :
  Monotone f  := by
by_contra h
obtain ⟨a, b, c, hab, hbc, hfa_lt_fb, hfc_lt_fb⟩ : ∃ a b c, a < b ∧ b < c ∧ f a < f b ∧ f c < f b := ?sorry_0
have hmax : ∃ u, a < u ∧ u < c ∧ ∀ x ∈ Set.Icc a c, f x ≤ f u
  exact ?sorry_1
obtain ⟨u, hau, huc, hmax_u⟩ := hmax
by_cases hmin : ∃ v, a < v ∧ v < c ∧ ∀ x ∈ Set.Icc a c, f v ≤ f x
· obtain ⟨v, hav, hvc, hmin_v⟩ := hmin
  have himage_ac : f '' Set.Ioo a c = Set.Icc (f v) (f u)
    exact ?sorry_2
  have hnot_open : ¬ IsOpen (f '' Set.Ioo a c)
    exact ?sorry_3
  have hopen : IsOpen (f '' Set.Ioo a c)
    exact hof (Set.Ioo a c) (isOpen_Ioo)
  exact hnot_open hopen
· let d := min (f a) (f c)
  have himage_ac' : f '' Set.Ioo a c = Set.Ioc d (f u)
    exact ?sorry_4
  have hnot_open' : ¬ IsOpen (f '' Set.Ioo a c)
    exact ?sorry_5
  have hopen' : IsOpen (f '' Set.Ioo a c)
    exact hof (Set.Ioo a c) (isOpen_Ioo)
  exact hnot_open' hopen'


theorem exercise_2_19a {X : Type*} [MetricSpace X]
  (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) :
  SeparatedNhds A B  := by
have h_disjoint : A ∩ B = ∅
  exact ?sorry_0
have hA_closure_B : A ∩ closure B = ∅
  exact ?sorry_1
have h_closure_A_B : closure A ∩ B = ∅
  exact ?sorry_2
exact ?sorry_3


theorem exercise_1_11a (z : ℂ) :
  ∃ (r : ℝ) (w : ℂ), abs w = 1 ∧ z = r * w  := by
if h : z = 0 then
  use 0
  use 1
  have hw : abs (1 : ℂ) = 1
    exact ?sorry_0
  have hz : z = 0 * 1
    exact ?sorry_1
  exact ⟨hw, hz⟩
  else
    let r := abs z
    let w := z / r
    use r
    use w
    have hw : abs w = 1
      exact ?sorry_2
    have hz : z = r * w
      exact ?sorry_3
    exact ⟨hw, hz⟩


theorem exercise_5_15 {f : ℝ → ℝ} (a M0 M1 M2 : ℝ)
  (hf' : DifferentiableOn ℝ f (Set.Ici a))
  (hf'' : DifferentiableOn ℝ (deriv f) (Set.Ici a))
  (hM0 : M0 = sSup {(|f x|) | x ∈ (Set.Ici a)})
  (hM1 : M1 = sSup {(|deriv f x|) | x ∈ (Set.Ici a)})
  (hM2 : M2 = sSup {(|deriv (deriv f) x|) | x ∈ (Set.Ici a)}) :
  (M1 ^ 2) ≤ 4 * M0 * M2  := by
have hM0_finite : ∃ C : ℝ, M0 < C
  exact ?sorry_0
have hM2_finite : ∃ C : ℝ, M2 < C
  exact ?sorry_1
have hM2_pos : 0 < M2
  exact ?sorry_2
let h := Real.sqrt (M0 / M2)
have h_deriv_bound : ∀ x, a < x → |deriv f x| ≤ 2 * Real.sqrt (M0 * M2)
  exact ?sorry_3
have h_example : ∃ f_example, ∀ x, a < x → |f_example x| ≤ M0 ∧ |deriv f_example x| ≤ M1 ∧ |deriv (deriv f_example) x| ≤ M2
  exact ?sorry_4
have h_vector_case : ∀ (n : ℕ) (f_vec : ℝ → (Fin n → ℝ)),
  (∀ i, DifferentiableOn ℝ (fun x => f_vec x i) (Set.Ici a)) →
  (∀ i, DifferentiableOn ℝ (fun x => deriv (fun y => f_vec y i) x) (Set.Ici a)) →
  (∀ i, sSup {(|f_vec x i|) | x ∈ (Set.Ici a)} ≤ M0) →
  (∀ i, sSup {(|deriv (fun y => f_vec y i) x|) | x ∈ (Set.Ici a)} ≤ M1) →
  (∀ i, sSup {(|deriv (deriv (fun y => f_vec y i)) x|) | x ∈ (Set.Ici a)} ≤ M2) →
  (M1 ^ 2) ≤ 4 * M0 * M2 := ?sorry_5
exact ?sorry_6


theorem exercise_4_6
  (f : ℝ → ℝ)
  (E : Set ℝ)
  (G : Set (ℝ × ℝ))
  (h₁ : IsCompact E)
  (h₂ : G = {(x, f x) | x ∈ E})
  : ContinuousOn f E ↔ IsCompact G  := by
let φ : ℝ → ℝ × ℝ := fun x => (x, f x)
have φ_continuous_if_f_continuous : ContinuousOn f E → ContinuousOn φ E
  intro hf
  exact ?sorry_0
have f_continuous_if_φ_continuous : ContinuousOn φ E → ContinuousOn f E
  intro hφ
  exact ?sorry_1
have G_compact_if_f_continuous : ContinuousOn f E → IsCompact G
  intro hf
  exact ?sorry_2
have f_continuous_if_G_compact : IsCompact G → ContinuousOn f E
  intro hG
  exact ?sorry_3
apply Iff.intro
· exact G_compact_if_f_continuous
· exact f_continuous_if_G_compact


theorem exercise_5_1
  {f : ℝ → ℝ} (hf : ∀ x y : ℝ, |(f x - f y)| ≤ (x - y) ^ 2) :
  ∃ c, f = λ x => c  := by
have h_deriv_zero : ∀ y : ℝ, deriv f y = 0
  intro y
  have h_limit : ∀ ε > 0, ∃ δ > 0, ∀ x, |x - y| < δ → |(f x - f y) / (x - y)| < ε
    exact ?sorry_0
  have h_limit_zero : ∀ x, x ≠ y → |(f x - f y) / (x - y)| ≤ |x - y|
    exact ?sorry_1
  exact ?sorry_2
have h_const : ∀ x y : ℝ, f x = f y
  intros x y
  have h_zero_deriv : ∀ t, deriv f t = 0
    exact h_deriv_zero
  have h_mvt : ∀ a b, f a = f b
    exact ?sorry_3
  exact h_mvt x y
use f 0
funext x
exact h_const x 0


theorem exercise_2_24 {X : Type*} [MetricSpace X]
  (hX : ∀ (A : Set X), Infinite A → ∃ (x : X), x ∈ closure A) :
  SeparableSpace X  := by
by_contra h
let δ := 1
let x_i : ℕ → X := ?sorry_0
let S := {x : X | ∃ (i : ℕ), ∀ (j : ℕ), i ≠ j → dist x (x_i j) ≥ δ}
have hS_infinite : Infinite S
  exact ?sorry_1
obtain ⟨x, hx⟩ := hX S hS_infinite
have h_no_limit_point : ∀ x ∈ S, ∀ ε > 0, ∃ y ∈ S, dist x y ≥ ε
  exact ?sorry_2
have h_totally_bounded : ∀ ε > 0, ∃ (F : Finset X), ∀ x : X, ∃ y ∈ F, dist x y < ε
  exact ?sorry_3
let A := ⋃ (n : ℕ), {x : X | ∃ (j : ℕ), x ∈ Metric.ball (x_i j) (1 / (n + 1))}
have hA_dense : Dense A
  exact ?sorry_4
have hA_countable : Countable A
  exact ?sorry_5
have h_contradiction : SeparableSpace X
  exact ⟨A, hA_countable, hA_dense⟩
contradiction


theorem exercise_4_3
  {α : Type} [MetricSpace α]
  (f : α → ℝ) (h : Continuous f) (z : Set α) (g : z = f⁻¹' {0})
  : IsClosed z  := by
let z' := f ⁻¹' {0}
have hz : z' = f ⁻¹' {0}
  exact rfl
have h_closed_set : IsClosed ({0} : Set ℝ)
  exact ?sorry_0
have h_preimage_closed : IsClosed z'
  exact ?sorry_1
rw [g]
exact h_preimage_closed
