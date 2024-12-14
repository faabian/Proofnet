import Mathlib

open scoped BigOperators

theorem exercise_2018_b2 (n : ℕ) (hn : n > 0) (f : ℕ → ℂ → ℂ)
  (hf : ∀ n : ℕ, f n = λ (z : ℂ) => (∑ i : Fin n, (n-i)* z^(i : ℕ))) :
  ¬ (∃ z : ℂ, ‖z‖ ≤ 1 ∧ f n z = 0)  := by
have h1 : 0 < Complex.re (f n 1)
  exact ?sorry_0
have h2 : ∀ z : ℂ, (z - 1) * f n z = (∑ i in Finset.range n, z^(i + 1)) - n
  exact ?sorry_1
have h3 : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖∑ i in Finset.range n, z^(i + 1)‖ ≤ n
  exact ?sorry_2
have h4 : ∀ z : ℂ, ‖z‖ ≤ 1 → (‖∑ i in Finset.range n, z^(i + 1)‖ = n ↔ z = 1)
  exact ?sorry_3
intro h
obtain ⟨z, hz1, hz2⟩ := h
have hz3 : (z - 1) * f n z = 0
  exact ?sorry_4
have hz4 : z = 1
  exact ?sorry_5
have hz5 : f n 1 ≠ 0
  exact ?sorry_6
have hz6 : f n 1 = 0
  rw [←hz4, hz2]
exact hz5 hz6


theorem exercise_2017_b3 (f : ℝ → ℝ) (c : ℕ → ℝ)
  (hf : f = λ x => (∑' (i : ℕ), (c i) * x^i))
  (hc : ∀ n, c n = 0 ∨ c n = 1)
  (hf1 : f (2/3) = 3/2) :
  Irrational (f (1/2))  := by
by_contra h
have h_periodic : ∃ m n, ∀ i ≥ n, c i = c (m + i)
  exact ?sorry_0
rcases h_periodic with ⟨m, n, h_periodic⟩
let g := λ x => ∑ i in Finset.range n, c i * x^i
let h := λ x => ∑ i in Finset.range m, c (n + i) * x^i
have hf_expansion : ∀ x, f x = g x + (x^n / (1 - x^m)) * h x
  exact ?sorry_1
have hf_2_3 : f (2/3) = g (2/3) + ((2/3)^n / (1 - (2/3)^m)) * h (2/3)
  exact ?sorry_2
have contradiction : False
  exact ?sorry_3
exact contradiction


theorem exercise_1999_b4 (f : ℝ → ℝ) (hf: ContDiff ℝ 3 f)
  (hf1 : ∀ n ≤ 3, ∀ x : ℝ, iteratedDeriv n f x > 0)
  (hf2 : ∀ x : ℝ, iteratedDeriv 3 f x ≤ f x) :
  ∀ x : ℝ, deriv f x < 2 * f x  := by
let g := fun x => iteratedDeriv 2 f x * iteratedDeriv 3 f x - iteratedDeriv 2 f x * f x - (deriv f x)^2
have hg_neg : ∀ x, g x < 0
  exact ?sorry_0
have h_fact : ∀ x, iteratedDeriv 2 f x * iteratedDeriv 3 f x < iteratedDeriv 2 f x * f x + (deriv f x)^2
  exact ?sorry_1
have h_ineq1 : ∀ x, (1/2) * (iteratedDeriv 2 f x)^2 < f x * deriv f x
  exact ?sorry_2
let h := fun x => 2 * deriv f x * iteratedDeriv 2 f x - 2 * deriv f x * iteratedDeriv 2 f x - 2 * f x * iteratedDeriv 3 f x
have hh_neg : ∀ x, h x < 0
  exact ?sorry_3
have h_ineq2 : ∀ x, (deriv f x)^2 ≤ 2 * f x * iteratedDeriv 2 f x
  exact ?sorry_4
have h_combined : ∀ x, (deriv f x)^3 < 8 * (f x)^3
  exact ?sorry_5
intro x
have : deriv f x < 2 * f x
  exact ?sorry_6
exact this


theorem exercise_2018_a5 (f : ℝ → ℝ) (hf : ContDiff ℝ ⊤ f)
  (hf0 : f 0 = 0) (hf1 : f 1 = 1) (hf2 : ∀ x, f x ≥ 0) :
  ∃ (n : ℕ) (x : ℝ), iteratedDeriv n f x = 0  := by
let ultraconvex (g : ℝ → ℝ) := ∀ n x, iteratedDeriv n g x ≥ 0
let S := {g : ℝ → ℝ | ultraconvex g ∧ g 0 = 0}
have h_neg_zero : ∀ g ∈ S, ∀ x < 0, g x = 0
  exact ?sorry_0
have h_f_prime_zero : ∀ g ∈ S, iteratedDeriv 1 g 0 = 0
  exact ?sorry_1
have h_induction : ∀ g ∈ S, ∀ n x, 0 ≤ x ∧ x ≤ 1 → g x ≤ iteratedDeriv n g 1 / Nat.factorial n * x^n
  exact ?sorry_2
have h_base_case : ∀ g ∈ S, ∀ x, 0 ≤ x ∧ x ≤ 1 → g x ≤ iteratedDeriv 0 g 1
  exact ?sorry_3
have h_inductive_step : ∀ g ∈ S, ∀ n x, 0 ≤ x ∧ x ≤ 1 → g x ≤ iteratedDeriv (n + 1) g 1 / Nat.factorial (n + 1) * x^(n + 1)
  exact ?sorry_4
have h_f1_bound : ∀ g ∈ S, ∀ n, g 1 ≤ iteratedDeriv n g 1 / Nat.factorial n
  exact ?sorry_5
have h_taylor : ∀ g ∈ S, ∀ n x, x ≥ 1 → g x ≥ ∑ k in Finset.range (n + 1), iteratedDeriv k g 1 / Nat.factorial k * (x - 1)^k
  exact ?sorry_6
have h_f2_bound : ∀ g ∈ S, ∀ n, g 2 ≥ ∑ k in Finset.range (n + 1), iteratedDeriv k g 1 / Nat.factorial k
  exact ?sorry_7
have h_limit_zero : ∀ g ∈ S, Filter.Tendsto (fun n => iteratedDeriv n g 1 / Nat.factorial n) Filter.atTop (nhds 0)
  exact ?sorry_8
have h_f1_zero : ∀ g ∈ S, g 1 = 0
  exact ?sorry_9
have h_f_zero : ∀ g ∈ S, ∀ x, g x = 0
  exact ?sorry_10
have h_not_ultraconvex : ¬ ultraconvex f
  exact ?sorry_11
exact ?sorry_12


theorem exercise_2001_a5 :
  ∃! an : ℕ × ℕ, an.1 > 0 ∧ an.2 > 0 ∧ an.1^(an.2+1) - (an.1+1)^an.2 = 2001  := by
let a : ℕ := ?sorry_0
let n : ℕ := ?sorry_1
have h1 : a^(n+1) - (a+1)^n = 2001
  exact ?sorry_2
have h2 : a ∣ 2002
  exact ?sorry_3
have h3 : a % 3 = 1
  exact ?sorry_4
have h4 : n % 2 = 0
  exact ?sorry_5
have h5 : a % 2 = 1
  exact ?sorry_6
have h6 : a ∣ 1001 ∧ a % 4 = 1
  exact ?sorry_7
have h7 : a ∣ 91
  exact ?sorry_8
have h8 : a = 13
  exact ?sorry_9
have h9 : 13^(2+1) - (13+1)^2 = 2001
  exact ?sorry_10
have h10 : ∀ n' > 2, 13^(n'+1) ≠ 2001
  exact ?sorry_11
existsi (13, 2)
constructor
· exact ⟨exact ?sorry_12, exact ?sorry_13, exact ?sorry_14⟩
· intros y hy
  have ha' : y.1 = 13
    exact ?sorry_15
  have hn' : y.2 = 2
    exact ?sorry_16
  exact Prod.ext ha' hn'
