import Mathlib

open scoped BigOperators

theorem exercise_2018_a5 (f : ℝ → ℝ) (hf : ContDiff ℝ ⊤ f)
  (hf0 : f 0 = 0) (hf1 : f 1 = 1) (hf2 : ∀ x, f x ≥ 0) :
  ∃ (n : ℕ) (x : ℝ), iteratedDeriv n f x = 0  := by
rw [contDiff_top_iff_fderiv] at hf
rcases hf with ⟨hf', hf'_diff⟩
exact
  ⟨0, 0, by simpa only [Nat.zero_eq, iteratedDeriv_zero] using hf0⟩


theorem exercise_2018_b4 (a : ℝ) (x : ℕ → ℝ) (hx0 : x 0 = a)
  (hx1 : x 1 = a)
  (hxn : ∀ n : ℕ, n ≥ 2 → x (n+1) = 2*(x n)*(x (n-1)) - x (n-2))
  (h : ∃ n, x n = 0) :
  ∃ c, Function.Periodic x c  := by
rcases h with ⟨n, hn⟩
rcases eq_or_ne n 1 with rfl | hne
· exact ⟨0, fun n ↦ by simp [hn]⟩
· exact ⟨n - n, by simp [sub_eq_zero.mp (Nat.sub_self n)]⟩

