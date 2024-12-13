import Mathlib

open scoped BigOperators

theorem exercise_2018_a5 (f : ℝ → ℝ) (hf : ContDiff ℝ ⊤ f)
  (hf0 : f 0 = 0) (hf1 : f 1 = 1) (hf2 : ∀ x, f x ≥ 0) :
  ∃ (n : ℕ) (x : ℝ), iteratedDeriv n f x = 0  := by
rw [contDiff_top_iff_deriv] at hf
rcases hf.2 with ⟨n, hn⟩
exact ⟨_, _, hf.hasFTaylorSeriesUpTo_iteratedDeriv n le_top⟩
exact ⟨n, hf0, Eq.trans (hn.zero_eq x) (hf1.symm ▸ hasDerivAt_zero_fun).eq_iteratedFDeriv⟩
exact ⟨n, f, tendsto_nhds_unique (tendsto_iteratedDeriv hf.1) (tendsto_iteratedDeriv hf.2)⟩
exact ⟨_, _, HasFTaylorSeriesUpTo.hasFTaylorSeriesAt hn hf0 hf1⟩
exact ⟨_, _, HasFTaylorSeriesUpTo_iteratedFDeriv hn hf0 hf1⟩
rw [← hasFTaylorSeriesUpToOn_univ_iff] at hn
exact ⟨_, _, HasFTaylorSeriesUpToOn.iteratedFDeriv_eq_zero hn hf0 hf1⟩
exact ⟨_, _, HasFTaylorSeriesUpToOn.eq_iteratedFDeriv hn hf1 hf2⟩
simp [← iteratedDeriv_eqFTaylorSeriesUpToOn_iteratedFDeriv hf.1 hn] at hf2 ⊢
exact ⟨0, f 0, by simp [hf0]⟩


theorem exercise_2018_b4 (a : ℝ) (x : ℕ → ℝ) (hx0 : x 0 = a)
  (hx1 : x 1 = a)
  (hxn : ∀ n : ℕ, n ≥ 2 → x (n+1) = 2*(x n)*(x (n-1)) - x (n-2))
  (h : ∃ n, x n = 0) :
  ∃ c, Function.Periodic x c  := by
refine ⟨0, ?_⟩
simpa [sub_eq_zero] using h

