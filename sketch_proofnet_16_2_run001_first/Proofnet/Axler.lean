import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem exercise_1_3 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] {v : V} : -(-v) = v  := by
rw [neg_neg ]


theorem exercise_1_4 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] (v : V) (a : F): a • v = 0 ↔ a = 0 ∨ v = 0  := by
simpa only [smul_eq_zero, or_comm] using exercise_4 v a


theorem exercise_1_8 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] {ι : Type*} (u : ι → Submodule F V) :
  ∃ U : Submodule F V, (⋂ (i : ι), (u i).carrier) = ↑U  := by
letI := Classical.decEq ι
refine ⟨iInf u, ?_⟩
simp [iInf, exercise_1] <;> rfl


theorem exercise_3_1 {F V : Type*}
  [AddCommGroup V] [Field F] [Module F V] [FiniteDimensional F V]
  (T : V →ₗ[F] V) (hT : finrank F V = 1) :
  ∃ c : F, ∀ v : V, T v = c • v := by
have hV : Nonempty (V ≃ₗ[F] F)
· exact ?sorry_0
  haveI : FiniteDimensional F V := .of_finrank_eq_succ hT
  apply nonempty_linearEquiv_of_finrank_eq
  rw [hT, finrank_self ]
· obtain ⟨φ⟩ := hV
  let v₀ := φ.symm 1
  have hTv₀ : ∃ c : F, T v₀ = c • v₀
  · exact ?sorry_1
    exact ⟨_, rfl⟩
    exact ⟨_, rfl⟩
    exact ⟨_, rfl⟩
    simpa [v₀, ← φ.toEquiv.apply_eq_iff_eq] using (finrank_eq_one_iff_of_nonzero' φ.toEquiv v₀).mp hT
  · obtain ⟨c, hc⟩ := hTv₀
    use c
    intro v
    have hv : ∃ a : F, v = a • v₀
    · exact ?sorry_2
      exact ⟨_, rfl⟩
      exact ⟨_, (φ v).symm⟩
      exact ⟨_, rfl⟩
      exact ⟨φ v, by simp [v₀, ← φ.injective.eq_iff, φ.apply_symm_apply]⟩
    · rcases hv with ⟨a, rfl⟩
      calc
  T (a • v₀) = a • T v₀ := by rw [T.map_smul]
  _ = a • (c • v₀) := by rw [hc]
  _ = (a * c) • v₀ := by rw [smul_smul]
      exact ?sorry_3
      rw [smul_smul, mul_comm ]

