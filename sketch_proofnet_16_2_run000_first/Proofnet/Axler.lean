import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem exercise_1_3 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] {v : V} : -(-v) = v  := by
have h1 : (-v) + (-(-v)) = 0
· exact ?sorry_0
  simp
· have h2 : v + (-v) = 0
  · exact ?sorry_1
    simpa only [neg_neg, add_right_neg] using h1
  · have h3 : v = -(-v)
    · exact ?sorry_2
      rw [neg_neg ]
    · exact h3.symm


theorem exercise_1_4 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] (v : V) (a : F): a • v = 0 ↔ a = 0 ∨ v = 0  := by
simpa only [smul_eq_zero, or_comm] using exercise_4 v a


theorem exercise_1_8 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] {ι : Type*} (u : ι → Submodule F V) :
  ∃ U : Submodule F V, (⋂ (i : ι), (u i).carrier) = ↑U  := by
letI := Classical.decEq ι
refine ⟨_, Exercise.coeFn exercises_1 exercises_2⟩
refine ⟨_, Submodule.iInter_carrier_eq_of_rel fun i j => ?_⟩
refine ⟨_, Set.ext <| iInter_congr fun i => ?_⟩
refine ⟨iInf u, ?_⟩
simp
rfl


theorem exercise_3_1 {F V : Type*}
  [AddCommGroup V] [Field F] [Module F V] [FiniteDimensional F V]
  (T : V →ₗ[F] V) (hT : finrank F V = 1) :
  ∃ c : F, ∀ v : V, T v = c • v := by
have basis : Basis (Fin 1) F V
· exact ?sorry_0
  apply basisUnique
  exact hT
· let v := basis 0
  have hv : ∀ w : V, ∃ a : F, w = a • v
  · exact ?sorry_1
    exact fun w => ⟨_, basis.repr_apply_apply w 0⟩
    exact fun w => ⟨_, Basis.repr_apply_apply _ _ _⟩
    exact fun w => ⟨_, basis.repr_apply_apply w 0⟩
    exact fun w => ⟨_, basis.repr_apply_apply w 0⟩
    exact fun w =>
  ⟨basis.repr w 0, Eq.symm (by simpa [v] using basis.sum_repr w)⟩
  · have hc : ∃ c : F, T v = c • v
    · exact ?sorry_2
      exact (hv (T v)).imp fun a => by simp
    · obtain ⟨c, hc⟩ := hc
      use c
      intro w
      obtain ⟨a, ha⟩ := hv w
      rw [ha, LinearMap.map_smul, hc]
      simp only [smul_smul]
      rw [mul_comm]

