import Mathlib

open Filter Real Function
open scoped Topology
noncomputable section

theorem exercise_2_26 {M : Type*} [TopologicalSpace M]
  (U : Set M) : IsOpen U ↔ ∀ x ∈ U, ¬ ClusterPt x (𝓟 Uᶜ)  := by
rw [isOpen_iff_mem_nhds ]
simp only [ClusterPt, not_forall, not_not, mem_principal, U] <;> exact fun _ => exercise_1_26
congr! 4 with x
simp
rw [← Filter.mem_iff_inf_principal_compl, mem_nhds_iff ]


theorem exercise_2_32a (A : Set ℕ) : IsClopen A  := by
exact isClopen_discrete A


theorem exercise_2_41 (m : ℕ) {X : Type*} [NormedSpace ℝ ((Fin m) → ℝ)] :
  IsCompact (Metric.closedBall 0 1)  := by
apply isCompact_closedBall

