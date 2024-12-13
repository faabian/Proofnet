import Mathlib

open Filter Real Function
open scoped Topology
noncomputable section

theorem exercise_2_26 {M : Type*} [TopologicalSpace M]
  (U : Set M) : IsOpen U ↔ ∀ x ∈ U, ¬ ClusterPt x (𝓟 Uᶜ)  := by
simp only [isOpen_iff_mem_nhds, ClusterPt, not_neBot, mem_principal, mem_compl_iff] <;> rfl
aesop
· simpa only [←principal_le_nhds, mem_iff_inf_principal_compl] using a x a_1
· simpa [a x a_1, ← disjoint_iff, disjoint_principal_right, mem_iff_inf_principal_compl]
  using (a x a_1).symm


theorem exercise_2_32a (A : Set ℕ) : IsClopen A  := by
rw [← compl_compl A ]
simpa [← compl_eq_self] using exercise_1 chicagoA


theorem exercise_2_41 (m : ℕ) {X : Type*} [NormedSpace ℝ ((Fin m) → ℝ)] :
  IsCompact (Metric.closedBall 0 1)  := by
apply isCompact_closedBall

