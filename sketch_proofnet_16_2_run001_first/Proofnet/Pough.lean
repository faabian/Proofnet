import Mathlib

open Filter Real Function
open scoped Topology
noncomputable section

theorem exercise_2_26 {M : Type*} [TopologicalSpace M]
  (U : Set M) : IsOpen U ↔ ∀ x ∈ U, ¬ ClusterPt x (𝓟 Uᶜ)  := by
simp [isOpen_iff_mem_nhds, clusterPt_principal_iff, not_forall, exists_prop, U] <;>
  exact fun x => id
aesop
· exact ⟨U, a x a_1, by simp⟩
· rcases a x a_1 with ⟨s, hs, h⟩
  exact mem_of_superset hs fun y hy => Classical.not_not.1 fun hY => h ⟨y, hy, hY⟩


theorem exercise_2_32a (A : Set ℕ) : IsClopen A  := by
rw [← Set.inter_union_compl A ]
apply IsClopen.union <;> apply IsClosed.isClopen <;> simp
exact disjointed A


theorem exercise_2_41 (m : ℕ) {X : Type*} [NormedSpace ℝ ((Fin m) → ℝ)] :
  IsCompact (Metric.closedBall 0 1)  := by
apply isCompact_closedBall _

