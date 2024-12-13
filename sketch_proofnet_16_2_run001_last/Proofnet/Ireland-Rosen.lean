import Mathlib

open Real
open scoped BigOperators
noncomputable section

theorem exercise_1_31  : (⟨1, 1⟩ : GaussianInt) ^ 2 ∣ 2  := by
have h1 : (⟨1, 1⟩ : GaussianInt) ^ 2 = ⟨0, 2⟩
· exact ?sorry_0
  decide
· have h2 : 2 = (⟨1, 1⟩ : GaussianInt) ^ 2 * -⟨0, 1⟩
  · exact ?sorry_1
    rw [h1 ]
    rfl
  · exact Exists.intro (-⟨0, 1⟩) h2

