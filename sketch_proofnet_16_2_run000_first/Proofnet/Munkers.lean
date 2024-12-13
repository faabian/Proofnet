import Mathlib

open Filter Set TopologicalSpace
open scoped Topology
noncomputable section

theorem exercise_13_1 (X : Type*) [TopologicalSpace X] (A : Set X)
  (h1 : ∀ x ∈ A, ∃ U : Set X, x ∈ U ∧ IsOpen U ∧ U ⊆ A) :
  IsOpen A  := by
rw [isOpen_iff_forall_mem_open ]
intro x hxU
obtain ⟨U, hU, hU'⟩ := h1 x hxU
exact ⟨U, hU'.2, hU'.1, hU⟩


theorem exercise_16_4 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (π₁ : X × Y → X)
  (π₂ : X × Y → Y)
  (h₁ : π₁ = Prod.fst)
  (h₂ : π₂ = Prod.snd) :
  IsOpenMap π₁ ∧ IsOpenMap π₂  := by
subst h₁
refine ⟨isOpenMap_fst, ?_⟩
rw [h₂ ]
exact isOpenMap_snd


theorem exercise_17_4 {X : Type*} [TopologicalSpace X]
  (U A : Set X) (hU : IsOpen U) (hA : IsClosed A) :
  IsOpen (U \ A) ∧ IsClosed (A \ U)  := by
have h1 : U \ A = U ∩ Aᶜ
· ext x
  simp only [Set.mem_diff, Set.mem_inter_iff, Set.mem_compl_iff]
· have h2 : IsOpen (U ∩ Aᶜ)
  · apply IsOpen.inter
    · exact hU
    · exact isOpen_compl_iff.mpr hA
  · have h3 : IsOpen (U \ A)
    · rw [h1]
      exact h2
    · have h4 : A \ U = A ∩ Uᶜ
      · ext x
        simp only [Set.mem_diff, Set.mem_inter_iff, Set.mem_compl_iff]
      · have h5 : IsClosed (A ∩ Uᶜ)
        · apply IsClosed.inter
          · exact hA
          · exact isClosed_compl_iff.mpr hU
        · have h6 : IsClosed (A \ U)
          · rw [h4]
            exact h5
          · exact ⟨h3, h6⟩


theorem exercise_18_8a {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [LinearOrder Y] [OrderTopology Y] {f g : X → Y}
  (hf : Continuous f) (hg : Continuous g) :
  IsClosed {x | f x ≤ g x}  := by
simpa only [Set.setOf_and, Set.setOf_forall, ← forall_and] using
  isClosed_le hf hg


theorem exercise_18_8b {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [LinearOrder Y] [OrderTopology Y] {f g : X → Y}
  (hf : Continuous f) (hg : Continuous g) :
  Continuous (λ x => min (f x) (g x))  := by
apply Continuous.min
· · exact hf
· · exact hg


theorem exercise_19_6a
  {n : ℕ}
  {f : Fin n → Type*} {x : ℕ → Πa, f a}
  (y : Πi, f i)
  [Πa, TopologicalSpace (f a)] :
  Tendsto x atTop (𝓝 y) ↔ ∀ i, Tendsto (λ j => (x j) i) atTop (𝓝 (y i))  := by
rw [tendsto_pi_nhds ]


theorem exercise_22_2b {X : Type*} [TopologicalSpace X]
  {A : Set X} (r : X → A) (hr : Continuous r) (h : ∀ x : A, r x = x) :
  QuotientMap r  := by
rw [quotientMap_iff ]
aesop
· exact fun a => ⟨a, h a a.2⟩
· exact hr.isOpen_preimage _ a
· simp [isOpen_coinduced, preimage_setOf_eq] at a ⊢
  convert a
  rw [preimage_preimage ]
  simp [preimage_id', preimage_id] at a
  rw [isOpen_induced_iff ]
  aesop


theorem exercise_22_5 {X Y : Type*} [TopologicalSpace X]
  [TopologicalSpace Y] (p : X → Y) (hp : IsOpenMap p)
  (A : Set X) (hA : IsOpen A) : IsOpenMap (p ∘ Subtype.val : A → Y)  := by
simpa using hp.restrict hA


theorem exercise_23_2 {X : Type*}
  [TopologicalSpace X] {A : ℕ → Set X} (hA : ∀ n, IsConnected (A n))
  (hAn : ∀ n, A n ∩ A (n + 1) ≠ ∅) :
  IsConnected (⋃ n, A n)  := by
apply IsConnected.iUnion_of_chain
· exact hA
· exact fun n => Set.Nonempty.mono (inter_subset_inter_right _ <| A_succ_subset (hAn n)) <|
 exercise_14_2 hA hAn n
  intro n
  rw [inter_comm ]
  push_neg at hAn
  simpa [inter_comm] using hAn n


theorem exercise_32_3 {X : Type*} [TopologicalSpace X]
  (hX : LocallyCompactSpace X) (hX' : T2Space X) :
  RegularSpace X  := by
infer_instance

