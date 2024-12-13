import Mathlib

open Filter Set TopologicalSpace
open scoped Topology
noncomputable section

theorem exercise_13_1 (X : Type*) [TopologicalSpace X] (A : Set X)
  (h1 : ∀ x ∈ A, ∃ U : Set X, x ∈ U ∧ IsOpen U ∧ U ⊆ A) :
  IsOpen A  := by
rw [isOpen_iff_forall_mem_open ]
simpa [subset_def, and_assoc, and_comm, and_left_comm] using h1


theorem exercise_16_4 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (π₁ : X × Y → X)
  (π₂ : X × Y → Y)
  (h₁ : π₁ = Prod.fst)
  (h₂ : π₂ = Prod.snd) :
  IsOpenMap π₁ ∧ IsOpenMap π₂  := by
have hπ₁_open : IsOpenMap π₁
· intro U hU
  rw [h₁]
  have h_basis : ∀ (V : Set Y), IsOpen (U ×ˢ V) → IsOpen U
  · exact ?sorry_0
    tauto
  · have h_image : IsOpen (Prod.fst '' U)
    · exact ?sorry_1
      exact isOpenMap_fst _ hU
    · exact h_image
· have hπ₂_open : IsOpenMap π₂
  · intro V hV
    rw [h₂]
    have h_basis : ∀ (U : Set X), IsOpen (U ×ˢ V) → IsOpen V
    · exact ?sorry_2
      tauto
    · have h_image : IsOpen (Prod.snd '' V)
      · exact ?sorry_3
        exact isOpenMap_snd _ hV
      · exact h_image
  · exact ⟨hπ₁_open, hπ₂_open⟩


theorem exercise_17_4 {X : Type*} [TopologicalSpace X]
  (U A : Set X) (hU : IsOpen U) (hA : IsClosed A) :
  IsOpen (U \ A) ∧ IsClosed (A \ U)  := by
rw [← isOpen_compl_iff] at hA
aesop
· rw [diff_eq_compl_inter ]
  exact IsOpen.inter hA.isOpen_compl hU
· exact hA.sdiff hU


theorem exercise_18_8a {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [LinearOrder Y] [OrderTopology Y] {f g : X → Y}
  (hf : Continuous f) (hg : Continuous g) :
  IsClosed {x | f x ≤ g x}  := by
apply isClosed_le hf hg


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
trivial
· exact fun a => ⟨_, h a⟩
· ext
  rw [isOpen_induced_iff ]
  aesop
  · exact (continuous_subtype_val.comp hr).isOpen_preimage w left
  · exact ⟨_, a, Set.ext fun x => by simp [Subtype.ext_iff, h x x.2]⟩


theorem exercise_22_5 {X Y : Type*} [TopologicalSpace X]
  [TopologicalSpace Y] (p : X → Y) (hp : IsOpenMap p)
  (A : Set X) (hA : IsOpen A) : IsOpenMap (p ∘ Subtype.val : A → Y)  := by
simpa only [Set.restrict_eq, Subtype.range_coe_subtype] using hp.restrict hA


theorem exercise_23_2 {X : Type*}
  [TopologicalSpace X] {A : ℕ → Set X} (hA : ∀ n, IsConnected (A n))
  (hAn : ∀ n, A n ∩ A (n + 1) ≠ ∅) :
  IsConnected (⋃ n, A n)  := by
apply IsConnected.iUnion_of_chain
· assumption
· simpa [← Set.nonempty_iff_ne_empty] using hAn


theorem exercise_25_4 {X : Type*} [TopologicalSpace X]
  [LocPathConnectedSpace X] (U : Set X) (hU : IsOpen U)
  (hcU : IsConnected U) : IsPathConnected U  := by
rw [isPathConnected_iff_pathConnectedSpace ]
haveI := locPathConnected_of_isOpen hU hcU
haveI := locPathConnected_of_isOpen hU hcU
haveI := locPathConnected_of_isOpen hU hcU
haveI := locPathConnected_of_isOpen hU hcU
haveI := locPathConnected_of_isOpen hU
rw [pathConnectedSpace_iff_connectedSpace ]
rw [isConnected_iff_connectedSpace] at hcU
exact hcU


theorem exercise_32_3 {X : Type*} [TopologicalSpace X]
  (hX : LocallyCompactSpace X) (hX' : T2Space X) :
  RegularSpace X  := by
infer_instance

