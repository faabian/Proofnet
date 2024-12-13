import Mathlib

open Filter Set TopologicalSpace
open scoped Topology
noncomputable section

theorem exercise_13_1 (X : Type*) [TopologicalSpace X] (A : Set X)
  (h1 : ∀ x ∈ A, ∃ U : Set X, x ∈ U ∧ IsOpen U ∧ U ⊆ A) :
  IsOpen A  := by
rw [isOpen_iff_mem_nhds ]
intro x hx
rcases h1 x hx with ⟨U, ⟨hx, hUo, hU⟩⟩
exact mem_of_superset (hUo.mem_nhds hx) hU


theorem exercise_16_4 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (π₁ : X × Y → X)
  (π₂ : X × Y → Y)
  (h₁ : π₁ = Prod.fst)
  (h₂ : π₂ = Prod.snd) :
  IsOpenMap π₁ ∧ IsOpenMap π₂  := by
subst h₁
rw [h₂ ]
exact ⟨isOpenMap_fst, isOpenMap_snd⟩


theorem exercise_17_4 {X : Type*} [TopologicalSpace X]
  (U A : Set X) (hU : IsOpen U) (hA : IsClosed A) :
  IsOpen (U \ A) ∧ IsClosed (A \ U)  := by
have h1 : U \ A = U ∩ Aᶜ
· exact ?sorry_0
  rfl
· have h2 : IsOpen (U ∩ Aᶜ)
  · exact ?sorry_1
    exact hU.inter hA.isOpen_compl
  · have h3 : A \ U = A ∩ Uᶜ
    · exact ?sorry_2
      rw [diff_eq, inter_comm ]
    · have h4 : IsClosed (A ∩ Uᶜ)
      · exact ?sorry_3
        apply hA.inter
        exact isClosed_compl_iff.mpr hU
      · exact ⟨h2, h4⟩


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
apply Continuous.min hf hg <;> apply continuous_const


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
let i : A → X := fun a => a
have hi : Continuous i
· exact ?sorry_0
  exact continuous_subtype_val
· have hri : ∀ a : A, (r ∘ i) a = a
  · intro a
    simp [Function.comp, h]
  · have hQuotient : QuotientMap r
    · exact ?sorry_1
      simp [Function.comp, hri] at h
      unfold QuotientMap
      refine ⟨fun _ => ⟨_, h _⟩, ?_⟩
      exact ⟨fun a => ⟨_, h a.prop⟩, rfl⟩
      exact ⟨fun x => ⟨_, ⟨x, rfl⟩, h _ _⟩, congr_arg _ hi⟩
      exact ⟨fun a => ⟨_, (h _ _).symm⟩, rfl⟩
      exact ⟨fun a => ⟨_, h a⟩, (TopCat.homeoOfIso (subHomeomorphEquivSubtypeProdEq _ _ h)).symm.continuous⟩
      refine ⟨fun x => ⟨x, h _ x.2⟩, ?_⟩
      ext U
      letI := Subtype.instTopologicalSpace A
      rw [isOpen_induced_iff ]
      exact ⟨fun ⟨V, hV, f⟩ ↦ congr_arg ((↑) : A → Set X) hV ▸ hV.2.preimage hi,
  fun hV ↦ ⟨_, hV.2.preimage hi, Subtype.coe_injective.preimage_image⟩⟩
      exact ⟨fun ⟨V, hV, hVU⟩ ↦ hVU ▸ isOpen_induced hr (V.preimage i), fun hV ↦
  ⟨_, hi.isOpen_preimage hV, Set.Subtype.preimage_coe_eq_preimage_coe hV⟩⟩
      exact ⟨fun ⟨a, _, rfl⟩ ↦ hi.isOpenMap _ a.2, fun h ↦ ⟨_, hi.isOpenMap _ a.2, h⟩⟩
      aesop
      · apply Continuous.isOpen_preimage hr
        exact hi.isOpen_preimage _ left
      · exact ⟨_, a.1.preimage hi, preimage_compl hi.ne_univ⟩
        exact ⟨_, hi a, preimage_subtype_coe_eq_compl Subset.rfl⟩
        exact ⟨_, hr.isOpen_preimage a, preimage_subtype_coe_eq_compl hi⟩
        exact ⟨_, hr.isOpen_preimage hr, rfl⟩
        exact ⟨Set.iUnion fun a : A => Set.iUnion fun b => Set.iUnion fun _ => U, a, le_antisymm hi a⟩
        exact ⟨_, a.1.preimage hi, preimage_preimage⟩
        exact ⟨_, a.1.preimage hi, preimage_subtype_coe_eq_compl U⟩
        exact ⟨Set.iUnion fun a : A => (a : Set X) • ((↑) : A → X) ⁻¹' U,
  isOpen_iUnion fun a => (a : Set X).2.2.preimage hi, preimage_iUnion₂ _ _ _⟩
        exact ⟨_, a.2.preimage hi, preimage_id U⟩
        aesop
    · exact hQuotient


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
· intro n
  rw [inter_comm ]
  rw [inter_comm ]
  exact (Set.nonempty_iff_ne_empty.mpr (hAn n)).imp fun x hx => ⟨hx.1, hx.2⟩


theorem exercise_32_3 {X : Type*} [TopologicalSpace X]
  (hX : LocallyCompactSpace X) (hX' : T2Space X) :
  RegularSpace X  := by
infer_instance

