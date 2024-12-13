import Mathlib

open Filter Set TopologicalSpace
open scoped Topology
noncomputable section

theorem exercise_13_1 (X : Type*) [TopologicalSpace X] (A : Set X)
  (h1 : ∀ x ∈ A, ∃ U : Set X, x ∈ U ∧ IsOpen U ∧ U ⊆ A) :
  IsOpen A  := by
let U := ⋃ x ∈ A, Classical.choose (h1 x ‹x ∈ A›)
have hA_eq_union : A = U
· have hA_subset_U : A ⊆ U
  · exact ?sorry_0
    intro x hx
    exact mem_iUnion₂.2 ⟨x, hx, (h1 x hx).choose_spec.1⟩
  · have hU_subset_A : U ⊆ A
    · exact ?sorry_1
      exact iUnion₂_subset fun x hx => (Classical.choose_spec <| h1 x hx).2.2
    · exact ?sorry_2
      exact hA_subset_U.antisymm hU_subset_A
· have hU_open : IsOpen U
  · exact ?sorry_3
    exact isOpen_iUnion fun x => isOpen_iUnion fun _ => (Classical.choose_spec <| h1 x _).2.1
    exact isOpen_iUnion fun x => isOpen_iUnion fun _ => (Classical.choose_spec <| h1 x ‹_›).2.1
  · rw [hA_eq_union]
    exact hU_open


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
rw [and_comm ]
exact ⟨hA.sdiff hU, hU.sdiff hA⟩


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
have h_continuous_min : Continuous (fun p : Y × Y => min p.1 p.2)
· exact continuous_min
· have h_prod_continuous : Continuous (fun x => (f x, g x))
  · exact Continuous.prod_mk hf hg
  · exact h_continuous_min.comp h_prod_continuous


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
rw [quotientMap_iff_closed ]
exact ⟨fun x => ⟨x, fun _ => rfl⟩, fun s => ⟨fun hs => ⟨_, hs.preimage hr⟩, fun hs => ⟨_, hs.image hr⟩⟩⟩
exact ⟨fun a => ⟨_, (h a).symm⟩, fun s => ⟨_, hr.isClosed_preimage⟩⟩
exact ⟨Function.Surjective.of_comp fun x => (h x).symm, fun s => hr.isClosed_preimage⟩
exact ⟨fun a => ⟨_, h a⟩, fun s => ⟨_, @isClosed_quotientMap_iff _ _ (QuotientMap.mk r) s⟩⟩
exact ⟨fun x => ⟨r x, fun _ => x.property, fun _ => rfl⟩, fun s => ⟨fun h1 => ?_,
  fun h2 => (isClosed_subtype_iff h2).mpr h1⟩⟩
refine ⟨fun x => ⟨r x, ?_⟩, fun s => ⟨fun hs => ?_, fun hs => ?_⟩⟩
· rw [h ]
  exact h x
· exact hs.preimage hr
· convert show IsClosed ((↑) ⁻¹' s) from hs
  rw [isClosed_induced_iff ]
  exact ⟨fun ⟨t, ht, hs⟩ => hs, fun hs => ⟨_, ht.preimage (continuous_subtype_val.comp hr), hs⟩⟩
  exact ⟨fun ⟨t, ht, h⟩ => h ▸ ht, fun hs => ⟨range (clusion hs), hs, rfl⟩⟩
  aesop


theorem exercise_22_5 {X Y : Type*} [TopologicalSpace X]
  [TopologicalSpace Y] (p : X → Y) (hp : IsOpenMap p)
  (A : Set X) (hA : IsOpen A) : IsOpenMap (p ∘ Subtype.val : A → Y)  := by
simpa only [Set.restrict_eq, Subtype.range_coe_subtype] using hp.restrict hA


theorem exercise_23_2 {X : Type*}
  [TopologicalSpace X] {A : ℕ → Set X} (hA : ∀ n, IsConnected (A n))
  (hAn : ∀ n, A n ∩ A (n + 1) ≠ ∅) :
  IsConnected (⋃ n, A n)  := by
apply IsConnected.iUnion_of_chain hA
simpa [← Set.nonempty_iff_ne_empty] using hAn


theorem exercise_25_4 {X : Type*} [TopologicalSpace X]
  [LocPathConnectedSpace X] (U : Set X) (hU : IsOpen U)
  (hcU : IsConnected U) : IsPathConnected U  := by
rw [isPathConnected_iff_pathConnectedSpace ]
rw [pathConnectedSpace_iff_connectedSpace ]
· rw [isConnected_iff_connectedSpace] at hcU
  exact hcU
· exact locPathConnected_of_isOpen hU


theorem exercise_32_3 {X : Type*} [TopologicalSpace X]
  (hX : LocallyCompactSpace X) (hX' : T2Space X) :
  RegularSpace X  := by
infer_instance

