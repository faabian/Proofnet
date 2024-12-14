import Mathlib

open Filter Set TopologicalSpace
open scoped Topology
noncomputable section

theorem exercise_13_1 (X : Type*) [TopologicalSpace X] (A : Set X)
  (h1 : ∀ x ∈ A, ∃ U : Set X, x ∈ U ∧ IsOpen U ∧ U ⊆ A) :
  IsOpen A  := by
let U := ⋃ x ∈ A, Classical.choose (h1 x ‹x ∈ A›)
have hU_open : IsOpen U
  exact ?sorry_0
have hU_subset : U ⊆ A
  exact ?sorry_1
have hA_subset : A ⊆ U
  exact ?sorry_2
have hA_eq_U : A = U
  exact ?sorry_3
rw [hA_eq_U]
exact hU_open


theorem exercise_31_2 {X : Type*}
  [TopologicalSpace X] [NormalSpace X] {A B : Set X}
  (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) :
  ∃ (U V : Set X), IsOpen U ∧ IsOpen V ∧ A ⊆ U ∧ B ⊆ V ∧ closure U ∩ closure V = ∅  := by
have hUV : ∃ (U V : Set X), IsOpen U ∧ IsOpen V ∧ A ⊆ U ∧ B ⊆ V ∧ Disjoint U V
  exact ?sorry_0
rcases hUV with ⟨U, V, hU_open, hV_open, hA_U, hB_V, hUV_disjoint⟩
have h_closureU_disjoint_B : Disjoint (closure U) B
  have hXminusV_closed : IsClosed (Set.univ \ V)
    exact ?sorry_1
  have hU_subset_XminusV : U ⊆ Set.univ \ V
    exact ?sorry_2
  have h_closureU_subset_XminusV : closure U ⊆ Set.univ \ V
    exact ?sorry_3
  exact ?sorry_4
have h_closureV_disjoint_A : Disjoint (closure V) A
  have hXminusU_closed : IsClosed (Set.univ \ U)
    exact ?sorry_5
  have hV_subset_XminusU : V ⊆ Set.univ \ U
    exact ?sorry_6
  have h_closureV_subset_XminusU : closure V ⊆ Set.univ \ U
    exact ?sorry_7
  exact ?sorry_8
have h_closureU_closureV_disjoint : closure U ∩ closure V = ∅
  exact ?sorry_9
exact ⟨U, V, hU_open, hV_open, hA_U, hB_V, h_closureU_closureV_disjoint⟩


theorem exercise_25_4 {X : Type*} [TopologicalSpace X]
  [LocPathConnectedSpace X] (U : Set X) (hU : IsOpen U)
  (hcU : IsConnected U) : IsPathConnected U  := by
let pathComponents := {C : Set X | IsPathConnected C ∧ C ⊆ U}
have hPathCompOpenInU : ∀ (C : Set X), C ∈ pathComponents → IsOpen (C ∩ U)
  exact ?sorry_0
have hPathCompClopen : ∀ (C : Set X), C ∈ pathComponents → IsClopen (C ∩ U)
  exact ?sorry_1
have hPathCompAllOrEmpty : ∀ (C : Set X), C ∈ pathComponents → (C = ∅ ∨ C = U)
  exact ?sorry_2
have hUPathConnected : IsPathConnected U
  exact ?sorry_3
exact hUPathConnected


theorem exercise_29_10 {X : Type*}
  [TopologicalSpace X] [T2Space X] (x : X)
  (hx : ∃ U : Set X, x ∈ U ∧ IsOpen U ∧ (∃ K : Set X, U ⊂ K ∧ IsCompact K))
  (U : Set X) (hU : IsOpen U) (hxU : x ∈ U) :
  ∃ (V : Set X), IsOpen V ∧ x ∈ V ∧ IsCompact (closure V) ∧ closure V ⊆ U  := by
rcases hx with ⟨W, hxW, hW_open, ⟨C, hWC, hC_compact⟩⟩
let UW := U ∩ W
have hUW_open : IsOpen UW
  exact ?sorry_0
have hxUW : x ∈ UW
  exact ?sorry_1
let F := C \ UW
have hF_closed_in_C : IsClosed F
  exact ?sorry_2
have hF_compact : IsCompact F
  exact ?sorry_3
have h_disjoint : ∃ V1 V2 : Set X, IsOpen V1 ∧ IsOpen V2 ∧ x ∈ V1 ∧ F ⊆ V2 ∧ Disjoint V1 V2
  exact ?sorry_4
rcases h_disjoint with ⟨V1, V2, hV1_open, hV2_open, hxV1, hFV2, h_disj⟩
let V := V1 ∩ U ∩ W
have hV_open : IsOpen V
  exact ?sorry_5
have hxV : x ∈ V
  exact ?sorry_6
have h_closureV_compact : IsCompact (closure V)
  exact ?sorry_7
have h_closureV_subset_U : closure V ⊆ U
  exact ?sorry_8
exact ⟨V, hV_open, hxV, h_closureV_compact, h_closureV_subset_U⟩


theorem exercise_22_2b {X : Type*} [TopologicalSpace X]
  {A : Set X} (r : X → A) (hr : Continuous r) (h : ∀ x : A, r x = x) :
  QuotientMap r  := by
let i : A → X := Subtype.val
have hi : Continuous i
  exact ?sorry_0
have hri : ∀ x : A, (r ∘ i) x = x
  intro x
  simp [Function.comp, i]
  exact h x
have hquot : r ∘ i = id
  exact ?sorry_1
exact ?sorry_2


theorem exercise_23_3 {X : Type*} [TopologicalSpace X]
  [TopologicalSpace X] {A : ℕ → Set X}
  (hAn : ∀ n, IsConnected (A n))
  (A₀ : Set X)
  (hA : IsConnected A₀)
  (h : ∀ n, A₀ ∩ A n ≠ ∅) :
  IsConnected (A₀ ∪ (⋃ n, A n))  := by
have hA₀n_connected : ∀ n, IsConnected (A₀ ∪ A n)
  intro n
  have h_inter : A₀ ∩ A n ≠ ∅
    exact h n
  have h_connected : IsConnected (A n)
    exact hAn n
  exact ?sorry_0
have h_union_connected : IsConnected (⋃ n, A₀ ∪ A n)
  exact ?sorry_1
have h_final : A₀ ∪ (⋃ n, A n) = ⋃ n, A₀ ∪ A n
  exact ?sorry_2
rw [h_final]
exact h_union_connected


theorem exercise_31_1 {X : Type*} [TopologicalSpace X]
  (hX : RegularSpace X) (x y : X) :
  ∃ (U V : Set X), IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ closure U ∩ closure V = ∅  := by
have hHausdorff : ∃ (U V : Set X), IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ U ∩ V = ∅
  exact ?sorry_0
obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := hHausdorff
have hy_not_closureU : y ∉ closure U
  exact ?sorry_1
have hRegular : ∃ (U' V' : Set X), IsOpen U' ∧ IsOpen V' ∧ closure U ⊆ U' ∧ y ∈ V' ∧ U' ∩ V' = ∅
  exact ?sorry_2
obtain ⟨U', V', hU', hV', hClosureU_U', hyV', hU'V'⟩ := hRegular
have hDisjointClosures : closure U ∩ closure V' = ∅
  exact ?sorry_3
exact ⟨U, V', hU, hV', hxU, hyV', hDisjointClosures⟩


theorem exercise_20_2
  [TopologicalSpace (ℝ ×ₗ ℝ)] [OrderTopology (ℝ ×ₗ ℝ)]
  : MetrizableSpace (ℝ ×ₗ ℝ)  := by
have h_dict_eq_prod : (ℝ ×ₗ ℝ) = (ℝ × ℝ)
  exact ?sorry_0
have h_metrizable_Rd : MetrizableSpace ℝ
  exact ?sorry_1
have h_metrizable_R : MetrizableSpace ℝ
  exact ?sorry_2
have h_prod_metrizable : MetrizableSpace (ℝ × ℝ)
  let X := ℝ
  let Y := ℝ
  let d : X → X → ℝ := ?sorry_3
  let d' : Y → Y → ℝ := ?sorry_4
  let ρ : (X × Y) → (X × Y) → ℝ := fun (x y : X × Y) => max (d x.1 y.1) (d' x.2 y.2)
  have h_ρ_metric : MetricSpace (X × Y)
    exact ?sorry_5
  have h_ρ_induces_prod_topology : TopologicalSpace (X × Y)
    exact ?sorry_6
  exact ?sorry_7
exact ?sorry_8


theorem exercise_24_2 {f : (Metric.sphere 0 1 : Set ℝ) → ℝ}
  (hf : Continuous f) : ∃ x, f x = f (-x)  := by
by_contra h
let g : (Metric.sphere 0 1 : Set ℝ) → ℝ := λ x => f x - f (-x)
have hg : Continuous g
  exact ?sorry_0
have hgt : ∃ x, g x > 0
  exact ?sorry_1
rcases hgt with ⟨x, hx_pos⟩
have hlt : g (-x) < 0
  exact ?sorry_2
have hy : ∃ y, g y = 0
  exact ?sorry_3
rcases hy with ⟨y, hy_eq⟩
have : f y = f (-y)
  exact eq_of_sub_eq_zero hy_eq
exact h ⟨y, this⟩


theorem exercise_27_4
  {X : Type*} [MetricSpace X] [ConnectedSpace X] (hX : ∃ x y : X, x ≠ y) :
  ¬ Countable (univ : Set X)  := by
rcases hX with ⟨x, y, hxy⟩
let d_x : X → ℝ := λ z => dist x z
have h_continuous : Continuous d_x
  exact ?sorry_0
have h_connected_image : IsConnected (d_x '' (univ : Set X))
  exact ?sorry_1
have h_zero_in_image : 0 ∈ d_x '' (univ : Set X)
  exact ?sorry_2
have h_dxy_pos : dist x y > 0
  exact ?sorry_3
have h_interval : ∃ δ > 0, Icc 0 δ ⊆ d_x '' (univ : Set X)
  exact ?sorry_4
have h_uncountable : ¬ Countable (univ : Set X)
  exact ?sorry_5
exact h_uncountable


theorem exercise_28_6 {X : Type*} [MetricSpace X]
  [CompactSpace X] {f : X → X} (hf : Isometry f) :
  Function.Bijective f  := by
have h_inj : Function.Injective f
  exact ?sorry_0
by_contra h_not_surj
have h_compact_fX : IsCompact (Set.range f)
  exact ?sorry_1
have h_closed_fX : IsClosed (Set.range f)
  exact ?sorry_2
obtain ⟨a, ha⟩ : ∃ a, a ∉ Set.range f := ?sorry_3
let x : ℕ → X := fun n => Nat.recOn n a (fun _ xn => f xn)
have h_dist : ∃ ε > 0, ∀ n m, n ≠ m → dist (x n) (x m) ≥ ε
  exact ?sorry_4
have h_no_convergent_subseq : ¬ ∃ l : X, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Filter.Tendsto (x ∘ φ) Filter.atTop (nhds l)
  exact ?sorry_5
have h_contradiction : False
  exact ?sorry_6
exact h_contradiction


theorem exercise_34_9
  (X : Type*) [TopologicalSpace X] [CompactSpace X]
  (X1 X2 : Set X) (hX1 : IsClosed X1) (hX2 : IsClosed X2)
  (hX : X1 ∪ X2 = univ) (hX1m : MetrizableSpace X1)
  (hX2m : MetrizableSpace X2) : MetrizableSpace X  := by
have hX1_compact : CompactSpace X1
  exact ?sorry_0
have hX2_compact : CompactSpace X2
  exact ?sorry_1
have hX1_hausdorff : T2Space X1
  exact ?sorry_2
have hX2_hausdorff : T2Space X2
  exact ?sorry_3
have hX1_second_countable : SecondCountableTopology X1
  exact ?sorry_4
have hX2_second_countable : SecondCountableTopology X2
  exact ?sorry_5
have hX_second_countable : SecondCountableTopology X
  by_cases h_disjoint : X1 ∩ X2 = ∅
  · have hX1_open : IsOpen X1 := ?sorry_6
    have hX2_open : IsOpen X2
      exact ?sorry_7
    have h_union_basis : ∃ B : Set (Set X), (∀ U ∈ B, IsOpen U) ∧ (∀ x, ∃ U ∈ B, x ∈ U) ∧ B.Countable
      exact ?sorry_8
    exact ?sorry_9
  · have h_basis : ∃ B : Set (Set X), (∀ U ∈ B, IsOpen U) ∧ (∀ x, ∃ U ∈ B, x ∈ U) ∧ B.Countable := by
    have h_basis_X1 : ∃ B1 : Set (Set X), (∀ U ∈ B1, IsOpen U) ∧ (∀ x ∈ X1, ∃ U ∈ B1, x ∈ U) ∧ B1.Countable
      exact ?sorry_10
    have h_basis_X2 : ∃ B2 : Set (Set X), (∀ U ∈ B2, IsOpen U) ∧ (∀ x ∈ X2, ∃ U ∈ B2, x ∈ U) ∧ B2.Countable
      exact ?sorry_11
    have h_combined_basis : ∃ B : Set (Set X), (∀ U ∈ B, IsOpen U) ∧ (∀ x, ∃ U ∈ B, x ∈ U) ∧ B.Countable
      exact ?sorry_12
    exact ?sorry_13
    exact ?sorry_14
exact ?sorry_15


theorem exercise_23_9 {X Y : Type*}
  [TopologicalSpace X] [TopologicalSpace Y]
  (A₁ A₂ : Set X)
  (B₁ B₂ : Set Y)
  (hA : A₁ ⊂ A₂)
  (hB : B₁ ⊂ B₂)
  (hA : IsConnected A₂)
  (hB : IsConnected B₂) :
  IsConnected ({x | ∃ a b, x = (a, b) ∧ a ∈ A₂ ∧ b ∈ B₂} \
      {x | ∃ a b, x = (a, b) ∧ a ∈ A₁ ∧ b ∈ B₁})  := by
have h_nonempty : ((A₂ \ A₁) ×ˢ (B₂ \ B₁)).Nonempty
  exact ?sorry_0
rcases h_nonempty with ⟨c, d, hc, hd⟩
let U_x (x : X) : Set (X × Y) := (A₂ ×ˢ {c.2}) ∪ ({x} ×ˢ B₂)
have hUx_connected : ∀ x ∈ A₂ \ A₁, IsConnected (U_x x)
  intro x hx
  have h1 : IsConnected (A₂ ×ˢ {c.2})
    exact ?sorry_1
  have h2 : IsConnected ({x} ×ˢ B₂)
    exact ?sorry_2
  have h_common : (A₂ ×ˢ {c.2}) ∩ ({x} ×ˢ B₂) ≠ ∅
    exact ?sorry_3
  exact ?sorry_4
let U := ⋃ x ∈ A₂ \ A₁, U_x x
have hU_connected : IsConnected U
  have h_common_point : ∀ x ∈ A₂ \ A₁, (c.1, c.2) ∈ U_x x
    exact ?sorry_5
  exact ?sorry_6
let V_y (y : Y) : Set (X × Y) := (A₂ ×ˢ {y}) ∪ ({c.1} ×ˢ B₂)
have hVy_connected : ∀ y ∈ B₂ \ B₁, IsConnected (V_y y)
  intro y hy
  have h1 : IsConnected (A₂ ×ˢ {y})
    exact ?sorry_7
  have h2 : IsConnected ({c.1} ×ˢ B₂)
    exact ?sorry_8
  have h_common : (A₂ ×ˢ {y}) ∩ ({c.1} ×ˢ B₂) ≠ ∅
    exact ?sorry_9
  exact ?sorry_10
let V := ⋃ y ∈ B₂ \ B₁, V_y y
have hV_connected : IsConnected V
  have h_common_point : ∀ y ∈ B₂ \ B₁, (c.1, c.2) ∈ V_y y
    exact ?sorry_11
  exact ?sorry_12
have h_union : ({x | ∃ a b, x = (a, b) ∧ a ∈ A₂ ∧ b ∈ B₂} \ {x | ∃ a b, x = (a, b) ∧ a ∈ A₁ ∧ b ∈ B₁}) = U ∪ V
  exact ?sorry_13
have h_common_UV : (U ∩ V).Nonempty
  exact ?sorry_14
exact ?sorry_15


theorem exercise_17_4 {X : Type*} [TopologicalSpace X]
  (U A : Set X) (hU : IsOpen U) (hA : IsClosed A) :
  IsOpen (U \ A) ∧ IsClosed (A \ U)  := by
have h1 : U \ A = U ∩ (Set.univ \ A)
  exact ?sorry_0
have h2 : IsOpen (U ∩ (Set.univ \ A))
  exact ?sorry_1
have h3 : IsOpen (U \ A)
  exact ?sorry_2
have h4 : A \ U = A ∩ (Set.univ \ U)
  exact ?sorry_3
have h5 : IsClosed (A ∩ (Set.univ \ U))
  exact ?sorry_4
have h6 : IsClosed (A \ U)
  exact ?sorry_5
exact ⟨h3, h6⟩


theorem exercise_18_8b {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [LinearOrder Y] [OrderTopology Y] {f g : X → Y}
  (hf : Continuous f) (hg : Continuous g) :
  Continuous (λ x => min (f x) (g x))  := by
have h_min_continuous : Continuous (λ p : Y × Y => min p.1 p.2)
  exact ?sorry_0
have h_prod_continuous : Continuous (λ x => (f x, g x))
  apply Continuous.prod_mk
  · exact hf
  · exact hg
exact Continuous.comp h_min_continuous h_prod_continuous


theorem exercise_32_1 {X : Type*} [TopologicalSpace X]
  (hX : NormalSpace X) (A : Set X) (hA : IsClosed A) :
  NormalSpace {x // x ∈ A}  := by
have hT1 : ∀ y : {x // x ∈ A}, IsClosed ({y} : Set {x // x ∈ A})
  intro y
  have hy_closed_in_X : IsClosed ({y.val} : Set X)
    exact ?sorry_0
  have hy_closed_in_A : IsClosed ({y} : Set {x // x ∈ A})
    exact ?sorry_1
  exact hy_closed_in_A
have hT4 : ∀ F G : Set {x // x ∈ A}, IsClosed F → IsClosed G → Disjoint F G →
  ∃ U V : Set {x // x ∈ A}, IsOpen U ∧ IsOpen V ∧ F ⊆ U ∧ G ⊆ V ∧ Disjoint U V := by
  intros F G hF_closed hG_closed h_disjoint
  have hF_closed_in_X : IsClosed (Subtype.val '' F : Set X)
    exact ?sorry_2
  have hG_closed_in_X : IsClosed (Subtype.val '' G : Set X)
    exact ?sorry_3
  have h_disjoint_in_X : Disjoint (Subtype.val '' F) (Subtype.val '' G)
    exact ?sorry_4
  obtain ⟨U, V, hU_open, hV_open, hF_U, hG_V, hUV_disjoint⟩ :
    ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ (Subtype.val '' F) ⊆ U ∧ (Subtype.val '' G) ⊆ V ∧ Disjoint U V := ?sorry_5
  let U' : Set {x // x ∈ A} := {x | x.val ∈ U}
  let V' : Set {x // x ∈ A} := {x | x.val ∈ V}
  have hU'_open : IsOpen U'
    exact ?sorry_6
  have hV'_open : IsOpen V'
    exact ?sorry_7
  have hF_U' : F ⊆ U'
    exact ?sorry_8
  have hG_V' : G ⊆ V'
    exact ?sorry_9
  have hU'V'_disjoint : Disjoint U' V'
    exact ?sorry_10
  exact ⟨U', V', hU'_open, hV'_open, hF_U', hG_V', hU'V'_disjoint⟩
apply NormalSpace.mk
intro F G hF_closed hG_closed h_disjoint
exact hT4 F G hF_closed hG_closed h_disjoint
