import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators
noncomputable section

theorem exercise_1_1_2a : ∃ a b : ℤ, a - b ≠ b - a  := by
let a := 1
let b := -1
have h1 : a - b = 1 - (-1)
· exact ?sorry_0
  ring
· have h2 : b - a = -1 - 1
  · exact ?sorry_1
    ring
  · have h3 : a - b ≠ b - a
    · exact ?sorry_2
      omega
    · exact ⟨a, b, h3⟩


theorem exercise_1_1_3 (n : ℤ) :
  ∀ (a b c : ℤ), (a+b)+c ≡ a+(b+c) [ZMOD n]  := by
intro a b c
rw [← Int.add_assoc ]


theorem exercise_1_1_4 (n : ℕ) :
  ∀ (a b c : ℕ), (a * b) * c ≡ a * (b * c) [ZMOD n]  := by
intro a b c
rw [mul_assoc ]


theorem exercise_1_1_15 {G : Type*} [Group G] (as : List G) :
  as.prod⁻¹ = (as.reverse.map (λ x => x⁻¹)).prod  := by
simpa [List.prod_inv_reverse] using exercise_11_1_16 as.reverse


theorem exercise_1_1_16 {G : Type*} [Group G]
  (x : G) (hx : x ^ 2 = 1) :
  orderOf x = 1 ∨ orderOf x = 2  := by
have : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx
rwa [Nat.dvd_prime Nat.prime_two] at this


theorem exercise_1_1_17 {G : Type*} [Group G] {x : G} {n : ℕ}
  (hxn: orderOf x = n) :
  x⁻¹ = x ^ (n - 1 : ℤ)  := by
rw [← hxn, zpow_sub, zpow_one, zpow_natCast ]
simp
exact pow_orderOf_eq_one x


theorem exercise_1_1_20 {G : Type*} [Group G] {x : G} :
  orderOf x = orderOf x⁻¹  := by
simp


theorem exercise_1_1_25 {G : Type*} [Group G]
  (h : ∀ x : G, x ^ 2 = 1) : ∀ a b : G, a*b = b*a  := by
intros a b
rw [← mul_right_inj a, ← mul_left_inj b ]
calc
  a * (a * b) * b = a ^ 2 * b ^ 2 := by simp only [pow_two]; group
  _ = 1 := by rw [h, h, mul_one]
  _ = (a * b) ^ 2 := by rw [h]
  _ = a * (b * a) * b := by simp only [pow_two]; group


theorem exercise_1_3_8 : Infinite (Equiv.Perm ℕ)  := by
let f : ℕ → Equiv.Perm ℕ := fun n => Equiv.swap 1 n
have h_injective : Function.Injective f
· intro n m h_eq
  exact ?sorry_0
  simp [f, Equiv.swap_eq_iff] at h_eq
  simpa [f] using Equiv.congr_fun h_eq 1
· have h_card_le : Cardinal.mk ℕ ≤ Cardinal.mk (Equiv.Perm ℕ)
  · apply Cardinal.mk_le_of_injective h_injective
  · have h_aleph0 : Cardinal.mk ℕ = Cardinal.aleph0
    · exact Cardinal.mk_nat
    · rw [h_aleph0] at h_card_le
      exact Cardinal.infinite_iff.2 h_card_le


theorem exercise_1_6_11 {A B : Type*} [Group A] [Group B] :
  Nonempty (A × B ≃* B × A)  := by
let φ : A × B → B × A := fun p => (p.2, p.1)
let ψ : B × A → A × B := fun p => (p.2, p.1)
have h_bij : Function.Bijective φ
· exact ?sorry_0
  constructor <;> intro p <;> simp [φ, ψ] <;> clear p
· have h_inv : Function.LeftInverse ψ φ ∧ Function.RightInverse ψ φ
  · exact ?sorry_1
    exact ⟨fun p ↦ rfl, fun p ↦ rfl⟩
  · have h_hom : ∀ (x y : A × B), φ (x * y) = φ x * φ y
    · intros x y
      rcases x with ⟨a1, b1⟩
      rcases y with ⟨a2, b2⟩
      calc
  φ ((a1, b1) * (a2, b2)) = φ (a1 * a2, b1 * b2) := by rfl
  _ = (b1 * b2, a1 * a2) := by rfl
  _ = (b1, a1) * (b2, a2) := by rfl
  _ = φ (a1, b1) * φ (a2, b2) := by rfl
    · exact ⟨{ toFun := φ, invFun := ψ, left_inv := ?sorry_2, right_inv := ?sorry_3, map_mul' := h_hom }⟩
      exact ⟨{ toFun := φ, invFun := ψ, left_inv := h_inv.1, right_inv := h_inv.2, map_mul' := h_hom }⟩


theorem exercise_3_1_3a {A : Type*} [CommGroup A] (B : Subgroup A) :
  ∀ a b : A ⧸ B, a*b = b*a  := by
have h_normal : ∀ x y : A, x * y = y * x
· intros x y
  exact CommGroup.mul_comm x y
· intro xB yB
  have h_mul : (xB * yB) = (xB * yB)
  · exact ?sorry_0
    rfl
  · have h_comm : ∀ x y : A, x * y = y * x
    · exact ?sorry_1
      exact h_normal
    · have h_quot_comm : (xB * yB) = (yB * xB)
      · exact ?sorry_2
        rw [mul_comm xB yB, mul_comm yB xB ]
      · exact h_quot_comm


theorem exercise_3_1_22a (G : Type*) [Group G] (H K : Subgroup G)
  [Normal H] [Normal K] :
  Normal (H ⊓ K)  := by
rw [inf_comm ]
infer_instance


theorem exercise_3_1_22b {G : Type*} [Group G] (I : Type*)
  (H : I → Subgroup G) (hH : ∀ i : I, Normal (H i)) :
  Normal (⨅ (i : I), H i) := by
let N := ⨅ (i : I), H i
refine ⟨fun n hn g => ?_⟩
have hgn : ∀ i : I, g * n * g⁻¹ ∈ H i
· intro i
  have hni : n ∈ H i
  · exact ?sorry_0
    exact mem_iInf.1 hn i
  · exact ?sorry_1
    apply (hH _).conj_mem _ hni
· exact ?sorry_2
  rwa [Subgroup.mem_iInf ]


theorem exercise_3_2_11 {G : Type*} [Group G] {H K : Subgroup G}
  (hHK : H ≤ K) :
  H.index = K.index * H.relindex K  := by
rw [← relindex_mul_index hHK, mul_comm ]


theorem exercise_3_4_5a {G : Type*} [Group G]
  (H : Subgroup G) [IsSolvable G] : IsSolvable H  := by
infer_instance


theorem exercise_3_4_11 {G : Type*} [Group G] [IsSolvable G]
  {H : Subgroup G} (hH : H ≠ ⊥) [H.Normal] :
  ∃ A ≤ H, A.Normal ∧ ∀ a b : A, a*b = b*a  := by
have := exercise_5_6_11 hH
have := exercise_3_4 hH
refine ⟨_, le_normalClosure_of_normal H, inferInstance, fun a b => ?_⟩
let A := (2 : ℕ).primeFactors
let B : ℕ := A.prod id
have hA : A.prod id = B := rfl
have hB : B ≠ 0 := by
  rw [← hA]
  exact Finset.prod_ne_zero_iff.2 fun p hp => (Nat.prime_of_mem_factors (List.mem_toFinset.mp hp)).ne_zero
refine ⟨A.map ⟨_, MulEquiv.mulRight' 1⟩, le_trans (Finset.map_subset_iff.mpr ?_) (Subgroup.map_le _),
  inferInstance, fun a b ↦ ?_⟩
rw [← hA] at hB
rw [Finset.prod_eq_multiset_prod] at hA
replace hA := (mul_one B).symm
rw [mul_one] at hA
refine ⟨A, le_trans ?_ (le_normalizer.trans (le_of_eq hA)), inferInstance, fun a b ↦ ?_⟩
refine ⟨⊥, bot_le, inferInstance, ?_⟩
simp


theorem exercise_4_4_6a {G : Type*} [Group G] (H : Subgroup G)
  [Characteristic H] : Normal H   := by
apply normal_of_characteristic


theorem exercise_4_5_16 {p q r : ℕ} {G : Type*} [Group G]
  [Fintype G]  (hpqr : p < q ∧ q < r)
  (hpqr1 : p.Prime ∧ q.Prime ∧ r.Prime)(hG : card G = p*q*r) :
  Nonempty (Sylow p G) ∨ Nonempty (Sylow q G) ∨ Nonempty (Sylow r G)  := by
simp [Nat.mul_assoc] at hG
rw [or_iff_not_imp_left, or_iff_not_imp_left, not_nonempty_iff, not_nonempty_iff ]
intro h1 h2
simp [IsEmpty.eq_empty] at h1 h2 ⊢


theorem exercise_7_1_2 {R : Type*} [Ring R] {u : R}
  (hu : IsUnit u) : IsUnit (-u)  := by
let u_unit := hu.unit
let v := ↑u_unit⁻¹
have h1 : (-u) * (-v) = 1
· calc
  (-u) * (-v) = u * v := ?sorry_0
  _ = 1 := u_unit.val_inv
  simp
· have h2 : (-v) * (-u) = 1
  · calc
  (-v) * (-u) = v * u := ?sorry_1
  _ = 1 := u_unit.inv_val
    rw [neg_mul, mul_neg, neg_neg ]
  · use Units.mk (-u) (-v) h1 h2


theorem exercise_7_1_11 {R : Type*} [Ring R] [IsDomain R]
  {x : R} (hx : x^2 = 1) : x = 1 ∨ x = -1  := by
have h_eq : x^2 - 1 = 0
· exact ?sorry_0
  exact sub_eq_zero.mpr hx
· have h_factor : (x - 1) * (x + 1) = 0
  · exact ?sorry_1
    convert h_eq using 1 <;> ring
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    rw [h_eq ]
    simpa [_sq, sub_eq_zero, add_eq_zero_iff_eq_neg] using h_eq
  · have h_zero_factor : x - 1 = 0 ∨ x + 1 = 0
    · exact ?sorry_2
      simpa [hx, sub_eq_zero, add_eq_zero] using h_factor
    · exact ?sorry_3
      cases' h_zero_factor with h_zero_factor h_zero_factor <;> simp_all


theorem exercise_7_1_12 {F : Type*} [Field F] {K : Subring F}
  (hK : (1 : F) ∈ K) : IsDomain K  := by
constructor


theorem exercise_7_1_15 {R : Type*} [Ring R] (hR : ∀ a : R, a^2 = a) (a b : R) :
  a * b = b * a  := by
have h_neg : ∀ a : R, -a = a
· intro a
  calc
  -a = (-a)^2 := by rw [hR (-a)]
  _ = (-1)^2 * a^2 := ?sorry_0
  _ = a^2 := ?sorry_1
  _ = a := by rw [hR a]
  · simp
  · simp
· have h_add : ∀ a b : R, a + b = a + a * b + b * a + b
  · intro a b
    calc
  a + b = (a + b)^2 := by rw [hR (a + b)]
  _ = a^2 + a * b + b * a + b^2 := ?sorry_2
  _ = a + a * b + b * a + b := by rw [hR a, hR b]
    ring_nf
    rw [sq, sq, sq, add_mul, mul_add, add_assoc ]
    ring
    ring_nf
    ring
    ring_nf
    ring
    ring_nf
    ring
    abel
    ring_nf
    ring
    rw [mul_add ]
  · have h_comm_zero : a * b + b * a = 0
    · have h_eq : a + b = a + a * b + b * a + b
      · exact h_add a b
      · exact ?sorry_3
        simp only [add_assoc, add_left_comm, ← h_add] at h_eq
        simpa [add_comm, add_left_comm] using h_eq
    · have h_neg_comm : a * b = -(b * a)
      · rw [eq_neg_iff_add_eq_zero]
        exact h_comm_zero
      · calc
  a * b = -(b * a) := h_neg_comm
  _ = b * a := by rw [h_neg (b * a)]


theorem exercise_7_3_37 {p m : ℕ} (hp : p.Prime) :
  IsNilpotent (span ({↑p} : Set $ ZMod $ p^m) : Ideal $ ZMod $ p^m)  := by
let N : Ideal (ZMod (p^m)) := Ideal.span ({↑p} : Set (ZMod (p^m)))
have h_nilpotent : N^m = ⊥
· have h_pow : (Ideal.span ({↑p} : Set (ZMod (p^m))))^m = Ideal.span ({↑(p^m)} : Set (ZMod (p^m)))
  · exact ?sorry_0
    rw [Nat.cast_pow ]
    rw [Ideal.span_singleton_pow ]
  · have h_eq : Ideal.span ({↑(p^m)} : Set (ZMod (p^m))) = ⊥
    · exact ?sorry_1
      rw [← h_pow ]
      rw [h_pow ]
      rw [Ideal.span_singleton_eq_bot ]
      simpa [N, Ideal.zero_eq_bot] using h_pow.symm
    · rw [h_pow, h_eq]
· exact ⟨m, h_nilpotent⟩


theorem exercise_7_4_27 {R : Type*} [CommRing R] (hR : (0 : R) ≠ 1)
  {a : R} (ha : IsNilpotent a) (b : R) :
  IsUnit (1-a*b)  := by
rw [← IsUnit.neg_iff, neg_sub ]
rw [sub_eq_add_neg ]
rw [add_comm ]
rw [add_comm ]
rw [add_comm ]
rw [add_comm ]
rw [mul_comm ]
ring_nf
apply IsNilpotent.isUnit_add_left_of_commute
· simpa only [← smul_eq_mul] using ha.smul b
· exact isUnit_one.neg
· simp
