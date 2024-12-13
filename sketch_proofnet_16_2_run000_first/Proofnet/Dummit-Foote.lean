import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators
noncomputable section

theorem exercise_1_1_2a : ∃ a b : ℤ, a - b ≠ b - a  := by
exact ⟨-1, 1, by decide⟩


theorem exercise_1_1_3 (n : ℤ) :
  ∀ (a b c : ℤ), (a+b)+c ≡ a+(b+c) [ZMOD n]  := by
intro a b c
rw [Int.add_assoc ]


theorem exercise_1_1_15 {G : Type*} [Group G] (as : List G) :
  as.prod⁻¹ = (as.reverse.map (λ x => x⁻¹)).prod  := by
simpa [List.prod_inv_reverse] using exercise_1_1_2 as.reverse


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
rw [orderOf_eq_orderOf_iff ]
simp


theorem exercise_1_1_25 {G : Type*} [Group G]
  (h : ∀ x : G, x ^ 2 = 1) : ∀ a b : G, a*b = b*a  := by
intro a b
rw [← mul_right_inj a, ← mul_left_inj b ]
ring_nf
calc
  a * (a * b) * b = a ^ 2 * b ^ 2 := by simp only [pow_two]; group
  _ = 1 := by rw [h, h, mul_one]
  _ = (a * b) ^ 2 := by rw [h]
  _ = a * (b * a) * b := by simp only [pow_two]; group


theorem exercise_1_3_8 : Infinite (Equiv.Perm ℕ)  := by
let f : ℕ → Equiv.Perm ℕ := λ n => Equiv.swap 1 n
have hf_injective : Function.Injective f
· exact ?sorry_0
  intro m n h
  simp [f, Equiv.swap_apply_eq_iff] at h
  simp only [Equiv.swap_apply_eq_iff, swap_apply_right] at h
  simpa [f] using Equiv.congr_fun h 1
· have h_card_le : Cardinal.aleph0 ≤ Cardinal.mk (Equiv.Perm ℕ)
  · exact ?sorry_1
    simpa using Cardinal.mk_le_of_injective hf_injective
  · exact Cardinal.infinite_iff.2 h_card_le


theorem exercise_1_6_11 {A B : Type*} [Group A] [Group B] :
  Nonempty (A × B ≃* B × A)  := by
let φ : A × B → B × A := fun p => (p.2, p.1)
let ψ : B × A → A × B := fun p => (p.2, p.1)
have h_bij : Function.Bijective φ
· exact ?sorry_0
  simpa [φ, ψ] using (Equiv.prodComm _ _).bijective
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
      exact
  ⟨{ toFun := φ, invFun := ψ, left_inv := h_inv.1, right_inv := h_inv.2, map_mul' := h_hom }⟩


theorem exercise_3_1_3a {A : Type*} [CommGroup A] (B : Subgroup A) :
  ∀ a b : A ⧸ B, a*b = b*a  := by
intro a b
obtain ⟨x, hx⟩ := Quotient.exists_rep a
obtain ⟨y, hy⟩ := Quotient.exists_rep b
rw [←hx, ←hy]
change QuotientGroup.mk (x * y) = QuotientGroup.mk (y * x)
rw [mul_comm]


theorem exercise_3_1_22a (G : Type*) [Group G] (H K : Subgroup G)
  [Normal H] [Normal K] :
  Normal (H ⊓ K)  := by
rw [inf_comm ]
infer_instance


theorem exercise_3_1_22b {G : Type*} [Group G] (I : Type*)
  (H : I → Subgroup G) (hH : ∀ i : I, Normal (H i)) :
  Normal (⨅ (i : I), H i) := by
let K := ⨅ (i : I), H i
refine ⟨fun n hn g => ?_⟩
have hn_in : ∀ i : I, n ∈ H i
· exact ?sorry_0
  exact mem_iInf.mp hn
· have hgn_in : ∀ i : I, g * n * g⁻¹ ∈ H i
  · intro i
    have h_normal : g * n * g⁻¹ ∈ H i
    · exact (hH i).conj_mem n (hn_in i) g
    · exact h_normal
  · exact ?sorry_1
    rw [Subgroup.mem_iInf ]
    exact hgn_in


theorem exercise_3_2_8 {G : Type*} [Group G] (H K : Subgroup G)
  [Fintype H] [Fintype K]
  (hHK : Nat.Coprime (card H) (card K)) :
  H ⊓ K = ⊥  := by
contrapose! hHK
exact Nat.not_coprime_of_dvd_of_dvd (card_pos.2 ⟨1, one_mem H⟩) (card_pos.2 ⟨1, one_mem K⟩)
  hHK
exact fun h => hHK <| inf_eq_bot_of_coprime h


theorem exercise_3_2_11 {G : Type*} [Group G] {H K : Subgroup G}
  (hHK : H ≤ K) :
  H.index = K.index * H.relindex K  := by
rw [← relindex_mul_index fun x hx => hHK hx] <;> assumption
rw [mul_comm ]


theorem exercise_3_2_16 (p : ℕ) (hp : Nat.Prime p) (a : ℕ) :
  Nat.Coprime a p → a ^ p ≡ a [ZMOD p]  := by
rw [Nat.coprime_comm ]
rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm ]
rw [Nat.gcd_comm, Nat.gcd_rec ]
intro h
rw [← ZMod.intCast_eq_intCast_iff ]
norm_cast
rw [Nat.cast_pow, ZMod.pow_card ]
exact ⟨hp⟩


theorem exercise_3_4_11 {G : Type*} [Group G] [IsSolvable G]
  {H : Subgroup G} (hH : H ≠ ⊥) [H.Normal] :
  ∃ A ≤ H, A.Normal ∧ ∀ a b : A, a*b = b*a  := by
let K :=.NormalizerCondition.subgroupOf H
repeat' rw [← Subgroup.toSubmonoid_eq] at hH ⊢
let A := (conjugatesOf H).carrier
refine ⟨⟨_, mul_memoyalities H⟩, Subgroup.mul_le_right, inferInstance, ?_⟩
let x := Classical.arbitrary H
let _ := x * x
rw [← bot_lt_iff_ne_bot] at hH
refine ⟨_, le_of_lt hH, inferInstance, fun a b ↦ ?_⟩
apply Subsingleton.elim


theorem exercise_4_4_6a {G : Type*} [Group G] (H : Subgroup G)
  [Characteristic H] : Normal H   := by
revert H
intro H
infer_instance


theorem exercise_4_5_16 {p q r : ℕ} {G : Type*} [Group G]
  [Fintype G]  (hpqr : p < q ∧ q < r)
  (hpqr1 : p.Prime ∧ q.Prime ∧ r.Prime)(hG : card G = p*q*r) :
  Nonempty (Sylow p G) ∨ Nonempty (Sylow q G) ∨ Nonempty (Sylow r G)  := by
rw [Nat.mul_assoc, Nat.mul_comm q, ← Nat.mul_assoc] at hG
simp only [Nat.mul_assoc] at hG
simpa [or_iff_not_imp_left, Sylow, ← exercise_4_5_7 hpqr hpqr1.1 hpqr1.2.1,
  ← exercise_4_5_7 hpqr hpqr1.1 hpqr1.2.2, ← exercise_4_5_7 hpqr hpqr1.1 hpqr1.2.1,
  ← exercise_4_5_7 hpqr hpqr1.1 hpqr1.2.2] using exercise_4_5_7' hpqr1.1 hpqr1.2.1


theorem exercise_7_1_2 {R : Type*} [Ring R] {u : R}
  (hu : IsUnit u) : IsUnit (-u)  := by
rw [← neg_one_mul ]
exact isUnit_one.neg.mul hu


theorem exercise_7_1_11 {R : Type*} [Ring R] [IsDomain R]
  {x : R} (hx : x^2 = 1) : x = 1 ∨ x = -1  := by
simpa [← pow_two] using hx


theorem exercise_7_1_12 {F : Type*} [Field F] {K : Subring F}
  (hK : (1 : F) ∈ K) : IsDomain K  := by
have : NeZero ((1 : F) : K) := ⟨1, hK⟩
rw [← Int.cast_one] at hK
simp [SetLike.coe_ofNat, SetLike.coe_one] at hK
rw [← Rat.cast_one] at hK
simp [SetLike.coe_sort_coe, one_mul] at hK
have : midfielder K = ⟨1, hK⟩ := rfl
replace hK := Set.mem_of_mem_singleton hK
have : NeZero (1 : F) := ⟨one_ne_zero⟩
infer_instance


theorem exercise_7_1_15 {R : Type*} [Ring R] (hR : ∀ a : R, a^2 = a) (a b : R) :
  a * b = b * a  := by
have h_neg : ∀ a : R, -a = a
· intro a
  calc
  -a = (-a)^2 := by rw [hR (-a)]
  _  = (-1)^2 * a^2 := ?sorry_0
  _  = a^2 := ?sorry_1
  _  = a := by rw [hR a]
  · simp
  · simp
· have h_add : (a + b)^2 = a + a * b + b * a + b
  · calc
  (a + b)^2 = a^2 + a * b + b * a + b^2 := ?sorry_2
  _ = a + a * b + b * a + b := by rw [hR a, hR b]
    simpa only [sq, add_mul, mul_add, add_assoc, add_left_comm] using
  @exercise_2 R _ hR (a + b) b a
  · have h_comm_zero : a * b + b * a = 0
    · have h_sq : (a + b)^2 = a + b
      · rw [hR (a + b)]
      · rw [h_add] at h_sq
        exact ?sorry_3
        rw [add_comm] at h_sq
        rw [add_assoc] at h_sq
        simpa [add_comm, add_left_comm] using h_sq
    · calc
  a * b = - (b * a) := ?sorry_4
  _ = b * a := by rw [h_neg (b * a)]
      rw [← add_eq_zero_iff_eq_neg, ← h_comm_zero ]


theorem exercise_7_3_37 {p m : ℕ} (hp : p.Prime) :
  IsNilpotent (span ({↑p} : Set $ ZMod $ p^m) : Ideal $ ZMod $ p^m)  := by
let N : Ideal (ZMod (p^m)) := Ideal.span ({↑p} : Set (ZMod (p^m)))
have h_pow : N ^ m = ⊥
· exact ?sorry_0
  rw [eq_bot_iff ]
  rw [← Ideal.zero_eq_bot ]
  rw [Ideal.zero_eq_bot, le_bot_iff ]
  rw [eq_bot_iff ]
  rw [Ideal.span_singleton_pow, span_le, Set.singleton_subset_iff ]
  rw [SetLike.mem_coe, Ideal.mem_bot ]
  change Ideal.span _ = ⊥
  norm_cast
  simp
· exact ⟨m, h_pow⟩


theorem exercise_7_4_27 {R : Type*} [CommRing R] (hR : (0 : R) ≠ 1)
  {a : R} (ha : IsNilpotent a) (b : R) :
  IsUnit (1-a*b)  := by
obtain ⟨n, hn⟩ := ha
let c := a * b
have hc_nilpotent : IsNilpotent c
· exact ?sorry_0
  use n
  rw [← hn ]
  ring_nf
  rw [hn, zero_mul ]
· have h_unit : IsUnit (1 - c)
  · exact ?sorry_1
    rw [← IsUnit.neg_iff, neg_sub ]
    obtain ⟨k,hk⟩ := hc_nilpotent
    rw [sub_eq_add_neg ]
    rw [← sub_eq_add_neg ]
    exact IsNilpotent.isUnit_sub_one ⟨k, hk⟩
  · exact h_unit

