import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators
noncomputable section

theorem exercise_1_1_2a : ∃ a b : ℤ, a - b ≠ b - a  := by
let a := 1
let b := -1
have h1 : a - b = 2
· exact ?sorry_0
  rfl
· have h2 : b - a = -2
  · exact ?sorry_1
    rw [← neg_sub, h1 ]
  · have h3 : a - b ≠ b - a
    · exact ?sorry_2
      rw [h1, h2] <;> decide
    · exact ⟨a, b, h3⟩


theorem exercise_1_1_3 (n : ℤ) :
  ∀ (a b c : ℤ), (a+b)+c ≡ a+(b+c) [ZMOD n]  := by
intro a b c
rw [add_assoc ]


theorem exercise_1_1_15 {G : Type*} [Group G] (as : List G) :
  as.prod⁻¹ = (as.reverse.map (λ x => x⁻¹)).prod  := by
simpa [List.prod_inv_reverse] using exercise_1_1_11 as.reverse


theorem exercise_1_1_16 {G : Type*} [Group G]
  (x : G) (hx : x ^ 2 = 1) :
  orderOf x = 1 ∨ orderOf x = 2  := by
have : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx
rwa [Nat.dvd_prime Nat.prime_two] at this


theorem exercise_1_1_17 {G : Type*} [Group G] {x : G} {n : ℕ}
  (hxn: orderOf x = n) :
  x⁻¹ = x ^ (n - 1 : ℤ)  := by
rw [← hxn ]
rw [hxn ]
rw [(Nat.card_zpowers _).symm] at hxn
rw [Nat.card_zpowers] at hxn
rw [← hxn, zpow_sub, zpow_one, zpow_natCast ]
simp
exact pow_orderOf_eq_one x


theorem exercise_1_1_20 {G : Type*} [Group G] {x : G} :
  orderOf x = orderOf x⁻¹  := by
simp


theorem exercise_1_1_25 {G : Type*} [Group G]
  (h : ∀ x : G, x ^ 2 = 1) : ∀ a b : G, a*b = b*a  := by
let a b := (⟨1, 1⟩ : G) * ⟨0, 1⟩
intros a b
rw [← mul_right_inj a, ← mul_left_inj b ]
ring_nf
calc
  a * (a * b) * b = a ^ 2 * b ^ 2 := by simp only [pow_two]; group
  _ = 1 := by rw [h, h, mul_one]
  _ = (a * b) ^ 2 := by rw [h]
  _ = a * (b * a) * b := by simp only [pow_two]; group


theorem exercise_1_3_8 : Infinite (Equiv.Perm ℕ)  := by
let f : ℕ → Equiv.Perm ℕ := fun n => Equiv.swap 1 n
have h_injective : Function.Injective f
· exact ?sorry_0
  intro n m hnm
  simpa [f] using Equiv.congr_fun hnm 1
· have h_card : Cardinal.aleph0 ≤ Cardinal.mk (Equiv.Perm ℕ)
  · exact ?sorry_1
    have := Cardinal.mk_congr (Equiv.Permaroo observ) .rfl
    have h_card : Fintype.card (Equiv.Perm ℕ) = 4 ^ Cardinal.aleph0 := Cardinal.mk_perm_eq_self_power
    simpa [Cardinal.mk_perm_eq_self_power, power_one] using Cardinal.aleph0_le_continuum
  · exact Cardinal.infinite_iff.2 h_card


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
rintro ⟨a⟩ ⟨b⟩
exact (mul_comm _ _).symm


theorem exercise_3_1_22a (G : Type*) [Group G] (H K : Subgroup G)
  [Normal H] [Normal K] :
  Normal (H ⊓ K)  := by
by_contra h
have := exercise_3_1_2a H K
simp only [Normal, Subgroup.inf, Subgroup.mem_inf, not_and] at h
rw [← Subgroup.normalizer_eq_top] at h
rw [← Ne] at h
rw [Ne] at h
rw [← Ne, ← lt_top_iff_ne_top] at h
rw [lt_top_iff_ne_top, Ne, normalizer_eq_top, inf_comm] at h
exact h inferInstance


theorem exercise_3_1_22b {G : Type*} [Group G] (I : Type*)
  (H : I → Subgroup G) (hH : ∀ i : I, Normal (H i)) :
  Normal (⨅ (i : I), H i) := by
constructor
rintro x hx y
simp [mem_iInf, SetCoe.forall] at hx ⊢
rw [Subgroup.mem_iInf] at hx ⊢
exact fun i => (hH i).conj_mem _ (hx i) y


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
let index_GK := K.index
let relindex_KH := H.relindex K
have index_relation : H.index = index_GK * relindex_KH
· exact ?sorry_0
  apply Nat.dvd_antisymm <;> apply index_dvd_of_le
  · rw [← relindex_mul_index (show H ≤ K from hHK), mul_comm ]
  · rw [← relindex_mul_index (show H ≤ K from hHK), mul_comm ]
· exact index_relation


theorem exercise_3_2_16 (p : ℕ) (hp : Nat.Prime p) (a : ℕ) :
  Nat.Coprime a p → a ^ p ≡ a [ZMOD p]  := by
rw [← ZMod.intCast_eq_intCast_iff ]
simp
rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_rec ]
intro h
have : a % p < p := Nat.mod_lt a hp.pos
rw [← ZMod.natCast_mod, ZMod.pow_card ]
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
let _ := H.index
haveI := fintypeOfIndexNeZero H
haveI := H.finiteIndex_of FiniteType
haveI := H.finiteIndex_of_index_ne_zero
haveI := H.finiteIndex_ofFinite_quotient
infer_instance


theorem exercise_4_5_16 {p q r : ℕ} {G : Type*} [Group G]
  [Fintype G]  (hpqr : p < q ∧ q < r)
  (hpqr1 : p.Prime ∧ q.Prime ∧ r.Prime)(hG : card G = p*q*r) :
  Nonempty (Sylow p G) ∨ Nonempty (Sylow q G) ∨ Nonempty (Sylow r G)  := by
rw [Nat.mul_assoc] at hG
rw [← Nat.mul_assoc] at hG
rw [Nat.mul_assoc] at hG
simp only [← Nat.card_eq_fintype_card] at hG
simp [Nat.card_eq_fintype_card] at hG
simpa [or_iff_not_imp_left, Sylow, ← exercise_4_5_6 hpqr hpqr1 hG]
  using exercise_3_4_5 hpqr hpqr1 hG


theorem exercise_7_1_2 {R : Type*} [Ring R] {u : R}
  (hu : IsUnit u) : IsUnit (-u)  := by
simpa only [Units.isUnit, Units.val_neg] using IsUnit.neg hu


theorem exercise_7_1_11 {R : Type*} [Ring R] [IsDomain R]
  {x : R} (hx : x^2 = 1) : x = 1 ∨ x = -1  := by
have h_eq : x^2 - 1 = 0
· exact ?sorry_0
  rw [hx, sub_self ]
· have h_factor : (x - 1) * (x + 1) = 0
  · exact ?sorry_1
    aesop
  · have h_zero_product : x - 1 = 0 ∨ x + 1 = 0
    · exact ?sorry_2
      simpa [hx] using h_factor
    · exact ?sorry_3
      rwa [sub_eq_zero, add_eq_zero_iff_eq_neg] at h_zero_product


theorem exercise_7_1_12 {F : Type*} [Field F] {K : Subring F}
  (hK : (1 : F) ∈ K) : IsDomain K  := by
have no_zero_divisors : ∀ x y : K, x * y = 0 → x = 0 ∨ y = 0
· intros x y hxy
  have hx : (x : F) = 0 ∨ (y : F) = 0
  · exact ?sorry_0
    simpa [← Subring.coe_mul] using hxy
  · exact ?sorry_1
    simpa only [← Subring.coe_eq_zero_iff] using hx
· have nontrivial : (0 : K) ≠ 1
  · have h01 : (0 : F) ≠ (1 : F)
    · exact ?sorry_2
      exact zero_ne_one
    · exact ?sorry_3
      norm_num
  · apply IsDomain.mk


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

