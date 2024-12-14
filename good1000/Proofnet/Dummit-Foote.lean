import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators
noncomputable section

theorem exercise_8_3_6b {q : ℕ} (hq0 : q.Prime)
  (hq1 : q ≡ 3 [ZMOD 4]) {R : Type} [Ring R]
  (hR : R = (GaussianInt ⧸ span ({↑q} : Set GaussianInt))) :
  IsField R ∧ ∃ finR : Fintype R, @card R finR = q^2  := by
have h_representation : ∀ x : GaussianInt, ∃ a b : ℤ, 0 ≤ a ∧ a < q ∧ 0 ≤ b ∧ b < q ∧ (x - (a + b * ⟨0, 1⟩)) ∈ span ({⟨q, 0⟩} : Set GaussianInt)
  exact ?sorry_0
have h_distinct : ∀ (a1 a2 b1 b2 : ℤ),
  (⟨a1, b1⟩ - ⟨a2, b2⟩) ∈ span ({⟨q, 0⟩} : Set GaussianInt) → (a1 ≡ a2 [ZMOD q] ∧ b1 ≡ b2 [ZMOD q]) := ?sorry_1
have h_order : ∃ finR : Fintype R, @card R finR = q^2
  exact ?sorry_2
have h_irreducible : Irreducible (⟨q, 0⟩ : GaussianInt)
  exact ?sorry_3
have h_prime_ideal : Ideal.IsPrime (span ({⟨q, 0⟩} : Set GaussianInt))
  exact ?sorry_4
have h_integral_domain : IsDomain R
  exact ?sorry_5
have h_field : IsField R
  exact ?sorry_6
exact ⟨h_field, h_order⟩


theorem exercise_7_3_37 {p m : ℕ} (hp : p.Prime) :
  IsNilpotent (span ({↑p} : Set $ ZMod $ p^m) : Ideal $ ZMod $ p^m)  := by
let N : Ideal (ZMod (p^m)) := Ideal.span ({↑p} : Set (ZMod (p^m)))
have hNm : N ^ m = ⊥
  have : (Ideal.span ({↑p} : Set (ZMod (p^m)))) ^ m = Ideal.span ({↑(p^m)} : Set (ZMod (p^m)))
    exact ?sorry_0
  have : Ideal.span ({↑(p^m)} : Set (ZMod (p^m))) = ⊥
    exact ?sorry_1
  exact ?sorry_2
exact ⟨m, hNm⟩


theorem exercise_7_4_27 {R : Type*} [CommRing R] (hR : (0 : R) ≠ 1)
  {a : R} (ha : IsNilpotent a) (b : R) :
  IsUnit (1-a*b)  := by
have hnil : IsNilpotent (a * b)
  exact ?sorry_0
have hunit : IsUnit (1 - a * b)
  exact ?sorry_1
exact hunit


theorem exercise_1_6_23 {G : Type*}
  [Group G] (σ : MulAut G) (hs : ∀ g : G, σ g = 1 → g = 1)
  (hs2 : ∀ g : G, σ (σ g) = g) :
  ∀ x y : G, x*y = y*x  := by
let f : G → G := λ x => x⁻¹ * σ x
have f_injective : ∀ x y : G, f x = f y → x = y
  intro x y h
  have h1 : x⁻¹ * σ x = y⁻¹ * σ y
    exact h
  have h2 : x * y⁻¹ = σ x * σ (y⁻¹)
    exact ?sorry_0
  have h3 : x * y⁻¹ = σ (x * y⁻¹)
    exact ?sorry_1
  have h4 : x * y⁻¹ = 1
    exact ?sorry_2
  exact ?sorry_3
have f_surjective : ∀ z : G, ∃ x : G, f x = z
  intro z
  have h : ∃ x : G, x⁻¹ * σ x = z
    exact ?sorry_4
  exact h
have sigma_inversion : ∀ z : G, σ z = z⁻¹
  intro z
  obtain ⟨x, hx⟩ := f_surjective z
  have h1 : x⁻¹ * σ x = z
    exact hx
  have h2 : σ z = σ (x⁻¹ * σ x)
    rw [←h1]
  have h3 : σ z = σ x⁻¹ * x
    exact ?sorry_5
  have h4 : σ z = (x⁻¹ * σ x)⁻¹
    exact ?sorry_6
  have h5 : σ z = z⁻¹
    exact ?sorry_7
  exact h5
intro x y
have h1 : σ (x * y) = (x * y)⁻¹
  exact ?sorry_8
have h2 : σ (x * y) = σ y * σ x
  exact ?sorry_9
have h3 : (x * y)⁻¹ = y⁻¹ * x⁻¹
  exact ?sorry_10
have h4 : σ y * σ x = y⁻¹ * x⁻¹
  exact ?sorry_11
have h5 : y * x = x * y
  exact ?sorry_12
exact h5.symm


theorem exercise_1_1_15 {G : Type*} [Group G] (as : List G) :
  as.prod⁻¹ = (as.reverse.map (λ x => x⁻¹)).prod  := by
induction as with
  | nil =>
    have h_nil : ([] : List G).prod = 1
      exact ?sorry_0
    have h_nil_inv : (1 : G)⁻¹ = 1
      exact ?sorry_1
    rw [h_nil, h_nil_inv]
    simp
  | cons a as ih =>
    have h_prod : (a :: as).prod = a * as.prod
      exact ?sorry_2
    have h_inv : (a * as.prod)⁻¹ = as.prod⁻¹ * a⁻¹
      exact ?sorry_3
    have h_ih : as.prod⁻¹ = (as.reverse.map (λ x => x⁻¹)).prod
      exact ih
    rw [h_prod, h_inv, h_ih]
    have h_reverse : (a :: as).reverse = as.reverse ++ [a]
      exact ?sorry_4
    have h_map : (as.reverse ++ [a]).map (λ x => x⁻¹) = (as.reverse.map (λ x => x⁻¹)) ++ [a⁻¹]
      exact ?sorry_5
    rw [h_reverse, h_map]
    simp


theorem exercise_11_1_13 {ι : Type*} [Fintype ι] :
  Nonempty ((ι → ℝ) ≃ₗ[ℚ] ℝ)  := by
let n := Fintype.card ι
let B : Basis ι ℚ (ι → ℝ) := ?sorry_0
let C : Basis (Fin n) ℚ ℝ := ?sorry_1
have h_iso : (ι → ℝ) ≃ₗ[ℚ] ℝ
  exact ?sorry_2
exact ⟨h_iso⟩


theorem exercise_4_4_6a {G : Type*} [Group G] (H : Subgroup G)
  [Characteristic H] : Normal H   := by
have hChar : ∀ (α : G ≃* G), α '' H ≤ H
  exact ?sorry_0
have hInner : ∀ (g : G), (MulAut.conj g) '' H ≤ H
  exact ?sorry_1
have hConj : ∀ (g : G), ∀ (h : H), g * h * g⁻¹ ∈ H
  exact ?sorry_2
exact ?sorry_3


theorem exercise_9_4_9 :
  Irreducible (X^2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2))  := by
by_contra h_reducible
have h_root : ∃ (a b : ℤ), (a + b * (⟨0, 1⟩ : ℤ × ℤ)) ^ 2 = (⟨0, 1⟩ : ℤ × ℤ)
  exact ?sorry_0
rcases h_root with ⟨a, b, h_eq⟩
have h_expand : (a + b * (⟨0, 1⟩ : ℤ × ℤ)) ^ 2 = a^2 + 2 * a * b * (⟨0, 1⟩ : ℤ × ℤ) + 2 * b^2
  exact ?sorry_1
have h_coeff : 2 * a * b = 1
  exact ?sorry_2
have h_contradiction : False
  exact ?sorry_3
contradiction


theorem exercise_9_3_2 {f g : Polynomial ℚ} (i j : ℕ)
  (hfg : ∀ n : ℕ, ∃ a : ℤ, (f*g).coeff = a) :
  ∃ a : ℤ, f.coeff i * g.coeff j = a  := by
have ⟨r, hr⟩ : ∃ r : ℚ, ∀ n : ℕ, ∃ a : ℤ, (r • f).coeff n = a
  exact ?sorry_0
have ⟨s, hs⟩ : ∃ s : ℚ, ∀ n : ℕ, ∃ a : ℤ, (s • g).coeff n = a
  exact ?sorry_1
have hsr : s = r⁻¹
  exact ?sorry_2
have hf_i : ∃ a : ℤ, r * f.coeff i = a
  exact ?sorry_3
have hg_j : ∃ b : ℤ, r⁻¹ * g.coeff j = b
  exact ?sorry_4
have hprod : ∃ c : ℤ, (r * f.coeff i) * (r⁻¹ * g.coeff j) = c
  exact ?sorry_5
exact ?sorry_6


theorem exercise_3_1_3a {A : Type*} [CommGroup A] (B : Subgroup A) :
  ∀ a b : A ⧸ B, a*b = b*a  := by
haveI : CommGroup (A ⧸ B)
  exact inferInstance
intro xB yB
have h1 : (xB * yB) = (xB * yB)
  exact ?sorry_0
have h2 : (xB * yB) = (yB * xB)
  exact ?sorry_1
exact h2


theorem exercise_1_3_8 : Infinite (Equiv.Perm ℕ)  := by
let f : ℕ → Equiv.Perm ℕ := fun n => Equiv.swap 1 n
have f_injective : Function.Injective f
  intro n m h
  exact ?sorry_0
have infinite_SN : Infinite (Equiv.Perm ℕ)
  apply Infinite.of_injective f f_injective
exact infinite_SN


theorem exercise_4_3_26 {α : Type*} [Fintype α] (ha : card α > 1)
  (h_tran : ∀ a b: α, ∃ σ : Equiv.Perm α, σ a = b) :
  ∃ σ : Equiv.Perm α, ∀ a : α, σ a ≠ a  := by
have h_stab : ∀ a : α, ∃ g : Equiv.Perm α, g a ≠ a
  exact ?sorry_0
have h_transitive : ∀ a b : α, ∃ g : Equiv.Perm α, g b = a
  exact ?sorry_1
let stabilizer (a : α) : Set (Equiv.Perm α) := {σ | σ a = a}
have h_stabilizer_relation : ∀ a b : α, ∃ g : Equiv.Perm α,
  ∀ h : Equiv.Perm α, (h b = b ↔ (g⁻¹ * h * g) a = a) := ?sorry_2
have h_conjugate : ∀ a b : α, ∃ g : Equiv.Perm α,
  stabilizer b = {σ | (g⁻¹ * σ * g) a = a} := ?sorry_3
have h_proper_subgroup : ∀ a : α, stabilizer a ⊂ Set.univ
  exact ?sorry_4
have h_union_conjugates : (⋃ a : α, stabilizer a) ⊂ Set.univ
  exact ?sorry_5
have h_sigma : ∃ σ : Equiv.Perm α, ∀ a : α, σ a ≠ a
  exact ?sorry_6
exact h_sigma


theorem exercise_2_4_16a {G : Type*} [Group G] {H : Subgroup G}
  (hH : H ≠ ⊤) :
  ∃ M : Subgroup G, M ≠ ⊤ ∧
  ∀ K : Subgroup G, M ≤ K → K = M ∨ K = ⊤ ∧
  H ≤ M  := by
classical
  by_contra h
  push_neg at h
  have h_chain : ∀ (K : Subgroup G), H ≤ K → K ≠ ⊤ → ∃ L : Subgroup G, K < L ∧ L ≠ ⊤
    exact ?sorry_0
  let chain : ℕ → Subgroup G := fun n => exact ?sorry_1
  have chain_start : chain 0 = H
    exact ?sorry_2
  have chain_step : ∀ n, chain n < chain (n + 1) ∧ chain (n + 1) ≠ ⊤
    exact ?sorry_3
  have chain_bounded : ∀ n, chain n ≠ ⊤
    exact ?sorry_4
  have chain_increasing : ∀ n, chain n < chain (n + 1)
    exact ?sorry_5
  have chain_finite : ∃ n, chain n = ⊤
    exact ?sorry_6
  obtain ⟨n, hn⟩ := chain_finite
  have hn' : chain n ≠ ⊤
    exact chain_bounded n
  contradiction


theorem exercise_3_1_22b {G : Type*} [Group G] (I : Type*)
  (H : I → Subgroup G) (hH : ∀ i : I, Normal (H i)) :
  Normal (⨅ (i : I), H i) := by
let N := ⨅ (i : I), H i
have hN : ∀ g : G, ∀ n : N, g * n * g⁻¹ ∈ N
  intro g n
  have hn : ∀ i : I, ↑n ∈ H i
    exact ?sorry_0
  have hgn : ∀ i : I, g * ↑n * g⁻¹ ∈ H i
    intro i
    apply Normal.conj_mem (hH i)
    exact hn i
  exact ?sorry_1
exact ?sorry_2


theorem exercise_1_1_5 (n : ℕ) (hn : 1 < n) :
  IsEmpty (Group (ZMod n))  := by
have h : Group (ZMod n)
  exact ?sorry_0
have zero_no_inv : ¬∃ k : ZMod n, 0 * k = 1
  exact ?sorry_1
have inv_exists : ∃ k : ZMod n, 0 * k = 1
  exact ?sorry_2
contradiction


theorem exercise_2_1_5 {G : Type*} [Group G] [Fintype G]
  (hG : card G > 2) (H : Subgroup G) [Fintype H] :
  card H ≠ card G - 1  := by
intro h_card_eq
have h_card_H : Fintype.card H = Fintype.card G - 1
  exact h_card_eq
have exists_nonid_x : ∃ x ∈ H, x ≠ 1
  exact ?sorry_0
rcases exists_nonid_x with ⟨x, hxH, hx_ne_one⟩
have exists_y_not_in_H : ∃ y : G, y ∉ H
  exact ?sorry_1
rcases exists_y_not_in_H with ⟨y, hy_not_in_H⟩
have xy_in_H_or_not : (x * y ∈ H) ∨ (x * y ∉ H)
  exact ?sorry_2
cases xy_in_H_or_not with
| inl hxy_in_H =>
  have y_in_H : y ∈ H
    have x_inv_in_H : x⁻¹ ∈ H
      exact Subgroup.inv_mem H hxH
    have y_eq : y = x⁻¹ * (x * y)
      group
    rw [y_eq]
    exact Subgroup.mul_mem H x_inv_in_H hxy_in_H
  contradiction
| inr hxy_not_in_H =>
  have xy_eq_y : x * y = y
    exact ?sorry_3
  have x_eq_one : x = 1
    calc
  x = x * 1 := by rw [mul_one]
  _ = x * (y * y⁻¹) := by rw [mul_right_inv]
  _ = (x * y) * y⁻¹ := by rw [mul_assoc]
  _ = y * y⁻¹ := by rw [xy_eq_y]
  _ = 1 := by rw [mul_right_inv]
  contradiction


theorem exercise_8_1_12 {N : ℕ} (hN : N > 0) {M M': ℤ} {d : ℕ}
  (hMN : M.gcd N = 1) (hMd : d.gcd N.totient = 1)
  (hM' : M' ≡ M^d [ZMOD N]) :
  ∃ d' : ℕ, d' * d ≡ 1 [ZMOD N.totient] ∧
  M ≡ M'^d' [ZMOD N]  := by
have h_d' : ∃ d' : ℕ, d' * d ≡ 1 [ZMOD N.totient]
  exact ?sorry_0
have euler_theorem : M^N.totient ≡ 1 [ZMOD N]
  exact ?sorry_1
obtain ⟨d', hd'⟩ := h_d'
have hMdd' : M^(d * d') ≡ M [ZMOD N]
  calc
  M^(d * d') ≡ M^1 [ZMOD N] := ?sorry_2
  _ ≡ M [ZMOD N] := ?sorry_3
have hM'_d' : M ≡ M'^d' [ZMOD N]
  exact ?sorry_4
exact ⟨d', hd', hM'_d'⟩


theorem exercise_8_3_4 {R : Type*} {n : ℤ} {r s : ℚ}
  (h : r^2 + s^2 = n) :
  ∃ a b : ℤ, a^2 + b^2 = n  := by
let r_num := r.num
let r_denom := r.den
let s_num := s.num
let s_denom := s.den
have h1 : n * (r_denom * s_denom)^2 = r_num^2 * s_denom^2 + s_num^2 * r_denom^2
  exact ?sorry_0
have h2 : ∀ q : ℕ, Prime q → q ≡ 3 [MOD 4] → ∀ i : ℕ, (q : ℤ)^i ∣ n → Even i
  exact ?sorry_1
have h3 : ∀ q : ℕ, Prime q → q ≡ 3 [MOD 4] → ∃ j : ℕ, (q : ℤ)^j ∣ r_denom * s_denom
  exact ?sorry_2
have h4 : ∀ q : ℕ, Prime q → q ≡ 3 [MOD 4] → ∀ i j : ℕ, (q : ℤ)^i ∣ n → (q : ℤ)^j ∣ r_denom * s_denom → Even (i - 2 * j)
  exact ?sorry_3
have h5 : ∃ a b : ℤ, a^2 + b^2 = n
  exact ?sorry_4
exact h5


theorem exercise_1_6_4 :
  IsEmpty (Multiplicative ℝ ≃* Multiplicative ℂ)  := by
by_contra iso
have hR : ∀ n : ℕ, n > 0 → (∃ x : ℝ, x ≠ 0 ∧ x ^ n = 1) → n = 1 ∨ n = 2
  exact ?sorry_0
have hC : ∃ x : ℂ, x ≠ 0 ∧ x ^ 4 = 1
  exact ?sorry_1
have order_contradiction : False
  exact ?sorry_2
exact order_contradiction


theorem exercise_1_6_11 {A B : Type*} [Group A] [Group B] :
  Nonempty (A × B ≃* B × A)  := by
let φ : A × B → B × A := λ (p : A × B) => (p.2, p.1)
let ψ : B × A → A × B := λ (p : B × A) => (p.2, p.1)
have h_bij : Function.Bijective φ
  exact ?sorry_0
have h_hom : ∀ (a1 a2 : A) (b1 b2 : B),
  φ ((a1, b1) * (a2, b2)) = φ (a1, b1) * φ (a2, b2) := by
  intro a1 a2 b1 b2
  calc
  φ ((a1, b1) * (a2, b2)) = φ (a1 * a2, b1 * b2) := ?sorry_1
  _ = (b1 * b2, a1 * a2) := ?sorry_2
  _ = (b1, a1) * (b2, a2) := ?sorry_3
  _ = φ (a1, b1) * φ (a2, b2) := ?sorry_4
have h_iso : A × B ≃* B × A
  exact ?sorry_5
exact ⟨h_iso⟩


theorem exercise_8_3_6a {R : Type} [Ring R]
  (hR : R = (GaussianInt ⧸ span ({⟨0, 1⟩} : Set GaussianInt))) :
  IsField R ∧ ∃ finR : Fintype R, @card R finR = 2  := by
have h1 : ∀ a b : ℤ, (a ≡ b [ZMOD 2]) → (⟨a, b⟩ : GaussianInt) ∈ span ({⟨0, 1⟩} : Set GaussianInt)
  exact ?sorry_0
have h2 : ∀ a b : ℤ, ¬ (a ≡ b [ZMOD 2]) → (⟨a - 1, b⟩ : GaussianInt) ∈ span ({⟨0, 1⟩} : Set GaussianInt)
  exact ?sorry_1
have h3 : ∀ x : GaussianInt, x ∈ span ({⟨0, 1⟩} : Set GaussianInt) ∨ x + ⟨1, 0⟩ ∈ span ({⟨0, 1⟩} : Set GaussianInt)
  exact ?sorry_2
have h4 : ∃ finR : Fintype R, @card R finR = 2
  exact ?sorry_3
have h5 : IsField R
  exact ?sorry_4
exact ⟨h5, h4⟩


theorem exercise_4_2_8 {G : Type*} [Group G] {H : Subgroup G}
  {n : ℕ} (hn : n > 0) (hH : H.index = n) :
  ∃ K ≤ H, K.Normal ∧ K.index ≤ n.factorial  := by
let action : G →* Equiv.Perm (G ⧸ H) := ?sorry_0
let K : Subgroup G := action.ker
have hK_normal : K.Normal
  exact ?sorry_1
have hK_le_H : K ≤ H
  exact ?sorry_2
have h_injective : Function.Injective (QuotientGroup.mk' K)
  exact ?sorry_3
have h_inj_hom : ∃ (f : (G ⧸ K) →* Equiv.Perm (G ⧸ H)), Function.Injective f
  exact ?sorry_4
have h_index_bound : K.index ≤ n.factorial
  exact ?sorry_5
exact ⟨K, hK_le_H, hK_normal, h_index_bound⟩


theorem exercise_1_1_34 {G : Type*} [Group G] {x : G}
  (hx_inf : orderOf x = 0) (n m : ℤ) :
  x ^ n ≠ x ^ m  := by
intro h_eq
wlog h_wlog : n ≤ m with h_symm
exact ?sorry_0
let k := m - n
have k_pos : k > 0
  exact ?sorry_1
have h_contradiction : x ^ k = 1
  exact ?sorry_2
have h_inf_order : orderOf x = 0
  exact hx_inf
have h_contradict : k ≥ orderOf x
  exact ?sorry_3
have h_final : False
  exact ?sorry_4
contradiction


theorem exercise_3_4_1 (G : Type*) [CommGroup G] [IsSimpleGroup G] :
    IsCyclic G ∧ ∃ G_fin : Fintype G, Nat.Prime (@card G G_fin)  := by
classical
  by_cases hG : ∃ G_fin : Fintype G, true
  case pos =>
    obtain ⟨G_fin, _⟩ := hG
    have h_card : card G = card G
      exact rfl
    by_cases h_prime : Nat.Prime (card G)
    case pos =>
      have h_cyclic : IsCyclic G
        exact ?sorry_0
      exact ⟨h_cyclic, ⟨G_fin, h_prime⟩⟩
    case neg =>
      have h_composite : ¬ Nat.Prime (card G)
        exact ?sorry_1
      have h_decompose : ∃ p m, Nat.Prime p ∧ m ≠ 1 ∧ card G = p * m
        exact ?sorry_2
      obtain ⟨p, m, hp, hm, hpm⟩ := h_decompose
      have h_cauchy : ∃ x : G, orderOf x = p
        exact ?sorry_3
      obtain ⟨x, hx⟩ := h_cauchy
      have h_subgroup : Subgroup.zpowers x < ⊤
        exact ?sorry_4
      have h_contradiction : False
        exact ?sorry_5
      contradiction
  case neg =>
    have h_infinite : Infinite G
      exact ?sorry_6
    have h_nontrivial : ∃ x : G, x ≠ 1
      exact ?sorry_7
    obtain ⟨x, hx⟩ := h_nontrivial
    by_cases h_finite_order : ∃ n, orderOf x = n
    case pos =>
      obtain ⟨n, hn⟩ := h_finite_order
      have h_subgroup : Subgroup.zpowers x < ⊤
        exact ?sorry_8
      have h_contradiction : False
        exact ?sorry_9
      contradiction
    case neg =>
      have h_infinite_order : orderOf x = 0
        exact ?sorry_10
      have h_subgroup : Subgroup.zpowers (x^2) < ⊤
        exact ?sorry_11
      have h_contradiction : False
        exact ?sorry_12
      contradiction


theorem exercise_7_1_15 {R : Type*} [Ring R] (hR : ∀ a : R, a^2 = a) (a b : R) :
  a * b = b * a  := by
have h_neg : ∀ a : R, -a = a
  intro a
  calc
  -a = (-a)^2 := by rw [hR (-a)]
  _ = (-1)^2 * a^2 := ?sorry_0
  _ = a^2 := ?sorry_1
  _ = a := by rw [hR a]
have h_add : ∀ a b : R, a + b = a + a * b + b * a + b
  intro a b
  calc
  a + b = (a + b)^2 := by rw [hR (a + b)]
  _ = a^2 + a * b + b * a + b^2 := ?sorry_2
  _ = a + a * b + b * a + b := by rw [hR a, hR b]
have h_comm_zero : ∀ a b : R, a * b + b * a = 0
  intro a b
  have h_eq : a + b = a + a * b + b * a + b
    exact h_add a b
  exact ?sorry_3
have h_comm : ∀ a b : R, a * b = b * a
  intro a b
  have h_neg_comm : a * b = -(b * a)
    have h
      exact h_comm_zero a b
    rw [add_eq_zero_iff_eq_neg] at h
    exact h
  rw [h_neg (b * a)] at h_neg_comm
  exact h_neg_comm
exact h_comm a b


theorem exercise_4_2_14 {G : Type*} [Fintype G] [Group G]
  (hG : ¬ (card G).Prime) (hG1 : ∀ k : ℕ, k ∣ card G →
  ∃ (H : Subgroup G) (fH : Fintype H), @card H fH = k) :
  ¬ IsSimpleGroup G  := by
have h_prime_div : ∃ p : ℕ, p.Prime ∧ p ∣ card G
  exact ?sorry_0
rcases h_prime_div with ⟨p, hp_prime, hp_div⟩
have h_card : ∃ m : ℕ, card G = p * m
  exact ?sorry_1
rcases h_card with ⟨m, hm⟩
have h_subgroup_m : ∃ (H : Subgroup G) (fH : Fintype H), @card H fH = m
  exact ?sorry_2
rcases h_subgroup_m with ⟨H, fH, hH_card⟩
have h_index_p : index H = p
  exact ?sorry_3
have h_normal : H.Normal
  exact ?sorry_4
have h_not_simple : ¬ IsSimpleGroup G
  exact ?sorry_5
exact h_not_simple


theorem exercise_7_1_12 {F : Type*} [Field F] {K : Subring F}
  (hK : (1 : F) ∈ K) : IsDomain K  := by
have hnodiv : ∀ x y : K, x * y = 0 → x = 0 ∨ y = 0
  intros x y hxy
  have hxF : (x : F) = x
    exact ?sorry_0
  have hyF : (y : F) = y
    exact ?sorry_1
  have hzero : (0 : K) = (0 : F)
    exact ?sorry_2
  have hfield : (x : F) = 0 ∨ (y : F) = 0
    exact ?sorry_3
  exact ?sorry_4
have hnontrivial : (0 : K) ≠ (1 : K)
  exact ?sorry_5
exact ?sorry_6


theorem exercise_3_2_11 {G : Type*} [Group G] {H K : Subgroup G}
  (hHK : H ≤ K) :
  H.index = K.index * H.relindex K  := by
let cosetsG_K := G ⧸ K
let cosetsK_H := K ⧸ (Subgroup.comap K.subtype H)
have bijection : cosetsG_K ≃ cosetsK_H × cosetsG_K
  exact ?sorry_0
have index_relation : H.index = K.index * H.relindex K
  exact ?sorry_1
exact index_relation


theorem exercise_3_4_4 {G : Type*} [CommGroup G] [Fintype G] {n : ℕ}
    (hn : n ∣ (card G)) :
    ∃ (H : Subgroup G) (H_fin : Fintype H), @card H H_fin = n   := by
by_cases hG : card G = 0
·
  exact ?sorry_0
by_cases hG_prime : Nat.Prime (card G)
·
  have h_div : n = 1 ∨ n = card G
    exact ?sorry_1
  cases h_div with
  | inl h1 =>
    exact ?sorry_2
  | inr hG =>
    exact ?sorry_3
have h_ind : ∀ {G' : Type u_1} [CommGroup G'] [Fintype G'], card G' < card G →
  ∀ (n' : ℕ), n' ∣ card G' → ∃ (H' : Subgroup G') (H'_fin : Fintype H'), @card H' H'_fin = n' := ?sorry_4
have hn_pos : n > 1
  exact ?sorry_5
by_cases hn_prime : Nat.Prime n
·
  have x : G
    exact ?sorry_6
  have hx_order : orderOf x = n
    exact ?sorry_7
  let H := Subgroup.zpowers x
  have H_fin : Fintype H
    exact ?sorry_8
  use H, H_fin
  have hH_order : @card H H_fin = n
    exact ?sorry_9
  exact hH_order
have hp : ∃ p, Nat.Prime p ∧ p ∣ n
  exact ?sorry_10
rcases hp with ⟨p, hp_prime, hp_div⟩
let k := n / p
have hk : n = k * p
  exact ?sorry_11
have x : G
  exact ?sorry_12
have hx_order : orderOf x = p
  exact ?sorry_13
let N := Subgroup.zpowers x
have N_fin : Fintype N
  exact ?sorry_14
have hG_N : card (G ⧸ N) = card G / card N
  exact ?sorry_15
have hG_N_lt : card (G ⧸ N) < card G
  exact ?sorry_16
have h_subgroup : ∃ (K : Subgroup (G ⧸ N)) (K_fin : Fintype K), @card K K_fin = k
  exact ?sorry_17
rcases h_subgroup with ⟨K, K_fin, hK_card⟩
have H : Subgroup G
  exact ?sorry_18
have H_fin : Fintype H
  exact ?sorry_19
use H, H_fin
have hH_order : @card H H_fin = n
  exact ?sorry_20
exact hH_order


theorem exercise_2_1_13 (H : AddSubgroup ℚ) {x : ℚ}
  (hH : x ∈ H → (1 / x) ∈ H):
  H = ⊥ ∨ H = ⊤  := by
classical
  by_cases h : ∃ a : ℚ, a ≠ 0 ∧ a ∈ H
  ·
    obtain ⟨a, ha, haH⟩ := h
    have ha_form : ∃ p q : ℤ, a = p / q ∧ Int.gcd p q = 1
      exact ?sorry_0
    obtain ⟨p, q, ha_eq, h_gcd⟩ := ha_form
    have hpH : (p : ℚ) ∈ H
      exact ?sorry_1
    have hq_invH : (q : ℚ)⁻¹ ∈ H
      exact ?sorry_2
    have h1H : (1 : ℚ) ∈ H
      exact ?sorry_3
    have hZ_in_H : ∀ n : ℤ, (n : ℚ) ∈ H
      exact ?sorry_4
    have hQ_in_H : ∀ m n : ℤ, n ≠ 0 → (m / n : ℚ) ∈ H
      exact ?sorry_5
    exact Or.inr (AddSubgroup.ext fun x => ⟨fun hx => exact ?sorry_6, fun _ => exact ?sorry_7⟩)
  ·
    have hH_zero : H = ⊥
      exact ?sorry_8
    exact Or.inl hH_zero


theorem exercise_7_1_2 {R : Type*} [Ring R] {u : R}
  (hu : IsUnit u) : IsUnit (-u)  := by
obtain ⟨u_unit, rfl⟩ := hu
let v := u_unit.inv
have h_neg_vu : (-v) * (-↑u_unit) = 1
  calc
  (-v) * (-↑u_unit) = v * ↑u_unit := ?sorry_0
  _ = 1 := u_unit.inv_val
have h_neg_uv : (-↑u_unit) * (-v) = 1
  calc
  (-↑u_unit) * (-v) = ↑u_unit * v := ?sorry_1
  _ = 1 := u_unit.val_inv
exact ⟨⟨-↑u_unit, -v, h_neg_uv, h_neg_vu⟩, rfl⟩


theorem exercise_4_5_1a {p : ℕ} {G : Type*} [Group G]
  {P : Subgroup G} (hP : IsPGroup p P) (H : Subgroup G)
  (hH : P ≤ H) : IsPGroup p H  := by
have hSylowG : ∀ Q : Subgroup G, IsPGroup p Q → Q ≤ P → Q = P
  exact ?sorry_0
have hIndexG : ¬ p ∣ (Subgroup.index P)
  exact ?sorry_1
have hIndexFormula : Subgroup.index P = Subgroup.index H * Subgroup.index (Subgroup.comap H.subtype P)
  exact ?sorry_2
have hIndexH : ¬ p ∣ Subgroup.index (Subgroup.comap H.subtype P)
  exact ?sorry_3
have hSylowH : ∀ Q : Subgroup H, IsPGroup p Q → Q ≤ Subgroup.comap H.subtype P → Q = Subgroup.comap H.subtype P
  exact ?sorry_4
exact ?sorry_5
