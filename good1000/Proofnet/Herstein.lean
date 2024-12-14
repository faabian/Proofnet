import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators
noncomputable section

theorem exercise_2_8_15 {G H: Type*} [Fintype G] [Group G] [Fintype H]
  [Group H] {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
  (h : p > q) (h1 : q ∣ p - 1) (hG : card G = p*q) (hH : card G = p*q) :
  Nonempty (G ≃* H)  := by
have hG_nonabelian : ¬∀ x y : G, x * y = y * x
  exact ?sorry_0
have hH_nonabelian : ¬∀ x y : H, x * y = y * x
  exact ?sorry_1
let a : G := ?sorry_2
let b : G := ?sorry_3
let c : H := ?sorry_4
let d : H := ?sorry_5
let k : ℕ := ?sorry_6
have hG_relation : ∃ k, a * b * a⁻¹ = b^(k^(p-1)/q)
  exact ?sorry_7
have hH_relation : ∃ l, c * d * c⁻¹ = d^(k^(l*(p-1)/q))
  exact ?sorry_8
let φ : H → G := ?sorry_9
have φ_well_defined : ∀ x y : H, φ (x * y) = φ x * φ y
  exact ?sorry_10
have φ_injective : Function.Injective φ
  exact ?sorry_11
have φ_surjective : Function.Surjective φ
  exact ?sorry_12
have φ_isomorphism : H ≃* G
  exact ?sorry_13
exact ⟨φ_isomorphism.symm⟩


theorem exercise_2_5_23 {G : Type*} [Group G]
  (hG : ∀ (H : Subgroup G), H.Normal) (a b : G) :
  ∃ (j : ℤ) , b*a = a^j * b := by
let H := Subgroup.closure ({a} : Set G)
have hH : H.Normal
  exact hG H
have h_conj : ∀ g ∈ H, b * g * b⁻¹ ∈ H
  intro g hg
  exact hH.conj_mem g hg b
have h_exists_j : ∃ (j : ℤ), b * a = a ^ j * b
  exact ?sorry_0
exact h_exists_j


theorem exercise_2_7_7 {G : Type*} [Group G] {G' : Type*} [Group G']
  (φ : G →* G') (N : Subgroup G) [N.Normal] :
  (Subgroup.map φ N).Normal   := by
have h1 : (1 : G') ∈ Subgroup.map φ N
  exact ?sorry_0
have h2 : ∀ (a' b' : G'), a' ∈ Subgroup.map φ N → b' ∈ Subgroup.map φ N → a' * b'⁻¹ ∈ Subgroup.map φ N
  exact ?sorry_1
have h3 : ∀ (x' : G') (h' : G'), h' ∈ Subgroup.map φ N → x' * h' * x'⁻¹ ∈ Subgroup.map φ N
  exact ?sorry_2
exact ?sorry_3


theorem exercise_2_1_26 {G : Type*} [Group G]
  [Fintype G] (a : G) : ∃ (n : ℕ), a ^ n = 1  := by
let elements := (Finset.univ : Finset G)
have exists_ij : ∃ i j : ℕ, i ≠ j ∧ a ^ i = a ^ j
  exact ?sorry_0
have exists_ij' : ∃ i j : ℕ, i > j ∧ a ^ i = a ^ j
  exact ?sorry_1
rcases exists_ij' with ⟨i, j, hij, a_eq⟩
let n := i - j
have a_pow_n_eq_e : a ^ n = 1
  exact ?sorry_2
exact ⟨n, a_pow_n_eq_e⟩


theorem exercise_4_5_23 {p q: Polynomial (ZMod 7)}
  (hp : p = X^3 - 2) (hq : q = X^3 + 2) :
  Irreducible p ∧ Irreducible q ∧
  (Nonempty $ Polynomial (ZMod 7) ⧸ span ({p} : Set $ Polynomial $ ZMod 7) ≃+*
  Polynomial (ZMod 7) ⧸ span ({q} : Set $ Polynomial $ ZMod 7))  := by
have hp_irred : Irreducible p
  have no_roots_p : ∀ x : ZMod 7, p.eval x ≠ 0
    exact ?sorry_0
  exact ?sorry_1
have hq_irred : Irreducible q
  have no_roots_q : ∀ x : ZMod 7, q.eval x ≠ 0
    exact ?sorry_2
  exact ?sorry_3
have field_iso : Nonempty $ Polynomial (ZMod 7) ⧸ span ({p} : Set $ Polynomial $ ZMod 7) ≃+*
  Polynomial (ZMod 7) ⧸ span ({q} : Set $ Polynomial $ ZMod 7) := by
  let τ : Polynomial (ZMod 7) ⧸ span ({p} : Set $ Polynomial $ ZMod 7) →
    Polynomial (ZMod 7) ⧸ span ({q} : Set $ Polynomial $ ZMod 7) := ?sorry_4
  have τ_onto : Function.Surjective τ
    exact ?sorry_5
  have τ_one_to_one : Function.Injective τ
    exact ?sorry_6
  have τ_hom : ∀ n m, τ (n * m) = τ n * τ m
    exact ?sorry_7
  exact ?sorry_8
exact ⟨hp_irred, hq_irred, field_iso⟩


theorem exercise_2_3_16 {G : Type*} [Group G]
  (hG : ∀ H : Subgroup G, H = ⊤ ∨ H = ⊥) :
  IsCyclic G ∧ ∃ (p : ℕ) (Fin : Fintype G), Nat.Prime p ∧ @card G Fin = p  := by
classical
  by_cases hGtriv : ∀ x : G, x = 1
  · have hGcyclic : IsCyclic G := ?sorry_0
    have hGfinite : ∃ (p : ℕ) (Fin : Fintype G), Nat.Prime p ∧ @card G Fin = p
      exact ?sorry_1
    exact ⟨hGcyclic, hGfinite⟩
  · push_neg at hGtriv
    obtain ⟨a, ha⟩ := hGtriv
    let H := Subgroup.closure ({a} : Set G)
    have hHsub : H ≤ ⊤
      exact ?sorry_2
    have hHnontriv : H ≠ ⊥
      exact ?sorry_3
    have hHeqG : H = ⊤
      cases hG H with
      | inl hH => exact hH
      | inr hH => contradiction
    have hGcyclic : IsCyclic G
      exact ?sorry_4
    have hGfinite : ∃ (p : ℕ) (Fin : Fintype G), Nat.Prime p ∧ @card G Fin = p
      exact ?sorry_5
    exact ⟨hGcyclic, hGfinite⟩


theorem exercise_2_1_18 {G : Type*} [Group G]
  [Fintype G] (hG2 : Even (card G)) :
  ∃ (a : G), a ≠ 1 ∧ a = a⁻¹  := by
have h_order2 : ∀ a : G, a = a⁻¹ ↔ a ^ 2 = 1
  exact ?sorry_0
let S := {a : G | a ≠ 1 ∧ a ≠ a⁻¹}
have h_finite_S : Fintype S
  exact ?sorry_1
let S_finset := S.toFinset
have h_even_S : Even S_finset.card
  exact ?sorry_2
have h_identity : ∃! e : G, e = 1
  exact ?sorry_3
have h_card_G : Fintype.card G = 2 * (Fintype.card G / 2)
  exact ?sorry_4
let n := Fintype.card G / 2
have h_elements_order2 : Fintype.card G - S_finset.card - 1 = 2 * (n - S_finset.card / 2) - 1
  exact ?sorry_5
have h_nonzero : 2 * (n - S_finset.card / 2) - 1 ≠ 0
  exact ?sorry_6
have h_exists_order2 : ∃ a : G, a ≠ 1 ∧ a = a⁻¹
  exact ?sorry_7
exact h_exists_order2


theorem exercise_4_6_2 : Irreducible (X^3 + 3*X + 2 : Polynomial ℚ)  := by
by_contra h
have h_root : ∃ (r : ℚ), (X^3 + 3*X + 2).eval r = 0
  exact ?sorry_0
have h_rat_root : ∃ (p q : ℤ), q ≠ 0 ∧ gcd p q = 1 ∧
  (X^3 + 3*X + 2).eval (p / q) = 0 := ?sorry_1
obtain ⟨p, q, hq_ne_zero, gcd_pq, h_eq⟩ := h_rat_root
have h_eval : (p / q)^3 + 3 * (p / q) + 2 = 0
  exact ?sorry_2
have h_int_form : p^3 + 3 * p * q^2 = -2 * q^3
  exact ?sorry_3
have h_div : p ∣ q
  exact ?sorry_4
have h_contradiction : False
  exact ?sorry_5
exact h_contradiction


theorem exercise_2_5_37 (G : Type*) [Group G] [Fintype G]
  (hG : card G = 6) (nonCommG : ∃ a b : G, a * b ≠ b * a) :
  Nonempty (G ≃* Equiv.Perm (Fin 3))  := by
have h1 : ¬ ∃ x : G, orderOf x = 6
  exact ?sorry_0
have h2 : ∀ x : G, x ≠ 1 → orderOf x = 2 ∨ orderOf x = 3
  exact ?sorry_1
have h3 : ¬ ∀ x : G, x ≠ 1 → orderOf x = 3
  exact ?sorry_2
have h4 : ∃ a : G, orderOf a = 2
  exact ?sorry_3
have h5 : ∃ b : G, orderOf b = 3
  exact ?sorry_4
obtain ⟨a, ha⟩ := h4
obtain ⟨b, hb⟩ := h5
let elts : Finset G := ⟨[1, a, b, b^2, a * b, a * b^2], exact ?sorry_5⟩
have h6 : elts = Finset.univ
  exact ?sorry_6
have h7 : ∃ c : G, c ∈ elts ∧ b * a = c
  exact ?sorry_7
have h8 : b * a ≠ 1 ∧ b * a ≠ a ∧ b * a ≠ b ∧ b * a ≠ b^2
  exact ?sorry_8
have h9 : b * a = a * b^2
  exact ?sorry_9
have h10 : G ≃* Equiv.Perm (Fin 3)
  exact ?sorry_10
exact ⟨h10⟩


theorem exercise_5_3_10 : IsAlgebraic ℚ (cos (Real.pi / 180))  := by
let z := Complex.exp (Complex.I * Real.pi / 180)
have hz : z ^ 360 = 1
  exact ?sorry_0
have z_algebraic : IsAlgebraic ℚ z
  exact ?sorry_1
have z_real : z.re = Real.cos (Real.pi / 180)
  exact ?sorry_2
have z_imag : z.im = Real.sin (Real.pi / 180)
  exact ?sorry_3
have cos_algebraic : IsAlgebraic ℚ z.re
  exact ?sorry_4
rw [←z_real]
exact cos_algebraic


theorem exercise_2_8_12 {G H : Type*} [Fintype G] [Fintype H]
  [Group G] [Group H] (hG : card G = 21) (hH : card H = 21)
  (nonCommG : ∃ a b : G, a * b ≠ b * a) (nonCommH : ∃ a b : H, a * b ≠ b * a) :
  Nonempty (G ≃* H)  := by
have exists_order3_G : ∃ a : G, orderOf a = 3
  exact ?sorry_0
have exists_order7_G : ∃ b : G, orderOf b = 7
  exact ?sorry_1
have exists_order3_H : ∃ c : H, orderOf c = 3
  exact ?sorry_2
have exists_order7_H : ∃ d : H, orderOf d = 7
  exact ?sorry_3
have normal_subgroup_G : ∀ b : G, orderOf b = 7 → ∃ i, i ≠ 0 ∧ i ≠ 1 ∧ ∀ a : G, a * b * a⁻¹ = b ^ i
  exact ?sorry_4
have normal_subgroup_H : ∀ d : H, orderOf d = 7 → ∃ j, j ≠ 0 ∧ j ≠ 1 ∧ ∀ c : H, c * d * c⁻¹ = d ^ j
  exact ?sorry_5
have possible_i : ∀ i, i^3 ≡ 1 [MOD 7] → i = 2 ∨ i = 4
  exact ?sorry_6
have possible_j : ∀ j, j^3 ≡ 1 [MOD 7] → j = 2 ∨ j = 4
  exact ?sorry_7
have structure_G : ∃ a b : G, orderOf a = 3 ∧ orderOf b = 7 ∧ a * b * a⁻¹ = b^2
  exact ?sorry_8
have structure_H : ∃ c d : H, orderOf c = 3 ∧ orderOf d = 7 ∧ c * d * c⁻¹ = d^4
  exact ?sorry_9
let φ : G → H := ?sorry_10
have homomorphism : ∀ x y : G, φ (x * y) = φ x * φ y
  exact ?sorry_11
let φ_monoid_hom : G →* H := { toFun := φ, map_one' := ?sorry_12, map_mul' := homomorphism }
have bijective : Function.Bijective φ
  exact ?sorry_13
exact ⟨MulEquiv.ofBijective φ_monoid_hom bijective⟩


theorem exercise_2_5_44 {G : Type*} [Group G] [Fintype G] {p : ℕ}
  (hp : Nat.Prime p) (hG : card G = p^2) :
  ∃ (N : Subgroup G) (Fin : Fintype N), @card N Fin = p ∧ N.Normal  := by
classical
  by_cases hCyclic : ∃ g : G, IsCyclic G
  ·
    obtain ⟨g, hg⟩ := hCyclic
    have hOrderG : orderOf g = p^2
      exact ?sorry_0
    have hSubgroup : ∃ (H : Subgroup G) (Fin : Fintype H), @card H Fin = p
      exact ?sorry_1
    rcases hSubgroup with ⟨H, FinH, hH⟩
    have hNormal : H.Normal
      exact ?sorry_2
    exact ⟨H, FinH, hH, hNormal⟩
  ·
    have hNonCyclic : ¬∃ g : G, IsCyclic G
      exact hCyclic
    have hOrder : ∃ a : G, orderOf a = p
      exact ?sorry_3
    rcases hOrder with ⟨a, ha⟩
    let A := Subgroup.zpowers a
    have hAcard : @card A _ = p
      exact ?sorry_4
    have hIndex : Fintype.card (G ⧸ A) = p
      exact ?sorry_5
    have hFactorial : p^2 ∣ Nat.factorial p
      exact ?sorry_6
    have hNormalSubgroup : ∃ (K : Subgroup G), K ≠ ⊥ ∧ K ≤ A ∧ K.Normal
      exact ?sorry_7
    rcases hNormalSubgroup with ⟨K, hKnontrivial, hKsubA, hKnormal⟩
    have hKcard : @card K _ = p
      exact ?sorry_8
    exact ⟨K, inferInstance, hKcard, hKnormal⟩


theorem exercise_4_2_6 {R : Type*} [Ring R] (a x : R)
  (h : a ^ 2 = 0) : a * (a * x + x * a) = (x + x * a) * a  := by
have h1 : a * (a * x + x * a) = a * (a * x) + a * (x * a)
  exact ?sorry_0
have h2 : a * (a * x) + a * (x * a) = a ^ 2 * x + a * x * a
  exact ?sorry_1
have h3 : a ^ 2 * x + a * x * a = 0 + a * x * a
  exact ?sorry_2
have h4 : 0 + a * x * a = a * x * a
  exact ?sorry_3
have h5 : (a * x + x * a) * a = (a * x) * a + (x * a) * a
  exact ?sorry_4
have h6 : (a * x) * a + (x * a) * a = a * x * a + x * a ^ 2
  exact ?sorry_5
have h7 : a * x * a + x * a ^ 2 = a * x * a + 0
  exact ?sorry_6
have h8 : a * x * a + 0 = a * x * a
  exact ?sorry_7
exact ?sorry_8


theorem exercise_5_1_8 {p m n: ℕ} {F : Type*} [Field F]
  (hp : Nat.Prime p) (hF : CharP F p) (a b : F) (hm : m = p ^ n) :
  (a + b) ^ m = a^m + b^m  := by
have hma : m * a = 0
  exact ?sorry_0
have hmb : m * b = 0
  exact ?sorry_1
have binom_expansion : (a + b) ^ m = ∑ i in Finset.range (m + 1), ↑(Nat.choose m i) * a^i * b^(m-i)
  exact ?sorry_2
have hdiv : ∀ i, 1 ≤ i ∧ i < m → p ∣ Nat.choose m i
  exact ?sorry_3
have sum_vanishes : ∑ i in Finset.range (m + 1), ↑(Nat.choose m i) * a^i * b^(m-i) = a^m + b^m
  exact ?sorry_4
rw [binom_expansion]
exact sum_vanishes


theorem exercise_2_1_27 {G : Type*} [Group G]
  [Fintype G] : ∃ (m : ℕ), ∀ (a : G), a ^ m = 1  := by
let orders := Finset.univ.image (fun a : G => orderOf a)
let m := orders.fold lcm 1 id
use m
intro a
let n := orderOf a
have h_lcm : ∃ c, m = n * c
  exact ?sorry_0
obtain ⟨c, hc⟩ := h_lcm
have h_order : a ^ n = 1
  exact ?sorry_1
calc
  a ^ m = a ^ (n * c) := by rw [hc]
  _ = (a ^ n) ^ c := ?sorry_2
  _ = 1 ^ c := by rw [h_order]
  _ = 1 := by rw [one_pow]


theorem exercise_3_2_21 {α : Type*} [Fintype α] {σ τ: Equiv.Perm α}
  (h1 : ∀ a : α, σ a = a ↔ τ a ≠ a) (h2 : τ ∘ σ = id) :
  σ = 1 ∧ τ = 1  := by
have h_inv : τ = σ⁻¹
  exact ?sorry_0
have h_nonidentity : ∀ a : α, σ a ≠ a → τ a ≠ a
  exact ?sorry_1
have h_cycle : ∃ i : α, σ i ≠ i
  exact ?sorry_2
have h_sigma_cycle : ∀ i : α, σ i ≠ i → ∃ j : α, σ j = i
  exact ?sorry_3
have h_tau_cycle : ∀ i : α, τ i ≠ i → ∃ j : α, τ j = i
  exact ?sorry_4
have h_disturb : ∃ i : α, σ i ≠ i ∧ τ i ≠ i
  exact ?sorry_5
have h_conclude : σ = 1 ∧ τ = 1
  exact ?sorry_6
exact h_conclude


theorem exercise_4_1_19 : Infinite {x : Quaternion ℝ | x^2 = -1}  := by
have : ∃ a b c : ℝ, a^2 + b^2 + c^2 = 1
  exact ?sorry_0
rcases this with ⟨a, b, c, h_abc⟩
let x : Quaternion ℝ := ⟨0, a, b, c⟩
have h1 : x^2 = ⟨0, a, b, c⟩ * ⟨0, a, b, c⟩
  exact ?sorry_1
have h2 : x^2 = -a^2 - b^2 - c^2
  exact ?sorry_2
have h3 : -a^2 - b^2 - c^2 = -1
  exact ?sorry_3
have h4 : a^2 + b^2 + c^2 = 1
  exact ?sorry_4
have h5 : Infinite {⟨a, b, c⟩ : ℝ × ℝ × ℝ | a^2 + b^2 + c^2 = 1 ∧ -1 < a ∧ a < 1 ∧ -1 < b ∧ b < 1 ∧ -1 < c ∧ c < 1}
  exact ?sorry_5
exact ?sorry_6


theorem exercise_2_4_36 {a n : ℕ} (h : a > 1) :
  n ∣ (a ^ n - 1).totient  := by
have gcd_one : Nat.gcd a (a ^ n - 1) = 1
  exact ?sorry_0
have a_in_U : a ∈ {b : ℕ | Nat.gcd b (a ^ n - 1) = 1}
  exact ?sorry_1
have order_divides_totient : ∃ m, m ∣ (a ^ n - 1).totient
  exact ?sorry_2
exact ?sorry_3


theorem exercise_4_6_3 :
  Infinite {a : ℤ | Irreducible (X^7 + 15*X^2 - 30*X + (a : Polynomial ℚ) : Polynomial ℚ)}  := by
have h_eisenstein : ∀ a : ℤ, (5 ∣ a ∧ ¬ (25 ∣ a)) → Irreducible (X^7 + 15*X^2 - 30*X + (a : Polynomial ℚ))
  exact ?sorry_0
have h_sequence : ∀ k : ℕ, 5 ∣ (5 * 2^k) ∧ ¬ (25 ∣ (5 * 2^k))
  exact ?sorry_1
have h_infinite : Infinite {a : ℤ | ∃ k : ℕ, a = 5 * 2^k}
  exact ?sorry_2
exact ?sorry_3


theorem exercise_2_1_21 (G : Type*) [Group G] [Fintype G]
  (hG : card G = 5) (a b : G) :
  a * b = b * a  := by
have h1 : a ≠ 1
  exact ?sorry_0
have h2 : b ≠ 1
  exact ?sorry_1
have h3 : a * b ≠ b * a
  exact ?sorry_2
have h4 : ∀ x : G, x = 1 ∨ x = a ∨ x = b ∨ x = a * b ∨ x = b * a
  exact ?sorry_3
have h5 : a^2 ≠ a
  exact ?sorry_4
have h6 : a^2 ≠ a * b
  exact ?sorry_5
have h7 : a^2 ≠ b * a
  exact ?sorry_6
have h8 : a^2 = 1 ∨ a^2 = b
  exact ?sorry_7
have h9 : a * b * a ≠ a
  exact ?sorry_8
have h10 : a * b * a ≠ b
  exact ?sorry_9
have h11 : a * b * a ≠ a * b
  exact ?sorry_10
have h12 : a * b * a ≠ b * a
  exact ?sorry_11
have h13 : a * b * a = 1
  exact ?sorry_12
have h14 : a^2 ≠ 1
  exact ?sorry_13
have h15 : a^2 = b
  exact ?sorry_14
have h16 : a * b = a * a^2
  exact ?sorry_15
have h17 : a * b = b * a
  exact ?sorry_16
contradiction


theorem exercise_5_3_7 {K : Type*} [Field K] {F : Subfield K}
  {a : K} (ha : IsAlgebraic F (a ^ 2)) : IsAlgebraic F a  := by
obtain ⟨f, hf_nonzero, hf⟩ := ha
let g := Polynomial.comp f (Polynomial.X ^ 2)
have hg_nonzero : g ≠ 0
  exact ?sorry_0
have hg_zero : Polynomial.aeval a g = 0
  exact ?sorry_1
exact ⟨g, hg_nonzero, hg_zero⟩


theorem exercise_2_5_43 (G : Type*) [Group G] [Fintype G]
  (hG : card G = 9) (a b : G) :
  a * b = b * a  := by
by_cases h_cyclic : ∃ g : G, ∀ x : G, x ∈ Subgroup.zpowers g
·
  exact ?sorry_0
·
  have h_order3 : ∃ a : G, orderOf a = 3
    exact ?sorry_1
  rcases h_order3 with ⟨a, ha⟩
  let A := Subgroup.zpowers a
  have hA_card : Fintype.card A = 3
    exact ?sorry_2
  have hA_normal : A ≤ Subgroup.normalizer A
    exact ?sorry_3
  have h_exists_b : ∃ b : G, b ∉ A
    exact ?sorry_4
  rcases h_exists_b with ⟨b, hb⟩
  have h_conj : ∃ i : ℤ, b * a * b⁻¹ = a ^ i
    exact ?sorry_5
  rcases h_conj with ⟨i, hi⟩
  have h_i1 : i = 1
    exact ?sorry_6
  exact ?sorry_7


theorem exercise_2_3_17 {G : Type*} [Mul G] [Group G] (a x : G) :
  centralizer {x⁻¹*a*x} =
  (λ g : G => x⁻¹*g*x) '' (centralizer {a})  := by
have h1 : ∀ p ∈ centralizer {x⁻¹ * a * x}, (x * p * x⁻¹) ∈ centralizer {a}
  intro p hp
  have hpxax : p * (x⁻¹ * a * x) = (x⁻¹ * a * x) * p
    exact ?sorry_0
  have h1_step1 : (p * x⁻¹ * a) * x = x⁻¹ * (a * x * p)
    exact ?sorry_1
  have h1_step2 : x * (p * x⁻¹ * a) = (a * x * p) * x⁻¹
    exact ?sorry_2
  have h1_step3 : (x * p * x⁻¹) * a = a * (x * p * x⁻¹)
    exact ?sorry_3
  exact ?sorry_4
have h1_conclusion : centralizer {x⁻¹ * a * x} ⊆ (λ g : G => x⁻¹ * g * x) '' (centralizer {a})
  exact ?sorry_5
have h2 : ∀ q ∈ (λ g : G => x⁻¹ * g * x) '' (centralizer {a}), q ∈ centralizer {x⁻¹ * a * x}
  intro q hq
  rcases hq with ⟨y, hy, rfl⟩
  have hy_ca : y ∈ centralizer {a}
    exact ?sorry_6
  have hy_comm : y * a = a * y
    exact ?sorry_7
  let q := x⁻¹ * y * x
  have hq_xax : q * (x⁻¹ * a * x) = (x⁻¹ * a * x) * q
    exact ?sorry_8
  exact ?sorry_9
have h2_conclusion : (λ g : G => x⁻¹ * g * x) '' (centralizer {a}) ⊆ centralizer {x⁻¹ * a * x}
  exact ?sorry_10
exact ?sorry_11


theorem exercise_2_6_15 {G : Type*} [CommGroup G] {m n : ℕ}
  (hm : ∃ (g : G), orderOf g = m)
  (hn : ∃ (g : G), orderOf g = n)
  (hmn : m.Coprime n) :
  ∃ (g : G), orderOf g = m * n  := by
classical
  let a := Classical.choose hm
  have ha
    exact Classical.choose_spec hm
  let b := Classical.choose hn
  have hb
    exact Classical.choose_spec hn
  have hab_order : orderOf (a * b) ∣ m * n
    exact ?sorry_0
  have hmn_order : (a * b) ^ (m * n) = 1
    exact ?sorry_1
  have a_k_eq_b_inv_k : ∀ k, a ^ k = b ^ (-k : ℤ)
    exact ?sorry_2
  have bezout : ∃ x y : ℤ, m * x + n * y = 1
    exact ?sorry_3
  obtain ⟨x, y, hxy⟩ := bezout
  have a_kx_eq_e : ∀ k, (a ^ k) ^ x = 1
    exact ?sorry_4
  have b_ky_eq_e : ∀ k, (b ^ k) ^ y = 1
    exact ?sorry_5
  have m_div_ky : ∀ k : ℕ, m ∣ (k * (y.natAbs : ℕ))
    exact ?sorry_6
  have n_div_kx : ∀ k : ℕ, n ∣ (k * (x.natAbs : ℕ))
    exact ?sorry_7
  have mn_div_k : ∀ k : ℕ, m * n ∣ k
    exact ?sorry_8
  have order_eq_mn : orderOf (a * b) = m * n
    exact ?sorry_9
  exact ⟨a * b, order_eq_mn⟩


theorem exercise_2_9_2 {G H : Type*} [Fintype G] [Fintype H] [Group G]
  [Group H] (hG : IsCyclic G) (hH : IsCyclic H) :
  IsCyclic (G × H) ↔ (card G).Coprime (card H)  := by
constructor
· intro hCyclic
  have order_prod : card (G × H) = card G * card H
    exact ?sorry_0
  have exists_gen : ∃ g : G × H, orderOf g = card (G × H)
    exact ?sorry_1
  rcases exists_gen with ⟨g, hg⟩
  have coprime_condition : (card G).Coprime (card H)
    exact ?sorry_2
  exact coprime_condition
· intro hCoprime
  obtain ⟨g, hg⟩ := hG.exists_generator
  obtain ⟨h, hh⟩ := hH.exists_generator
  have order_g : orderOf g = card G
    exact ?sorry_3
  have order_h : orderOf h = card H
    exact ?sorry_4
  have order_gh : orderOf (g, h) = card G * card H
    exact ?sorry_5
  have is_cyclic : IsCyclic (G × H)
    exact ?sorry_6
  exact is_cyclic


theorem exercise_4_1_34 : Nonempty (Equiv.Perm (Fin 3) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 2))  := by
let A1 : Matrix (Fin 2) (Fin 2) (ZMod 2) := ![![1, 0], ![0, 1]]
let A2 : Matrix (Fin 2) (Fin 2) (ZMod 2) := ![![0, 1], ![1, 0]]
let A3 : Matrix (Fin 2) (Fin 2) (ZMod 2) := ![![1, 0], ![1, 1]]
let A4 : Matrix (Fin 2) (Fin 2) (ZMod 2) := ![![1, 1], ![0, 1]]
let A5 : Matrix (Fin 2) (Fin 2) (ZMod 2) := ![![0, 1], ![1, 1]]
let A6 : Matrix (Fin 2) (Fin 2) (ZMod 2) := ![![1, 1], ![1, 0]]
let id : Equiv.Perm (Fin 3) := Equiv.refl _
let σ12 : Equiv.Perm (Fin 3) := Equiv.swap 0 1
let σ13 : Equiv.Perm (Fin 3) := Equiv.swap 0 2
let σ23 : Equiv.Perm (Fin 3) := Equiv.swap 1 2
let σ123 : Equiv.Perm (Fin 3) := (Equiv.swap 0 1) * (Equiv.swap 1 2)
let σ132 : Equiv.Perm (Fin 3) := (Equiv.swap 0 2) * (Equiv.swap 1 2)
let τ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) → Equiv.Perm (Fin 3) := ?sorry_0
have τ_hom : ∀ A B, τ (A * B) = τ A * τ B
  exact ?sorry_1
have τ_bij : Function.Bijective τ
  exact ?sorry_2
have τ_iso : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) ≃* Equiv.Perm (Fin 3)
  exact ?sorry_3
let τ_iso_inv : Equiv.Perm (Fin 3) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) := τ_iso.symm
exact ⟨τ_iso_inv⟩


theorem exercise_2_2_5 {G : Type*} [Group G]
  (h : ∀ (a b : G), (a * b) ^ 3 = a ^ 3 * b ^ 3 ∧ (a * b) ^ 5 = a ^ 5 * b ^ 5) (a b : G) :
  a * b = b * a  := by
have h3
  exact (h a b).1
have h5
  exact (h a b).2
have h3_expanded : (a * b) * (a * b) * (a * b) = a * (a * a * b * b) * b
  exact ?sorry_0
have step1 : a * (b * a) * (b * a) * b = a * (a * a * b * b) * b
  exact ?sorry_1
have H1 : (b * a) * (b * a) = a * a * b * b
  exact ?sorry_2
have h5_expanded : (a * b) * (a * b) * (a * b) * (a * b) * (a * b) = a * (a * a * a * a * b * b * b * b) * b
  exact ?sorry_3
have step2 : a * (b * a) * (b * a) * (b * a) * (b * a) * b = a * (a * a * a * a * b * b * b * b) * b
  exact ?sorry_4
have H2 : (b * a) * (b * a) * (b * a) * (b * a) = a * a * a * a * b * b * b * b
  exact ?sorry_5
have H1_squared : ((b * a) * (b * a)) * ((b * a) * (b * a)) = (a * a * b * b) * (a * a * b * b)
  exact ?sorry_6
have H_combined : (a * a * b * b) * (a * a * b * b) = (a * a) * (a * a * b * b) * (b * b)
  exact ?sorry_7
have H_final : a * a * (b * b * a * a) * b * b = a * a * a * a * b * b * b * b
  exact ?sorry_8
have h_cancel : b * b * a * a = a * a * b * b
  exact ?sorry_9
have h_eq : b * b * a * a = (b * a) * (b * a)
  exact ?sorry_10
have h_eq' : b * (b * a) * a = (b * a) * (b * a)
  exact ?sorry_11
have h_eq'' : b * (b * a) * a = b * (a * b) * a
  exact ?sorry_12
have h_comm : b * a = a * b
  exact ?sorry_13
exact Eq.symm h_comm
