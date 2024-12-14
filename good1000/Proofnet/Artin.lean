import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators
noncomputable section

theorem exercise_10_4_7a {R : Type*} [CommRing R] [NoZeroDivisors R]
  (I J : Ideal R) (hIJ : I + J = ⊤) : I * J = I ⊓ J  := by
have hIJ_le : I * J ≤ I ⊓ J
  exact ?sorry_0
have hIJ_ge : I ⊓ J ≤ I * J
  intro k hk
  have h1 : ∃ i ∈ I, ∃ j ∈ J, i + j = 1
    exact ?sorry_1
  rcases h1 with ⟨i, hi, j, hj, hij⟩
  have h2 : k = i * k + j * k
    calc
  k = k * 1 := by rw [mul_one]
  _ = k * (i + j) := by rw [hij]
  _ = i * k + j * k := ?sorry_2
  have h3 : i * k ∈ I * J
    exact ?sorry_3
  have h4 : j * k ∈ I * J
    exact ?sorry_4
  rw [h2]
  exact Ideal.add_mem (I * J) h3 h4
exact le_antisymm hIJ_le hIJ_ge


theorem exercise_11_4_6b {F : Type*} [Field F] [Fintype F] (hF : card F = 31) :
  Irreducible (X ^ 3 - 9 : Polynomial F)  := by
by_contra h
have h_root : ∃ a : ZMod 7, (Polynomial.C a + Polynomial.X) ∣ (Polynomial.C (1 : ZMod 7) + Polynomial.X ^ 2)
  exact ?sorry_0
have h_check : ∀ a : ZMod 7, (Polynomial.C (1 : ZMod 7) + Polynomial.X ^ 2).eval a ≠ 0
  exact ?sorry_1
rcases h_root with ⟨a, ha⟩
have h_eval : (Polynomial.C (1 : ZMod 7) + Polynomial.X ^ 2).eval a = 0
  exact ?sorry_2
exact h_check a h_eval


theorem exercise_2_8_6 {G H : Type*} [Group G] [Group H] :
  Nonempty (center (G × H) ≃* (center G) × (center H) )  := by
let ZGH := center (G × H)
let ZG := center G
let ZH := center H
let toProd : ZGH → ZG × ZH := fun z => ⟨⟨z.1.1, exact ?sorry_0⟩, ⟨z.1.2, exact ?sorry_1⟩⟩
let fromProd : ZG × ZH → ZGH := fun p => ⟨(p.1.1, p.2.1), exact ?sorry_2⟩
have toProd_fromProd : ∀ x : ZG × ZH, toProd (fromProd x) = x
  exact ?sorry_3
have fromProd_toProd : ∀ z : ZGH, fromProd (toProd z) = z
  exact ?sorry_4
exact ⟨{ toFun := toProd, invFun := fromProd, left_inv := fromProd_toProd, right_inv := toProd_fromProd, map_mul' := ?sorry_5 }⟩


theorem exercise_11_4_6c : Irreducible (X^3 - 9 : Polynomial (ZMod 31))  := by
by_contra h_red
have h_factor : ∃ a : ZMod 31, (X - C a) ∣ (X^3 - 9)
  exact ?sorry_0
have h_no_root : ∀ a : ZMod 31, (a^3 - 9) ≠ 0
  exact ?sorry_1
have h_contradiction : False
  exact ?sorry_2
exact h_contradiction


theorem exercise_11_4_6a {F : Type*} [Field F] [Fintype F] (hF : card F = 7) :
  Irreducible (X ^ 2 + 1 : Polynomial F)  := by
by_contra h
have h0 : (0 : ZMod 2) ^ 2 + (0 : ZMod 2) + 1 = 0
  exact ?sorry_0
have h1 : (1 : ZMod 2) ^ 2 + (1 : ZMod 2) + 1 = 0
  exact ?sorry_1
have h0_ne : (0 : ZMod 2) ^ 2 + (0 : ZMod 2) + 1 ≠ 0
  exact ?sorry_2
have h1_ne : (1 : ZMod 2) ^ 2 + (1 : ZMod 2) + 1 ≠ 0
  exact ?sorry_3
contradiction


theorem exercise_2_3_2 {G : Type*} [Group G] (a b : G) :
  ∃ g : G, b* a = g * a * b * g⁻¹  := by
let g := a⁻¹
have h1 : g * a * b * g⁻¹ = (a⁻¹) * a * b * (a⁻¹)⁻¹
  exact ?sorry_0
have h2 : (a⁻¹) * a = 1
  exact ?sorry_1
have h3 : 1 * b = b
  exact ?sorry_2
have h4 : b * 1 = b
  exact ?sorry_3
have h5 : b * (a⁻¹)⁻¹ = b * a
  exact ?sorry_4
exact ⟨g, exact ?sorry_5⟩


theorem exercise_10_4_6 {R : Type*} [CommRing R]
  [NoZeroDivisors R] (I J : Ideal R) (x : ↑(I ⊓ J)) :
  IsNilpotent ((Ideal.Quotient.mk (I*J)) x)  := by
have hxI : (x : R) ∈ I
  exact x.2.1
have hxJ : (x : R) ∈ J
  exact x.2.2
have hx2IJ : (x : R) * (x : R) ∈ I * J
  exact ?sorry_0
have hQuot : (Ideal.Quotient.mk (I * J)) ((x : R) * (x : R)) = 0
  exact ?sorry_1
use 2
rw [pow_two]
exact hQuot


theorem exercise_11_4_1b {F : Type*} [Field F] [Fintype F] (hF : card F = 2) :
  Irreducible (12 + 6 * X + X ^ 3 : Polynomial F)  := by
have h1 : (Polynomial.C 12 + Polynomial.C 6 * X + X ^ 3).coeff 0 = 12
  exact ?sorry_0
have h2 : (Polynomial.C 12 + Polynomial.C 6 * X + X ^ 3).coeff 1 = 6
  exact ?sorry_1
have h3 : (Polynomial.C 12 + Polynomial.C 6 * X + X ^ 3).coeff 2 = 0
  exact ?sorry_2
have h4 : (Polynomial.C 12 + Polynomial.C 6 * X + X ^ 3).coeff 3 = 1
  exact ?sorry_3
have h5 : 3 ∣ 12
  exact ?sorry_4
have h6 : 3 ∣ 6
  exact ?sorry_5
have h7 : 3 ∣ 0
  exact ?sorry_6
have h8 : ¬(3 ∣ 1)
  exact ?sorry_7
exact ?sorry_8


theorem exercise_2_11_3 {G : Type*} [Group G] [Fintype G]
  (hG : Even (card G)) : ∃ x : G, orderOf x = 2  := by
have h_paired : ∀ g : G, g ≠ g⁻¹ → ∃ h : G, h = g⁻¹
  exact ?sorry_0
have h_one_unpaired : ∀ g : G, g = 1 → g = g⁻¹
  exact ?sorry_1
have h_unpaired_exists : ∃ a : G, a ≠ 1 ∧ a = a⁻¹
  exact ?sorry_2
rcases h_unpaired_exists with ⟨a, ha_ne, ha_unpaired⟩
have ha_order_2 : a ^ 2 = 1
  exact ?sorry_3
use a
have ha_order : orderOf a = 2
  exact ?sorry_4
exact ha_order


theorem exercise_11_4_8 (p : ℕ) (hp : Prime p) (n : ℕ) :
  -- p ∈ ℕ can be written as p ∈ ℚ[X]
  Irreducible (X ^ n - (p : Polynomial ℚ) : Polynomial ℚ)  := by
let f := X ^ n - (p : Polynomial ℚ)
have h_eisenstein : ∀ (k : ℕ), k < n → (f.coeff k : ℚ) = 0 ∨ (p : ℚ) ∣ f.coeff k
  exact ?sorry_0
have h_leading : ¬ (p : ℚ) ∣ f.coeff n
  exact ?sorry_1
have h_constant : (p : ℚ) ∣ f.coeff 0 ∧ ¬ (p : ℚ)^2 ∣ f.coeff 0
  exact ?sorry_2
have h_irreducible : Irreducible f
  exact ?sorry_3
exact h_irreducible


theorem exercise_10_1_13 {R : Type*} [Ring R] {x : R}
  (hx : IsNilpotent x) : IsUnit (1 + x)  := by
cases hx with
| intro n hn =>
  let y := ∑ k in Finset.range n, (-1 : R)^k * x^k
  have hxy : (1 + x) * y = 1
    calc
  (1 + x) * y = (1 + x) * ∑ k in Finset.range n, (-1)^k * x^k := rfl
  _ = ∑ k in Finset.range n, (1 + x) * ((-1)^k * x^k) := by rw [Finset.mul_sum]
  _ = ∑ k in Finset.range n, ((-1)^k * x^k) + ∑ k in Finset.range n, x * ((-1)^k * x^k) := ?sorry_0
  _ = 1 + (-1)^(n-1) * x^n := ?sorry_1
  _ = 1 + (-1)^(n-1) * 0 := by rw [hn]
  _ = 1 + 0 := by rw [mul_zero]
  _ = 1 := by rw [add_zero]
  have hyx : y * (1 + x) = 1
    exact ?sorry_2
  have hUnit : IsUnit (1 + x)
    use Units.mk (1 + x) y hxy hyx
  exact hUnit


theorem exercise_6_1_14 (G : Type*) [Group G]
  (hG : IsCyclic $ G ⧸ (center G)) :
  center G = ⊤   := by
obtain ⟨x, hx⟩ : ∃ x : G, (G ⧸ center G) = Subgroup.closure {QuotientGroup.mk' (center G) x} := ?sorry_0
have h_forall_g : ∀ g : G, ∃ m : ℤ, ∃ z : center G, g = x ^ m * z
  intro g
  have h_coset : ∃ m : ℤ, QuotientGroup.mk' (center G) g = (QuotientGroup.mk' (center G) x) ^ m
    exact ?sorry_1
  obtain ⟨m, hm⟩ := h_coset
  have h_eq_coset : QuotientGroup.mk' (center G) g = QuotientGroup.mk' (center G) (x ^ m)
    exact ?sorry_2
  have h_g : ∃ z : center G, g = x ^ m * z
    exact ?sorry_3
  exact ⟨m, h_g⟩
have h_abelian : ∀ g h : G, g * h = h * g
  intros g h
  obtain ⟨a1, z1, hg⟩ : ∃ a1 : ℤ, ∃ z1 : center G, g = x ^ a1 * z1 := h_forall_g g
  obtain ⟨a2, z2, hh⟩ : ∃ a2 : ℤ, ∃ z2 : center G, h = x ^ a2 * z2 := h_forall_g h
  have h_gh : g * h = (x ^ a1 * z1) * (x ^ a2 * z2)
    exact ?sorry_4
  have h_hg : h * g = (x ^ a2 * z2) * (x ^ a1 * z1)
    exact ?sorry_5
  calc
  g * h = x ^ a1 * x ^ a2 * z1 * z2 := ?sorry_6
  _ = x ^ (a1 + a2) * z2 * z1 := ?sorry_7
  _ = x ^ a2 * x ^ a1 * z2 * z1 := ?sorry_8
  _ = x ^ a2 * z2 * x ^ a1 * z1 := ?sorry_9
  _ = h * g := ?sorry_10
have h_center : center G = ⊤
  exact ?sorry_11
exact h_center


theorem exercise_3_7_2 {K V : Type*} [Field K] [AddCommGroup V]
  [Module K V] {ι : Type*} [Fintype ι] (γ : ι → Submodule K V)
  (h : ∀ i : ι, γ i ≠ ⊤) :
  (⋂ (i : ι), (γ i : Set V)) ≠ ⊤  := by
by_contra h_union
let n := Fintype.card ι
have h_cover : ∀ v : V, ∃ i : ι, v ∈ γ i
  exact ?sorry_0
have h_basis : ∃ v : V, ∀ i : ι, v ∉ γ i
  exact ?sorry_1
have h_contradiction : False
  exact ?sorry_2
exact h_contradiction
