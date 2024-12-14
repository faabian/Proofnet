import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem exercise_6_16 {K V : Type*} [RCLike K] [NormedAddCommGroup V] [InnerProductSpace K V]
  {U : Submodule K V} :
  U.orthogonal = ⊥  ↔ U = ⊤  := by
have h_forward : U.orthogonal = ⊥ → U = ⊤
  intro hUperp
  have h_decomp : V = U ⊔ U.orthogonal
    exact ?sorry_0
  rw [hUperp] at h_decomp
  have hUtop : U = ⊤
    exact ?sorry_1
  exact hUtop
have h_backward : U = ⊤ → U.orthogonal = ⊥
  intro hUtop
  have hUperp : U.orthogonal = ⊥
    exact ?sorry_2
  exact hUperp
exact ⟨h_forward, h_backward⟩


theorem exercise_7_10 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V] (T : End ℂ V)
  (hT : T * adjoint T = adjoint T * T) (hT1 : T^9 = T^8) :
  IsSelfAdjoint T ∧ T^2 = T  := by
have h_basis : ∃ (b : Basis (Fin (FiniteDimensional.finrank ℂ V)) ℂ V),
  Orthonormal ℂ b ∧ ∀ i, ∃ μ : ℂ, T (b i) = μ • (b i) := ?sorry_0
rcases h_basis with ⟨b, h_orthonormal, h_eigen⟩
have h_eigenvalues : ∀ i, ∃ μ : ℂ, T (b i) = μ • (b i) ∧ (μ^9 = μ^8)
  exact ?sorry_1
have h_real_eigenvalues : ∀ i, ∃ μ : ℝ, T (b i) = (μ : ℂ) • (b i)
  exact ?sorry_2
have h_self_adjoint : IsSelfAdjoint T
  exact ?sorry_3
have h_T2_eq_T : ∀ i, (T ∘ T) (b i) = T (b i)
  exact ?sorry_4
have h_T2_eq_T_whole : T^2 = T
  exact ?sorry_5
exact ⟨h_self_adjoint, h_T2_eq_T_whole⟩


theorem exercise_1_3 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] {v : V} : -(-v) = v  := by
apply neg_neg


theorem exercise_1_6 : ∃ U : Set (ℝ × ℝ),
  (U ≠ ∅) ∧
  (∀ (u v : ℝ × ℝ), u ∈ U ∧ v ∈ U → u + v ∈ U) ∧
  (∀ (u : ℝ × ℝ), u ∈ U → -u ∈ U) ∧
  (∀ U' : Submodule ℝ (ℝ × ℝ), U ≠ ↑U')  := by
let U := {p : ℝ × ℝ | ∃ (x y : ℤ), p = (↑x, ↑y)}
have h_nonempty : U ≠ ∅
  exact ?sorry_0
have h_add_closed : ∀ (u v : ℝ × ℝ), u ∈ U ∧ v ∈ U → u + v ∈ U
  exact ?sorry_1
have h_inv_closed : ∀ (u : ℝ × ℝ), u ∈ U → -u ∈ U
  exact ?sorry_2
have h_not_subspace : ∀ U' : Submodule ℝ (ℝ × ℝ), U ≠ ↑U'
  exact ?sorry_3
exact ⟨U, h_nonempty, h_add_closed, h_inv_closed, h_not_subspace⟩


theorem exercise_5_12 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] {S : End F V}
  (hS : ∀ v : V, ∃ c : F, v ∈ eigenspace S c) :
  ∃ c : F, S = c • LinearMap.id  := by
have h_scalar : ∀ v : V, ∃ a_v : F, S v = a_v • v
  exact ?sorry_0
have h_unique : ∀ v : V, v ≠ 0 → ∃! a_v : F, S v = a_v • v
  exact ?sorry_1
have h_independent : ∀ v w : V, v ≠ 0 → w ≠ 0 → (∃ b : F, w = b • v) → ∀ a_v a_w : F, S v = a_v • v → S w = a_w • w → a_v = a_w
  exact ?sorry_2
have h_dependent : ∀ v w : V, (∃ b : F, w = b • v) → ∀ a_v a_w : F, S v = a_v • v → S w = a_w • w → a_v = a_w
  exact ?sorry_3
have h_independent_case : ∀ v w : V, v ≠ 0 → w ≠ 0 → ¬(∃ b : F, w = b • v) → ∀ a_v a_w : F, S v = a_v • v → S w = a_w • w → a_v = a_w
  exact ?sorry_4
have h_single_scalar : ∃ c : F, ∀ v : V, S v = c • v
  exact ?sorry_5
rcases h_single_scalar with ⟨c, hc⟩
use c
ext v
rw [hc v]
exact ?sorry_6


theorem exercise_7_5 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V] (hV : finrank V ≥ 2) :
  ∀ U : Submodule ℂ (End ℂ V), U.carrier ≠
  {T | T * adjoint T = adjoint T * T}  := by
have basis_exists : ∃ (e : Fin 2 → V), Orthonormal ℂ e
  exact ?sorry_0
obtain ⟨e, h_orthonormal⟩ := basis_exists
let S : End ℂ V := ?sorry_1
let T : End ℂ V := ?sorry_2
have S_normal : S * adjoint S = adjoint S * S
  exact ?sorry_3
have T_normal : T * adjoint T = adjoint T * T
  exact ?sorry_4
let ST := S + T
have ST_not_normal : ST * adjoint ST ≠ adjoint ST * ST
  exact ?sorry_5
have not_subspace : ¬ (∀ x y : End ℂ V, x ∈ {T | T * adjoint T = adjoint T * T} →
  y ∈ {T | T * adjoint T = adjoint T * T} → x + y ∈ {T | T * adjoint T = adjoint T * T}) := ?sorry_6
intro U
by_contra h
have S_in_U : S ∈ U.carrier
  rw [h]
  exact S_normal
have T_in_U : T ∈ U.carrier
  rw [h]
  exact T_normal
have ST_in_U : ST ∈ U.carrier
  rw [h]
  exact ?sorry_7
exact ST_not_normal (by rw [h] at ST_in_U; exact ST_in_U)


theorem exercise_3_8 {F V W : Type*}  [AddCommGroup V]
  [AddCommGroup W] [Field F] [Module F V] [Module F W]
  (L : V →ₗ[F] W) :
  ∃ U : Submodule F V, U ⊓ (ker L) = ⊥ ∧
  (range L = range (domRestrict L U)) := by
have exists_complement : ∃ U : Submodule F V, V = U ⊔ (ker L) ∧ U ⊓ (ker L) = ⊥
  exact ?sorry_0
obtain ⟨U, hU⟩ := exists_complement
have V_decomp : V = U ⊔ (ker L)
  exact hU.1
have U_inter_ker : U ⊓ (ker L) = ⊥
  exact hU.2
have range_eq : range L = range (domRestrict L U)
  exact ?sorry_1
exact ⟨U, U_inter_ker, range_eq⟩


theorem exercise_5_20 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] [FiniteDimensional F V] {S T : End F V}
  (h1 : card (T.Eigenvalues) = finrank F V)
  (h2 : ∀ v : V, ∃ c : F, v ∈ eigenspace S c ↔ ∃ c : F, v ∈ eigenspace T c) :
  S * T = T * S  := by
let n := finrank F V
have basis_eigenvectors : ∃ (v : Fin n → V), LinearIndependent F v ∧
  Submodule.span F (Set.range v) = ⊤ ∧
  ∀ j, ∃ mu : F, T (v j) = mu • (v j) := ?sorry_0
rcases basis_eigenvectors with ⟨v, hv_li, hv_span, hv_eigen⟩
have eigenvalues_T : ∀ j, ∃ mu : F, T (v j) = mu • (v j)
  exact ?sorry_1
have eigenvalues_S : ∀ j, ∃ a : F, S (v j) = a • (v j)
  exact ?sorry_2
have commutes_on_basis : ∀ j, (S * T) (v j) = (T * S) (v j)
  intro j
  obtain ⟨mu, hT⟩ := eigenvalues_T j
  obtain ⟨a, hS⟩ := eigenvalues_S j
  calc
  (S * T) (v j) = S (T (v j)) := ?sorry_3
  _ = S (mu • (v j)) := by rw [hT]
  _ = mu • (S (v j)) := ?sorry_4
  _ = mu • (a • (v j)) := by rw [hS]
  _ = a • (mu • (v j)) := ?sorry_5
  _ = a • (T (v j)) := by rw [hT]
  _ = T (a • (v j)) := ?sorry_6
  _ = T (S (v j)) := by rw [hS]
  _ = (T * S) (v j) := ?sorry_7
have commutes_on_whole_space : S * T = T * S
  exact ?sorry_8
exact commutes_on_whole_space


theorem exercise_5_13 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] [FiniteDimensional F V] {T : End F V}
  (hS : ∀ U : Submodule F V, finrank F U = finrank F V - 1 →
  Submodule.map T U = U) : ∃ c : F, T = c • LinearMap.id  := by
by_contra h
obtain ⟨u, hu⟩ : ∃ u : V, ¬∃ c : F, T u = c • u := ?sorry_0
have lin_indep : LinearIndependent F ![u, T u]
  exact ?sorry_1
have basis_extension : ∃ (v : Fin (finrank F V - 2) → V),
  LinearIndependent F (Fin.cons u (Fin.cons (T u) v)) ∧
  Submodule.span F (Set.range (Fin.cons u (Fin.cons (T u) v))) = ⊤ := ?sorry_2
obtain ⟨v, hv_indep, hv_span⟩ := basis_extension
let U := Submodule.span F (Set.range (Fin.cons u v))
have hU_dim : finrank F U = finrank F V - 1
  exact ?sorry_3
have hU_not_invariant : Submodule.map T U ≠ U
  exact ?sorry_4
exact hU_not_invariant (hS U hU_dim)


theorem exercise_3_1 {F V : Type*}
  [AddCommGroup V] [Field F] [Module F V] [FiniteDimensional F V]
  (T : V →ₗ[F] V) (hT : finrank F V = 1) :
  ∃ c : F, ∀ v : V, T v = c • v := by
have basis : Basis (Fin 1) F V
  exact ?sorry_0
let e := basis.equivFun.symm (fun _ => 1)
have he : ∀ v : V, ∃ a : F, v = a • e
  exact ?sorry_1
let c := (basis.equivFun (T e)) 0
have hc : T e = c • e
  exact ?sorry_2
use c
intro v
rcases he v with ⟨a, ha⟩
calc
  T v = T (a • e) := by rw [ha]
  _ = a • T e := by rw [LinearMap.map_smul]
  _ = a • (c • e) := by rw [hc]
  _ = (a * c) • e := by rw [smul_smul]
  _ = c • (a • e) := by rw [mul_comm, smul_smul]
  _ = c • v := by rw [ha]


theorem exercise_6_3 {n : ℕ} (a b : Fin n → ℝ) :
  (∑ i, a i * b i) ^ 2 ≤ (∑ i : Fin n, i * a i ^ 2) * (∑ i, b i ^ 2 / i)  := by
have h1 : (∑ i, a i * b i) = ∑ i, (a i * b i * (Real.sqrt (↑(↑i)) / Real.sqrt (↑(↑i))))
  exact ?sorry_0
have h2 : (∑ i, a i * b i * (Real.sqrt (↑(↑i)) / Real.sqrt (↑(↑i)))) =
  ∑ i, (Real.sqrt (↑(↑i)) * a i) * (b i / Real.sqrt (↑(↑i))) := ?sorry_1
have h3 : (∑ i, (Real.sqrt (↑(↑i)) * a i) * (b i / Real.sqrt (↑(↑i)))) ^ 2 ≤
  (∑ i, (Real.sqrt (↑(↑i)) * a i) ^ 2) * (∑ i, (b i / Real.sqrt (↑(↑i))) ^ 2) := ?sorry_2
have h4 : (∑ i, (Real.sqrt (↑(↑i)) * a i) ^ 2) = ∑ i, ↑(↑i) * a i ^ 2
  exact ?sorry_3
have h5 : (∑ i, (b i / Real.sqrt (↑(↑i))) ^ 2) = ∑ i, b i ^ 2 / ↑(↑i)
  exact ?sorry_4
calc
  (∑ i, a i * b i) ^ 2
    = (∑ i, (Real.sqrt (↑(↑i)) * a i) * (b i / Real.sqrt (↑(↑i)))) ^ 2 := ?sorry_5
  _ ≤ (∑ i, (Real.sqrt (↑(↑i)) * a i) ^ 2) * (∑ i, (b i / Real.sqrt (↑(↑i))) ^ 2) := by apply h3
  _ = (∑ i, ↑(↑i) * a i ^ 2) * (∑ i, b i ^ 2 / ↑(↑i)) := by rw [h4, h5]


theorem exercise_5_24 {V : Type*} [AddCommGroup V]
  [Module ℝ V] [FiniteDimensional ℝ V] {T : End ℝ V}
  (hT : ∀ c : ℝ, eigenspace T c = ⊥) {U : Submodule ℝ V}
  (hU : Submodule.map T U = U) : Even (finrank U)  := by
have hTU : ∀ u ∈ U, T u ∈ U
  exact ?sorry_0
apply by_contradiction
intro hOdd
have hEigen : ∃ (c : ℝ) (u : U), u ≠ 0 ∧ T u = c • u
  exact ?sorry_1
obtain ⟨c, u, hu, hTu⟩ := hEigen
have hContradiction : T u = c • u → eigenspace T c ≠ ⊥
  exact ?sorry_2
have hNoEigen : eigenspace T c = ⊥
  exact hT c
have hContradict : eigenspace T c ≠ ⊥
  exact hContradiction hTu
exact hContradict hNoEigen
