import Mathlib

open Real
open scoped BigOperators
noncomputable section

theorem exercise_1_30 {n : ℕ} :
  ¬ ∃ a : ℤ, ∑ i : Fin n, (1 : ℚ) / (n+2) = a  := by
let s : ℕ := ?sorry_0
have h_largest_power : ∃ k ≤ n, 2^s = k
  exact ?sorry_1
let H_n := ∑ i in Finset.range n, (1 : ℚ) / (i + 1)
let sum_part := ∑ i in (Finset.range n).filter (fun i => i + 1 ≠ 2^s), (1 : ℚ) / (i + 1)
have h_Hn_decomposition : H_n = (1 / 2^s) + sum_part
  exact ?sorry_2
have h_sum_odd_denominators : sum_part = (1 / 2^(s-1)) * (∑ i in Finset.range n, exact ?sorry_3)
  exact ?sorry_4
have h_not_divisible : ¬ (∃ b : ℤ, sum_part * (2^s) = b)
  exact ?sorry_5
have h_contradiction : ∃ b : ℤ, sum_part * (2^s) = b
  exact ?sorry_6
contradiction


theorem exercise_1_27 {n : ℕ} (hn : Odd n) : 8 ∣ (n^2 - 1)  := by
have h1 : n^2 - 1 = (n + 1) * (n - 1)
  exact ?sorry_0
have h2 : Even (n + 1)
  exact ?sorry_1
have h3 : Even (n - 1)
  exact ?sorry_2
have h4 : 4 ∣ (n + 1) ∨ 4 ∣ (n - 1)
  exact ?sorry_3
have h5 : 8 ∣ (n + 1) * (n - 1)
  exact ?sorry_4
exact ?sorry_5


theorem exercise_5_13 {p x: ℤ} (hp : Prime p)
  (hpx : p ∣ (x^4 - x^2 + 1)) : p ≡ 1 [ZMOD 12]  := by
have h1 : p ∣ (x^6 + 1)
  exact ?sorry_0
have h2 : p ≡ 1 [ZMOD 4]
  have legendre_neg1 : True
    exact ?sorry_1
  exact ?sorry_2
have h3 : p ∣ ((2 * x - 1)^2 + 3)
  exact ?sorry_3
have h4 : p ≡ 1 [ZMOD 3]
  have legendre_neg3 : True
    exact ?sorry_4
  have legendre_p3 : True
    exact ?sorry_5
  exact ?sorry_6
have h5 : p ≡ 1 [ZMOD 12]
  have h4_div : 4 ∣ (p - 1)
    exact ?sorry_7
  have h3_div : 3 ∣ (p - 1)
    exact ?sorry_8
  exact ?sorry_9
exact h5


theorem exercise_5_37 {p q : ℕ} [Fact (p.Prime)] [Fact (q.Prime)] {a : ℤ}
  (ha : a < 0) (h0 : p ≡ q [ZMOD 4*a]) (h1 : ¬ ((p : ℤ) ∣ a)) :
  legendreSym p a = legendreSym q a  := by
let A := -a
have hA : A > 0
  exact ?sorry_0
have hLegendreA : legendreSym p A = legendreSym q A
  exact ?sorry_1
have hLegendreP : legendreSym p a = (-1) ^ ((p - 1) / 2) * legendreSym p A
  exact ?sorry_2
have hLegendreQ : legendreSym q a = (-1) ^ ((q - 1) / 2) * legendreSym q A
  exact ?sorry_3
have hParity : (-1) ^ ((p - 1) / 2) = (-1) ^ ((q - 1) / 2)
  exact ?sorry_4
calc
  legendreSym p a = (-1) ^ ((p - 1) / 2) * legendreSym p A := hLegendreP
  _ = (-1) ^ ((q - 1) / 2) * legendreSym q A := by rw [hParity, hLegendreA]
  _ = legendreSym q a := hLegendreQ.symm
