import SwarmProofs.A024219
import SwarmProofs.A024220
import SwarmProofs.DigitWord
import Mathlib
import SwarmProofs.A286282
import SwarmProofs.ErdosStraus97
import SwarmProofs.EgyptianDivisor
import SwarmProofs.ErdosMoser
import SwarmProofs.ErdosMoserThree

/- The A027171 diagonal of the A027170 binomial triangle, in integer arithmetic.
   Source: https://oeis.org/A027171 and https://oeis.org/A027170 -/
namespace Rec027171

def b (r k : ℕ) : ℤ := (r.choose k : ℤ)
def c (n : ℕ) : ℤ := b (2*n) n
def a (n : ℕ) : ℤ := b (2*n+2) (n+1) + b (2*n+1) n + b (2*n+1) (n+1) + b (2*n) n - 4

lemma closed (n : ℕ) : a n = 2*c (n+1) + c n - 4 := by
  have h : b (2*n+1) n + b (2*n+1) (n+1) = b (2*n+2) (n+1) := by
    unfold b
    exact_mod_cast (Nat.choose_succ_succ (2*n+1) n).symm
  unfold a c
  rw [show 2*(n+1) = 2*n+2 by omega]
  linarith

lemma step (k : ℕ) : ((k:ℤ)+1) * c (k+1) = 2*(2*(k:ℤ)+1)*c k := by
  change ((k:ℤ)+1) * (Nat.centralBinom (k+1) : ℤ) = 2*(2*(k:ℤ)+1)*(Nat.centralBinom k : ℤ)
  exact_mod_cast Nat.succ_mul_centralBinom_succ k

/-- Mathar's recurrence at n = k + 2, covering every n ≥ 2. -/
theorem recurrence (k : ℕ) : 2*((k:ℤ)+3)*a (k+2) + (-7*(k:ℤ)-19)*a (k+1) + (-4*(k:ℤ)-2)*a k + (-36*(k:ℤ)-60) = 0 := by
  have h0 := step k
  have h1 := step (k+1)
  have h2 := step (k+2)
  push_cast at h1 h2
  simp only [closed]
  linear_combination 4*h2 + 4*h1 + h0

theorem mathar (n : ℕ) (hn : 2 ≤ n) :
    2*((n:ℤ)+1)*a n + (-7*(n:ℤ)-5)*a (n-1) +
    2*(-2*(n:ℤ)+3)*a (n-2) + 12*(-3*(n:ℤ)+1) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k+2 := ⟨n-2, by omega⟩
  rw [show k+2-1 = k+1 by omega, show k+2-2 = k by omega]
  push_cast
  linear_combination recurrence k

/-- Homogeneous recurrence obtained by two forward differences. -/
theorem homogeneous (k : ℕ) :
    (2*(k:ℤ)+10)*a (k+4) + (-11*(k:ℤ)-49)*a (k+3) +
    (12*(k:ℤ)+48)*a (k+2) + ((k:ℤ)-7)*a (k+1) + (-4*(k:ℤ)-2)*a k = 0 := by
  have h0 := recurrence k
  have h1 := recurrence (k+1)
  have h2 := recurrence (k+2)
  push_cast at h1 h2
  linear_combination h2 - 2*h1 + h0

end Rec027171
#print axioms Rec027171.mathar
#print axioms Rec027171.homogeneous

/- Strictly increasing positive Egyptian denominators in Erdős problem 242. -/
namespace Egypt242
def HasTriple (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4 / n : ℚ) = 1 / x + 1 / y + 1 / z

lemma even (k : ℕ) : HasTriple (2*(k+2)) := by
  refine ⟨k+2, k+3, (k+2)*(k+3), ?_, ?_, ?_, ?_⟩
  · omega
  · ring_nf; omega
  · ring_nf; omega
  · push_cast
    field_simp (disch := positivity); ring

lemma three_four (k : ℕ) : HasTriple (4*k+3) := by
  refine ⟨k+1, (4*k+3)*(k+1)+1, ((4*k+3)*(k+1))*((4*k+3)*(k+1)+1), ?_, ?_, ?_, ?_⟩
  · omega
  · ring_nf; omega
  · ring_nf; omega
  · push_cast
    field_simp (disch := positivity); ring

lemma five_eight (k : ℕ) : HasTriple (8*k+5) := by
  refine ⟨2*(k+1), (8*k+5)*(k+1), 2*((8*k+5)*(k+1)), ?_, ?_, ?_, ?_⟩
  · omega
  · ring_nf; omega
  · ring_nf; omega
  · push_cast
    field_simp (disch := positivity); ring

lemma multiple_three (k : ℕ) : HasTriple (3*(k+1)) := by
  refine ⟨k+1, 3*(k+1)+1, (3*(k+1))*(3*(k+1)+1), ?_, ?_, ?_, ?_⟩
  · omega
  · ring_nf; omega
  · ring_nf; omega
  · push_cast
    field_simp (disch := positivity); ring

lemma two_three (k : ℕ) : HasTriple (3*k+5) := by
  refine ⟨k+2, 3*k+5, (k+2)*(3*k+5), ?_, ?_, ?_, ?_⟩
  · omega
  · ring_nf; omega
  · ring_nf; omega
  · push_cast
    field_simp (disch := positivity); ring

/-- Every residue class modulo 24 except 1, for n > 2. -/
theorem covered (n : ℕ) (hn : 2 < n) (hr : n % 24 ≠ 1) : HasTriple n := by
  by_cases he : n % 2 = 0
  · convert even (n/2-2) using 1; omega
  by_cases h4 : n % 4 = 3
  · convert three_four (n/4) using 1; omega
  by_cases h8 : n % 8 = 5
  · convert five_eight (n/8) using 1; omega
  by_cases h3 : n % 3 = 0
  · convert multiple_three (n/3-1) using 1; omega
  convert two_three (n/3-1) using 1; omega
end Egypt242
#print axioms Egypt242.covered
