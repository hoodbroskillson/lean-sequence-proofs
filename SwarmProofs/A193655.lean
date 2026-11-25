import SwarmProofs.A193654

/-! The executable row sum of OEIS A193655 uses the upper integer half
of (n+1)(n+k+2). A193654 uses the lower integer half of the same product.
Combining the two recovers an affine row, allowing a direct comparison
with the existing A193654 theorem and a proof of Mathar's generating function.
https://oeis.org/A193655 -/

namespace A193655

/-- The product and the added half in Kimberling's Mathematica definition. -/
def tile (n k : Nat) : Int := (1 + ((n : Int)+1)*((n : Int)+k+2))/2

/-- Sum of tile(n,k) times the Q-weight at n-k, including both endpoints. -/
def term (n : Nat) : Int := A193654.weighted n (tile n)

/-- Complementary rounding recovers the original product in every cell. -/
private theorem tile_sum (n k : Nat) :
    tile n k + A193654.tile n k = ((n : Int)+1)*((n : Int)+k+2) := by
  unfold tile A193654.tile
  omega

private theorem row_sum (n t j : Nat) :
    A193654.weighted t (fun k => tile n (j+k)) +
      A193654.weighted t (fun k => A193654.tile n (j+k)) =
      ((n : Int)+1)*(((n : Int)+j+3)*2^t-1) := by
  induction t generalizing j with
  | zero => simp [A193654.weighted, tile_sum]; grind
  | succ t ih =>
    have head := tile_sum n j
    have tail := ih (j+1)
    simp only [A193654.weighted, Nat.add_zero, A193654.weight, Int.pow_succ]
    simp only [Int.natCast_succ] at tail
    have shift (f : Nat → Int) :
        (fun k => f (j+(k+1))) = (fun k => f (j+1+k)) := by
      funext k
      congr 1
      omega
    rw [shift (tile n), shift (A193654.tile n)]
    grind

/-- The exact discrepancy between upper and lower rounding in the two entries. -/
theorem correction (n : Nat) :
    3 * (term n - A193654.term n) = (1-A193654.parity n)*(2^n-1) := by
  have total := row_sum n n 0
  simp only [Nat.zero_add, Int.natCast_zero, Int.add_zero] at total
  change term n + A193654.term n = _ at total
  have floor := A193654.scaled n
  grind

/-- Closed form for six times the executable A193655 sequence. -/
theorem scaled (n : Nat) :
    6*term n = 3*((n : Int)+1)*(((n : Int)+3)*2^n-1)
      + (1-A193654.parity n)*(2^n-1) := by
  have h := correction n
  have h' := A193654.scaled n
  grind

private theorem parity_step (k : Nat) : A193654.parity (k+1) = 1 - A193654.parity k := by
  simp only [A193654.parity, Int.natCast_succ]
  omega

private theorem tail_relation (n : Nat) :
    term (n+7)-5*term (n+6)+3*term (n+5)+21*term (n+4)
      -36*term (n+3)+32*term (n+1)-16*term n = 0 := by
  have h0 := scaled n
  have h1 := scaled (n+1)
  have h3 := scaled (n+3)
  have h4 := scaled (n+4)
  have h5 := scaled (n+5)
  have h6 := scaled (n+6)
  have h7 := scaled (n+7)
  simp only [Int.natCast_succ, Int.pow_succ, parity_step] at h1 h3 h4 h5 h6 h7
  grind

/-- Coefficient in degree n after shifting the generating series by k. -/
def lag (k n : Nat) : Int := if k ≤ n then term (n-k) else 0

/-- Coefficients of the numerator when the denominator has constant term one. -/
def numerator : Nat → Int
  | 0 => 1
  | 1 => 2
  | 2 => -3
  | 3 => -9
  | 4 => 8
  | 5 => 4
  | _ => 0

/-- Mathar's generating function in every degree. The denominator is
(1+x)(1+2x)(1−x)²(1−2x)³. -/
theorem coefficient_identity (n : Nat) :
    term n - 5*lag 1 n + 3*lag 2 n + 21*lag 3 n - 36*lag 4 n
      + 32*lag 6 n - 16*lag 7 n = numerator n := by
  by_cases hn : n < 7
  · have h : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 ∨ n=6 := by omega
    rcases h with h|h|h|h|h|h|h <;> subst n <;> decide
  · obtain ⟨k, rfl⟩ : ∃ k, n = k+7 := ⟨n-7, by omega⟩
    simpa [lag, numerator] using tail_relation k

/-- The literal heading has floor((2n+k+3)/(2(n+k+2))) in each cell. -/
theorem heading_zero (n k : Nat) : (2*n+k+3)/(2*(n+k+2)) = 0 := by
  apply Nat.div_eq_of_lt
  grind

end A193655

/-- info: 'A193655.correction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms A193655.correction

/-- info: 'A193655.scaled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms A193655.scaled

/-- info: 'A193655.coefficient_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms A193655.coefficient_identity

/-- info: 'A193655.heading_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms A193655.heading_zero
