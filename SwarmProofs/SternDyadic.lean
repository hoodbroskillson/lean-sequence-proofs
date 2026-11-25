import Std

/-! Stern's diatomic sequence (OEIS A002487), and its dyadic block formula.
Bruce Reznick, *Regularity Properties of the Stern Enumeration of the Rationals*,
Corollary 4 (2008): https://cs.uwaterloo.ca/journals/JIS/VOL11/Reznick/reznick4.pdf -/

namespace SternDyadic

/-- The binary recurrences of the diatomic sequence. -/
def stern (n : Nat) : Nat :=
  if _h : n < 2 then n
  else if n % 2 = 0 then stern (n/2)
  else stern (n/2) + stern (n/2+1)
termination_by n
decreasing_by all_goals omega

@[simp] theorem stern_zero : stern 0 = 0 := by rw [stern]; decide
@[simp] theorem stern_one : stern 1 = 1 := by rw [stern]; decide

theorem stern_even (n : Nat) : stern (2*n) = stern n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [stern, dite_eq_right (by omega), ite_eq_left (by omega)]
    congr 1
    omega

theorem stern_odd (n : Nat) : stern (2*n+1) = stern n + stern (n+1) := by
  cases n with
  | zero => simp
  | succ n =>
    rw [stern, dite_eq_right (by omega), ite_eq_right (by omega)]
    rw [show (2*(n+1)+1)/2 = n+1 by omega]

/-- Every entry of a dyadic block is a linear combination of the two endpoints. -/
theorem block (r n k : Nat) (hk : k ≤ 2^r) :
    stern (2^r*n+k) = stern (2^r-k)*stern n + stern k*stern (n+1) := by
  induction r generalizing k with
  | zero =>
    simp only [Nat.pow_zero, Nat.one_mul] at *
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl <;> simp
  | succ r ih =>
    let w := 2^r
    change k ≤ w*2 at hk
    change stern (w*2*n+k) = stern (w*2-k)*stern n + stern k*stern (n+1)
    let j := k/2
    have hj : j ≤ w := by dsimp [j]; omega
    have hwidth : w*2*n = 2*(w*n) := by grind
    by_cases he : k%2 = 0
    · have hk' : k = 2*j := by dsimp [j]; omega
      rw [hk', hwidth, show 2*(w*n)+2*j = 2*(w*n+j) by omega,
        show w*2-2*j = 2*(w-j) by omega, stern_even, stern_even, stern_even]
      exact ih j hj
    · have hk' : k = 2*j+1 := by dsimp [j]; omega
      have hj' : j+1 ≤ w := by omega
      rw [hk', hwidth, show 2*(w*n)+(2*j+1) = 2*(w*n+j)+1 by omega,
        show w*2-(2*j+1) = 2*(w-(j+1))+1 by omega, stern_odd, stern_odd, stern_odd]
      have left := ih j hj
      have right := ih (j+1) hj'
      change stern (w*n+j) = stern (w-j)*stern n + stern j*stern (n+1) at left
      change stern (w*n+(j+1)) = stern (w-(j+1))*stern n + stern (j+1)*stern (n+1) at right
      rw [left, Nat.add_assoc (w*n) j 1, right, show w-(j+1)+1 = w-j by omega]
      grind

end SternDyadic

/-- info: 'SternDyadic.block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SternDyadic.block
