import SwarmProofs.A208355

/-! The executable triangle in OEIS A208101 and its A208355 diagonal.
The Mathematica and Haskell programs in A208101 update columns two apart.
The entry's heading uses a different recursion.
https://oeis.org/A208101 · https://oeis.org/A208355 -/

namespace A208101

/-- The tabulation rule, extended by zero beyond the end of each row.
At the right boundary the first summand comes from column two places back
and the second summand is the zero just beyond the preceding row. -/
def entry : Nat → Nat → Nat
  | 0, k => if k = 0 then 1 else 0
  | _+1, 0 => 1
  | n+1, 1 => n+1
  | n+1, k+2 =>
      if k+2 ≤ n+1 then entry n k + entry n (k+2) else 0

/-- Difference of adjacent binomial coefficients, with the leftmost
coefficient equal to one. Integer subtraction also covers the ghost column. -/
private def ballot (n : Nat) : Nat → Int
  | 0 => 1
  | j+1 => (n.choose (j+1) : Int) - n.choose j

private theorem ballot_step (n j : Nat) :
    ballot (n+1) (j+1) = ballot n j + ballot n (j+1) := by
  cases j with
  | zero => simp [ballot, Nat.choose_succ_succ] <;> omega
  | succ j =>
    simp only [ballot, Nat.choose_succ_succ, Int.natCast_add, Nat.succ_eq_add_one]
    ring

private def cell (n k : Nat) : Int :=
  if k % 2 = 0 then ballot n (k/2) else ballot (n+1) (k/2+1)

private theorem cell_step (n k : Nat) :
    cell (n+1) (k+2) = cell n k + cell n (k+2) := by
  unfold cell
  rw [show (k+2)%2 = k%2 by omega, show (k+2)/2 = k/2+1 by omega]
  split <;> simp_all only [ballot_step]

private theorem ballot_edge (j : Nat) : ballot (2*j+1) (j+1) = 0 := by
  simp [ballot, Nat.choose_symm_half]

private theorem cell_ghost (n : Nat) : cell n (n+1) = 0 := by
  unfold cell
  split
  · rename_i he
    let j := n/2
    have h : n = 2*j+1 := by dsimp [j]; omega
    change ballot n ((n+1)/2) = 0
    rw [show (n+1)/2 = j+1 by dsimp [j]; omega, h]
    exact ballot_edge j
  · rename_i ho
    let j := n/2
    have h : n+1 = 2*j+1 := by dsimp [j]; omega
    rw [show (n+1)/2 = j by dsimp [j]; omega, h]
    exact ballot_edge j

private theorem row_formula (n k : Nat) (hk : k ≤ n+1) :
    (entry n k : Int) = cell n k := by
  induction n generalizing k with
  | zero =>
    have h : k = 0 ∨ k = 1 := by omega
    rcases h with h | h <;> subst k <;> decide
  | succ n ih =>
    cases k with
    | zero => simp [entry, cell, ballot]
    | succ k =>
      cases k with
      | zero =>
        simp [entry, cell, ballot]
      | succ k =>
        by_cases hb : k+2 ≤ n+1
        · rw [entry, ite_eq_left hb, Int.natCast_add,
            ih k (by omega), ih (k+2) hb, cell_step]
        · rw [entry, ite_eq_right hb, show k+2 = n+1+1 by omega, cell_ghost]
          rfl

private theorem ballot_middle (j : Nat) : ballot (2*j) j = (catalan j : Int) := by
  cases j with
  | zero => simp [ballot]
  | succ j =>
    have hc := succ_mul_catalan_eq_centralBinom (j+1)
    change (j+2) * catalan (j+1) = (2*(j+1)).choose (j+1) at hc
    have hr := Nat.choose_succ_right_eq (2*(j+1)) j
    rw [show 2*(j+1)-j = j+2 by omega] at hr
    have hprev : (2*(j+1)).choose j = (j+1)*catalan (j+1) := by
      apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < j+2)
      grind
    simp only [ballot, hprev, ← hc, Int.natCast_mul, Int.natCast_add,
      Int.cast_ofNat_Int]
    grind

/-- Every executable diagonal entry is the repeated Catalan number from A208355. -/
theorem diagonal (n : Nat) : entry n n = A208355.term n := by
  have h := row_formula n n (by omega)
  unfold cell at h
  unfold A208355.term
  split at h
  · rename_i he
    let j := n/2
    have hn : n = 2*j := by dsimp [j]; omega
    change (entry n n : Int) = ballot n j at h
    rw [show ballot n j = ballot (2*j) j from congrArg (fun m => ballot m j) hn,
      ballot_middle] at h
    rw [show (n+1)/2 = j by dsimp [j]; omega]
    exact Int.ofNat_inj.mp h
  · rename_i ho
    let j := n/2+1
    have hn : n+1 = 2*j := by dsimp [j]; omega
    change (entry n n : Int) = ballot (n+1) j at h
    rw [hn, ballot_middle] at h
    rw [show (n+1)/2 = j by dsimp [j]; omega]
    exact Int.ofNat_inj.mp h

/-- Mathar's recurrence for the diagonal computed directly by the row update. -/
theorem recurrence (n : Nat) (hn : 2 ≤ n) :
    (n+3)*(n-2)*entry n n + 4*entry (n-1) (n-1) =
      4*(n-1)^2*entry (n-2) (n-2) := by
  simpa only [diagonal] using A208355.recurrence n hn

end A208101

/-- info: 'A208101.diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms A208101.diagonal

/-- info: 'A208101.recurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms A208101.recurrence
