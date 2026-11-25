import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Tactic

/-! R. J. Mathar's recurrence for the repeated Catalan numbers in OEIS A208355.
The separate triangle below follows the literal header of the linked A208101.
Its diagonal and the published numerical table disagree at index five.
https://oeis.org/A208355 · https://oeis.org/A208101 -/

namespace A208355

/-- The published Catalan characterization with the original zero-based indexing. -/
def term (n : Nat) : Nat := catalan ((n+1)/2)

private theorem catalan_step (k : Nat) :
    (k+2) * catalan (k+1) = 2*(2*k+1)*catalan k := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_succ k)
  have h := Nat.succ_mul_centralBinom_succ k
  rw [← succ_mul_catalan_eq_centralBinom (k+1), ← succ_mul_catalan_eq_centralBinom k] at h
  grind

/-- Mathar's proposed recurrence for every index with both preceding terms defined. -/
theorem recurrence (n : Nat) (hn : 2 ≤ n) :
    (n+3)*(n-2)*term n + 4*term (n-1) = 4*(n-1)^2*term (n-2) := by
  let k := (n-2)/2
  have h := catalan_step k
  unfold term
  by_cases he : n % 2 = 0
  · have hn' : n = 2*k+2 := by dsimp [k]; omega
    rw [show (n+1)/2 = k+1 by omega, show (n-1+1)/2 = k+1 by omega,
      show (n-2+1)/2 = k by omega,
      show n-1 = 2*k+1 by omega, show n-2 = 2*k by omega, hn']
    grind
  · have hn' : n = 2*k+3 := by dsimp [k]; omega
    have h' := catalan_step (k+1)
    rw [show (n+1)/2 = k+2 by omega, show (n-1+1)/2 = k+1 by omega,
      show (n-2+1)/2 = k+1 by omega,
      show n-1 = 2*k+2 by omega, show n-2 = 2*k+1 by omega, hn']
    grind

/-- The literal A208101 header on its triangular domain; entries outside are zero. -/
def headerTriangle (n k : Nat) : Nat :=
  if n < k then 0
  else if k = 0 then 1
  else if k = 1 then n
  else if k = n then headerTriangle (n-1) (n-2)
  else headerTriangle (n-2) (k-1) + headerTriangle (n-1) k
termination_by n
decreasing_by all_goals omega

/-- At index five the title-rule diagonal violates the proposed equality. -/
theorem header_counterexample :
    let d := fun i => headerTriangle i i
    d 3 = 2 ∧ d 4 = 2 ∧ d 5 = 3 ∧
      (5+3)*(5-2)*d 5 + 4*d 4 ≠ 4*(5-1)^2*d 3 := by
  dsimp only
  simp [headerTriangle]

end A208355

/-- info: 'A208355.recurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms A208355.recurrence

/-- info: 'A208355.header_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms A208355.header_counterexample
