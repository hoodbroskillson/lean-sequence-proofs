import Std

/-! Two recurrences that R. J. Mathar proposed for OEIS A286282.
Graham's published characterization identifies the first-order recurrence
below with the first arrival times of Knowlton's elevator, version 2.
The Lean proof starts at that recurrence. https://oeis.org/A286282 -/

namespace A286282

/-- `term k` is the published value at floor `k+1`. -/
def term : Nat → Int
  | 0 => 1
  | k + 1 =>
    let n := (k : Int) + 1
    n * term k + n^2 - 3*n + 3

/-- Mathar's fourth-order recurrence, with the target floor `k+5`. -/
theorem orderFour (k : Nat) :
    let n := (k : Int) + 5
    term (k+4) + (-n-2)*term (k+3) + 3*(n-1)*term (k+2)
      + (-3*n+8)*term (k+1) + (n-4)*term k = 0 := by
  simp only [term, Int.natCast_succ]
  grind

/-- Mathar's third-order recurrence, with the target floor `k+4`. -/
theorem orderThree (k : Nat) :
    let n := (k : Int) + 4
    (n+1)*term (k+3) + (-n^2+3*n-27)*term (k+2)
      + 3*(-n^2+10*n-13)*term (k+1) + (n-3)*(4*n-17)*term k = 0 := by
  simp only [term, Int.natCast_succ]
  grind

end A286282

/-- info: 'A286282.orderFour' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms A286282.orderFour

/-- info: 'A286282.orderThree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms A286282.orderThree
