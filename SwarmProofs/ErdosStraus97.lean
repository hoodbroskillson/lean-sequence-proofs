import Std

/-! This progression is contained in the known type I family of Elsholtz and Tao,
Proposition 1.9, with parameters a = 1, c = 5, f = 3.
https://doi.org/10.1017/S1446788712000468 -/

namespace ErdosStraus97

/-- An explicit family of distinct positive denominators for the class 97 mod 120.
    The displayed identity is the unit-fraction equation after clearing denominators. -/
theorem covered (k : Nat) :
    let n := 120 * k + 97
    ∃ x y z : Nat, 0 < x ∧ x < y ∧ y < z ∧
      4 * x * y * z = n * (x * y + x * z + y * z) := by
  let n := 120 * k + 97
  let x := 30 * k + 25
  let r := n * (6 * k + 5)
  let y := 5 * (240 * k ^ 2 + 394 * k + 162)
  refine ⟨x, y, r * y, ?_, ?_, ?_, ?_⟩
  · dsimp [x]
    omega
  · dsimp [x, y]
    omega
  · have hr : 1 < r := by
      dsimp [r, n]
      grind
    have hy : 0 < y := by
      dsimp [y]
      omega
    simpa using Nat.mul_lt_mul_of_pos_right hr hy
  · dsimp [r, n, x, y]
    grind

end ErdosStraus97

/-- info: 'ErdosStraus97.covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErdosStraus97.covered
