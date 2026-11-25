import Std

/-! A divisor test for splitting 3/q into two unit fractions. See David
Eppstein's account of the classical two-unit-fraction problem.
https://www.ics.uci.edu/~eppstein/numth/egypt/smallnum.html -/

namespace EgyptianDivisor

/-- For q congruent to 1 modulo 3, the positive two-unit-fraction equation
for 3/q has a solution exactly when q² has a divisor congruent to 2 modulo 3. -/
theorem three_over_iff (q : Nat) (hq : q % 3 = 1) :
    (∃ y z : Nat, 0 < y ∧ 0 < z ∧ 3*y*z = q*(y+z)) ↔
      ∃ d : Nat, d ∣ q*q ∧ d % 3 = 2 := by
  have hqpos : 0 < q := by omega
  constructor
  · rintro ⟨y, z, hy, hz, h⟩
    have hly : q*z < (3*y)*z := by
      rw [h, Nat.mul_add]
      have := Nat.mul_pos hqpos hy
      omega
    have hlz : q*y < (3*z)*y := by
      rw [show (3*z)*y = 3*y*z by grind, h, Nat.mul_add]
      have := Nat.mul_pos hqpos hz
      omega
    have ybound : q < 3*y := Nat.lt_of_mul_lt_mul_right hly
    have zbound : q < 3*z := Nat.lt_of_mul_lt_mul_right hlz
    let d := 3*y-q
    let e := 3*z-q
    have hd : d+q = 3*y := by dsimp [d]; omega
    have he : e+q = 3*z := by dsimp [e]; omega
    refine ⟨d, ⟨e, ?_⟩, by omega⟩
    grind
  · rintro ⟨d, ⟨e, hde⟩, hd⟩
    have hm := congrArg (· % 3) hde
    simp only [Nat.mul_mod q q 3, Nat.mul_mod d e 3, hq, hd] at hm
    have he : e % 3 = 2 := by omega
    let y := (q+d)/3
    let z := (q+e)/3
    have hy : 3*y = q+d := by dsimp [y]; omega
    have hz : 3*z = q+e := by dsimp [z]; omega
    refine ⟨y,z,by omega,by omega,?_⟩
    grind

end EgyptianDivisor

/-- info: 'EgyptianDivisor.three_over_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms EgyptianDivisor.three_over_iff
