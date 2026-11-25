import Std

/-! The fixed-first-denominator factor-pair criterion for Erdős–Straus.
See Theorem 3.1 of *Erdős–Straus Decompositions*:
https://www.researchgate.net/publication/405220221_Erdos--Straus_Decompositions
The identity applies even when the residual numerator and denominator share a factor. -/

namespace ErdosStrausFixedFirst

/-- Complete the product for a two-unit-fraction split with numerator k and denominator q. -/
theorem twoUnit_iff (k q : Nat) (hk : 0 < k) (hq : 0 < q) :
    (∃ y z : Nat, 0 < y ∧ 0 < z ∧ k*y*z = q*(y+z)) ↔
      ∃ d e : Nat, d*e = q*q ∧ k ∣ q+d ∧ k ∣ q+e := by
  constructor
  · rintro ⟨y, z, hy, hz, h⟩
    have hy' : q < k*y := by
      apply Nat.lt_of_mul_lt_mul_right (a := z)
      rw [h, Nat.mul_add]
      have := Nat.mul_pos hq hy
      omega
    have hz' : q < k*z := by
      apply Nat.lt_of_mul_lt_mul_right (a := y)
      rw [show k*z*y = k*y*z by grind, h, Nat.mul_add]
      have := Nat.mul_pos hq hz
      omega
    let d := k*y-q
    let e := k*z-q
    have hd : q+d = k*y := by dsimp [d]; omega
    have he : q+e = k*z := by dsimp [e]; omega
    refine ⟨d, e, ?_, ⟨y, hd⟩, ⟨z, he⟩⟩
    grind
  · rintro ⟨d, e, hde, ⟨y, hy⟩, ⟨z, hz⟩⟩
    have hy' : 0 < y := by cases y <;> simp_all
    have hz' : 0 < z := by cases z <;> simp_all
    refine ⟨y, z, hy', hz', ?_⟩
    apply Nat.eq_of_mul_eq_mul_left hk
    grind

/-- For a specified x, factor pairs of (nx)² recognize all completions of 4/n. -/
theorem fixedFirst_iff (n x : Nat) (hn : 0 < n) (hx : n < 4*x) :
    (∃ y z : Nat, 0 < y ∧ 0 < z ∧ 4*x*y*z = n*(x*y+x*z+y*z)) ↔
      ∃ d e : Nat, d*e = (n*x)*(n*x) ∧ (4*x-n) ∣ n*x+d ∧ (4*x-n) ∣ n*x+e := by
  have hx' : 0 < x := by omega
  have hk : 0 < 4*x-n := by omega
  have hk' : (4*x-n)+n = 4*x := by omega
  rw [← twoUnit_iff (4*x-n) (n*x) hk (Nat.mul_pos hn hx')]
  apply exists_congr
  intro y
  apply exists_congr
  intro z
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  have split : 4*x*y*z = (4*x-n)*y*z+n*y*z := by
    calc
      4*x*y*z = ((4*x-n)+n)*y*z := by rw [hk']
      _ = _ := by grind
  grind

end ErdosStrausFixedFirst

/-- info: 'ErdosStrausFixedFirst.fixedFirst_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErdosStrausFixedFirst.fixedFirst_iff
