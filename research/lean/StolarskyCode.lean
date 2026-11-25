import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Order.Floor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
namespace Stolarsky
noncomputable section
def phi : ℝ := (1 + Real.sqrt 5)/2
theorem phi_sq : phi*phi=phi+1 := by
  unfold phi
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤5)]
theorem bounds : (161803:ℝ)/100000<phi ∧ phi<(161804:ℝ)/100000 := by
  have h : 0<phi := by unfold phi; positivity
  constructor
  · by_contra! bad
    nlinarith [mul_nonneg (sub_nonneg.mpr bad) (by linarith : 0≤phi+(161803:ℝ)/100000-1),phi_sq]
  · by_contra! bad
    nlinarith [mul_nonneg (sub_nonneg.mpr bad) (by linarith : 0≤phi+(161804:ℝ)/100000-1),phi_sq]

def phase (n : ℕ) := Int.fract ((n:ℝ)*phi)
/-- The second Wythoff column, using the one-based OEIS row convention. -/
def wythoff (n : ℕ) : ℤ := 2*⌊(n:ℝ)*phi⌋+(n:ℤ)-1
/-- The second Stolarsky column; nearest integer is floor(x+1/2). -/
def stolarsky (n : ℕ) : ℤ :=
  ⌊(⌊((n:ℝ)-1)*(phi+1)+1+phi/2⌋:ℝ)*phi+1/2⌋
def delta (n : ℕ) := wythoff n-stolarsky n
def colour (x : ℝ) : ℤ := if x<(phi-1)/2 then 1 else if x<phi/2 then 0 else -1

theorem code (n : ℕ) : delta n=colour (phase n) := by
  let k : ℤ := ⌊(n:ℝ)*phi⌋
  let r := phase n
  have A : (k:ℝ)+r = (n:ℝ)*phi := Int.floor_add_fract _
  have r0 : 0≤r := Int.fract_nonneg _
  have r1 : r<1 := Int.fract_lt_one _
  have b := bounds
  have sq := phi_sq
  have p : 0<2-phi := by linarith
  have c : ((n:ℝ)+(k:ℝ))*phi=2*(k:ℝ)+n+r*(2-phi) := by
    linear_combination (phi-2)*A + (n:ℝ)*sq
  change 2*k+n-1-⌊(⌊((n:ℝ)-1)*(phi+1)+1+phi/2⌋:ℝ)*phi+1/2⌋=colour r
  by_cases hr : r<phi/2
  · have fl : ⌊((n:ℝ)-1)*(phi+1)+1+phi/2⌋ = (n:ℤ)+k-1 := by
      apply Int.floor_eq_iff.mpr
      push_cast; constructor <;> linarith
    rw [fl]
    by_cases hl : r<(phi-1)/2
    · have q := mul_lt_mul_of_pos_right hl p
      have fl' : ⌊(((n:ℤ)+k-1:ℤ):ℝ)*phi+1/2⌋=2*k+n-2 := by
        apply Int.floor_eq_iff.mpr
        push_cast
        constructor <;> nlinarith [mul_nonneg r0 p.le]
      rw [fl']; simp [colour,hl]
    · have q := mul_le_mul_of_nonneg_right (le_of_not_gt hl) p.le
      have fl' : ⌊(((n:ℤ)+k-1:ℤ):ℝ)*phi+1/2⌋=2*k+n-1 := by
        apply Int.floor_eq_iff.mpr
        push_cast
        constructor <;> nlinarith [mul_lt_mul_of_pos_right r1 p]
      rw [fl']; simp [colour,hl,hr]
  · have fl : ⌊((n:ℝ)-1)*(phi+1)+1+phi/2⌋ = (n:ℤ)+k := by
      apply Int.floor_eq_iff.mpr
      push_cast; constructor <;> linarith
    have fl' : ⌊(((n:ℤ)+k:ℤ):ℝ)*phi+1/2⌋=2*k+n := by
      apply Int.floor_eq_iff.mpr
      push_cast
      constructor <;> nlinarith [mul_nonneg r0 p.le,mul_lt_mul_of_pos_right r1 p]
    rw [fl,fl']; simp [colour,hr,show ¬ r<(phi-1)/2 by linarith]
end
end Stolarsky
#print axioms Stolarsky.code
