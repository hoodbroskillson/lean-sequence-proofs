import Std

/-! Clark Kimberling's sequence A024219. R. J. Mathar proposed its
recurrence in 2011 and Andrew Howroyd confirmed it in 2018.
https://oeis.org/A024219 -/

namespace A024219

/-- Elementary sums of degrees one and two on 1, 4, ..., 3m-2. -/
def sums : Nat → Int × Int
  | 0 => (0, 0)
  | m+1 =>
    let (s, p) := sums m
    let t := 3*(m : Int)+1
    (s+t, p+s*t)

def term (n : Nat) : Int := (sums (n+1)).2 / (sums (n+1)).1

private theorem sums_closed (m : Nat) :
    let t := (m : Int)
    2*(sums m).1 = t*(3*t-1) ∧
    8*(sums m).2 = t*(t-1)*(9*t^2-9*t-2) := by
  induction m with
  | zero => decide
  | succ m ih =>
    obtain ⟨hs, hp⟩ := ih
    simp [sums, Int.natCast_succ]
    grind

/-- Howroyd's floor formula, derived from the elementary sums. -/
theorem floorFormula (n : Nat) :
    let t := (n : Int)
    term n = (t*(9*t^2+9*t-2)) / (4*(3*t+2)) := by
  obtain ⟨hs, hp⟩ := sums_closed (n+1)
  simp only [Int.natCast_succ] at hs hp
  have hd : 8*(sums (n+1)).1 = ((n:Int)+1)*(4*(3*n+2)) := by grind
  have hn : 8*(sums (n+1)).2 = ((n:Int)+1)*(n*(9*(n:Int)^2+9*n-2)) := by grind
  unfold term
  calc
    _ = (8*(sums (n+1)).2) / (8*(sums (n+1)).1) :=
        (Int.mul_ediv_mul_of_pos _ _ (by decide : (0:Int)<8)).symm
    _ = _ := by rw [hn, hd]; exact Int.mul_ediv_mul_of_pos _ _ (by omega)

private def correction (n : Nat) : Int := if n % 4 < 2 then 4 else 2

private theorem scaled (n : Nat) (hn : 0 < n) :
    4*term n = (n:Int)*(3*n+1)-correction n := by
  let t := (n : Int)
  let v := t*(3*t+1)-correction n
  have hv : v % 4 = 0 := by
    dsimp [v, t, correction]
    rw [Int.sub_emod, Int.mul_emod, Int.add_emod, Int.mul_emod (3:Int)]
    have h : (n:Int) % 4 = (n % 4 : Nat) := by omega
    rw [h]
    have hr : n%4=0 ∨ n%4=1 ∨ n%4=2 ∨ n%4=3 := by omega
    rcases hr with h | h | h | h <;> rw [h] <;> decide
  let y := v / 4
  have hy : 4*y = t*(3*t+1)-correction n := by dsimp [y]; omega
  have gap : t*(9*t^2+9*t-2)-y*(4*(3*t+2)) = correction n*(3*t+2)-4*t := by grind
  have eq : term n = y := by
    rw [floorFormula]
    apply (Int.ediv_eq_iff_of_pos (by omega)).2
    change y*(4*(3*t+2)) ≤ t*(9*t^2+9*t-2) ∧ t*(9*t^2+9*t-2) < y*(4*(3*t+2)) + 4*(3*t+2)
    have ht : 0 < t := by dsimp [t]; omega
    unfold correction at gap
    split at gap <;> omega
  rw [eq]
  exact hy

private theorem correction_pair (i : Nat) : correction (i+2)+correction i = 6 := by
  unfold correction
  split <;> split <;> omega

/-- Mathar's recurrence in forward form. Since the sequence begins at 1,
the target index ranges over all integers at least 6. -/
theorem recurrence (n : Nat) (hn : 0 < n) :
    term (n+5) - 3*term (n+4) + 4*term (n+3) - 4*term (n+2)
      + 3*term (n+1) - term n = 0 := by
  have h0 := scaled n hn
  have h1 := scaled (n+1) (by omega)
  have h2 := scaled (n+2) (by omega)
  have h3 := scaled (n+3) (by omega)
  have h4 := scaled (n+4) (by omega)
  have h5 := scaled (n+5) (by omega)
  have c0 := correction_pair n
  have c1 := correction_pair (n+1)
  have c2 := correction_pair (n+2)
  have c3 := correction_pair (n+3)
  simp only [Int.natCast_add, Int.cast_ofNat_Int] at *
  grind

end A024219

/-- info: 'A024219.floorFormula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms A024219.floorFormula

/-- info: 'A024219.recurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms A024219.recurrence
