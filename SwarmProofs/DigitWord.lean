import Std

/-! The fixed-point description of the digit-sum word in OEIS A173527
and A053828, for arbitrary base and initial symbol.
https://oeis.org/A173527 · https://oeis.org/A053828 -/

namespace DigitWord

/-- Remove the least significant base-b digit and add its value. -/
def digitSum (b : Nat) (hb : 2 ≤ b) (n : Nat) : Nat :=
  if _hn : n = 0 then 0 else digitSum b hb (n / b) + n % b
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- Concatenate the length-b blocks [a, a+1, ..., a+b-1] for symbols a of w.
Position n lies in block n/b and has offset n%b in that block. -/
def substitute (b : Nat) (w : Nat → Nat) (n : Nat) : Nat :=
  w (n / b) + n % b

/-- The digit-sum word is the unique substitution fixed point with the given
initial symbol. For b = 7 and seed = 1 this gives OEIS A173527. -/
theorem fixed_iff (b seed : Nat) (hb : 2 ≤ b) (w : Nat → Nat) :
    (substitute b w = w ∧ w 0 = seed) ↔ w = fun n => seed + digitSum b hb n := by
  constructor
  · rintro ⟨hfix, hzero⟩
    funext n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      by_cases hn : n = 0
      · subst n
        simpa [digitSum] using hzero
      · have h := congrFun hfix n
        change w (n/b) + n%b = w n at h
        rw [← h, ih (n/b) (Nat.div_lt_self (by omega) (by omega))]
        conv => rhs; rw [digitSum, dite_eq_right hn]
        exact Nat.add_assoc _ _ _
  · rintro rfl
    constructor
    · funext n
      by_cases hn : n = 0
      · subst n
        simp [substitute]
      · change (seed + digitSum b hb (n/b)) + n%b = seed + digitSum b hb n
        conv => rhs; rw [digitSum, dite_eq_right hn]
        exact Nat.add_assoc _ _ _
    · simp [digitSum]

end DigitWord

/-- info: 'DigitWord.fixed_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms DigitWord.fixed_iff
