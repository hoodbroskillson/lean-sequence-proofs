import Std

/-! Zumkeller's A193652 interleaves A020988 with the same values plus one.
A020988 consists of the binary block 10 repeated n times. We derive the
closed form and R. J. Mathar's 2015 generating function from this description.
https://oeis.org/A193652 · https://oeis.org/A020988 · https://oeis.org/A007583 -/

namespace A193652

/-- Appending the binary digits 10 multiplies by four and adds two. -/
def blocks : Nat → Int
  | 0 => 0
  | k+1 => 4*blocks k + 2

def term (n : Nat) : Int := blocks (n/2) + ↑(n%2)

private theorem blocks_scaled (k : Nat) : 3*blocks k = 2*(4^k - 1) := by
  induction k with
  | zero => decide
  | succ k ih => simp only [blocks, Int.pow_succ]; omega

theorem closed_form (n : Nat) :
    term n = 2*(4^(n/2) - 1)/3 + ↑(n%2) := by
  have h := blocks_scaled (n/2)
  unfold term
  omega

private theorem recurrence (n : Nat) :
    term (n+4) - 5*term (n+2) + 4*term n = 0 := by
  have h₁ : (n+2)/2 = n/2 + 1 := by omega
  have h₂ : (n+4)/2 = n/2 + 2 := by omega
  have h₃ : (n+2)%2 = n%2 := by omega
  have h₄ : (n+4)%2 = n%2 := by omega
  simp only [term, h₁, h₂, h₃, h₄, blocks]
  omega

private def lag (k n : Nat) : Int := if k ≤ n then term (n-k) else 0

/-- Coefficients of (1−x²)(1−4x²)A(x) = x+2x²−2x³. -/
theorem generating_function (n : Nat) :
    term n - 5*lag 2 n + 4*lag 4 n =
      (if n = 1 then 1 else if n = 2 then 2 else if n = 3 then -2 else 0) := by
  by_cases hn : n < 4
  · have h : n=0 ∨ n=1 ∨ n=2 ∨ n=3 := by omega
    rcases h with h|h|h|h <;> subst n <;> decide
  · obtain ⟨k,rfl⟩ : ∃ k, n = k+4 := ⟨n-4, by omega⟩
    simpa [lag] using recurrence k

end A193652

/-- info: 'A193652.closed_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms A193652.closed_form

/-- info: 'A193652.generating_function' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms A193652.generating_function
