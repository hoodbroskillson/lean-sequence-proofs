import SwarmProofs.A193656

/-! The Mathematica program of OEIS A193649 takes the coefficient of x^k
in the (n+1)st Fibonacci polynomial and applies the downstep weight for
degree n−k. This reverses all n+1 coefficient slots, including any zero
constant. R. J. Mathar proposed the resulting generating function in 2015.
The reciprocal evaluation at two also has the recurrence of the known
sequence A006131. https://oeis.org/A193649 · https://oeis.org/A006131 -/

namespace A193649

open A193656 (Row evalAt residue twice_residue)

private def addRows : {n : Nat} → Row n → Row n → Row n
  | _, .constant a, .constant b => .constant (a+b)
  | _, .horner a p, .horner b q => .horner (a+b) (addRows p q)

/-- Append one slot at the highest degree. -/
private def appendHigh {n : Nat} (p : Row n) (c : Int) : Row (n+1) :=
  match p with
  | .constant a => .horner a (.constant c)
  | .horner a t => .horner a (appendHigh t c)

/-- Ordinary F_(n+1), from F_1=1, F_2=x and F_(n+3)=x F_(n+2)+F_(n+1).
The two appended zeros let us add polynomials with the same number of slots. -/
def fibonacci : (n : Nat) → Row n
  | 0 => .constant 1
  | 1 => .horner 0 (.constant 1)
  | n+2 => addRows (.horner 0 (fibonacci (n+1)))
      (appendHigh (appendHigh (fibonacci n) 0) 0)

/-- Reverse the order of the coefficient slots without discarding zeros. -/
def reverse {n : Nat} (p : Row n) : Row n :=
  match p with
  | .constant a => .constant a
  | .horner a t => appendHigh (reverse t) a

def term (n : Nat) : Int := residue (reverse (fibonacci n))

/-- Apply the downstep to the Fibonacci polynomial in ordinary power order. -/
def ordinaryTerm (n : Nat) : Int := residue (fibonacci n)

private theorem eval_append {n : Nat} (p : Row n) (c x : Int) :
    evalAt x (appendHigh p c) = evalAt x p + c*x^(n+1) := by
  induction p with
  | constant a => simp [appendHigh, evalAt]; grind
  | horner a t ih => simp only [appendHigh, evalAt, ih, Int.pow_succ]; grind

private theorem reverse_append {n : Nat} (p : Row n) (c : Int) :
    reverse (appendHigh p c) = .horner c (reverse p) := by
  induction p with
  | constant a => rfl
  | horner a t ih => simp only [appendHigh, reverse, ih]

private theorem eval_reverse_add {n : Nat} (p q : Row n) (x : Int) :
    evalAt x (reverse (addRows p q)) =
      evalAt x (reverse p) + evalAt x (reverse q) := by
  induction p with
  | constant a => cases q; rfl
  | horner a t ih =>
    cases q with
    | horner b u => simp only [addRows, reverse, eval_append, ih]; grind

/-- Evaluation after reversal satisfies the reciprocal polynomial recursion. -/
private theorem reverse_step (n : Nat) (x : Int) :
    evalAt x (reverse (fibonacci (n+2))) =
      evalAt x (reverse (fibonacci (n+1))) + x^2 * evalAt x (reverse (fibonacci n)) := by
  simp only [fibonacci, eval_reverse_add, reverse_append, reverse, eval_append, evalAt]
  grind

private theorem reverse_zero : ∀ n, evalAt 0 (reverse (fibonacci n)) = 1
  | 0 => by decide
  | 1 => by decide
  | n+2 => by rw [reverse_step, reverse_zero (n+1)]; simp

private theorem doubled (n : Nat) : 2 * term n = evalAt 2 (reverse (fibonacci n)) + 1 := by
  unfold term
  rw [twice_residue, reverse_zero]

private theorem step (n : Nat) : term (n+2) = term (n+1) + 4*term n - 2 := by
  have h := doubled (n+2)
  rw [reverse_step] at h
  have h₀ := doubled n
  have h₁ := doubled (n+1)
  omega

private def lag (a : Nat → Int) (k n : Nat) : Int := if k ≤ n then a (n-k) else 0

/-- Every coefficient of (1−x)(1−x−4x²)A(x) agrees with 1−x−2x². -/
theorem generating_function (n : Nat) :
    term n - 2*lag term 1 n - 3*lag term 2 n + 4*lag term 3 n =
      (if n = 0 then 1 else if n = 1 then -1 else if n = 2 then -2 else 0) := by
  cases n with
  | zero => decide
  | succ n =>
    cases n with
    | zero => decide
    | succ n =>
      cases n with
      | zero => decide
      | succ n =>
        have h := step n
        have h' := step (n+1)
        simp [lag]
        grind

private theorem eval_add {n : Nat} (p q : Row n) (x : Int) :
    evalAt x (addRows p q) = evalAt x p + evalAt x q := by
  induction p with
  | constant a => cases q; rfl
  | horner a t ih =>
    cases q with
    | horner b u => simp only [evalAt, addRows, ih]; grind

private theorem ordinary_step (n : Nat) (x : Int) :
    evalAt x (fibonacci (n+2)) = x * evalAt x (fibonacci (n+1)) +
      evalAt x (fibonacci n) := by
  simp [fibonacci, eval_add, evalAt, eval_append]

private theorem ordinary_tail (n : Nat) :
    ordinaryTerm (n+4) - 2*ordinaryTerm (n+3) - 2*ordinaryTerm (n+2)
      + 2*ordinaryTerm (n+1) + ordinaryTerm n = 0 := by
  have h (i : Nat) : 2 * ordinaryTerm i = evalAt 2 (fibonacci i) + evalAt 0 (fibonacci i) :=
    twice_residue (fibonacci i)
  have h₀ := h n
  have h₁ := h (n+1)
  have h₂ := h (n+2)
  have h₃ := h (n+3)
  have h₄ := h (n+4)
  simp only [ordinary_step] at h₂ h₃ h₄
  grind

/-- The unreversed polynomial interpretation has generating function
(1−x−x²)/((1−x²)(1−2x−x²)), certified in every degree. -/
theorem ordinary_generating_function (n : Nat) :
    ordinaryTerm n - 2*lag ordinaryTerm 1 n - 2*lag ordinaryTerm 2 n +
      2*lag ordinaryTerm 3 n + lag ordinaryTerm 4 n =
      (if n = 0 then 1 else if n = 1 ∨ n = 2 then -1 else 0) := by
  by_cases hn : n < 4
  · have h : n=0 ∨ n=1 ∨ n=2 ∨ n=3 := by omega
    rcases h with h|h|h|h <;> subst n <;> decide
  · obtain ⟨k,rfl⟩ : ∃ k, n = k+4 := ⟨n-4, by omega⟩
    simpa [lag] using ordinary_tail k

/-- The first coefficient-order discrepancy: the polynomial x³+2x gives
six when used directly and five when read in the program's order. -/
theorem orientation : ordinaryTerm 3 = 6 ∧ term 3 = 5 := by decide

end A193649

/-- info: 'A193649.generating_function' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms A193649.generating_function

/-- info: 'A193649.ordinary_generating_function' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms A193649.ordinary_generating_function

/-- info: 'A193649.orientation' depends on axioms: [propext] -/
#guard_msgs in
#print axioms A193649.orientation
