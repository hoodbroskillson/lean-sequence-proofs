import Std

/-! Clark Kimberling's all-ones Q-downstep (OEIS A193649) applied to the
geometric rows of A193656. R. J. Mathar proposed the closed form and rational
generating function there in 2015. The final theorem verifies the even-index
cross-reference in Paul Barry's A097111.
https://oeis.org/A193649 · https://oeis.org/A193656 · https://oeis.org/A097111 -/

namespace A193656

/-- A row with n+1 coefficients, in increasing order of exponent.
    The constructor `horner c p` represents c + x p(x). -/
inductive Row : Nat → Type where
  | constant (c : Int) : Row 0
  | horner {n : Nat} (c : Int) (p : Row n) : Row (n+1)

def evalAt (x : Int) : {n : Nat} → Row n → Int
  | _, .constant c => c
  | _, .horner c p => c + x * evalAt x p

private def addConstant (d : Int) : {n : Nat} → Row n → Row n
  | _, .constant c => .constant (d+c)
  | _, .horner c p => .horner (d+c) p

/-- Replace each coefficient by the sum of itself and the higher coefficients. -/
private def suffixSums : {n : Nat} → Row n → Row n
  | _, .constant c => .constant c
  | _, .horner c p => .horner (c + evalAt 1 p) (suffixSums p)

/-- In one all-ones downstep each positive monomial x^j contributes
    1+x+⋯+x^(j−1), and the original constant is added to the result. -/
def down {n : Nat} : Row (n+1) → Row n
  | .horner c p => addConstant c (suffixSums p)

/-- Iterate the downstep until the row consists of one coefficient. -/
def residue : {n : Nat} → Row n → Int
  | 0, .constant c => c
  | _+1, p => residue (down p)

private theorem eval_add {n : Nat} (x d : Int) (p : Row n) :
    evalAt x (addConstant d p) = d + evalAt x p := by
  cases p <;> simp [evalAt, addConstant, Int.add_assoc]

private theorem suffix_at_zero {n : Nat} (p : Row n) :
    evalAt 0 (suffixSums p) = evalAt 1 p := by
  cases p <;> simp [suffixSums, evalAt]

private theorem suffix_at_two {n : Nat} (p : Row n) :
    evalAt 2 (suffixSums p) + evalAt 1 p = 2 * evalAt 2 p := by
  induction p with
  | constant c => simp [evalAt, suffixSums]; omega
  | horner c p ih =>
    simp [evalAt, suffixSums]
    omega

/-- Evaluation at two plus evaluation at zero is invariant under the
    downstep. On a constant row it is twice the residue. -/
theorem twice_residue {n : Nat} (p : Row n) :
    2 * residue p = evalAt 2 p + evalAt 0 p := by
  induction n with
  | zero => cases p; simp [residue, evalAt]; omega
  | succ n ih =>
    cases p with
    | horner c p =>
      change 2 * residue (addConstant c (suffixSums p)) = _
      rw [ih, eval_add, eval_add, suffix_at_zero]
      have h := suffix_at_two p
      simp [evalAt]
      omega

/-- At scale one the coefficient of x^j is 2^j 5^(n−j), i.e. the
    entry 2^(n−k) 5^k in descending column k=n−j. -/
def geometric (n : Nat) (scale : Int) : Row n :=
  match n with
  | 0 => .constant scale
  | k+1 => .horner (scale * 5^(k+1)) (geometric k (2*scale))

private theorem geometric_zero (n : Nat) (s : Int) :
    evalAt 0 (geometric n s) = s * 5^n := by
  cases n <;> simp [geometric, evalAt]

private theorem geometric_two (n : Nat) (s : Int) :
    evalAt 2 (geometric n s) = s * (5^(n+1) - 4^(n+1)) := by
  induction n generalizing s with
  | zero => simp [geometric, evalAt]
  | succ n ih =>
    simp only [geometric, evalAt, ih, Int.pow_succ]
    grind

def term (n : Nat) : Int := residue (geometric n 1)

/-- Mathar's closed form for the original iterated Q-residue. -/
theorem closed_form (n : Nat) : term n = 3*5^n - 2*4^n := by
  have h := twice_residue (geometric n 1)
  rw [geometric_two, geometric_zero] at h
  unfold term
  simp only [Int.one_mul, Int.pow_succ] at h
  omega

/-- Coefficient of x^n after a shift by k powers of x. -/
private def lag (k n : Nat) : Int := if k ≤ n then term (n-k) else 0

/-- In every degree, multiplying the generating series by
    (1−5x)(1−4x) gives 1−2x. -/
theorem generating_function (n : Nat) :
    term n - 9 * lag 1 n + 20 * lag 2 n =
      (if n = 0 then 1 else if n = 1 then -2 else 0) := by
  cases n with
  | zero => decide
  | succ n =>
    cases n with
    | zero => decide
    | succ n =>
      simp [lag, closed_form, Int.pow_succ]
      grind

/-- The recurrence and initial terms of Barry's A097111, obtained by expanding
    (1+3x−2x²−12x³)/(1−9x²+20x⁴). -/
def barry : Nat → Int
  | 0 => 1
  | 1 => 3
  | 2 => 7
  | 3 => 15
  | n+4 => 9 * barry (n+2) - 20 * barry n

/-- The even-indexed terms of A097111 are the Q-residues in A193656. -/
theorem bisection : ∀ n : Nat, barry (2*n) = term n
  | 0 => by decide
  | 1 => by decide
  | n+2 => by
    rw [show 2*(n+2) = 2*n+4 by omega, barry,
        show 2*n+2 = 2*(n+1) by omega, bisection (n+1), bisection n]
    simp only [closed_form, Int.pow_succ]
    grind

end A193656

/-- info: 'A193656.twice_residue' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms A193656.twice_residue

/-- info: 'A193656.closed_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms A193656.closed_form

/-- info: 'A193656.generating_function' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms A193656.generating_function

/-- info: 'A193656.bisection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms A193656.bisection
