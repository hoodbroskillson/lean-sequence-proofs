import SwarmProofs.A193656

/-! Clark Kimberling's program for A193651 (2011) reads the coefficients of
∏_{j=1}^n (x+j) with the weight for degree n−k on the coefficient of x^k.
The reversed polynomial is ∏_{j=1}^n (1+jx). Peter Luschny recorded the
odd-double-factorial formula in 2014. https://oeis.org/A193651 -/

namespace A193651

open A193656 (Row evalAt residue twice_residue)

/-- The polynomial carry + (1+d*x)*p in increasing degree order. -/
private def mulLinear (d carry : Int) : {n : Nat} → Row n → Row (n+1)
  | _, .constant a => .horner (carry+a) (.constant (d*a))
  | _, .horner a q => .horner (carry+a) (mulLinear d (d*a) q)

private theorem eval_mulLinear {n : Nat} (d carry x : Int) (p : Row n) :
    evalAt x (mulLinear d carry p) = carry + (1+d*x)*evalAt x p := by
  induction p generalizing carry with
  | constant a => simp only [mulLinear, evalAt]; grind
  | horner a q ih => simp only [mulLinear, evalAt, ih]; grind

/-- Reciprocal coefficient rows of the rising-factorial polynomials. -/
def row : (n : Nat) → Row n
  | 0 => .constant 1
  | n+1 => mulLinear (n+1) 0 (row n)

def term (n : Nat) : Int := residue (row n)

/-- The product 1·3·5···(2n+1). -/
def oddProduct : Nat → Int
  | 0 => 1
  | n+1 => (2*(n:Int)+3)*oddProduct n

private theorem evaluations (n : Nat) :
    evalAt 0 (row n) = 1 ∧ evalAt 2 (row n) = oddProduct n := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    simp only [row, eval_mulLinear, oddProduct, ih.1, ih.2]
    constructor <;> grind

/-- Luschny's formula for Kimberling's iterated Q-downstep. -/
theorem closed_form (n : Nat) : term n = (oddProduct n + 1) / 2 := by
  have h := twice_residue (row n)
  rw [(evaluations n).1, (evaluations n).2] at h
  unfold term
  omega

end A193651

/-- info: 'A193651.closed_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms A193651.closed_form
