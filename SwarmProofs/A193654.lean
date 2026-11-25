import Std

/-! The executable Q-residue of OEIS A193654 and Mathar's proposed
generating function. The program multiplies the two factors in each row
entry. The heading of the entry instead describes a quotient.
https://oeis.org/A193654 -/

namespace A193654

/-- The weights in the Q-residue sum. -/
def weight : Nat → Int
  | 0 => 1
  | n+1 => 2^n

private def sumThrough (f : Nat → Int) : Nat → Int
  | 0 => f 0
  | n+1 => sumThrough f n + f (n+1)

/-- The specified weight at positive index is the sum of all preceding ones. -/
private theorem weight_rule (n : Nat) : sumThrough weight n = weight (n+1) := by
  induction n with
  | zero => decide
  | succ n ih => rw [sumThrough, ih]; simp [weight, Int.pow_succ]; omega

/-- Sum of f(k) times weight(n-k), for k from zero through n. The
successor case removes the first summand and shifts the remaining row. -/
def weighted : Nat → (Nat → Int) → Int
  | 0, f => f 0
  | n+1, f => weight (n+1) * f 0 + weighted n (fun i => f (i+1))

/-- The floor in the executable definition is integer division by two. -/
def tile (n k : Nat) : Int := ((n : Int)+1)*((n : Int)+k+2)/2

def term (n : Nat) : Int := weighted n (tile n)

/-- Zero at even indices and one at odd indices. -/
def parity (k : Nat) : Int := (k : Int) % 2

private theorem parity_step (k : Nat) : parity (k+1) = 1 - parity k := by
  simp only [parity, Int.natCast_succ]
  omega

private theorem twice_tile (n k : Nat) :
    2*tile n k = ((n : Int)+1)*((n : Int)+k+2) - (1-parity n)*parity k := by
  have h : (((n : Int)+1)*((n : Int)+k+2)) % 2 = (1-parity n)*parity k := by
    rw [Int.mul_emod]
    unfold parity
    rw [Int.add_emod (n : Int) 1, Int.add_emod ((n : Int)+k) 2, Int.add_emod (n : Int) k]
    have hn : (n : Int)%2 = 0 ∨ (n : Int)%2 = 1 := by omega
    have hk : (k : Int)%2 = 0 ∨ (k : Int)%2 = 1 := by omega
    rcases hn with hn | hn <;> rcases hk with hk | hk <;> rw [hn, hk] <;> decide
  unfold tile
  omega

/-- Linear relations between row functions pass through their weighted sums. -/
private theorem linear (n : Nat) (f g h : Nat → Int) (a b c d : Int)
    (rel : ∀ j, a*f j + b*g j + c*h j = d) :
    a*weighted n f + b*weighted n g + c*weighted n h = d*weighted n (fun _ => 1) := by
  induction n generalizing f g h with
  | zero => exact rel 0 |>.trans (by simp [weighted])
  | succ n ih =>
    have htail := ih (fun j => f (j+1)) (fun j => g (j+1))
      (fun j => h (j+1)) (fun j => rel (j+1))
    have hfirst := rel 0
    simp only [weighted]
    grind

private theorem mass (n : Nat) : weighted n (fun _ => 1) = 2^n := by
  induction n with
  | zero => decide
  | succ n ih => simp [weighted, weight, ih, Int.pow_succ]; omega

private theorem moment (n : Nat) : weighted n (fun i => (i : Int)) = 2^n-1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h := linear n (fun i => ((i+1 : Nat) : Int)) (fun i => (i : Int))
      (fun _ => 1) 1 (-1) 0 1 (by intro j; simp; omega)
    simp only [weighted, Int.natCast_zero, Int.mul_zero, Int.zero_add]
    rw [mass] at h
    rw [Int.pow_succ]
    omega

private theorem odd_mass (n : Nat) :
    3 * weighted n parity = 2^n - (1 - 2*parity n) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h := linear n (fun j => parity (j+1)) parity (fun _ => 1) 1 1 0 1
      (by intro j; rw [parity_step]; omega)
    have hzero : parity 0 = 0 := by decide
    simp only [weighted, hzero, Int.mul_zero, Int.zero_add]
    rw [parity_step, Int.pow_succ]
    rw [mass] at h
    omega

/-- A closed form for six times the executable row sum. -/
theorem scaled (n : Nat) :
    6*term n = 3*((n : Int)+1)*(((n : Int)+3)*2^n-1)
      - (1-parity n)*(2^n-1) := by
  have h := linear n (tile n) (fun k => (k : Int)) parity
    2 (-((n : Int)+1)) (1-parity n) (((n : Int)+1)*((n : Int)+2))
    (by intro j; have := twice_tile n j; grind)
  rw [mass, moment] at h
  have o := odd_mass n
  unfold term
  have hp : parity n = 0 ∨ parity n = 1 := by unfold parity; omega
  rcases hp with hp | hp <;> rw [hp] at h o ⊢ <;> grind

private theorem tail_relation (n : Nat) :
    term (n+7)-5*term (n+6)+3*term (n+5)+21*term (n+4)
      -36*term (n+3)+32*term (n+1)-16*term n = 0 := by
  have h0 := scaled n
  have h1 := scaled (n+1)
  have h3 := scaled (n+3)
  have h4 := scaled (n+4)
  have h5 := scaled (n+5)
  have h6 := scaled (n+6)
  have h7 := scaled (n+7)
  simp only [Int.natCast_succ, Int.pow_succ, parity_step] at h1 h3 h4 h5 h6 h7
  grind

/-- Coefficient of x^n in x^k times the generating series of the row sums. -/
def lag (k n : Nat) : Int := if k ≤ n then term (n-k) else 0

/-- Coefficients of 1+2x-4x²-4x³+8x⁵. -/
def numerator : Nat → Int
  | 0 => 1
  | 1 => 2
  | 2 | 3 => -4
  | 5 => 8
  | _ => 0

private theorem denominator_expansion (x : Int) :
    (1+x)*(1+2*x)*(1-x)^2*(1-2*x)^3 =
      1-5*x+3*x^2+21*x^3-36*x^4+32*x^6-16*x^7 := by grind

/-- Mathar's rational generating-function identity, coefficient by coefficient.
The denominator (1+x)(1+2x)(1-x)²(1-2x)³ has constant term one. -/
theorem coefficient_identity (n : Nat) :
    term n - 5*lag 1 n + 3*lag 2 n + 21*lag 3 n - 36*lag 4 n
      + 32*lag 6 n - 16*lag 7 n = numerator n := by
  by_cases hn : n < 7
  · have h : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 ∨ n=6 := by omega
    rcases h with h|h|h|h|h|h|h <;> subst n <;> decide
  · obtain ⟨k, rfl⟩ : ∃ k, n = k+7 := ⟨n-7, by omega⟩
    simpa [lag, numerator] using tail_relation k

/-- The successive divisions written in the heading give zero in every cell. -/
theorem heading_zero (n k : Nat) : (n+1)/(n+k+2)/2 = 0 := by
  rw [Nat.div_eq_of_lt (show n+1 < n+k+2 by omega)]

end A193654

/-- info: 'A193654.scaled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms A193654.scaled

/-- info: 'A193654.coefficient_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms A193654.coefficient_identity

/-- info: 'A193654.heading_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms A193654.heading_zero
