import Std

/-! Mathar's recurrence for the floored ratio of elementary symmetric functions
in OEIS A024220. Sources: https://oeis.org/A024220 and the known formula
for the third elementary symmetric function at https://oeis.org/A024213 . -/

namespace A024220

/-- The first three elementary symmetric functions of the first `m` terms of
the progression 1, 4, 7, ... . Appending a term adds it times the preceding
elementary symmetric function to each sum. -/
def sums : Nat → Int × Int × Int
  | 0 => (0, 0, 0)
  | m+1 =>
    let (a, b, c) := sums m
    let t := 3 * (m : Int) + 1
    (a + t, b + t * a, c + t * b)

/-- The floor of the sum of triple products divided by the sum of the terms,
using the progression from 1 through (3n+4), inclusive. -/
def term (n : Nat) : Int :=
  (sums (n + 2)).2.2 / (sums (n + 2)).1

private def P (n : Int) : Int := n * (n + 1) * (9 * n ^ 2 + 21 * n - 2)

private theorem sums_formulas (m : Nat) :
    let t := (m : Int)
    2 * (sums m).1 = t * (3*t-1) ∧
    8 * (sums m).2.1 = 9*t^4 - 18*t^3 + 7*t^2 + 2*t ∧
    48 * (sums m).2.2 = t * (3*t-1) * P (t-2) := by
  induction m with
  | zero => decide
  | succ m ih =>
    simp only [Int.natCast_succ] at *
    rcases ih with ⟨h1, h2, h3⟩
    simp [sums, P] at *
    grind

/-- The polynomial divided by 24 gives the original floor quotient. -/
private theorem term_formula (n : Nat) : term n = P n / 24 := by
  obtain ⟨h1, _, h3⟩ := sums_formulas (n+2)
  simp only [Int.natCast_add, Int.cast_ofNat_Int] at h1 h3
  have hpos : 0 < (sums (n+2)).1 := by grind
  have hscale : 24 * (sums (n+2)).2.2 = (sums (n+2)).1 * P n := by grind
  unfold term
  calc
    _ = (24 * (sums (n+2)).2.2) / (24 * (sums (n+2)).1) :=
      (Int.mul_ediv_mul_of_pos _ _ (by decide : (0:Int)<24)).symm
    _ = _ := by rw [hscale, Int.mul_comm 24]; exact Int.mul_ediv_mul_of_pos _ _ hpos

private def remTerm (n : Nat) : Int := if n % 3 = 1 then 8 else 0

private theorem polynomial_remainder (n : Nat) : P n % 24 = remTerm n := by
  let r : Int := n % 24
  let q : Int := n / 24
  let t : Int := n
  -- Dividing the difference P(t) - P(r) by t - r gives the polynomial d.
  let d := 9 * (t + r) * (t^2 + r^2) + 30 * (t^2 + t*r + r^2) + 19 * (t + r) - 2
  have split : t = r + 24*q := by dsimp [t, r, q]; omega
  have expand : P t = P r + (q*d)*24 := by dsimp [P,d]; grind
  -- The remainder depends only on the input modulo 24, so these cases suffice.
  have small : ∀ j : Fin 24, P (j.val : Int) % 24 = remTerm j.val := by decide
  have rr := small ⟨n%24, by omega⟩
  change P t % 24 = _
  rw [expand, Int.add_mul_emod_self_right]
  have hr : r = ((n%24 : Nat) : Int) := rfl
  rw [hr, rr]
  change (if n % 24 % 3 = 1 then (8:Int) else 0) = _
  rw [show n % 24 % 3 = n % 3 by omega]
  rfl

private theorem scaled_term (n : Nat) : 24 * term n = P n - remTerm n := by
  rw [term_formula, ← polynomial_remainder]
  omega

/-- R. J. Mathar's order-seven recurrence, in forward-shift form.
The OEIS offset is 1; the same identity extends to n = 0. -/
theorem recurrence (n : Nat) :
    term (n+7) - 4*term (n+6) + 6*term (n+5) - 5*term (n+4) +
      5*term (n+3) - 6*term (n+2) + 4*term (n+1) - term n = 0 := by
  have period (i : Nat) : remTerm (i+3) = remTerm i := by
    unfold remTerm
    rw [show (i+3)%3 = i%3 by omega]
  have h0 := scaled_term n
  have h1 := scaled_term (n+1)
  have h2 := scaled_term (n+2)
  have h3 := scaled_term (n+3)
  have h4 := scaled_term (n+4)
  have h5 := scaled_term (n+5)
  have h6 := scaled_term (n+6)
  have h7 := scaled_term (n+7)
  rw [period n] at h3
  rw [period (n+1)] at h4
  rw [period (n+2)] at h5
  rw [period (n+3), period n] at h6
  rw [period (n+4), period (n+1)] at h7
  simp only [P, Int.natCast_add, Int.cast_ofNat_Int] at *
  grind

end A024220

/-- info: 'A024220.recurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms A024220.recurrence
