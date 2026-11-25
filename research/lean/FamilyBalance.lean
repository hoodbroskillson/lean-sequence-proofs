import FamilyCount
import TurekInvariant
namespace MexFamily
open Nat
variable (q : Params)

/-- Sharp published characteristic-word bound, independently verified for these mex sequences. -/
theorem characteristic (i j k : ℕ) : C q (i+k)+C q j≤C q (j+k)+C q i+q.s :=
  FourCuts.characteristic_balanced q.ge (C_le q) (prefix_decomposition q) i j k

private def cut (i : ℕ) := (i-1)/q.s

private theorem residue (n : ℕ) : q.s*cut q n≤n ∧ n≤q.s*cut q n+q.s ∧
    (0<n → q.s*cut q n<n) := by
  cases n with
  | zero => simp [cut]
  | succ n =>
    have a:=Nat.mod_add_div n q.s
    have b:=Nat.mod_lt n (show 0<q.s by have :=q.ge;omega)
    simp only [cut,Nat.succ_sub_one]
    omega

private theorem cut_mono : Monotone (cut q) := fun _ _ h => Nat.div_le_div_right (Nat.sub_le_sub_right h _)

private theorem window (i j k : ℕ) : cut q (i+k)+cut q j≤cut q (j+k)+cut q i+1 := by
  cases k with
  | zero => simp;omega
  | succ k =>
    by_contra! bad
    have lo:=Nat.mul_le_mul_left q.s (show cut q (j+(k+1))+cut q i+2≤cut q (i+(k+1))+cut q j by omega)
    simp only [Nat.mul_add,Nat.mul_two] at lo
    have a:=residue q i
    have b:=residue q j
    have c:=residue q (i+(k+1))
    have d:=residue q (j+(k+1))
    have u:=c.2.2 (by omega)
    omega

private theorem comparison (m n j : ℕ) :
    C q (cut q (m+j))+C q (cut q n)≤C q (cut q (n+j))+C q (cut q m)+q.s+1 := by
  let h:=cut q (n+j)-cut q n
  have eq : cut q n+h=cut q (n+j) := Nat.add_sub_of_le (cut_mono q (show n≤n+j by omega))
  have w:=window q m n j
  have r : cut q (m+j)≤cut q m+h+1 := by omega
  have u:=(C_mono q) r
  have v:=C_succ q (cut q m+h)
  have z:=characteristic q (cut q m) (cut q n) h
  rw [eq] at z
  omega

/-- The integer D from Artstein-Avidan, Fraenkel and Sós, equation (3). -/
def D (m n j : ℕ) : ℤ := |(A q (m+j):ℤ)-A q m-((A q (n+j):ℤ)-A q n)|

/-- The bound of Theorem 3 for t=1 improves uniformly to s+1. -/
theorem improved (m n j : ℕ) : D q m n j≤q.s+1 := by
  have a:=comparison q m n j
  have b:=comparison q n m j
  unfold cut at a b
  unfold D
  rw [compress q (m+j),compress q m,compress q (n+j),compress q n]
  push_cast
  apply abs_le.mpr
  omega

/-- The original 2s+1 bound is strictly too large for every s≥2. -/
theorem nonsharp (m n j : ℕ) : D q m n j<2*q.s+1 := by
  have a:=improved q m n j
  have s:=q.ge
  omega
end MexFamily
#print axioms MexFamily.characteristic
#print axioms MexFamily.improved
#print axioms MexFamily.nonsharp
