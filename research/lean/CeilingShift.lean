import StolarskyCode
import Mathlib.Data.Nat.Fib.Basic
namespace CeilingWythoff
open Stolarsky
noncomputable section

/-- Value of a least-significant-first binary word, with first weight F_s. -/
def value : List Bool → ℕ → ℕ
  | [],_ => 0
  | b::bs,s => (if b then Nat.fib s else 0) + value bs (s+1)

private def poly : List Bool → ℝ
  | [] => 0
  | b::bs => (if b then 1 else 0)+(1-phi)*poly bs

private theorem polyBound (bs : List Bool) : -1<poly bs ∧ poly bs<phi := by
  have bp := bounds
  have sq := phi_sq
  have neg : 1-phi<0 := by linarith
  induction bs with
  | nil => dsimp [poly]; constructor <;> linarith
  | cons b bs ih =>
    have a := mul_lt_mul_of_neg_left ih.2 neg
    have d := mul_lt_mul_of_neg_left ih.1 neg
    cases b <;> simp only [poly,Bool.false_eq_true,if_false,if_true,zero_add]
      <;> constructor <;> nlinarith

private theorem fibErr (s : ℕ) : (Nat.fib (s+1):ℝ)-phi*Nat.fib s=(1-phi)^s := by
  induction s with
  | zero => norm_num [Nat.fib]
  | succ s ih =>
    rw [pow_succ,←ih]
    change (Nat.fib (s+2):ℝ)-phi*Nat.fib (s+1)=_
    rw [Nat.fib_add_two,Nat.cast_add]
    linear_combination -((Nat.fib s):ℝ)*phi_sq

private theorem wordErr (bs : List Bool) (s : ℕ) :
    (value bs (s+1):ℝ)-phi*value bs s=(1-phi)^s*poly bs := by
  induction bs generalizing s with
  | nil => simp [value,poly]
  | cons b bs ih =>
    have t := ih (s+1)
    rw [pow_succ] at t
    have f := fibErr s
    cases b <;> simp only [value,poly,Bool.false_eq_true,if_false,if_true,Nat.cast_add,Nat.cast_zero,zero_add]
    · linear_combination t
    · linear_combination f+t

theorem floorShift (bs : List Bool) :
    ⌊((value bs 2 : ℝ)+1)*phi⌋=(value bs 3 : ℤ)+1 := by
  have e:=wordErr bs 2
  change (value bs 3:ℝ)-phi*value bs 2=(1-phi)^2*poly bs at e
  have bp:=bounds
  have pb:=polyBound bs
  have eq : (1-phi)^2=2-phi := by nlinarith [phi_sq]
  rw [eq] at e
  have pos : 0<2-phi := by linarith
  have lower := mul_lt_mul_of_pos_left pb.1 pos
  have upper := mul_lt_mul_of_pos_left pb.2 pos
  apply Int.floor_eq_iff.mpr
  push_cast
  constructor <;> nlinarith [phi_sq]

private theorem value_add (bs : List Bool) (k s : ℕ) :
    value bs (s+k+1)=Nat.fib k*value bs s + Nat.fib (k+1)*value bs (s+1) := by
  induction bs generalizing s with
  | nil => simp [value]
  | cons b bs ih =>
    have h := ih (s+1)
    rw [show s+1+k+1=s+k+1+1 by omega] at h
    cases b <;> simp only [value,Bool.false_eq_true,if_false,if_true,zero_add]
    · exact h
    · rw [Nat.fib_add,h]
      ring

/-- Source formula for the Wythoff ceiling array. Both arguments are one-based. -/
def entry (n k : ℕ) : ℤ := (Nat.fib (k+1):ℤ)*⌈(n:ℝ)*phi⌉+(n-1:ℕ)*Nat.fib k

theorem floorNext (bs : List Bool) :
    ⌈((value bs 2:ℝ)+1)*phi⌉=(value bs 3 : ℤ)+2 := by
  have e := wordErr bs 2
  change (value bs 3:ℝ)-phi*value bs 2=(1-phi)^2*poly bs at e
  have bp:=bounds
  have pb:=polyBound bs
  have eq : (1-phi)^2=2-phi := by nlinarith [phi_sq]
  rw [eq] at e
  have pos : 0<2-phi := by linarith
  have lower := mul_lt_mul_of_pos_left pb.1 pos
  have upper := mul_lt_mul_of_pos_left pb.2 pos
  apply Int.ceil_eq_iff.mpr
  push_cast
  constructor <;> nlinarith [phi_sq]

theorem sourceDigital (bs : List Bool) (k : ℕ) :
    entry (value bs 2+1) k = (2*Nat.fib (k+1)+value bs (2+k+1):ℕ) := by
  unfold entry
  rw [Nat.cast_add,Nat.cast_one,floorNext,Nat.add_sub_cancel]
  rw [value_add]
  push_cast
  ring
end
end CeilingWythoff
#print axioms CeilingWythoff.floorShift
#print axioms CeilingWythoff.floorNext
#print axioms CeilingWythoff.sourceDigital
