import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.ByContra

namespace GreedyPrefix
open Finset

/-- Greedy digit count with the first k distinct weights, inspected in decreasing order. -/
def digits (w : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k+1,n => if w k≤n then digits w k (n-w k)+1 else digits w k n

/-- For a strictly increasing positive weight system, all relevant weights fit in the first n+1. -/
def cost (w : ℕ → ℕ) (n : ℕ) : ℕ := digits w (n+1) n

def total (w : ℕ → ℕ) (N : ℕ) : ℕ := ∑ n ∈ range N, cost w n

private theorem skip {w : ℕ → ℕ} (hw : StrictMono w) {n k : ℕ} (hk : n<w k) (d : ℕ) :
    digits w (k+d) n = digits w k n := by
  induction d with
  | zero => rfl
  | succ d ih =>
    have h := lt_of_lt_of_le hk (hw.monotone (Nat.le_add_right k d))
    rw [←Nat.add_assoc, digits, if_neg (not_le.mpr h),ih]

theorem reduce {w : ℕ → ℕ} (hw : StrictMono w) {k n : ℕ} (hn : n<w k) :
    cost w n = digits w k n := by
  have ge (j : ℕ) : j≤w j := hw.id_le j
  unfold cost
  rcases le_total k (n+1) with h|h
  · obtain ⟨d,e⟩ := Nat.exists_eq_add_of_le h
    rw [e]
    exact skip hw hn d
  · obtain ⟨d,e⟩ := Nat.exists_eq_add_of_le h
    rw [e]
    exact (skip hw (by have := ge (n+1); omega) d).symm

theorem leading {w : ℕ → ℕ} (hw : StrictMono w) (k r : ℕ)
    (h1 : w k+r<w (k+1)) (h2 : r<w k) : cost w (w k+r)=cost w r+1 := by
  rw [reduce hw h1,digits,if_pos (Nat.le_add_right _ _),Nat.add_sub_cancel_left,reduce hw h2]

theorem block {w : ℕ → ℕ} (hw : StrictMono w) (k r : ℕ)
    (h1 : w k+r≤w (k+1)) (h2 : r≤w k) :
    total w (w k+r) = total w (w k) + total w r + r := by
  unfold total
  rw [sum_range_add]
  have h : ∀ i∈range r, cost w (w k+i) = cost w i+1 := by
    intro i hi
    have H := mem_range.mp hi
    exact leading hw k i (by omega) (by omega)
  rw [sum_congr rfl h,sum_add_distrib]
  simp [Nat.add_assoc]

end GreedyPrefix
