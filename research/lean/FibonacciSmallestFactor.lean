import FibonacciLargeFactor
import Batteries.Tactic.OpenPrivate
open private FibonacciLargeFactor.divides_index FibonacciLargeFactor.small_excluded
  FibonacciLargeFactor.near_plus FibonacciLargeFactor.near_minus from FibonacciLargeFactor
namespace FibonacciSmallestFactor
/-- Every prime factor, including the smallest, can be forced to exceed Cq.
The prime index q can also be made arbitrarily large. -/
theorem all_factors (C B:ℕ) : ∃q:ℕ, q.Prime ∧ B<q ∧ 5<q ∧
    (∀p:ℕ, p.Prime → p∣Nat.fib q → C*q<p) := by
  obtain ⟨q,qp,gq,hcon⟩:=Nat.exists_prime_gt_modEq_one (max B 5)
    (Nat.ne_of_gt (Nat.factorial_pos (C+8)))
  have gt:5<q:=(le_max_right _ _).trans_lt gq
  refine ⟨q,qp,(le_max_left _ _).trans_lt gq,gt,?_⟩
  intro p pp fq
  have gp:=FibonacciLargeFactor.small_excluded qp gt pp fq
  by_contra! bound
  have d:=FibonacciLargeFactor.divides_index qp pp gp fq
  unfold WallResidue.index at d
  split at d
  next =>
    obtain ⟨k,e⟩:=d
    have eq:p=q*k+1:=by omega
    have hk:0<k:=by by_contra! non;rw [show k=0 by omega] at eq;simp at eq;omega
    have small:k≤C+1:=by
      apply Nat.le_of_mul_le_mul_left (c:=q) _ (by omega)
      rw [Nat.mul_add,Nat.mul_one,Nat.mul_comm q C];omega
    exact FibonacciLargeFactor.near_plus pp gt hk small hcon eq
  next inert =>
    obtain ⟨k,e⟩:=d
    have small:k≤C+1:=by
      apply Nat.le_of_mul_le_mul_left (c:=q) _ (by omega)
      rw [Nat.mul_add,Nat.mul_one,Nat.mul_comm q C];omega
    exact FibonacciLargeFactor.near_minus pp qp gp gt small hcon e inert


theorem min_factor (C B:ℕ) : ∃q:ℕ, q.Prime ∧ B<q ∧ 5<q ∧
    C*q<(Nat.fib q).minFac := by
  obtain ⟨q,pr,le,gt,h⟩:=all_factors C B
  have big:1<Nat.fib q := (Nat.fib_lt_fib (m:=2) (by decide)).mpr (by omega)
  exact ⟨q,pr,le,gt,h _ (Nat.minFac_prime (by omega)) (Nat.minFac_dvd _)⟩
end FibonacciSmallestFactor
#print axioms FibonacciSmallestFactor.all_factors
#print axioms FibonacciSmallestFactor.min_factor
