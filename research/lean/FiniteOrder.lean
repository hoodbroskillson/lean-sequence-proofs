import CanonicalZeros
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.ZMod.Basic
namespace FiniteOrder
open ZeroEnumeration
open scoped BigOperators
def sumAt {p d : ℕ} (c : Fin d → ZMod p) (n : ℕ) :=
  ∑ j : Fin d, c j*(entry (n+j.val):ZMod p)
noncomputable def sourceSum {p d : ℕ} (c : Fin d → ZMod p) (n : ℕ) :=
  ∑ j : Fin d, c j*(CanonicalZeros.a (n+j.val):ZMod p)

theorem bridge {p d : ℕ} (c : Fin d → ZMod p) (n : ℕ) (hn : 0<n) : sourceSum c n=sumAt c n := by
  unfold sourceSum sumAt
  apply Finset.sum_congr rfl
  intro j _
  rw [CanonicalZeros.source_entry _ (by omega)]

private theorem shift {p d : ℕ} (c : Fin d → ZMod p) (n : ℕ) (hn : 5≤n) :
  sumAt c (n+18)+4*sumAt c (n+6)=4*sumAt c (n+12)+sumAt c n := by
  unfold sumAt
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have eq := congrArg (fun i : ℕ => (i : ZMod p)) (sparse_recurrence (n+j.val) (by omega))
  push_cast at eq
  simp only [show n+18+j.val=n+j.val+18 by omega,show n+6+j.val=n+j.val+6 by omega,
    show n+12+j.val=n+j.val+12 by omega]
  linear_combination c j*eq

def ExactOrder (p d : ℕ) : Prop :=
  (∀(c : Fin d → ZMod p) (N : ℕ), (∀n, N≤n → sourceSum c n=0) → ∀i,c i=0) ∧
  ∃c : Fin (d+1) → ZMod p, c (Fin.last d)=1 ∧ ∀n,5≤n → sourceSum c n=0

theorem lower {p d : ℕ} (inv : Fin d → Fin d → ZMod p)
    (cert : ∀i j, (∑ k : Fin d, inv i k * (entry (5+k.val+j.val):ZMod p))=if i=j then 1 else 0)
    (c : Fin d → ZMod p) (N : ℕ) (h : ∀n,N≤n → sourceSum c n=0) (i : Fin d) : c i=0 := by
  have back : ∀k m,N≤m+k → 5≤m → sumAt c m=0 := by
    intro k
    induction k with
    | zero => intro m hm hl; rw [←bridge c m (by omega)]; apply h m (by omega)
    | succ k ih =>
      intro m hm hl
      have eq := shift c m hl
      rw [ih (m+18) (by omega) (by omega),ih (m+6) (by omega) (by omega),
        ih (m+12) (by omega) (by omega)] at eq
      simpa using eq.symm
  have zz : (∑ k : Fin d, inv i k * sumAt c (5+k.val))=0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [back N (5+k.val) (by omega) (by omega),mul_zero]
  unfold sumAt at zz
  simp_rw [Finset.mul_sum] at zz
  rw [Finset.sum_comm] at zz
  have swap (k j : Fin d) : inv i k*(c j*(entry (5+k.val+j.val):ZMod p))=
      c j*(inv i k*(entry (5+k.val+j.val):ZMod p)) := by ring
  simp_rw [swap,←Finset.mul_sum,cert] at zz
  simpa [mul_ite] using zz

theorem upper {p d : ℕ} {c : Fin d → ZMod p}
    (base : ∀i : Fin 18, sumAt c (5+i.val)=0) (n : ℕ) (hn : 5≤n) : sourceSum c n=0 := by
  rw [bridge c n (by omega)]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases small : n<23
    · simpa only [show 5+(n-5)=n by omega] using base ⟨n-5,by omega⟩
    · let m:=n-18
      have hm : 5≤m := by dsimp [m]; omega
      have e : m+18=n := by dsimp [m]; omega
      have eq:=shift c m hm
      rw [e,ih (m+6) (by omega) (by omega),ih (m+12) (by omega) (by omega),ih m (by omega) hm] at eq
      simpa using eq

end FiniteOrder
#print axioms FiniteOrder.lower
#print axioms FiniteOrder.upper
