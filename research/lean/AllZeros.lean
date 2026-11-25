import BaseCases

namespace LucasZeroSet
open LucasZeros GreedyPrefix

def cut (j : ℕ) := fib (j+2)-(if j%2=0 then 1 else 0)

private theorem margins (k : ℕ) :
    luc (k+6)<cut (k+4) ∧ cut (k+4)+4≤luc (k+7) := by
  have h6 := luc_fib (k+3)
  have h7 := luc_fib (k+4)
  have f6 : fib (k+6)=fib (k+5)+fib (k+4) := rfl
  have f4 : fib (k+4)=fib (k+3)+fib (k+2) := rfl
  have lo : fib 2≤fib (k+2) := fib_mono.monotone (by omega)
  have hi : fib 3≤fib (k+4) := fib_mono.monotone (by omega)
  change 3≤fib (k+2) at lo
  change 5≤fib (k+4) at hi
  simp only [Nat.add_assoc,Nat.reduceAdd] at h6 h7
  unfold cut
  simp only [Nat.add_assoc,Nat.reduceAdd]
  split <;> omega

/-- In each Lucas block the only equality points are the lower endpoint
and the indicated positions at the upper end. Counts here use [0,x). -/
theorem all_of_blocks (blocks : ∀j r, r≤luc (j+3) →
    (EqualAt (luc (j+4)+r) ↔ (EqualAt r ∧ (r=0 ∨ cut j≤r)))) (i x : ℕ)
    (lo : luc i≤x) (up : x<luc (i+1)) : EqualAt x ↔ Near i x := by
  induction i using Nat.strong_induction_on generalizing x with
  | h i ih =>
    by_cases base : i<8
    · exact small base lo up
    obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le (show 8≤i by omega)
    have ie : i=k+8 := by omega
    clear hk
    subst i
    let r:=x-luc (k+8)
    have xr : x=luc (k+8)+r := by dsimp [r]; omega
    have next : luc (k+9)=luc (k+8)+luc (k+7) := rfl
    change x<luc (k+9) at up
    have upper : r<luc (k+7) := by omega
    have b := blocks (k+4) r (show r≤luc (k+7) by omega)
    change (EqualAt (luc (k+8)+r) ↔ EqualAt r ∧ (r=0 ∨ cut (k+4)≤r)) at b
    rw [←xr] at b
    rw [b]
    have ends := margins k
    have parity : (k+8)%2=(k+6)%2 := by omega
    by_cases zero : r=0
    · have e0 : EqualAt 0 := rfl
      unfold Near
      simp only [zero,e0,true_or,or_true,and_self,iff_true_left]
      exact Or.inl (by omega)
    · have above : cut (k+4)≤r → luc (k+6)≤r := by omega
      have eq := ih (k+6) (by omega) r
      unfold Near at eq ⊢
      change (EqualAt r ∧ (r=0 ∨ cut (k+4)≤r)) ↔
        x=luc (k+8) ∨ x+1=luc (k+9) ∨ ( (k+8)%2=0 ∧ (x+2=luc (k+9) ∨ x+4=luc (k+9)))
      constructor
      · rintro ⟨er,cz|cr⟩
        · contradiction
        · have z := (eq (above cr) upper).mp er
          change r=luc (k+6) ∨ r+1=luc (k+7) ∨ ((k+6)%2=0 ∧ (r+2=luc (k+7) ∨ r+4=luc (k+7))) at z
          omega
      · intro hz
        have cr : cut (k+4)≤r := by omega
        refine ⟨(eq (above cr) upper).mpr ?_,Or.inr cr⟩
        change r=luc (k+6) ∨ r+1=luc (k+7) ∨ ((k+6)%2=0 ∧ (r+2=luc (k+7) ∨ r+4=luc (k+7)))
        omega
end LucasZeroSet
#print axioms LucasZeroSet.all_of_blocks
