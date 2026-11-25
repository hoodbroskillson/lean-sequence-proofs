import LucasZeros
open GreedyPrefix LucasZeros
namespace LucasZeroSet
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def EqualAt (x : ℕ) := total fib x=total luc x

def Near (i x : ℕ) := x=luc i ∨ x+1=luc (i+1) ∨
  (i%2=0 ∧ (x+2=luc (i+1) ∨ x+4=luc (i+1)))

private def tiny (w : ℕ→ℕ) (x : ℕ) := (Finset.range x).sum (digits w 12)

private theorem small_total (w : ℕ→ℕ) (hm : StrictMono w) {x : ℕ} (hx : x≤w 12) :
    total w x=tiny w x := by
  apply Finset.sum_congr rfl
  intro i hi
  exact reduce hm ((Finset.mem_range.mp hi).trans_le hx)

theorem small {i x : ℕ} (hi : i<8) (lo : luc i≤x) (up : x<luc (i+1)) :
    EqualAt x ↔ Near i x := by
  have b : x<47 := lt_of_lt_of_le up (luc_mono.monotone (by omega : i+1≤8))
  have tab : ∀i : Fin 8, ∀x : Fin 47,
      luc i.val≤x.val → x.val<luc (i.val+1) →
      (tiny fib x.val=tiny luc x.val ↔ Near i.val x.val) := by
    unfold Near; decide
  unfold EqualAt
  have jf : 47≤fib 12 := by decide
  have jl : 47≤luc 12 := by decide
  rw [small_total fib fib_mono (b.le.trans jf),small_total luc luc_mono (b.le.trans jl)]
  exact tab ⟨i,hi⟩ ⟨x,b⟩ lo up
end LucasZeroSet
#print axioms LucasZeroSet.small
