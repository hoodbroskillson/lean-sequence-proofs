import LucasZeros
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

namespace LucasPrefixes
open GreedyPrefix LucasZeros

private theorem total_succ (w : ℕ→ℕ) (n:ℕ) : total w (n+1)=total w n+cost w n := by
  exact Finset.sum_range_succ _ _

private def delta (L r : ℕ) : ℤ :=
  (total fib (L+r):ℤ)-total fib L-total fib r-r

private theorem delta_succ (L r : ℕ) : delta L (r+1)=delta L r+
    ((cost fib (L+r):ℤ)-cost fib r-1) := by
  simp only [delta,←Nat.add_assoc,total_succ,Nat.cast_add,Nat.cast_one]
  push_cast
  ring

theorem early (n i : ℕ) (hi:i<fib n) :
    cost fib (luc (n+4)+i)=cost fib i+2 := by
  have l:=luc_fib (n+1)
  have a : fib (n+2)=fib (n+1)+fib n := rfl
  have b : fib (n+4)=fib (n+3)+fib (n+2) := rfl
  have mono1:=fib_mono (show n<n+1 by omega)
  have mono2:=fib_mono (show n+2<n+3 by omega)
  have E:=leading fib_mono (n+3) (fib (n+1)+i) (by change _ < fib (n+4); omega) (by omega)
  have F:=leading fib_mono (n+1) i (by change _ < fib (n+2); omega) (by omega)
  change luc (n+4)=fib (n+3)+fib (n+1) at l
  rw [show luc (n+4)+i=fib (n+3)+(fib (n+1)+i) by omega,E,F]

theorem late
    (localAdd : ∀ j s, s<fib (j+2) → cost fib s≤cost fib (fib j+s))
    (n i : ℕ) (hc : fib n≤i) (hi : i<luc (n+3)) :
    cost fib (luc (n+4)+i)≤cost fib i+1 := by
  let s:=i-fib n
  have eq : i=fib n+s := by dsimp [s]; omega
  have l0:=luc_fib n
  have l1:=luc_fib (n+1)
  change luc (n+4)=fib (n+3)+fib (n+1) at l1
  have ff : fib (n+2)=fib (n+1)+fib n := rfl
  have f4 : fib (n+4)=fib (n+3)+fib (n+2) := rfl
  have f5 : fib (n+5)=fib (n+4)+fib (n+3) := rfl
  have hs : s<fib (n+2) := by omega
  have sm:=fib_mono (show n+2<n+3 by omega)
  have sm':=fib_mono (show n+2<n+4 by omega)
  have E:=leading fib_mono (n+4) s (by change _ < fib (n+5); omega) (by omega)
  rw [show luc (n+4)+i=fib (n+4)+s by omega,E,eq]
  exact Nat.add_le_add_right (localAdd n s hs) 1

private theorem balance (n : ℕ) : delta (luc (n+4)) (luc (n+3))=0 := by
  have lc : luc (n+4)+luc (n+3)=luc (n+5) := rfl
  have z:=block luc_mono (n+4) (luc (n+3)) (by rfl) (luc_mono.monotone (by omega))
  rw [lc] at z
  rw [delta,lc,equal_lucas (n+3),equal_lucas (n+2),equal_lucas (n+1),z]
  simp only [Nat.add_assoc,Nat.reduceAdd]
  push_cast
  ring

/-- When the increments first are nonnegative and then nonpositive,
zero total over the block implies all partial sums are nonnegative. -/
theorem crossing (f : ℕ→ℤ) (a b : ℕ) (hz:f 0=0) (hb:f b=0)
    (up:∀i,i<a→f i≤f (i+1)) (down:∀i,a≤i→i<b→f (i+1)≤f i)
    (r : ℕ) (hr:r≤b) : 0≤f r := by
  by_cases ha : r≤a
  · induction r with
    | zero => omega
    | succ i ih => exact (ih (by omega) (by omega)).trans (up i (by omega))
  · have falling : ∀ j, a≤j → j≤b → f b≤f j := by
      intro j hj hle
      obtain ⟨k,eq⟩:=Nat.exists_eq_add_of_le hle
      have hh : ∀ u, j+u≤b → f (j+u)≤f j := by
        intro u
        induction u with
        | zero => simp
        | succ u ih =>
          intro hu
          exact (down (j+u) (by omega) (by omega)).trans (ih (by omega))
      exact eq ▸ hh k (by omega)
    exact hb ▸ falling r (by omega) hr

theorem shifted_prefix
    (localAdd : ∀ j s, s<fib (j+2) → cost fib s≤cost fib (fib j+s))
    (n r : ℕ) (hr:r≤luc (n+3)) :
    total fib (luc (n+4))+total fib r+r≤total fib (luc (n+4)+r) := by
  let L:=luc (n+4)
  have h:=crossing (delta L) (fib n) (luc (n+3)) (by simp [delta,total]) (balance n)
    (by
      intro i hi
      dsimp only [L]
      rw [delta_succ,early n i hi]
      push_cast
      omega)
    (by
      intro i hc hi
      rw [delta_succ]
      have h:=late localAdd n i hc hi
      change cost fib (L+i)≤_ at h
      omega) r hr
  dsimp [delta,L] at h
  omega

/-- Global transfer by descending to the remainder below the previous Lucas weight. -/
theorem bound_of_local
    (localAdd : ∀ j s, s<fib (j+2) → cost fib s≤cost fib (fib j+s))
    (N : ℕ) : total luc N≤total fib N := by
  have bound (k : ℕ) : ∀ r, r≤luc (k+4) → total luc r≤total fib r := by
    induction k with
    | zero =>
      intro r hi
      change r≤7 at hi
      interval_cases r <;> decide
    | succ k ih =>
      intro x hx
      change x≤luc (k+5) at hx
      by_cases lo : x≤luc (k+4)
      · exact ih x lo
      let r:=x-luc (k+4)
      have eq : x=luc (k+4)+r := by dsimp [r]; omega
      have ls : luc (k+5)=luc (k+4)+luc (k+3) := rfl
      have sm:=luc_mono.monotone (show k+3≤k+4 by omega)
      have hr:r≤luc (k+3) := by omega
      have lb:=block luc_mono (k+4) r (by change _ ≤ luc (k+5); omega) (hr.trans sm)
      have fb:=shifted_prefix localAdd k r hr
      have sub:=ih r (hr.trans sm)
      have equ:=equal_lucas (k+2)
      change total fib (luc (k+4))=total luc (luc (k+4)) at equ
      rw [eq,lb]
      omega
  exact bound N N (by have := luc_mono.id_le (N+4); omega)

end LucasPrefixes
#print axioms LucasPrefixes.bound_of_local
