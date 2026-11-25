import LucasDominance
import Batteries.Tactic.OpenPrivate
open private LucasPrefixes.delta LucasPrefixes.delta_succ LucasPrefixes.balance from LucasPrefixes

namespace LucasZeroShape
open GreedyPrefix LucasZeros
private theorem late_cost (j s : ℕ) (hs:s<fib (j+2)) :
    cost fib (luc (j+4)+(fib j+s))=cost fib s+1 := by
  have l:=luc_fib (j+1)
  change luc (j+4)=fib (j+3)+fib (j+1) at l
  have a : fib (j+2)=fib (j+1)+fib j := rfl
  have b : fib (j+4)=fib (j+3)+fib (j+2) := rfl
  have c : fib (j+5)=fib (j+4)+fib (j+3) := rfl
  have sm:=fib_mono (show j+2<j+3 by omega)
  have sm':=fib_mono (show j+2<j+4 by omega)
  rw [show luc (j+4)+(fib j+s)=fib (j+4)+s by omega]
  exact leading fib_mono (j+4) s (by change _<fib (j+5); omega) (by omega)

private theorem descent (f : ℕ→ℤ) (a b : ℕ) (down : ∀i,a≤i→i<b→f (i+1)≤f i)
    (x y : ℕ) (hx:a≤x) (hxy:x≤y) (hy:y≤b) : f y≤f x := by
  obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le hxy
  induction k with
  | zero => simp
  | succ k ih => exact (down (x+k) (by omega) (by omega)).trans (ih (by omega) (by omega))

private theorem shape (f : ℕ→ℤ) (a b c : ℕ) (_hab:a≤b) (hbc:b<c)
    (h0:f 0=0) (hend:f c=0)
    (up:∀i,i<a→f i<f (i+1)) (down:∀i,a≤i→i<c→f (i+1)≤f i)
    (strict:f (b+1)<f b) (flat:∀i,b<i→i<c→f (i+1)=f i)
    (r:ℕ) (hr:r≤c) : f r=0 ↔ r=0 ∨ b+1≤r := by
  have z (x : ℕ) (h:b<x) (le:x≤c) : f x=0 := by
    have e1:=descent f (b+1) c (fun i hi lt => (flat i (by omega) lt).le) x c (by omega) le le_rfl
    have e2:=descent (fun i => -f i) (b+1) c (fun i hi lt => by dsimp only; rw [flat i (by omega) lt]) x c (by omega) le le_rfl
    dsimp at e2
    omega
  constructor
  · intro zero
    by_cases rz:r=0
    · exact Or.inl rz
    right
    by_contra no
    by_cases lo : r≤a
    · have e:=descent (fun i => -f i) 0 a (fun i _ hi => by dsimp only; have :=up i hi; omega) 1 r (by omega) (by omega) lo
      dsimp at e
      have rise : f 0<f 1:=up 0 (by omega)
      omega
    · have e:=descent f a c down r b (by omega) (by omega) (by omega)
      have lastz:=z (b+1) (by omega) (by omega)
      omega
  · rintro (rfl|hb)
    · exact h0
    · exact z r (by omega) hr

theorem zero_of_cut (j q r : ℕ) (hq:q<fib (j+2))
    (last:cost fib q<cost fib (fib j+q))
    (flat:∀s,q<s→s<fib (j+2)→cost fib (fib j+s)=cost fib s)
    (hr:r≤luc (j+3)) :
    (total fib (luc (j+4)+r)=total luc (luc (j+4)+r)) ↔
      (total fib r=total luc r ∧ (r=0 ∨ fib j+q+1≤r)) := by
  let L:=luc (j+4)
  let R:=luc (j+3)
  let f:=LucasPrefixes.delta L
  have l0:=luc_fib j
  have sign := shape f (fib j) (fib j+q) R (by omega) (by dsimp [R]; omega)
    (by simp [f,LucasPrefixes.delta,total]) (LucasPrefixes.balance j)
    (by
      intro i hi
      dsimp only [f,L]
      rw [LucasPrefixes.delta_succ,LucasPrefixes.early j i hi]
      push_cast
      omega)
    (by
      intro i hi hc
      dsimp only [f]
      rw [LucasPrefixes.delta_succ]
      have hl:=LucasPrefixes.late LocalZeck.local_add j i hi hc
      change cost fib (L+i)≤_ at hl
      omega)
    (by
      change LucasPrefixes.delta (luc (j+4)) ((fib j+q)+1)<_
      rw [LucasPrefixes.delta_succ,late_cost j q hq]
      push_cast
      change _<LucasPrefixes.delta (luc (j+4)) (fib j+q)
      omega)
    (by
      intro i hi hc
      let s:=i-fib j
      have eq : i=fib j+s := by dsimp [s]; omega
      have hs : s<fib (j+2) := by change i<luc (j+3) at hc; omega
      have v:=flat s (by omega) hs
      change LucasPrefixes.delta (luc (j+4)) (i+1)=_
      rw [LucasPrefixes.delta_succ,eq,late_cost j s hs,v]
      change _=LucasPrefixes.delta (luc (j+4)) (fib j+s)
      push_cast
      omega) r hr
  have sm:=luc_mono.monotone (show j+3≤j+4 by omega)
  have eq : luc (j+5)=luc (j+4)+luc (j+3) := rfl
  have bl:=block luc_mono (j+4) r (by change _≤luc (j+5); omega) (by omega)
  have pref:=LucasPrefixes.shifted_prefix LocalZeck.local_add j r hr
  have rem:=LucasPrefixes.bound_of_local LocalZeck.local_add r
  have endEq:=equal_lucas (j+2)
  change total fib (luc (j+4))=total luc (luc (j+4)) at endEq
  have sub : f r=(total fib (L+r):ℤ)-total fib L-total fib r-r := rfl
  change f r = (total fib (luc (j+4)+r):ℤ)-total fib (luc (j+4))-total fib r-r at sub
  constructor
  · intro overall
    exact ⟨by omega,sign.mp (by omega)⟩
  · rintro ⟨re,cut⟩
    have sf:=sign.mpr cut
    omega

end LucasZeroShape
#print axioms LucasZeroShape.zero_of_cut
