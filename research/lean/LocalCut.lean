import LocalZeck

namespace LocalCut
open GreedyPrefix LucasZeros

/-- The last starting integer below fib(j+2) where adding fib(j) raises the digit count. -/
def lastIndex : ℕ → ℕ
  | 0 => 0
  | 1 => 2
  | k+2 => fib (k+2)+lastIndex k

theorem last_formula (j : ℕ) : lastIndex j = fib (j+1) - (if j%2=0 then 2 else 1) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    match j with
    | 0 => decide
    | 1 => decide
    | k+2 =>
      have h := ih k (by omega)
      have he : (k+2)%2=k%2 := by omega
      have hf : fib (k+3)=fib (k+2)+fib (k+1) := rfl
      have g := fib_mono.monotone (show 1≤k+1 by omega)
      change 2≤fib (k+1) at g
      change lastIndex (k+2)=fib (k+3) - (if (k+2)%2=0 then 2 else 1)
      rw [lastIndex,h,he,hf]
      split <;> omega

theorem last_lt_next (j : ℕ) : lastIndex j < fib (j+1) := by
  rw [last_formula]
  have p := fib_pos (j+1)
  split <;> omega

theorem last_lt (j : ℕ) : lastIndex j < fib (j+2) :=
  lt_trans (last_lt_next j) (fib_mono (by omega))

/-- The middle interval of the Fibonacci addition rule reduces the index by two. -/
private theorem middle (k u : ℕ) (hu : u < fib (k+1)) :
    cost fib (fib (k+2)+u) = cost fib u + 1 ∧
    cost fib (fib (k+2)+(fib (k+2)+u)) = cost fib (fib k+u) + 1 := by
  have f2 : fib (k+2)=fib (k+1)+fib k := rfl
  have f3 : fib (k+3)=fib (k+2)+fib (k+1) := rfl
  have f4 : fib (k+4)=fib (k+3)+fib (k+2) := rfl
  constructor
  · apply leading fib_mono
    · change fib (k+2)+u < fib (k+3)
      omega
    · omega
  · rw [show fib (k+2)+(fib (k+2)+u)=fib (k+3)+(fib k+u) by omega]
    apply leading fib_mono
    · change fib (k+3)+(fib k+u)<fib (k+4)
      omega
    · omega

theorem last (j : ℕ) :
    cost fib (lastIndex j) < cost fib (fib j+lastIndex j) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    match j with
    | 0 => decide
    | 1 => decide
    | k+2 =>
      rw [lastIndex]
      obtain ⟨h0,h1⟩ := middle k (lastIndex k) (last_lt_next k)
      rw [h0,h1]
      exact Nat.add_lt_add_right (ih k (by omega)) 1

theorem flat (j s : ℕ) (hs : lastIndex j < s) (ht : s < fib (j+2)) :
    cost fib (fib j+s)=cost fib s := by
  induction j using Nat.strong_induction_on generalizing s with
  | h j ih =>
    match j with
    | 0 =>
      have test : ∀ i : Fin 3, lastIndex 0 < i.val →
          cost fib (fib 0+i.val)=cost fib i.val := by decide
      exact test ⟨s,ht⟩ hs
    | 1 =>
      have test : ∀ i : Fin 5, lastIndex 1 < i.val →
          cost fib (fib 1+i.val)=cost fib i.val := by decide
      exact test ⟨s,ht⟩ hs
    | k+2 =>
      change s<fib (k+4) at ht
      rw [lastIndex] at hs
      have f3 : fib (k+3)=fib (k+2)+fib (k+1) := rfl
      have f4 : fib (k+4)=fib (k+3)+fib (k+2) := rfl
      have f5 : fib (k+5)=fib (k+4)+fib (k+3) := rfl
      by_cases h : s<fib (k+3)
      · let u := s-fib (k+2)
        have eu : s=fib (k+2)+u := by dsimp [u]; omega
        have ub : u<fib (k+1) := by omega
        obtain ⟨h0,h1⟩ := middle k u ub
        have up : u<fib (k+2) := lt_trans ub (fib_mono (by omega))
        rw [eu,h1,h0,ih k (by omega) u (by omega) up]
      · let u := s-fib (k+3)
        have eu : s=fib (k+3)+u := by dsimp [u]; omega
        have h0 := leading fib_mono (k+3) u (by change _<fib (k+4); omega) (by omega)
        have h1 := leading fib_mono (k+4) u (by change _<fib (k+5); omega) (by omega)
        rw [eu,h0,show fib (k+2)+(fib (k+3)+u)=fib (k+4)+u by omega,h1]

theorem first_formula (j : ℕ) : fib j+lastIndex j+1 =
    fib (j+2) - (if j%2=0 then 1 else 0) := by
  rw [last_formula,show fib (j+2)=fib (j+1)+fib j by rfl]
  have g := fib_mono.monotone (show 1≤j+1 by omega)
  change 2≤fib (j+1) at g
  split <;> omega

end LocalCut
#print axioms LocalCut.last
#print axioms LocalCut.flat
#print axioms LocalCut.first_formula
