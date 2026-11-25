import LucasZeros
namespace LocalZeck
open GreedyPrefix LucasZeros

/-- Adding a Fibonacci weight does not decrease the number of summands when the
    starting integer is below the Fibonacci weight two places later. -/
theorem local_add (j s : ℕ) (hs : s < fib (j+2)) :
    cost fib s ≤ cost fib (fib j+s) := by
  induction j using Nat.strong_induction_on generalizing s with
  | h j ih =>
    match j with
    | 0 =>
      have test : ∀ t : Fin 3, cost fib t.val ≤ cost fib (fib 0+t.val) := by decide
      exact test ⟨s,hs⟩
    | 1 =>
      have test : ∀ t : Fin 5, cost fib t.val ≤ cost fib (fib 1+t.val) := by decide
      exact test ⟨s,hs⟩
    | k+2 =>
      change s < fib (k+4) at hs
      have order (i : ℕ) : fib i < fib (i+1) := fib_mono (by omega)
      have p0 := order k
      have p1 := order (k+1)
      have p2 := order (k+2)
      have p3 := order (k+3)
      have h2 : fib (k+2)=fib (k+1)+fib k := rfl
      have h3 : fib (k+3)=fib (k+2)+fib (k+1) := rfl
      have h4 : fib (k+4)=fib (k+3)+fib (k+2) := rfl
      have h5 : fib (k+5)=fib (k+4)+fib (k+3) := rfl
      simp only [Nat.add_assoc,Nat.reduceAdd] at p1 p2 p3
      by_cases low : s<fib (k+1)
      · have e := leading fib_mono (k+2) s (by change _<fib (k+3); omega) (by omega)
        omega
      by_cases mid : s<fib (k+2)
      · let u := s-fib (k+1)
        have hu : s=fib (k+1)+u := by dsimp [u]; omega
        have hz := leading fib_mono (k+1) u (by change _<fib (k+2); omega) (by omega)
        have hz' := leading fib_mono (k+3) u (by change _<fib (k+4); omega) (by omega)
        rw [hu,hz,show fib (k+2)+(fib (k+1)+u)=fib (k+3)+u by omega,hz']
      by_cases next : s<fib (k+3)
      · let u := s-fib (k+2)
        have hu : s=fib (k+2)+u := by dsimp [u]; omega
        have hz := leading fib_mono (k+2) u (by change _<fib (k+3); omega) (by omega)
        have hz' := leading fib_mono (k+3) (fib k+u) (by change _<fib (k+4); omega) (by omega)
        have smaller := ih k (by omega) u (by omega)
        rw [hu,hz,show fib (k+2)+(fib (k+2)+u)=fib (k+3)+(fib k+u) by omega,hz']
        omega
      · let u := s-fib (k+3)
        have hu : s=fib (k+3)+u := by dsimp [u]; omega
        have hz := leading fib_mono (k+3) u (by change _<fib (k+4); omega) (by omega)
        have hz' := leading fib_mono (k+4) u (by change _<fib (k+5); omega) (by omega)
        rw [hu,hz,show fib (k+2)+(fib (k+3)+u)=fib (k+4)+u by omega,hz']

end LocalZeck
#print axioms LocalZeck.local_add
