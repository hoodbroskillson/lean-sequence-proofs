import GreedyPrefix

namespace LucasZeros
open GreedyPrefix

/-- Increasing positive Fibonacci weights, with the repeated 1 listed once. -/
def fib : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | n+2 => fib (n+1)+fib n

/-- Increasing Lucas weights: the first two classical Lucas numbers swap order. -/
def luc : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 4
  | n+4 => luc (n+3)+luc (n+2)

theorem fib_pos (n : ℕ) : 0<fib n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => decide
    | 1 => decide
    | k+2 => rw [fib]; have := ih k (by omega); omega

theorem fib_mono : StrictMono fib := by
  apply strictMono_nat_of_lt_succ
  intro n
  cases n with
  | zero => decide
  | succ k => rw [fib]; have := fib_pos k; omega

theorem luc_pos (n : ℕ) : 0<luc n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | 3 => decide
    | k+4 => rw [luc]; have := ih (k+2) (by omega); omega

theorem luc_mono : StrictMono luc := by
  apply strictMono_nat_of_lt_succ
  intro n
  match n with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | k+3 => rw [luc]; have := luc_pos (k+2); omega

theorem luc_fib (n : ℕ) : luc (n+3) = fib (n+2)+fib n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => decide
    | 1 => decide
    | k+2 =>
      have h0 := ih k (by omega)
      have h1 := ih (k+1) (by omega)
      have l : luc (k+5)=luc (k+4)+luc (k+3) := rfl
      have f : fib (k+4)=fib (k+3)+fib (k+2) := rfl
      have g : fib (k+2)=fib (k+1)+fib k := rfl
      simp only [Nat.add_assoc, Nat.reduceAdd] at *
      omega

private def D (n : ℕ) := total fib (fib n)

private theorem D_rec (n : ℕ) : D (n+2)=D (n+1)+D n+fib n := by
  exact block fib_mono (n+1) (fib n) (by rfl) (fib_mono.monotone (by omega))

private theorem v_expand (n : ℕ) :
    total fib (luc (n+3)) = D (n+2)+D n+fib n := by
  rw [luc_fib]
  apply block fib_mono
  · have e : fib (n+3)=fib (n+2)+fib (n+1) := rfl
    have z := fib_mono (show n<n+1 by omega)
    change fib (n+2)+fib n≤fib (n+3)
    omega
  · exact fib_mono.monotone (by omega)

private theorem luc_block (n : ℕ) :
    total luc (luc (n+5)) = total luc (luc (n+4))+total luc (luc (n+3))+luc (n+3) :=
  block luc_mono (n+4) (luc (n+3)) (by rfl) (luc_mono.monotone (by omega))

private theorem fib_block (n : ℕ) :
    total fib (luc (n+5)) = total fib (luc (n+4))+total fib (luc (n+3))+luc (n+3) := by
  have e2 := v_expand (n+2)
  have e1 := v_expand (n+1)
  have e0 := v_expand n
  have d2 := D_rec (n+2)
  have d0 := D_rec n
  have f : fib (n+2)=fib (n+1)+fib n := rfl
  have l := luc_fib n
  simp only [Nat.add_assoc, Nat.reduceAdd] at *
  omega

/-- The two literal greedy digit totals agree on [0,L_k) for all k≥2. -/
theorem equal_lucas (k : ℕ) : total fib (luc (k+2)) = total luc (luc (k+2)) := by
  cases k with
  | zero => decide
  | succ n =>
    change total fib (luc (n+3)) = total luc (luc (n+3))
    induction n using Nat.strong_induction_on with
    | h n ih =>
      match n with
      | 0 => decide
      | 1 => decide
      | k+2 =>
        have e1 := ih (k+1) (by omega)
        have e0 := ih k (by omega)
        rw [fib_block k,luc_block k,e1,e0]

/-- U(n) and V(n) count the summands through n inclusively, as in Kimberling's paper. -/
def U (n : ℕ) := total luc (n+1)
def V (n : ℕ) := total fib (n+1)

theorem equality_at_lucas_pred (k : ℕ) :
    V (luc (k+2)-1) = U (luc (k+2)-1) := by
  have h := luc_pos (k+2)
  simpa [U,V,Nat.sub_add_cancel (show 1≤luc (k+2) by omega)] using equal_lucas k

theorem unbounded_equalities (N : ℕ) : ∃ n, N<n ∧ V n=U n := by
  refine ⟨luc (N+2)-1,?_,equality_at_lucas_pred N⟩
  have h := luc_mono.id_le (N+2)
  omega

end LucasZeros
#print axioms LucasZeros.equality_at_lucas_pred
#print axioms LucasZeros.unbounded_equalities
