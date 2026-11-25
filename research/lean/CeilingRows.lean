import CeilingShift
namespace CeilingWythoff

private theorem snoc (bs : List Bool) (b : Bool) (s : ℕ) :
    value (bs++[b]) s = value bs s + if b then Nat.fib (s+bs.length) else 0 := by
  induction bs generalizing s with
  | nil => simp [value]
  | cons a as ih =>
    simp only [List.cons_append,List.length_cons,value]
    have e := ih (s+1)
    change _ + value (as++[b]) (s+1) = _
    rw [e]
    rw [show s+1+as.length=s+(as.length+1) by omega]
    exact (Nat.add_assoc _ _ _).symm

private theorem represent (k : ℕ) : ∀n, n<Nat.fib (k+2) → ∃bs : List Bool, bs.length=k ∧ value bs 2=n := by
  induction k with
  | zero =>
    intro n hn
    have f : Nat.fib 2=1 := rfl
    rw [f] at hn
    exact ⟨[],rfl,by change 0=n; omega⟩
  | succ k ih =>
    intro n hn
    by_cases h : n<Nat.fib (k+2)
    · obtain ⟨bs,l,v⟩ := ih _ h
      refine ⟨bs++[false],by simp [l],?_⟩
      simpa only [snoc,Bool.false_eq_true,if_false,Nat.add_zero] using v
    · have hsum : Nat.fib (k+1+2)=Nat.fib (k+1)+Nat.fib (k+2) := Nat.fib_add_two
      have le := Nat.fib_mono (show k+1≤k+2 by omega)
      obtain ⟨bs,l,v⟩ := ih (n-Nat.fib (k+2)) (by omega)
      refine ⟨bs++[true],by simp [l],?_⟩
      rw [snoc,if_pos rfl,l,v,show 2+k=k+2 by omega]
      omega

/-- Every source row has a single binary word that generates every column. -/
theorem everyRow (n : ℕ) (hn : 1≤n) : ∃bs : List Bool, value bs 2=n-1 ∧ ∀k:ℕ,
    entry n k = (2*Nat.fib (k+1)+value bs (2+k+1):ℕ) := by
  have z := Nat.le_fib_add_one (n:=n+2)
  obtain ⟨bs,_,h⟩ := represent n (n-1) (by omega)
  refine ⟨bs,h,fun k => ?_⟩
  have d : value bs 2+1=n := by omega
  rw [←d,sourceDigital]
end CeilingWythoff
#print axioms CeilingWythoff.everyRow
