import Mathlib.Data.Nat.Nth
namespace ConsecutiveEnumeration

theorem infinite_hits {P : ℕ→Prop} (seed : ∃ n,P n) (more : ∀ n,P n → ∃ k,n<k ∧ P k) : (setOf P).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro b
  have ge : ∀t : ℕ, ∃n, t≤n ∧ P n := by
    intro t
    induction t with
    | zero => obtain ⟨n,h⟩ := seed; exact ⟨n,Nat.zero_le _,h⟩
    | succ t ih =>
      obtain ⟨n,hn,h⟩ := ih
      obtain ⟨k,hk,hp⟩ := more n h
      exact ⟨k,by omega,hp⟩
  obtain ⟨n,hn,h⟩ := ge (b+1)
  exact ⟨n,h,by omega⟩

theorem differences {P : ℕ→Prop} (inf : (setOf P).Infinite) (d : ℕ) :
    (∃ k, Nat.nth P (k+1)-Nat.nth P k=d) ↔
    ∃ n, P n ∧ 0<d ∧ P (n+d) ∧ ∀j, 0<j → j<d → ¬ P (n+j) := by
  have sm := Nat.nth_strictMono inf
  have mem := Nat.nth_mem_of_infinite inf
  constructor
  · rintro ⟨k,hd⟩
    have inc : Nat.nth P k<Nat.nth P (k+1) := sm (Nat.lt_succ_self k)
    refine ⟨Nat.nth P k,mem k,by omega,?_,?_⟩
    · rw [show Nat.nth P k+d=Nat.nth P (k+1) by omega]; exact mem _
    · intro j hj small h
      have := Nat.le_nth_of_lt_nth_succ (by omega : Nat.nth P k+j < Nat.nth P (k+1)) h
      omega
  · rintro ⟨n,hn,hd,hend,no⟩
    obtain ⟨k,hk⟩ := Nat.subset_range_nth hn
    obtain ⟨l,hl⟩ := Nat.subset_range_nth hend
    change Nat.nth P k=n at hk
    change Nat.nth P l=n+d at hl
    have less : k<l := sm.lt_iff_lt.mp (by omega)
    have adj : l=k+1 := by
      by_contra h
      have a := sm (by omega : k+1<l)
      have b : Nat.nth P k<Nat.nth P (k+1) := sm (Nat.lt_succ_self k)
      have e : n+(Nat.nth P (k+1)-n)=Nat.nth P (k+1) := by omega
      exact no _ (by omega) (by omega) (e.symm ▸ mem (k+1))
    exact ⟨k,by rw [←adj]; omega⟩
end ConsecutiveEnumeration
#print axioms ConsecutiveEnumeration.differences
