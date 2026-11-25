import AllZeros
import LucasZeroBlock
namespace LucasZeroSet
open LucasZeros GreedyPrefix

theorem all (i x : ℕ) (lo : luc i≤x) (up : x<luc (i+1)) : EqualAt x ↔ Near i x :=
  all_of_blocks (fun j r h => LucasZeroBlock.zero_iff j r h) i x lo up

/-- The OEIS index n is inclusive, so x=n+1. The block at the left contains
its endpoint and excludes the next one, without duplicating any index. -/
theorem source (i n : ℕ) (lo : luc i≤n+1) (up : n+1<luc (i+1)) :
    V n=U n ↔ n+1=luc i ∨ n+2=luc (i+1) ∨
      (i%2=0 ∧ (n+3=luc (i+1) ∨ n+5=luc (i+1))) := all i (n+1) lo up

theorem covers (n : ℕ) : ∃i, luc i≤n+1 ∧ n+1<luc (i+1) := by
  classical
  have ex : ∃j, n+1<luc j := ⟨n+2,by have := luc_mono.id_le (n+2); omega⟩
  let j := Nat.find ex
  have gt : n+1<luc j := Nat.find_spec ex
  have jpos : 0<j := by
    by_contra! z
    have eq : j=0 := by omega
    rw [eq] at gt
    change n+1<1 at gt
    omega
  obtain ⟨i,hi⟩ := Nat.exists_eq_succ_of_ne_zero jpos.ne'
  have before := Nat.find_min ex (show i<j by omega)
  exact ⟨i,by omega,by simpa only [hi] using gt⟩
end LucasZeroSet
#print axioms LucasZeroSet.source
#print axioms LucasZeroSet.covers
