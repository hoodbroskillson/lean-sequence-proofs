import FamilyCount
open private MexFamily.rank MexFamily.rank_spec MexFamily.partition_rank from FamilyCount
namespace MexFamily
variable (q : Params)

def W (n : ℕ) := q.s*n+C q n

/-- Every complete source block begins with s lower-column letters. -/
theorem forward (n r : ℕ) (hr : r≤q.s) : C q (W q n+r)=q.s*n+r := by
  let N:=W q n+r
  have split:=MexFamily.partition_rank q N
  have c:=C_spec q n
  have z:=MexFamily.rank_spec (strictB q) (starts q).2.1 N
  have p : B q (C q n)≤N := by
    dsimp [N,W,B]
    have :=Nat.mul_le_mul_left q.s c.1
    omega
  have h : N<B q (C q n+1) := by
    dsimp [N,W,B]
    have v:=Nat.mul_le_mul_left q.s (show n+1≤A q (C q n+1) by omega)
    rw [Nat.mul_add,Nat.mul_one] at v
    omega
  have eq : MexFamily.rank (B q) N=C q n := by
    rcases lt_trichotomy (MexFamily.rank (B q) N) (C q n) with lt|eq|gt
    · have := (strictB q).monotone (show MexFamily.rank (B q) N+1≤C q n by omega);omega
    · exact eq
    · have := (strictB q).monotone (show C q n+1≤MexFamily.rank (B q) N by omega);omega
  rw [eq] at split
  change C q N=_;dsimp [N,W] at split ⊢;omega

theorem nextA (n : ℕ) : C q (W q n+1)=C q (W q n)+1 := by
  have a:=forward q n 0 (Nat.zero_le _)
  have b:=forward q n 1 (by have :=q.ge;omega)
  simp only [Nat.add_zero] at a
  omega

theorem after_full (n : ℕ) : C q (W q n+q.s+1)=q.s*(n+1)+(1-(C q (n+1)-C q n)) := by
  have a:=C_succ q n
  have b : C q n≤C q (n+1) := C_mono q (Nat.le_succ n)
  by_cases ch : C q (n+1)=C q n
  · have w : W q n+q.s=W q (n+1) := by unfold W;rw [ch,Nat.mul_add,Nat.mul_one];omega
    rw [w,forward q (n+1) 1 (by have:=q.ge;omega),ch,Nat.sub_self,Nat.sub_zero]
  · have s : C q (n+1)=C q n+1 := by omega
    have w : W q n+q.s+1=W q (n+1) := by unfold W;rw [s,Nat.mul_add,Nat.mul_one];omega
    rw [w,s]
    have f:=forward q (n+1) 0 (Nat.zero_le _)
    simp only [Nat.add_zero] at f
    rw [f];omega
end MexFamily
#print axioms MexFamily.forward
#print axioms MexFamily.after_full
