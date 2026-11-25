import CeilingWitness
import CeilingSpacing
import ConsecutiveEnumeration
import GapChain
namespace CeilingBlocks
open LeastCarry CeilingWythoff

private theorem infiniteLang (m : Bool) : (setOf (lang m)).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  cases m with
  | false =>
    let j:=2*N+6
    let x:=weight [3,j]
    have z : digits x=[3,j] := identify _ ⟨by decide,⟨by dsimp [j]; omega,trivial⟩⟩
    have large : N<x := by
      have h:=Nat.le_fib_add_one (n:=j)
      change N<weight [3,j]
      simp only [weight_cons]
      dsimp [j] at *
      omega
    exact ⟨x,⟨by omega,(repeated_iff z).mpr ⟨by decide,by dsimp [j]; omega⟩⟩,large⟩
  | true =>
    let i:=2*N+4
    let x:=weight [i]
    have z : digits x=[i] := identify _ ⟨by dsimp [i]; omega,trivial⟩
    have large : N<x := by
      have h:=Nat.le_fib_add_one (n:=i)
      change N<weight [i]
      simp only [weight_cons]
      dsimp [i] at *
      omega
    exact ⟨x,⟨by omega,(singleCases z).2.mpr (by dsimp [i]; omega)⟩,large⟩

theorem exactGaps (m : Bool) (d : ℕ) : occurs m d ↔ allowed m d := by
  constructor
  · rintro ⟨n,hn,hd,hend,no⟩
    let k:=n+d+7
    have high : n+d<Nat.fib (k+2) := by
      have h:=Nat.le_fib_add_one (n:=k+2)
      dsimp [k] at *
      omega
    have head : n∈offsets m k 0 := (mem_offsets_source m k n).mpr ⟨by omega,hn⟩
    have last : n+d∈offsets m k 0 := (mem_offsets_source m k _).mpr ⟨high,hend⟩
    have pair := GapChain.extract (R:=step m) (fun h=>h.1) _ (steps k (by dsimp [k]; omega) m 0)
      head last (by omega) (fun z hh hz hy => by
        obtain ⟨_,hit⟩ := (mem_offsets_source m k z).mp hh
        have hh := no (z-n) (by omega) (by omega)
        rw [show n+(z-n)=z by omega] at hh
        exact hh hit)
    simpa only [Nat.add_sub_cancel_left] using pair.2
  · exact witness m d

theorem indexed (m : Bool) (d : ℕ) :
    (∃k, Nat.nth (lang m) (k+1)-Nat.nth (lang m) k=d) ↔ allowed m d :=
  (ConsecutiveEnumeration.differences (infiniteLang m) d).trans (exactGaps m d)

/-- A341261 is the increasing enumeration of positive repeated ceiling-array entries. -/
theorem A341261 (d : ℕ) :
    (∃k, Nat.nth (lang false) (k+1)-Nat.nth (lang false) k=d) ↔ d=3 ∨ d=5 ∨ d=10 ∨ d=13 := by
  simpa [allowed] using indexed false d
/-- A341262 is the increasing enumeration of positive integers missing from every source row. -/
theorem A341262 (d : ℕ) :
    (∃k, Nat.nth (lang true) (k+1)-Nat.nth (lang true) k=d) ↔ d=2 ∨ d=3 ∨ d=5 ∨ d=10 ∨ d=13 := by
  simpa [allowed] using indexed true d
end CeilingBlocks
#print axioms CeilingBlocks.A341261
#print axioms CeilingBlocks.A341262
