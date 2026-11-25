import CeilingOffsetsBridge
namespace CeilingBlocks

/-- Positive source integers absent from the array, or occurring twice. -/
def lang (m : Bool) (n : ℕ) := 0<n ∧ (if m then CeilingWythoff.missing n else CeilingWythoff.repeated n)

/-- Consecutive-gap occurrence in the actual positive source language. -/
def occurs (m : Bool) (d : ℕ) := ∃n, lang m n ∧ 0<d ∧ lang m (n+d) ∧
    ∀j, 0<j → j<d → ¬lang m (n+j)

private theorem certify (m : Bool) (n d : ℕ) (last : n+d<89)
    (a : n∈offsets m 9 0) (p : 0<d) (b : n+d∈offsets m 9 0)
    (f : ∀j:Fin d, 0<j.val → n+j.val∉offsets m 9 0) : occurs m d := by
  have F : Nat.fib (9+2)=89 := by decide
  refine ⟨n,((mem_offsets_source m 9 n).mp a).2,p,((mem_offsets_source m 9 (n+d)).mp b).2,?_⟩
  intro j j0 jd h
  exact f ⟨j,jd⟩ j0 ((mem_offsets_source m 9 _).mpr ⟨by rw [F];omega,h⟩)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem witness (m : Bool) (d : ℕ) :
    ((m=true ∧ d=2) ∨ d=3 ∨ d=5 ∨ d=10 ∨ d=13) → occurs m d := by
  cases m
  · rintro (⟨im,_⟩|rfl|rfl|rfl|rfl)
    · contradiction
    · apply certify false 23 3 <;> decide
    · apply certify false 26 5 <;> decide
    · apply certify false 68 10 <;> decide
    · apply certify false 10 13 <;> decide
  · rintro (⟨_,rfl⟩|rfl|rfl|rfl|rfl)
    · apply certify true 1 2 <;> decide
    · apply certify true 8 3 <;> decide
    · apply certify true 3 5 <;> decide
    · apply certify true 11 10 <;> decide
    · apply certify true 32 13 <;> decide

end CeilingBlocks
#print axioms CeilingBlocks.witness
