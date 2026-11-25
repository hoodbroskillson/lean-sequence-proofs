import FamilyMex
open private MexFamily.sets MexFamily.mex MexFamily.mex_fresh MexFamily.mex_fills from FamilyMex
namespace MexFamily
namespace Witness

def two : Params := ⟨2, by decide⟩
open Finset
/-- Finite certificate for a prefix of the MexFamily.mex construction. -/
private def certified : ℕ → Finset ℕ → List ℕ → Bool
  | _, _, [] => true
  | n, u, a::as => decide (a∉u) && (List.range a).all (fun x=>decide (x∈u)) &&
      certified (n+1) (insert a (insert (2*a+n) u)) as

private theorem certified_value (n : ℕ) (xs : List ℕ) (ok : certified n (MexFamily.sets two n) xs = true)
    (i : ℕ) (hi : i<xs.length) : xs.get? i=some (A two (n+i)) := by
  induction xs generalizing n i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [certified,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at ok
    rcases ok with ⟨⟨fresh,fill⟩,tail⟩
    have eq : MexFamily.mex (MexFamily.sets two n)=a := by
      apply le_antisymm
      · by_contra! h
        exact fresh (MexFamily.mex_fills _ h)
      · by_contra! h
        exact MexFamily.mex_fresh _ (fill _ (List.mem_range.mpr h))
    cases i with
    | zero => simp [A,eq]
    | succ i =>
      have next : certified (n+1) (MexFamily.sets two (n+1)) xs=true := by
        change certified (n+1) (insert (MexFamily.mex (MexFamily.sets two n)) (insert (2*MexFamily.mex (MexFamily.sets two n)+n) (MexFamily.sets two n))) xs=true
        rw [eq]; exact tail
      have rec := ih (n+1) next i (by simpa using hi)
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using rec

private def sample := [0,1,2,4,5,7,8,9,10,12,13,15,16,17,18,20,21,23,24,26,27,29,30,31,32,34,35,37,38,39,40,42,43,45,46,48,49,51,52,53,54,56,57,59,60,61,62,64,65,67,68,69,70,72,73,75,76,77,78]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem sample_ok : certified 0 (MexFamily.sets two 0) sample=true := by decide

theorem lower_witness : (A two (14+21)-A two 14) - (A two (37+21)-A two 37) = 3 := by
  have h₁ := certified_value 0 sample sample_ok 14 (by decide)
  have h₂ := certified_value 0 sample sample_ok 35 (by decide)
  have h₃ := certified_value 0 sample sample_ok 37 (by decide)
  have h₄ := certified_value 0 sample sample_ok 58 (by decide)
  change some 18=some (A two 14) at h₁
  change some 48=some (A two 35) at h₂
  change some 51=some (A two 37) at h₃
  change some 78=some (A two 58) at h₄
  change A two 35-A two 14-(A two 58-A two 37)=3
  simp only [Option.some.injEq] at h₁ h₂ h₃ h₄
  omega
end Witness
end MexFamily
#print axioms MexFamily.Witness.lower_witness
