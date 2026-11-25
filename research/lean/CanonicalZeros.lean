import ZeroIndex
import Mathlib.Data.Nat.Nth

namespace CanonicalZeros
open LucasZeros ZeroEnumeration

/-- The source set for A214980, with positive indices only. -/
def isZero (n : ℕ) := 0<n ∧ V n=U n

/-- The n-th term in one-based indexing, for n>0. -/
noncomputable def a (n : ℕ) := Nat.nth isZero (n-1)

private theorem range_positive : Set.range (fun j => entry (j+1)) = {n | isZero n} := by
  ext n
  constructor
  · rintro ⟨j,rfl⟩
    have pos : 0<entry (j+1) := (Nat.zero_lt_succ j).trans_le (entry_strict.id_le _)
    exact ⟨pos,(source_range _ pos).mpr ⟨_,Nat.zero_lt_succ _,rfl⟩⟩
  · rintro ⟨hp,eq⟩
    obtain ⟨j,hj,he⟩ := (source_range n hp).mp eq
    exact ⟨j-1,by change entry (j-1+1)=n; rwa [show j-1+1=j by omega]⟩

private theorem sameEnumeration (f g : ℕ→ℕ) (hf : StrictMono f) (hg : StrictMono g)
    (hr : Set.range f=Set.range g) (n : ℕ) : f n=g n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases lt_trichotomy (f n) (g n) with h|h|h
    · obtain ⟨j,ej⟩ := hr ▸ (Set.mem_range_self n : f n ∈ Set.range f)
      have jn : j<n := hg.lt_iff_lt.mp (ej.trans_lt h)
      exact False.elim ((hf jn).ne ((ih j jn).trans ej))
    · exact h
    · obtain ⟨j,ej⟩ := hr.symm ▸ (Set.mem_range_self n : g n ∈ Set.range g)
      have jn : j<n := hf.lt_iff_lt.mp (ej.trans_lt h)
      exact False.elim ((hg jn).ne ((ih j jn).symm.trans ej))

theorem source_entry (n : ℕ) (hn : 0<n) : a n=entry n := by
  let f (j : ℕ) := entry (j+1)
  have hf : StrictMono f := entry_strict.comp (fun _ _ h => Nat.succ_lt_succ h)
  have inf : (setOf isZero).Infinite := by
    rw [←range_positive]
    exact Set.infinite_range_of_injective hf.injective
  have eq := sameEnumeration f (Nat.nth isZero) hf (Nat.nth_strictMono inf)
    (range_positive.trans (Nat.range_nth_of_infinite inf).symm) (n-1)
  simpa [a,f,show n-1+1=n by omega] using eq.symm

theorem source_recurrence (n : ℕ) (hn : 5≤n) :
    a (n+18)+4*a (n+6)=4*a (n+12)+a n := by
  rw [source_entry (n+18) (by omega),source_entry (n+6) (by omega),
    source_entry (n+12) (by omega),source_entry n (by omega)]
  exact sparse_recurrence _ hn
end CanonicalZeros
#print axioms CanonicalZeros.source_entry
#print axioms CanonicalZeros.source_recurrence
