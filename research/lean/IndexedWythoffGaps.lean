import StolarskyGaps
import ConsecutiveEnumeration
namespace Stolarsky
noncomputable section

def positiveHits (c : ℤ) (n : ℕ) := 1≤n ∧ delta n=c
/-- Zero-based enumerator of positive positions: index 0 is OEIS term 1. -/
def positions (c : ℤ) := Nat.nth (positiveHits c)
private theorem indexed {c : ℤ} {w : ℕ} (seed : gap c w)
    (step : ∀ n,delta n=c → ∃e, returns (fun j => delta j=c) n e) (d : ℕ) :
    (∃k, positions c (k+1)-positions c k=d) ↔ gap c d := by
  obtain ⟨n,hn,hc,_⟩ := seed
  have inf : (setOf (positiveHits c)).Infinite := by
    apply ConsecutiveEnumeration.infinite_hits ⟨n,hn,hc⟩
    rintro x ⟨hp,hx⟩
    obtain ⟨e,he,hit,_⟩ := step x hx
    exact ⟨x+e,by omega,by change 1≤x+e ∧ delta (x+e)=c; exact ⟨by omega,hit⟩⟩
  unfold positions
  rw [ConsecutiveEnumeration.differences inf d]
  constructor
  · rintro ⟨x,⟨hp,hx⟩,hd,⟨_,hit⟩,no⟩
    exact ⟨x,hp,hx,hd,hit,fun j h1 h2 hj => no j h1 h2 ⟨by omega,hj⟩⟩
  · rintro ⟨x,hp,hx,hd,hit,no⟩
    exact ⟨x,⟨hp,hx⟩,hd,⟨by omega,hit⟩,fun j h1 h2 hj => no j h1 h2 hj.2⟩

theorem A387349 (d : ℕ) : (∃k,positions 0 (k+1)-positions 0 k=d) ↔ d=1 ∨ d=2 ∨ d=3 := by
  apply Iff.trans _ (middleGaps d)
  apply indexed ((middleGaps 1).mpr (by omega))
  intro n h
  obtain ⟨e,_,he⟩ := middleNext n h
  exact ⟨e,he⟩

theorem A387350 (d : ℕ) : (∃k,positions 1 (k+1)-positions 1 k=d) ↔ d=2 ∨ d=3 ∨ d=5 := by
  apply Iff.trans _ (plusGaps d)
  apply indexed ((plusGaps 2).mpr (by omega))
  intro n h
  obtain ⟨e,_,he⟩ := plusNext n h
  exact ⟨e,he⟩

theorem A387351 (d : ℕ) : (∃k,positions (-1) (k+1)-positions (-1) k=d) ↔ d=3 ∨ d=5 ∨ d=8 := by
  apply Iff.trans _ (minusGaps d)
  apply indexed ((minusGaps 3).mpr (by omega))
  intro n h
  obtain ⟨e,_,he⟩ := minusNext n h
  exact ⟨e,he⟩
end
end Stolarsky
#print axioms Stolarsky.A387349
#print axioms Stolarsky.A387350
#print axioms Stolarsky.A387351
