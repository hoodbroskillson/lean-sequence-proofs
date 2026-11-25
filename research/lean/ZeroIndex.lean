import ZeroEnumeration
import LucasEqualitySet

namespace ZeroEnumeration
open LucasZeros

private def sixValues (a b n : ℕ) : Prop :=
  n+2=a ∨ n+1=a ∨ n+5=b ∨ n+3=b ∨ n+2=b ∨ n+1=b

private theorem gap (k : ℕ) : luc (k+5)+5 ≤ luc (k+6) := by
  have e : luc (k+6)=luc (k+5)+luc (k+4) := rfl
  have h := luc_mono.monotone (show 4≤k+4 by omega)
  have c : luc 4=7 := rfl
  omega

private theorem block_source (t n : ℕ)
    (lo : luc (2*t+6)-2≤n) (hi : n<luc (2*t+8)-2) :
    V n=U n ↔ sixValues (luc (2*t+6)) (luc (2*t+7)) n := by
  let k := 2*t
  change luc (k+6)-2≤n at lo
  change n<luc (k+8)-2 at hi
  change _ ↔ sixValues (luc (k+6)) (luc (k+7)) n
  unfold sixValues
  have a := gap k
  have b := gap (k+1)
  have c := gap (k+2)
  simp only [Nat.add_assoc,Nat.reduceAdd] at a b c
  by_cases ha : n+1<luc (k+6)
  · have h := LucasZeroSet.source (k+5) n (by omega) (by exact ha)
    have p : (k+5)%2=1 := by dsimp [k]; omega
    rw [h]
    simp only [Nat.add_assoc,Nat.reduceAdd,p,true_and,false_and,or_false]
    clear h p
    constructor <;> intro hh <;> omega
  by_cases hb : n+1<luc (k+7)
  · have h := LucasZeroSet.source (k+6) n (by omega) hb
    have p : (k+6)%2=0 := by dsimp [k]; omega
    rw [h]
    simp only [Nat.add_assoc,Nat.reduceAdd,p,true_and,false_and,or_false]
    clear h p
    constructor <;> intro hh <;> omega
  · have h := LucasZeroSet.source (k+7) n (by omega) (by change n+1<luc (k+8); omega)
    have p : (k+7)%2=1 := by dsimp [k]; omega
    rw [h]
    simp only [Nat.add_assoc,Nat.reduceAdd,p,true_and,false_and,or_false]
    clear h p
    constructor <;> intro hh <;> omega

private theorem sizes (t : ℕ) : 5 ≤ luc (2*t+6) ∧ 5 ≤ luc (2*t+7) := by
  have a := luc_mono.monotone (show 4≤2*t+6 by omega)
  have b := luc_mono.monotone (show 4≤2*t+7 by omega)
  have c : luc 4=7 := rfl
  omega

private theorem first_slots (t : ℕ) :
    term t 0=luc (2*t+6)-2 ∧ term t 1=luc (2*t+6)-1 ∧ term t 2=luc (2*t+7)-5 ∧
    term t 3=luc (2*t+7)-3 ∧ term t 4=luc (2*t+7)-2 ∧ term t 5=luc (2*t+7)-1 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

private theorem slot_iff (t n : ℕ) :
    sixValues (luc (2*t+6)) (luc (2*t+7)) n ↔ ∃ j, j<6 ∧ term t j=n := by
  have b := sizes t
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := first_slots t
  unfold sixValues
  constructor
  · rintro (h|h|h|h|h|h)
    · exact ⟨0,by decide,by omega⟩
    · exact ⟨1,by decide,by omega⟩
    · exact ⟨2,by decide,by omega⟩
    · exact ⟨3,by decide,by omega⟩
    · exact ⟨4,by decide,by omega⟩
    · exact ⟨5,by decide,by omega⟩
  · rintro ⟨j,hj,h⟩
    have choices : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
    rcases choices with e|e|e|e|e|e <;> subst j <;> omega

/-- Exactly six of the source indices in each complete Lucas pair are zeros. -/
theorem block_iff (t n : ℕ) (lo : luc (2*t+6)-2 ≤ n) (hi : n < luc (2*t+8)-2) :
    V n=U n ↔ ∃ j, j<6 ∧ entry (6*t+j+9)=n := by
  rw [block_source t n lo hi,slot_iff]
  constructor <;> rintro ⟨j,hj,h⟩
  · exact ⟨j,hj,(six t j hj).trans h⟩
  · exact ⟨j,hj,(six t j hj).symm.trans h⟩

private theorem slots_ordered (t j : ℕ) (hj : j<6) :
    term t j < (if j=5 then term (t+1) 0 else term t (j+1)) := by
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := first_slots t
  have hn := (first_slots (t+1)).1
  rw [show 2*(t+1)+6=2*t+8 by omega] at hn
  have b := sizes t
  have h67 := gap (2*t+1)
  have h78 := gap (2*t+2)
  simp only [Nat.add_assoc, Nat.reduceAdd] at h67 h78
  have choices : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases choices with e|e|e|e|e|e <;> subst j <;> norm_num <;> omega

theorem entry_strict : StrictMono entry := by
  apply strictMono_nat_of_lt_succ
  intro n
  by_cases small : n<9
  · have test : ∀ i : Fin 9, entry i.val < entry (i.val+1) := by decide
    exact test ⟨n,small⟩
  let t := (n-9)/6
  let j := (n-9)%6
  have hj : j<6 := Nat.mod_lt _ (by decide)
  have en : n=6*t+j+9 := by dsimp [t,j]; omega
  have before := (six t j hj).symm
  rw [←en] at before
  rw [←before]
  have ord := slots_ordered t j hj
  by_cases last : j=5
  · rw [if_pos last] at ord
    rw [show n+1=6*(t+1)+0+9 by omega,six (t+1) 0 (by decide)]
    exact ord
  · rw [if_neg last] at ord
    rw [show n+1=6*t+(j+1)+9 by omega,six t (j+1) (by omega)]
    exact ord

private theorem bands (n : ℕ) (hn : 16≤n) :
    ∃ t, luc (2*t+6)-2≤n ∧ n<luc (2*t+8)-2 := by
  have ex : ∃t, n<luc (2*t+8)-2 := by
    refine ⟨n,?_⟩
    have h := luc_mono.id_le (2*n+8)
    omega
  let t := Nat.find ex
  refine ⟨t,?_,Nat.find_spec ex⟩
  cases et : t with
  | zero => exact hn
  | succ k =>
    have bad := Nat.find_min ex (show k<t by omega)
    change ¬n<luc (2*k+8)-2 at bad
    rw [show 2*(k+1)+6=2*k+8 by omega]
    omega

/-- Entries 1,2,... enumerate all the positive indices of equality in increasing order. -/
theorem source_range (n : ℕ) (hn : 0<n) : V n=U n ↔ ∃ m, 0<m ∧ entry m=n := by
  by_cases h : n<16
  · have base : ∀ j : Fin 16, 0<j.val →
        (V j.val=U j.val ↔ ∃ i : Fin 9, 0<i.val ∧ entry i.val=j.val) := by decide
    have g := base ⟨n,h⟩ hn
    constructor
    · intro eq
      obtain ⟨i,hi,he⟩ := g.mp eq
      exact ⟨i.val,hi,he⟩
    · rintro ⟨m,hm,he⟩
      have max : m<9 := by
        by_contra! bad
        have cmp := entry_strict.monotone bad
        have nine : entry 9=16 := rfl
        omega
      exact g.mpr ⟨⟨m,max⟩,hm,he⟩
  obtain ⟨t,lo,hi⟩ := bands n (by omega)
  rw [block_iff t n lo hi]
  constructor
  · rintro ⟨j,hj,he⟩
    exact ⟨6*t+j+9,by omega,he⟩
  · rintro ⟨m,_,he⟩
    have b0 : entry (6*t+9)=luc (2*t+6)-2 := by
      simpa using (six t 0 (by decide)).trans (first_slots t).1
    have b1 : entry (6*t+15)=luc (2*t+8)-2 := by
      have z := (six (t+1) 0 (by decide)).trans (first_slots (t+1)).1
      rw [show 6*(t+1)+0+9=6*t+15 by omega,show 2*(t+1)+6=2*t+8 by omega] at z
      exact z
    have lb : 6*t+9≤m := by
      by_contra! bad
      have z := entry_strict bad
      omega
    have ub : m<6*t+15 := by
      by_contra! bad
      have z := entry_strict.monotone bad
      omega
    refine ⟨m-(6*t+9),by omega,?_⟩
    rw [show 6*t+(m-(6*t+9))+9=m by omega,he]

end ZeroEnumeration
#print axioms ZeroEnumeration.block_iff

#print axioms ZeroEnumeration.entry_strict
#print axioms ZeroEnumeration.source_range
