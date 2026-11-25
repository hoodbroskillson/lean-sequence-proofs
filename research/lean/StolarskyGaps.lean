import StolarskyCode
import Mathlib.Tactic.IntervalCases
namespace Stolarsky
noncomputable section
def arc (l u : ℝ) (n : ℕ) := l≤phase n ∧ phase n<u
def returns (P : ℕ→Prop) (n d : ℕ) := 0<d ∧ P (n+d) ∧ ∀ j,0<j → j<d → ¬P (n+j)

private theorem phase_formula (n : ℕ) : phase n = (n:ℝ)*phi-(⌊(n:ℝ)*phi⌋:ℝ) := rfl

private theorem atShift (n j : ℕ) (k : ℤ) :
    phase (n+j)=phase n + (j:ℝ)*phi-k ↔
      0≤phase n + (j:ℝ)*phi-k ∧ phase n + (j:ℝ)*phi-k<1 := by
  constructor
  · intro h; rw [←h]; exact ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩
  · rintro ⟨hl,hu⟩
    apply Int.fract_eq_iff.mpr
    refine ⟨hl,hu,⌊(n:ℝ)*phi⌋+k,?_⟩
    rw [phase_formula,Nat.cast_add,Int.cast_add]
    ring

private theorem inside (l u : ℝ) (n j : ℕ) (k : ℤ) (hl : 0≤l) (hu : u≤1)
    (h1 : (k:ℝ)+l ≤phase n+(j:ℝ)*phi) (h2 : phase n+(j:ℝ)*phi<(k:ℝ)+u) :
    arc l u (n+j) := by
  unfold arc
  rw [(atShift n j k).mpr ⟨by linarith,by linarith⟩]
  constructor <;> linarith

private theorem outside (l u : ℝ) (n j : ℕ) (k : ℤ)
    (h1 : (k:ℝ)+u≤phase n+(j:ℝ)*phi) (h2 : phase n+(j:ℝ)*phi<(k:ℝ)+1+l) :
    ¬arc l u (n+j) := by
  rintro ⟨lo,hi⟩
  let s : ℤ := ⌊((n+j:ℕ):ℝ)*phi⌋-⌊(n:ℝ)*phi⌋
  have e : phase (n+j) = phase n + (j:ℝ)*phi - s := by
    rw [phase_formula,phase_formula]
    change _ = _ - ((⌊((n+j:ℕ):ℝ)*phi⌋ - ⌊(n:ℝ)*phi⌋:ℤ):ℝ)
    rw [Int.cast_sub,Nat.cast_add]
    ring
  have a : (k:ℝ)<(s:ℝ) := by linarith
  have b : (s:ℝ)<((k+1:ℤ):ℝ) := by push_cast; linarith
  have a' : k<s := by exact_mod_cast a
  have b' : s<k+1 := by exact_mod_cast b
  omega

theorem plus (n : ℕ) : delta n=1 ↔ arc 0 ((phi-1)/2) n := by
  rw [code]; unfold colour arc
  have := Int.fract_nonneg ((n:ℝ)*phi)
  change 0≤phase n at this
  split_ifs <;> simp_all

theorem middle (n : ℕ) : delta n=0 ↔ arc ((phi-1)/2) (phi/2) n := by
  rw [code]; unfold colour arc
  split_ifs <;> simp_all

theorem minus (n : ℕ) : delta n = -1 ↔ arc (phi/2) 1 n := by
  rw [code]; unfold colour arc
  have b := bounds
  have := Int.fract_lt_one ((n:ℝ)*phi)
  change phase n<1 at this
  split_ifs <;> simp_all
  linarith

def gap (c : ℤ) (d : ℕ) := ∃n:ℕ, 1≤n ∧ delta n=c ∧ returns (fun j => delta j=c) n d

private theorem unique {P : ℕ→Prop} {n d e : ℕ} (h : returns P n d) (g : returns P n e) : d=e := by
  by_contra! ne
  rcases lt_or_gt_of_ne ne with lt | gt
  · exact g.2.2 d h.1 lt h.2.1
  · exact h.2.2 e g.1 gt g.2.1
-- Generated cases

private theorem plusCell0 (n : ℕ) (lo : 0≤phase n) (hi : phase n<((5)/2+(-3)/2*phi)) :
    returns (fun j => delta j=1) n 2 := by
  have bp := bounds
  refine ⟨by decide,(plus _).mpr ?_,?_⟩
  · apply inside 0 ((phi-1)/2) n 2 3 <;> norm_num <;> linarith
  · intro j hj hd
    interval_cases j
    · exact fun h => outside 0 ((phi-1)/2) n 1 1 (by norm_num; linarith only [lo,hi,bp.1,bp.2]) (by norm_num; linarith only [lo,hi,bp.1,bp.2]) ((plus _).mp h)

private theorem plusCell1 (n : ℕ) (lo : ((5)/2+(-3)/2*phi)≤phase n) (hi : phase n<((5)+(-3)*phi)) :
    returns (fun j => delta j=1) n 5 := by
  have bp := bounds
  refine ⟨by decide,(plus _).mpr ?_,?_⟩
  · apply inside 0 ((phi-1)/2) n 5 8 <;> norm_num <;> linarith
  · intro j hj hd
    interval_cases j
    · exact fun h => outside 0 ((phi-1)/2) n 1 1 (by norm_num; linarith only [lo,hi,bp.1,bp.2]) (by norm_num; linarith only [lo,hi,bp.1,bp.2]) ((plus _).mp h)
    · exact fun h => outside 0 ((phi-1)/2) n 2 3 (by norm_num; linarith only [lo,hi,bp.1,bp.2]) (by norm_num; linarith only [lo,hi,bp.1,bp.2]) ((plus _).mp h)
    · exact fun h => outside 0 ((phi-1)/2) n 3 4 (by norm_num; linarith only [lo,hi,bp.1,bp.2]) (by norm_num; linarith only [lo,hi,bp.1,bp.2]) ((plus _).mp h)
    · exact fun h => outside 0 ((phi-1)/2) n 4 6 (by norm_num; linarith only [lo,hi,bp.1,bp.2]) (by norm_num; linarith only [lo,hi,bp.1,bp.2]) ((plus _).mp h)

private theorem plusCell2 (n : ℕ) (lo : ((5)+(-3)*phi)≤phase n) (hi : phase n<((phi-1)/2)) :
    returns (fun j => delta j=1) n 3 := by
  have bp := bounds
  refine ⟨by decide,(plus _).mpr ?_,?_⟩
  · apply inside 0 ((phi-1)/2) n 3 5 <;> norm_num <;> linarith
  · intro j hj hd
    interval_cases j
    · exact fun h => outside 0 ((phi-1)/2) n 1 1 (by norm_num; linarith only [lo,hi,bp.1,bp.2]) (by norm_num; linarith only [lo,hi,bp.1,bp.2]) ((plus _).mp h)
    · exact fun h => outside 0 ((phi-1)/2) n 2 3 (by norm_num; linarith only [lo,hi,bp.1,bp.2]) (by norm_num; linarith only [lo,hi,bp.1,bp.2]) ((plus _).mp h)

theorem plusNext (n : ℕ) (h : delta n=1) : ∃ d : ℕ, (d=2 ∨ d=3 ∨ d=5) ∧ returns (fun j => delta j=1) n d := by
  obtain ⟨hl,hu⟩ := (plus _).mp h
  by_cases t0 : phase n<((5)/2+(-3)/2*phi)
  · exact ⟨2,by omega,plusCell0 n hl t0⟩
  by_cases t1 : phase n<((5)+(-3)*phi)
  · exact ⟨5,by omega,plusCell1 n (le_of_not_gt t0) t1⟩
  exact ⟨3,by omega,plusCell2 n (le_of_not_gt t1) hu⟩

theorem plusGaps (d : ℕ) : gap 1 d ↔ d=2 ∨ d=3 ∨ d=5 := by
  constructor
  · rintro ⟨n,_,h,t⟩
    obtain ⟨e,hs,hh⟩ := plusNext n h
    rwa [unique t hh]
  · intro h
    rcases h with rfl|rfl|rfl
    · have bp := bounds
      have f : ⌊(13:ℝ)*phi⌋=21 := by apply Int.floor_eq_iff.mpr; norm_num; constructor <;> linarith
      have e : phase 13=(13:ℝ)*phi-21 := by rw [phase_formula]; change (13:ℝ)*phi-(⌊(13:ℝ)*phi⌋:ℝ)=_; rw [f]; norm_num
      refine ⟨13,by decide,(plus _).mpr ⟨by rw [e]; linarith,by rw [e]; linarith⟩,plusCell0 _ (by rw [e]; linarith) (by rw [e]; linarith)⟩
    · have bp := bounds
      have f : ⌊(2:ℝ)*phi⌋=3 := by apply Int.floor_eq_iff.mpr; norm_num; constructor <;> linarith
      have e : phase 2=(2:ℝ)*phi-3 := by rw [phase_formula]; change (2:ℝ)*phi-(⌊(2:ℝ)*phi⌋:ℝ)=_; rw [f]; norm_num
      refine ⟨2,by decide,(plus _).mpr ⟨by rw [e]; linarith,by rw [e]; linarith⟩,plusCell2 _ (by rw [e]; linarith) (by rw [e]; linarith)⟩
    · have bp := bounds
      have f : ⌊(5:ℝ)*phi⌋=8 := by apply Int.floor_eq_iff.mpr; norm_num; constructor <;> linarith
      have e : phase 5=(5:ℝ)*phi-8 := by rw [phase_formula]; change (5:ℝ)*phi-(⌊(5:ℝ)*phi⌋:ℝ)=_; rw [f]; norm_num
      refine ⟨5,by decide,(plus _).mpr ⟨by rw [e]; linarith,by rw [e]; linarith⟩,plusCell1 _ (by rw [e]; linarith) (by rw [e]; linarith)⟩

private theorem middleCell0 (n : ℕ) (lo : ((phi-1)/2)≤phase n) (hi : phase n<((3)+(-3)/2*phi)) :
    returns (fun j => delta j=0) n 2 := by
  have bp := bounds
  refine ⟨by decide,(middle _).mpr ?_,?_⟩
  · apply inside ((phi-1)/2) (phi/2) n 2 3 <;> norm_num <;> linarith
  · intro j hj hd
    interval_cases j
    · exact fun h => outside ((phi-1)/2) (phi/2) n 1 1 (by norm_num; linarith only [lo,hi,bp.1,bp.2]) (by norm_num; linarith only [lo,hi,bp.1,bp.2]) ((middle _).mp h)

private theorem middleCell1 (n : ℕ) (lo : ((3)+(-3)/2*phi)≤phase n) (hi : phase n<((3)/2+(-1)/2*phi)) :
    returns (fun j => delta j=0) n 3 := by
  have bp := bounds
  refine ⟨by decide,(middle _).mpr ?_,?_⟩
  · apply inside ((phi-1)/2) (phi/2) n 3 5 <;> norm_num <;> linarith
  · intro j hj hd
    interval_cases j
    · exact fun h => outside ((phi-1)/2) (phi/2) n 1 1 (by norm_num; linarith only [lo,hi,bp.1,bp.2]) (by norm_num; linarith only [lo,hi,bp.1,bp.2]) ((middle _).mp h)
    · exact fun h => outside ((phi-1)/2) (phi/2) n 2 3 (by norm_num; linarith only [lo,hi,bp.1,bp.2]) (by norm_num; linarith only [lo,hi,bp.1,bp.2]) ((middle _).mp h)

private theorem middleCell2 (n : ℕ) (lo : ((3)/2+(-1)/2*phi)≤phase n) (hi : phase n<(phi/2)) :
    returns (fun j => delta j=0) n 1 := by
  have bp := bounds
  refine ⟨by decide,(middle _).mpr ?_,?_⟩
  · apply inside ((phi-1)/2) (phi/2) n 1 2 <;> norm_num <;> linarith
  · intro j hj hd
    interval_cases j

theorem middleNext (n : ℕ) (h : delta n=0) : ∃ d : ℕ, (d=1 ∨ d=2 ∨ d=3) ∧ returns (fun j => delta j=0) n d := by
  obtain ⟨hl,hu⟩ := (middle _).mp h
  by_cases t0 : phase n<((3)+(-3)/2*phi)
  · exact ⟨2,by omega,middleCell0 n hl t0⟩
  by_cases t1 : phase n<((3)/2+(-1)/2*phi)
  · exact ⟨3,by omega,middleCell1 n (le_of_not_gt t0) t1⟩
  exact ⟨1,by omega,middleCell2 n (le_of_not_gt t1) hu⟩

theorem middleGaps (d : ℕ) : gap 0 d ↔ d=1 ∨ d=2 ∨ d=3 := by
  constructor
  · rintro ⟨n,_,h,t⟩
    obtain ⟨e,hs,hh⟩ := middleNext n h
    rwa [unique t hh]
  · intro h
    rcases h with rfl|rfl|rfl
    · have bp := bounds
      have f : ⌊(6:ℝ)*phi⌋=9 := by apply Int.floor_eq_iff.mpr; norm_num; constructor <;> linarith
      have e : phase 6=(6:ℝ)*phi-9 := by rw [phase_formula]; change (6:ℝ)*phi-(⌊(6:ℝ)*phi⌋:ℝ)=_; rw [f]; norm_num
      refine ⟨6,by decide,(middle _).mpr ⟨by rw [e]; linarith,by rw [e]; linarith⟩,middleCell2 _ (by rw [e]; linarith) (by rw [e]; linarith)⟩
    · have bp := bounds
      have f : ⌊(4:ℝ)*phi⌋=6 := by apply Int.floor_eq_iff.mpr; norm_num; constructor <;> linarith
      have e : phase 4=(4:ℝ)*phi-6 := by rw [phase_formula]; change (4:ℝ)*phi-(⌊(4:ℝ)*phi⌋:ℝ)=_; rw [f]; norm_num
      refine ⟨4,by decide,(middle _).mpr ⟨by rw [e]; linarith,by rw [e]; linarith⟩,middleCell0 _ (by rw [e]; linarith) (by rw [e]; linarith)⟩
    · have bp := bounds
      have f : ⌊(14:ℝ)*phi⌋=22 := by apply Int.floor_eq_iff.mpr; norm_num; constructor <;> linarith
      have e : phase 14=(14:ℝ)*phi-22 := by rw [phase_formula]; change (14:ℝ)*phi-(⌊(14:ℝ)*phi⌋:ℝ)=_; rw [f]; norm_num
      refine ⟨14,by decide,(middle _).mpr ⟨by rw [e]; linarith,by rw [e]; linarith⟩,middleCell1 _ (by rw [e]; linarith) (by rw [e]; linarith)⟩

private theorem minusCell0 (n : ℕ) (lo : (phi/2)≤phase n) (hi : phase n<((9)+(-5)*phi)) :
    returns (fun j => delta j=(-1)) n 5 := by
  have bp := bounds
  refine ⟨by decide,(minus _).mpr ?_,?_⟩
  · apply inside (phi/2) 1 n 5 8 <;> norm_num <;> linarith
  · intro j hj hd
    interval_cases j
    · exact fun h => outside (phi/2) 1 n 1 1 (by norm_num; linarith only [lo,hi,bp.1,bp.2]) (by norm_num; linarith only [lo,hi,bp.1,bp.2]) ((minus _).mp h)
    · exact fun h => outside (phi/2) 1 n 2 3 (by norm_num; linarith only [lo,hi,bp.1,bp.2]) (by norm_num; linarith only [lo,hi,bp.1,bp.2]) ((minus _).mp h)
    · exact fun h => outside (phi/2) 1 n 3 4 (by norm_num; linarith only [lo,hi,bp.1,bp.2]) (by norm_num; linarith only [lo,hi,bp.1,bp.2]) ((minus _).mp h)
    · exact fun h => outside (phi/2) 1 n 4 6 (by norm_num; linarith only [lo,hi,bp.1,bp.2]) (by norm_num; linarith only [lo,hi,bp.1,bp.2]) ((minus _).mp h)

private theorem minusCell1 (n : ℕ) (lo : ((9)+(-5)*phi)≤phase n) (hi : phase n<((5)+(-5)/2*phi)) :
    returns (fun j => delta j=(-1)) n 8 := by
  have bp := bounds
  refine ⟨by decide,(minus _).mpr ?_,?_⟩
  · apply inside (phi/2) 1 n 8 13 <;> norm_num <;> linarith
  · intro j hj hd
    interval_cases j
    · exact fun h => outside (phi/2) 1 n 1 1 (by norm_num; linarith only [lo,hi,bp.1,bp.2]) (by norm_num; linarith only [lo,hi,bp.1,bp.2]) ((minus _).mp h)
    · exact fun h => outside (phi/2) 1 n 2 3 (by norm_num; linarith only [lo,hi,bp.1,bp.2]) (by norm_num; linarith only [lo,hi,bp.1,bp.2]) ((minus _).mp h)
    · exact fun h => outside (phi/2) 1 n 3 4 (by norm_num; linarith only [lo,hi,bp.1,bp.2]) (by norm_num; linarith only [lo,hi,bp.1,bp.2]) ((minus _).mp h)
    · exact fun h => outside (phi/2) 1 n 4 6 (by norm_num; linarith only [lo,hi,bp.1,bp.2]) (by norm_num; linarith only [lo,hi,bp.1,bp.2]) ((minus _).mp h)
    · exact fun h => outside (phi/2) 1 n 5 8 (by norm_num; linarith only [lo,hi,bp.1,bp.2]) (by norm_num; linarith only [lo,hi,bp.1,bp.2]) ((minus _).mp h)
    · exact fun h => outside (phi/2) 1 n 6 9 (by norm_num; linarith only [lo,hi,bp.1,bp.2]) (by norm_num; linarith only [lo,hi,bp.1,bp.2]) ((minus _).mp h)
    · exact fun h => outside (phi/2) 1 n 7 11 (by norm_num; linarith only [lo,hi,bp.1,bp.2]) (by norm_num; linarith only [lo,hi,bp.1,bp.2]) ((minus _).mp h)

private theorem minusCell2 (n : ℕ) (lo : ((5)+(-5)/2*phi)≤phase n) (hi : phase n<1) :
    returns (fun j => delta j=(-1)) n 3 := by
  have bp := bounds
  refine ⟨by decide,(minus _).mpr ?_,?_⟩
  · apply inside (phi/2) 1 n 3 5 <;> norm_num <;> linarith
  · intro j hj hd
    interval_cases j
    · exact fun h => outside (phi/2) 1 n 1 1 (by norm_num; linarith only [lo,hi,bp.1,bp.2]) (by norm_num; linarith only [lo,hi,bp.1,bp.2]) ((minus _).mp h)
    · exact fun h => outside (phi/2) 1 n 2 3 (by norm_num; linarith only [lo,hi,bp.1,bp.2]) (by norm_num; linarith only [lo,hi,bp.1,bp.2]) ((minus _).mp h)

theorem minusNext (n : ℕ) (h : delta n=(-1)) : ∃ d : ℕ, (d=3 ∨ d=5 ∨ d=8) ∧ returns (fun j => delta j=(-1)) n d := by
  obtain ⟨hl,hu⟩ := (minus _).mp h
  by_cases t0 : phase n<((9)+(-5)*phi)
  · exact ⟨5,by omega,minusCell0 n hl t0⟩
  by_cases t1 : phase n<((5)+(-5)/2*phi)
  · exact ⟨8,by omega,minusCell1 n (le_of_not_gt t0) t1⟩
  exact ⟨3,by omega,minusCell2 n (le_of_not_gt t1) hu⟩

theorem minusGaps (d : ℕ) : gap (-1) d ↔ d=3 ∨ d=5 ∨ d=8 := by
  constructor
  · rintro ⟨n,_,h,t⟩
    obtain ⟨e,hs,hh⟩ := minusNext n h
    rwa [unique t hh]
  · intro h
    rcases h with rfl|rfl|rfl
    · have bp := bounds
      have f : ⌊(21:ℝ)*phi⌋=33 := by apply Int.floor_eq_iff.mpr; norm_num; constructor <;> linarith
      have e : phase 21=(21:ℝ)*phi-33 := by rw [phase_formula]; change (21:ℝ)*phi-(⌊(21:ℝ)*phi⌋:ℝ)=_; rw [f]; norm_num
      refine ⟨21,by decide,(minus _).mpr ⟨by rw [e]; linarith,by rw [e]; linarith⟩,minusCell2 _ (by rw [e]; linarith) (by rw [e]; linarith)⟩
    · have bp := bounds
      have f : ⌊(3:ℝ)*phi⌋=4 := by apply Int.floor_eq_iff.mpr; norm_num; constructor <;> linarith
      have e : phase 3=(3:ℝ)*phi-4 := by rw [phase_formula]; change (3:ℝ)*phi-(⌊(3:ℝ)*phi⌋:ℝ)=_; rw [f]; norm_num
      refine ⟨3,by decide,(minus _).mpr ⟨by rw [e]; linarith,by rw [e]; linarith⟩,minusCell0 _ (by rw [e]; linarith) (by rw [e]; linarith)⟩
    · have bp := bounds
      have f : ⌊(8:ℝ)*phi⌋=12 := by apply Int.floor_eq_iff.mpr; norm_num; constructor <;> linarith
      have e : phase 8=(8:ℝ)*phi-12 := by rw [phase_formula]; change (8:ℝ)*phi-(⌊(8:ℝ)*phi⌋:ℝ)=_; rw [f]; norm_num
      refine ⟨8,by decide,(minus _).mpr ⟨by rw [e]; linarith,by rw [e]; linarith⟩,minusCell1 _ (by rw [e]; linarith) (by rw [e]; linarith)⟩
end
end Stolarsky
#print axioms Stolarsky.plusNext
#print axioms Stolarsky.plusGaps
#print axioms Stolarsky.middleNext
#print axioms Stolarsky.middleGaps
#print axioms Stolarsky.minusNext
#print axioms Stolarsky.minusGaps
