import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice
import Mathlib.Tactic.Tauto
namespace MexFamily
open Finset
noncomputable section

private def mex (u : Finset ℕ) : ℕ := Nat.find (show ∃x:ℕ,x∉u from
  ⟨u.sup id + 1,fun h => by have c:=Finset.le_sup (f:=id) h; change u.sup id+1≤u.sup id at c;omega⟩)

private theorem mex_fresh (u : Finset ℕ) : mex u∉u := by unfold mex;exact Nat.find_spec (p:=fun x:ℕ=>x∉u) _
private theorem mex_fills (u : Finset ℕ) {x : ℕ} (hx : x<mex u) : x∈u := by
  by_contra n;exact (not_le.mpr hx) (Nat.find_min' _ n)

structure Params where
  s : ℕ
  ge : 2≤s

variable (q : Params)

private def sets : ℕ→Finset ℕ
  | 0 => ∅
  | n+1 => insert (mex (sets n)) (insert (q.s*mex (sets n)+n) (sets n))

/-- Minimum excluded value of the two previously constructed columns (equation (1)). -/
def A (n : ℕ) := mex ((sets q) n)
/-- Equation (2) of Artstein-Avidan, Fraenkel and Sós with s≥2 and t=1. -/
def B (n : ℕ) := q.s*(A q) n+n

theorem mem_sets (n x : ℕ) : x∈(sets q) n ↔ ∃i<n,x=(A q) i ∨ x=(B q) i := by
  induction n with
  | zero => simp [sets]
  | succ n ih =>
    change x∈insert ((A q) n) (insert ((B q) n) ((sets q) n)) ↔ _
    simp only [mem_insert,ih]
    constructor
    · rintro (r|r|⟨i,hi,r⟩)
      · exact ⟨n,by omega,Or.inl r⟩
      · exact ⟨n,by omega,Or.inr r⟩
      · exact ⟨i,by omega,r⟩
    · rintro ⟨i,hi,h⟩
      by_cases eq : i=n
      · subst i;tauto
      · exact Or.inr (Or.inr ⟨i,by omega,h⟩)

theorem starts : (A q) 0=0 ∧ (B q) 0=0 ∧ (A q) 1=1 := by
  have z : (A q) 0=0 := Nat.eq_zero_of_not_pos (fun pos => by have bad:=mex_fills ((sets q) 0) pos;simp [sets] at bad)
  have b : (B q) 0=0 := by simp [B,z]
  refine ⟨z,b,?_⟩
  have e (x : ℕ) : x∈(sets q) 1 ↔ x=0 := by rw [(mem_sets q)];simp [Nat.lt_one_iff,z,b]
  have l:=mex_fresh ((sets q) 1)
  have u : (A q) 1≤1 := by by_contra! h;have := (e 1).mp (mex_fills ((sets q) 1) h);omega
  have n : (A q) 1≠0 := fun h=>l ((e _).mpr h)
  omega

theorem strictA : StrictMono (A q) := by
  intro i j lt
  have f:=mex_fresh ((sets q) j)
  rcases lt_trichotomy ((A q) j) ((A q) i) with small|eq|large
  · obtain ⟨k,hk,m⟩ := ((mem_sets q) _ _).mp (mex_fills ((sets q) i) small)
    exact (f (((mem_sets q) _ _).mpr ⟨k,by omega,m⟩)).elim
  · exact (f (((mem_sets q) _ _).mpr ⟨i,lt,Or.inl eq⟩)).elim
  · exact large

theorem strictB : StrictMono (B q) := by intro i j h;have:=(strictA q) h;unfold B;have z:=Nat.mul_le_mul_left q.s (show (A q) i≤(A q) j from by omega);omega

private theorem separate (i j : ℕ) (hj : 0<j) : (A q) i≠(B q) j := by
  intro eq
  by_cases h : j<i
  · exact mex_fresh ((sets q) i) (((mem_sets q) _ _).mpr ⟨j,h,Or.inr eq⟩)
  · have le:=(strictA q).monotone (show i≤j by omega)
    unfold B at eq
    have z:=Nat.mul_le_mul_right ((A q) j) q.ge
    omega

theorem bracket (n : ℕ) (hn : 0<n) :
    ∃k : ℕ, (A q) n=n+k ∧ (B q) k<(A q) n ∧ (A q) n<(B q) (k+1) ∧ 2*k<n := by
  have floorA (i : ℕ) : i≤(A q) i := (strictA q).id_le i
  have apos : 0<(A q) n := lt_of_lt_of_le hn (floorA n)
  let k:=n.findGreatest (fun j => (B q) j<(A q) n)
  have kz : (B q) 0<(A q) n := by rw [(starts q).2.1];assumption
  have kl : (B q) k<(A q) n := Nat.findGreatest_spec (P:=fun j=>(B q) j<(A q) n) (Nat.zero_le _) kz
  have kn : k≤n := Nat.findGreatest_le _
  have kg : (A q) n<(B q) (k+1) := by
    by_contra! neg
    have h : (B q) (k+1)<(A q) n := lt_of_le_of_ne neg (Ne.symm ((separate q) n (k+1) (by omega)))
    have kk : k+1≤n := by by_contra! rev;have a:=(strictA q) (show n<k+1 by omega);unfold B at h;have z:=Nat.mul_le_mul_right ((A q) (k+1)) q.ge;omega
    have := Nat.le_findGreatest (P:=fun j=>(B q) j<(A q) n) kk h
    change k+1≤k at this;omega
  have d : Disjoint ((range n).image (A q)) ((range k).image (fun i=>(B q) (i+1))) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨i,_,rfl⟩:=mem_image.mp hx
    obtain ⟨j,_,eq⟩:=mem_image.mp hy
    exact (separate q) i (j+1) (by omega) eq.symm
  have eq : range ((A q) n)=((range n).image (A q)) ∪ ((range k).image (fun i=>(B q) (i+1))) := by
    ext x
    rw [mem_range,mem_union]
    constructor
    · intro h
      obtain ⟨i,hi,ea|eb⟩:=((mem_sets q) n x).mp (mex_fills ((sets q) n) h)
      · exact Or.inl (mem_image.mpr ⟨i,mem_range.mpr hi,ea.symm⟩)
      · cases i with
        | zero => exact Or.inl (mem_image.mpr ⟨0,mem_range.mpr hn,by rw [eb,(starts q).1,(starts q).2.1]⟩)
        | succ i =>
          have lt : i<k := by by_contra! small;have := (strictB q).monotone (show k+1≤i+1 by omega);omega
          exact Or.inr (mem_image.mpr ⟨i,mem_range.mpr lt,eb.symm⟩)
    · rintro (inA|inB)
      · obtain ⟨i,hi,rfl⟩:=mem_image.mp inA;exact (strictA q) (mem_range.mp hi)
      · obtain ⟨i,hi,rfl⟩:=mem_image.mp inB
        exact ((strictB q).monotone (show i+1≤k from mem_range.mp hi)).trans_lt kl
  have id : (A q) n=n+k := by
    have h:=congrArg Finset.card eq
    have inj : Function.Injective (fun i:ℕ =>(B q) (i+1)):=fun i j eq=>by have:=(strictB q).injective eq;omega
    simpa only [card_range,card_union_of_disjoint d,card_image_of_injective _ (strictA q).injective,card_image_of_injective _ inj] using h
  refine ⟨k,id,kl,kg,?_⟩
  unfold B at kl
  have a:=floorA k
  have b:=Nat.mul_le_mul_right ((A q) k) q.ge
  omega

end
end MexFamily
#print axioms MexFamily.bracket
