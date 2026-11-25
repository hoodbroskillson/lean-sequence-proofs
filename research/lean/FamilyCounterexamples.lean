import ArtsteinST
import Mathlib.Tactic.NormNum
namespace ArtsteinST
attribute [local irreducible] A B
def D (p:Params) (m n j:ℕ):ℤ := |(A p (m+j):ℤ)-A p m-((A p (n+j):ℤ)-A p n)|

private theorem ranked (p : Params) (n k x y : ℕ) (hn : 0<n)
    (a : A p k=x) (b : A p (k+1)=y)
    (lo : p.s*x+(p.t-1)*k<n) (hi : n≤p.s*y+(p.t-1)*(k+1)) :
    A p n=n+k := of_bracket p n k hn (a.symm ▸ lo) (b.symm ▸ hi)

private theorem digit (p : Params) (m n j x y z w : ℕ)
    (a : A p (m+j)=x) (b : A p m=y) (c : A p (n+j)=z) (d : A p n=w) :
    D p m n j=|(x:ℤ)-y-((z:ℤ)-w)| := by unfold D;rw [a,b,c,d]

namespace P42
def p : Params := ⟨4,by decide,2,by decide⟩
private theorem v0 : A p 0=0 := (starts p).1
private theorem v1 : A p 1=1 := (starts p).2.2
private theorem v2 : A p 2=2 := ranked p 2 0 _ _ (by decide) v0 v1 (by decide) (by decide)
private theorem v3 : A p 3=3 := ranked p 3 0 _ _ (by decide) v0 v1 (by decide) (by decide)
private theorem v4 : A p 4=4 := ranked p 4 0 _ _ (by decide) v0 v1 (by decide) (by decide)
private theorem v5 : A p 5=5 := ranked p 5 0 _ _ (by decide) v0 v1 (by decide) (by decide)
private theorem v6 : A p 6=7 := ranked p 6 1 _ _ (by decide) v1 v2 (by decide) (by decide)
private theorem v10 : A p 10=11 := ranked p 10 1 _ _ (by decide) v1 v2 (by decide) (by decide)
private theorem v11 : A p 11=13 := ranked p 11 2 _ _ (by decide) v2 v3 (by decide) (by decide)
private theorem v12 : A p 12=14 := ranked p 12 2 _ _ (by decide) v2 v3 (by decide) (by decide)
private theorem v25 : A p 25=29 := ranked p 25 4 _ _ (by decide) v4 v5 (by decide) (by decide)
private theorem v26 : A p 26=31 := ranked p 26 5 _ _ (by decide) v5 v6 (by decide) (by decide)
private theorem v27 : A p 27=32 := ranked p 27 5 _ _ (by decide) v5 v6 (by decide) (by decide)
private theorem v32 : A p 32=37 := ranked p 32 5 _ _ (by decide) v5 v6 (by decide) (by decide)
private theorem v33 : A p 33=38 := ranked p 33 5 _ _ (by decide) v5 v6 (by decide) (by decide)
private theorem v34 : A p 34=39 := ranked p 34 5 _ _ (by decide) v5 v6 (by decide) (by decide)
private theorem v62 : A p 62=72 := ranked p 62 10 _ _ (by decide) v10 v11 (by decide) (by decide)
private theorem v63 : A p 63=73 := ranked p 63 10 _ _ (by decide) v10 v11 (by decide) (by decide)
private theorem v64 : A p 64=75 := ranked p 64 11 _ _ (by decide) v11 v12 (by decide) (by decide)
private theorem v149 : A p 149=174 := ranked p 149 25 _ _ (by decide) v25 v26 (by decide) (by decide)
private theorem v150 : A p 150=175 := ranked p 150 25 _ _ (by decide) v25 v26 (by decide) (by decide)
private theorem v151 : A p 151=177 := ranked p 151 26 _ _ (by decide) v26 v27 (by decide) (by decide)
private theorem v185 : A p 185=217 := ranked p 185 32 _ _ (by decide) v32 v33 (by decide) (by decide)
private theorem v186 : A p 186=219 := ranked p 186 33 _ _ (by decide) v33 v34 (by decide) (by decide)
private theorem v355 : A p 355=417 := ranked p 355 62 _ _ (by decide) v62 v63 (by decide) (by decide)
private theorem v356 : A p 356=419 := ranked p 356 63 _ _ (by decide) v63 v64 (by decide) (by decide)
private theorem v850 : A p 850=999 := ranked p 850 149 _ _ (by decide) v149 v150 (by decide) (by decide)
private theorem v851 : A p 851=1001 := ranked p 851 150 _ _ (by decide) v150 v151 (by decide) (by decide)
private theorem v1059 : A p 1059=1244 := ranked p 1059 185 _ _ (by decide) v185 v186 (by decide) (by decide)
private theorem v1060 : A p 1060=1245 := ranked p 1060 185 _ _ (by decide) v185 v186 (by decide) (by decide)
private theorem v2032 : A p 2032=2387 := ranked p 2032 355 _ _ (by decide) v355 v356 (by decide) (by decide)
private theorem v4855 : A p 4855=5705 := ranked p 4855 850 _ _ (by decide) v850 v851 (by decide) (by decide)
private theorem v6036 : A p 6036=7095 := ranked p 6036 1059 _ _ (by decide) v1059 v1060 (by decide) (by decide)
theorem witness0 : D p 0 0 0=0 := by
  simp [D]
theorem witness1 : D p 5 0 1=1 := (digit p 5 0 1 _ _ _ _ v6 v5 v1 v0).trans (by decide)
theorem witness2 : D p 5 26 6=2 := (digit p 5 26 6 _ _ _ _ v11 v5 v32 v26).trans (by decide)
theorem witness3 : D p 150 26 36=3 := (digit p 150 26 36 _ _ _ _ v186 v150 v62 v26).trans (by decide)
theorem witness4 : D p 4855 851 1181=4 := (digit p 4855 851 1181 _ _ _ _ v6036 v4855 v2032 v851).trans (by decide)
theorem outside_condition : ¬(p.s-2≤(p.t-1)^2) := by decide
theorem upper_value : (p.s-2)/(p.t-1)+2=4 := by decide
theorem witnesses (d:ℕ) (le:d≤4) : ∃m n j:ℕ, D p m n j=d := by
  have h : d=0 ∨ d=1 ∨ d=2 ∨ d=3 ∨ d=4 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl
  · exact ⟨0,0,0,witness0⟩
  · exact ⟨5,0,1,witness1⟩
  · exact ⟨5,26,6,witness2⟩
  · exact ⟨150,26,36,witness3⟩
  · exact ⟨4855,851,1181,witness4⟩
end P42
namespace P73
def p : Params := ⟨7,by decide,3,by decide⟩
private theorem v0 : A p 0=0 := (starts p).1
private theorem v1 : A p 1=1 := (starts p).2.2
private theorem v2 : A p 2=2 := ranked p 2 0 _ _ (by decide) v0 v1 (by decide) (by decide)
private theorem v3 : A p 3=3 := ranked p 3 0 _ _ (by decide) v0 v1 (by decide) (by decide)
private theorem v8 : A p 8=8 := ranked p 8 0 _ _ (by decide) v0 v1 (by decide) (by decide)
private theorem v9 : A p 9=9 := ranked p 9 0 _ _ (by decide) v0 v1 (by decide) (by decide)
private theorem v10 : A p 10=11 := ranked p 10 1 _ _ (by decide) v1 v2 (by decide) (by decide)
private theorem v18 : A p 18=19 := ranked p 18 1 _ _ (by decide) v1 v2 (by decide) (by decide)
private theorem v19 : A p 19=21 := ranked p 19 2 _ _ (by decide) v2 v3 (by decide) (by decide)
private theorem v81 : A p 81=89 := ranked p 81 8 _ _ (by decide) v8 v9 (by decide) (by decide)
private theorem v82 : A p 82=91 := ranked p 82 9 _ _ (by decide) v9 v10 (by decide) (by decide)
private theorem v83 : A p 83=92 := ranked p 83 9 _ _ (by decide) v9 v10 (by decide) (by decide)
private theorem v92 : A p 92=101 := ranked p 92 9 _ _ (by decide) v9 v10 (by decide) (by decide)
private theorem v93 : A p 93=102 := ranked p 93 9 _ _ (by decide) v9 v10 (by decide) (by decide)
private theorem v94 : A p 94=103 := ranked p 94 9 _ _ (by decide) v9 v10 (by decide) (by decide)
private theorem v182 : A p 182=200 := ranked p 182 18 _ _ (by decide) v18 v19 (by decide) (by decide)
private theorem v184 : A p 184=202 := ranked p 184 18 _ _ (by decide) v18 v19 (by decide) (by decide)
private theorem v185 : A p 185=203 := ranked p 185 18 _ _ (by decide) v18 v19 (by decide) (by decide)
private theorem v801 : A p 801=882 := ranked p 801 81 _ _ (by decide) v81 v82 (by decide) (by decide)
private theorem v802 : A p 802=884 := ranked p 802 82 _ _ (by decide) v82 v83 (by decide) (by decide)
private theorem v900 : A p 900=992 := ranked p 900 92 _ _ (by decide) v92 v93 (by decide) (by decide)
private theorem v901 : A p 901=994 := ranked p 901 93 _ _ (by decide) v93 v94 (by decide) (by decide)
private theorem v1783 : A p 1783=1967 := ranked p 1783 184 _ _ (by decide) v184 v185 (by decide) (by decide)
private theorem v7777 : A p 7777=8578 := ranked p 7777 801 _ _ (by decide) v801 v802 (by decide) (by decide)
private theorem v8759 : A p 8759=9659 := ranked p 8759 900 _ _ (by decide) v900 v901 (by decide) (by decide)
theorem witness0 : D p 0 0 0=0 := by
  simp [D]
theorem witness1 : D p 9 0 1=1 := (digit p 9 0 1 _ _ _ _ v10 v9 v1 v0).trans (by decide)
theorem witness2 : D p 9 82 10=2 := (digit p 9 82 10 _ _ _ _ v19 v9 v92 v82).trans (by decide)
theorem witness3 : D p 801 82 100=3 := (digit p 801 82 100 _ _ _ _ v901 v801 v182 v82).trans (by decide)
theorem witness4 : D p 801 7777 982=4 := (digit p 801 7777 982 _ _ _ _ v1783 v801 v8759 v7777).trans (by decide)
theorem outside_condition : ¬(p.s-2≤(p.t-1)^2) := by decide
theorem upper_value : (p.s-2)/(p.t-1)+2=4 := by decide
theorem witnesses (d:ℕ) (le:d≤4) : ∃m n j:ℕ, D p m n j=d := by
  have h : d=0 ∨ d=1 ∨ d=2 ∨ d=3 ∨ d=4 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl
  · exact ⟨0,0,0,witness0⟩
  · exact ⟨9,0,1,witness1⟩
  · exact ⟨9,82,10,witness2⟩
  · exact ⟨801,82,100,witness3⟩
  · exact ⟨801,7777,982,witness4⟩
end P73
end ArtsteinST
#print axioms ArtsteinST.P42.witness4
#print axioms ArtsteinST.P42.outside_condition
#print axioms ArtsteinST.P42.upper_value
#print axioms ArtsteinST.P42.witnesses
#print axioms ArtsteinST.P73.witness4
#print axioms ArtsteinST.P73.outside_condition
#print axioms ArtsteinST.P73.upper_value
#print axioms ArtsteinST.P73.witnesses
