import CeilingColumns
namespace CeilingWythoff
open LeastCarry
open Stolarsky

theorem rowsStrict (k : ℕ) : StrictMono (fun n => entry n k) := by
  intro a b h
  have bp := bounds
  have hn : (a:ℝ)+1≤b := by exact_mod_cast h
  have cab := Int.ceil_mono (show (a:ℝ)*phi+1≤b*phi by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) (show 0≤phi by linarith)])
  rw [Int.ceil_add_one] at cab
  have fp : (0:ℤ)<Nat.fib (k+1) := by exact_mod_cast Nat.fib_pos.mpr (by omega : 0<k+1)
  have ab : ((a-1:ℕ):ℤ)≤((b-1:ℕ):ℤ) := by exact_mod_cast (show a-1≤b-1 by omega)
  unfold entry
  exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left (by omega) fp)
    (by exact_mod_cast Nat.mul_le_mul_right (Nat.fib k) (show a-1≤b-1 by omega))

private theorem oneIff {x i : ℕ} {xs : List ℕ} (h : digits x=i::xs) :
    hasColumn x 1 ↔ i%2=1 := by
  have good := digits_valid x
  rw [h] at good
  have low := good.1
  rw [columnOne]
  constructor
  · rintro ⟨t,ys,e⟩
    rw [h,List.cons.injEq] at e
    omega
  · intro hi
    exact ⟨(i-3)/2,xs,by rw [h,show 3+2*((i-3)/2)=i by omega]⟩

private theorem twoIff {x i j : ℕ} {xs : List ℕ} (h : digits x=i::j::xs) :
    hasColumn x 2 ↔ i=2 ∧ j%2=0 := by
  have good := digits_valid x
  rw [h] at good
  have lo:=good.1
  have sep:=good.2.1
  rw [columnTwo]
  constructor
  · rintro ⟨t,ys,e⟩
    rw [h,List.cons.injEq,List.cons.injEq] at e
    exact ⟨e.1,by omega⟩
  · rintro ⟨rfl,p⟩
    exact ⟨(j-4)/2,xs,by rw [h,show 4+2*((j-4)/2)=j by omega]⟩

private theorem highIff {x i j : ℕ} {xs : List ℕ} (h : digits x=i::j::xs) {r : ℕ} (hr : 2≤r) :
    hasColumn x (r+1) ↔ i=r ∧ j%2≠i%2 := by
  have good := digits_valid x
  rw [h] at good
  have sep:=good.2.1
  rw [columnHigh x r hr]
  constructor
  · rintro ⟨t,ys,e⟩
    rw [h,List.cons.injEq,List.cons.injEq] at e
    exact ⟨e.1,by omega⟩
  · rintro ⟨rfl,p⟩
    exact ⟨(j-(i+3))/2,xs,by rw [h,show i+3+2*((j-(i+3))/2)=j by omega]⟩

theorem twoDigits {x i j k : ℕ} {xs : List ℕ} (h : digits x=i::j::xs) (hk : 0<k) :
    hasColumn x k ↔ (k=1 ∧ i%2=1) ∨ (k=2 ∧ i=2 ∧ j%2=0) ∨ (k=i+1 ∧ j%2≠i%2) := by
  have g := digits_valid x
  rw [h] at g
  have gi := g.1
  rcases lt_trichotomy k 2 with low|rfl|high
  · have e : k=1 := by omega
    subst k; rw [oneIff h]; omega
  · rw [twoIff h]; omega
  · obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rw [highIff h (by omega)]
    omega

theorem singleton {x i k : ℕ} (h : digits x=[i]) (hk : 0<k) :
    hasColumn x k ↔ k=1 ∧ i%2=1 := by
  rcases lt_trichotomy k 2 with low|rfl|high
  · have e : k=1 := by omega
    subst k; rw [oneIff h]; simp
  · rw [columnTwo]; simp [h]
  · obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rw [columnHigh x r (by omega)]
    simp [h,show r+1≠1 by omega]

/-- Strict increase down each column makes these distinct column hits precisely distinct entries. -/
def repeated (x : ℕ) := ∃k l : ℕ, 0<k ∧ k<l ∧ hasColumn x k ∧ hasColumn x l
def missing (x : ℕ) := ∀k : ℕ, 0<k → ¬hasColumn x k

theorem repeated_iff {x i j : ℕ} {xs : List ℕ} (h : digits x=i::j::xs) :
    repeated x ↔ i%2=1 ∧ j%2=0 := by
  have g := digits_valid x
  rw [h] at g
  have gi := g.1
  constructor
  · rintro ⟨k,l,hk,kl,ck,cl⟩
    rw [twoDigits h hk] at ck
    rw [twoDigits h (by omega)] at cl
    omega
  · rintro ⟨p,q⟩
    exact ⟨1,i+1,by decide,by omega,(oneIff h).mpr p,(highIff h gi).mpr ⟨rfl,by omega⟩⟩

theorem missing_iff {x i j : ℕ} {xs : List ℕ} (h : digits x=i::j::xs) :
    missing x ↔ 4≤i ∧ i%2=0 ∧ j%2=0 := by
  have g := digits_valid x
  rw [h] at g
  have gi := g.1
  constructor
  · intro m
    have a := mt (oneIff h).mpr (m 1 (by decide))
    have b := mt (twoIff h).mpr (m 2 (by decide))
    have c := mt (highIff h gi).mpr (m (i+1) (by omega))
    omega
  · rintro ⟨_,_,_⟩ k hk ck
    rw [twoDigits h hk] at ck
    omega

theorem singleCases {x i : ℕ} (h : digits x=[i]) :
    ¬repeated x ∧ (missing x ↔ i%2=0) := by
  constructor
  · rintro ⟨k,l,hk,kl,ck,cl⟩
    rw [singleton h hk] at ck
    rw [singleton h (by omega)] at cl
    omega
  · constructor
    · intro m
      have := mt (oneIff h).mpr (m 1 (by decide))
      omega
    · intro even k hk ck
      rw [singleton h hk] at ck
      omega

theorem atMostTwo (x : ℕ) : ¬∃k l m : ℕ, 0<k ∧ k<l ∧ l<m ∧
    hasColumn x k ∧ hasColumn x l ∧ hasColumn x m := by
  rintro ⟨k,l,m,hk,kl,lm,ck,cl,cm⟩
  cases h : digits x with
  | nil =>
    have hx := digits_weight x
    rw [h] at hx
    have z : x=0 := by simpa [weight] using hx.symm
    have zz := (column x k).mp ck
    obtain ⟨ys,_,e⟩ := zz
    have := Nat.fib_pos.mpr (show 0<k+1 by omega)
    omega
  | cons i rest =>
    cases rest with
    | nil =>
      rw [singleton h hk] at ck
      rw [singleton h (by omega)] at cl
      omega
    | cons j xs =>
      rw [twoDigits h hk] at ck
      rw [twoDigits h (by omega)] at cl
      rw [twoDigits h (by omega)] at cm
      omega
end CeilingWythoff
#print axioms CeilingWythoff.rowsStrict
#print axioms CeilingWythoff.repeated_iff
#print axioms CeilingWythoff.missing_iff
#print axioms CeilingWythoff.singleCases
#print axioms CeilingWythoff.atMostTwo
