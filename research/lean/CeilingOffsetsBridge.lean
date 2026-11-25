import CeilingBlocks
import CeilingMultiplicity
namespace CeilingBlocks
open LeastCarry Nat CeilingWythoff

private def acc (is : List ℕ) (s : S) := is.foldr push s

/-- Decide the leaf classification after taking account of all higher indices in state s. -/
private def readDigits (m : Bool) (is : List ℕ) (s : S) : Bool :=
  match is with
  | [] => test m s
  | i::rest => if i=2 then m && (acc rest s == 0) else test m (push i (acc rest s))

private theorem read_append (m : Bool) (is : List ℕ) (i : ℕ) (hi : i≠2) (s : S) :
    readDigits m (is++[i]) s=readDigits m is (push i s) := by
  cases is <;> simp [readDigits,hi,acc,List.foldr_append]

private theorem digits_split (k n : ℕ) (lo : fib (k+3)≤n) (hi : n<fib (k+4)) :
    LeastCarry.digits n=LeastCarry.digits (n-fib (k+3))++[k+3] := by
  have g : greatestFib n=k+3 := by
    have a:=le_greatestFib.mpr lo
    have b:=greatestFib_lt.mpr hi
    omega
  have hn := Nat.fib_pos.mpr (by omega : 0<k+3)
  simp only [LeastCarry.digits]
  rw [zeckendorf_of_pos (by omega : 0<n),g,List.reverse_cons]

private theorem mem_rec (m : Bool) (k : ℕ) (s : S) (n : ℕ) :
    n∈offsets m k s ↔ n<fib (k+2) ∧ readDigits m (LeastCarry.digits n) s=true := by
  induction k using Nat.strong_induction_on generalizing s n with
  | h k ih =>
    match k with
    | 0 =>
      have f : fib 2=1 := by decide
      cases n with
      | zero => simp [offsets,LeastCarry.digits,readDigits,f]; split <;> simp_all
      | succ n => simp [offsets,f]; split <;> simp
    | 1 =>
      have f : fib 3=2 := by decide
      have d : LeastCarry.digits 1=[2] := by decide
      rcases n with _|(_|n)
      · simp [offsets,LeastCarry.digits,readDigits,f]; split <;> split <;> simp_all
      · simp [offsets,d,readDigits,acc,f]; split <;> split <;> simp_all
      · simp [offsets,f]; split <;> split <;> simp
    | k+2 =>
      have fibsum : fib (k+4)=fib (k+2)+fib (k+3) := Nat.fib_add_two
      have e := ih (k+1) (by omega) s n
      have e' (x : ℕ) := ih k (by omega) (push (k+3) s) x
      change n∈offsets m (k+1) s ++ (offsets m k (push (k+3) s)).map (fib (k+3)+·) ↔
        n<fib (k+4) ∧ _
      rw [List.mem_append,List.mem_map,e]
      by_cases low : n<fib (k+3)
      · constructor
        · rintro (⟨_,h⟩|⟨x,_,hx⟩)
          · exact ⟨by omega,h⟩
          · omega
        · exact fun h => Or.inl ⟨low,h.2⟩
      · constructor
        · rintro (⟨bad,_⟩|⟨x,hx,rfl⟩)
          · exact (low bad).elim
          · obtain ⟨b,v⟩ := (e' x).mp hx
            have upper : fib (k+3)+x<fib (k+4) := by omega
            rw [digits_split k _ (by omega) upper,Nat.add_sub_cancel_left,read_append _ _ _ (by omega)]
            exact ⟨upper,v⟩
        · rintro ⟨bound,h⟩
          rw [digits_split k _ (by omega) bound,read_append _ _ _ (by omega)] at h
          exact Or.inr ⟨n-fib (k+3),(e' _).mpr ⟨by omega,h⟩,by omega⟩

private theorem push_ne_zero (j : ℕ) (s : S) : push j s≠0 := by
  unfold push
  split_ifs <;> decide

private theorem even_push (j : ℕ) (s : S) : (push j s=1 ∨ push j s=3 ∨ push j s=4) ↔ j%2=0 := by
  unfold push
  split_ifs <;> simp_all

private theorem read_two (m : Bool) (i j : ℕ) (rest : List ℕ) :
    readDigits m (i::j::rest) 0=true ↔
    if m then i≠2 ∧ i%2=0 ∧ j%2=0 else i%2=1 ∧ j%2=0 := by
  let s:=push j (acc rest 0)
  have sn : s≠0 := push_ne_zero _ _
  have ev : (s=1 ∨ s=3 ∨ s=4) ↔ j%2=0 := even_push _ _
  change (if i=2 then m && (s==0) else test m (push i s))=true ↔ _
  by_cases ei : i=2
  · subst i; cases m <;> simp [sn]
  · by_cases p : i%2=0 <;> by_cases q : j%2=0 <;> cases m <;> simp [push,test,sn,ev,ei,p,q]
    all_goals omega

theorem mem_offsets_source (miss : Bool) (k n : ℕ) :
    n∈offsets miss k 0 ↔ n<fib (k+2) ∧ 0<n ∧
      (if miss then CeilingWythoff.missing n else CeilingWythoff.repeated n) := by
  rw [mem_rec]
  apply and_congr_right
  intro _
  cases d : LeastCarry.digits n with
  | nil =>
    have w:=digits_weight n
    rw [d] at w
    have hn : n=0 := by simpa [weight] using w.symm
    rw [hn]
    cases miss <;> simp [readDigits,test]
  | cons i xs =>
    have v:=digits_valid n
    rw [d] at v
    have li := v.1
    have hn : 0<n := by
      by_contra! z
      have e : n=0 := by omega
      rw [e] at d
      simp [LeastCarry.digits] at d
    rw [and_iff_right hn]
    cases xs with
    | nil =>
      have h:=singleCases d
      cases miss
      · rw [if_neg (by decide : false≠true),iff_false_intro h.1]
        by_cases e : i=2 <;> by_cases p : i%2=0 <;> simp [readDigits,acc,push,test,e,p]
      · rw [if_pos rfl,h.2]
        by_cases e : i=2 <;> by_cases p : i%2=0 <;> simp_all [readDigits,acc,push,test]
    | cons j ys =>
      rw [read_two]
      cases miss
      · simp [repeated_iff d]
      · simp [missing_iff d]
        omega

end CeilingBlocks
#print axioms CeilingBlocks.mem_offsets_source
