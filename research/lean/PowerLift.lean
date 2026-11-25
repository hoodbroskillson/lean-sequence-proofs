import WallLift
import Mathlib.Data.Nat.Choose.Dvd
import Batteries.Tactic.OpenPrivate
open private WallLift.U WallLift.addF from WallLift
namespace PowerLift
open WallLift PisanoSource

theorem state (m d:ℕ) : Fibonacci m d ↔ WallLift.U m d=0 ∧ WallLift.U m (d+1)=1 := by
  constructor
  · intro h
    constructor
    · simpa [F] using (h 0 le_rfl : (F (0+d):ZMod m)=F 0)
    · simpa only [Nat.add_comm 1 d,show F 1=1 by rfl,Nat.cast_one] using (h 1 (by omega) : (F (1+d):ZMod m)=F 1)
  · intro h n _
    change WallLift.U m (n+d)=WallLift.U m n
    rw [(WallLift.addF _ _ _).1,h.1,h.2];ring

private theorem expand {m d : ℕ} (M A B : ZMod m) (nil:M^3=0)
    (fa:WallLift.U m d=M*A) (fb:WallLift.U m (d+1)=1+M*B) (k:ℕ) :
    WallLift.U m (k*d)=(k:ZMod m)*M*A+(k.choose 2:ℕ)*M^2*(2*A*B-A^2) ∧
    WallLift.U m (k*d+1)=1+(k:ZMod m)*M*B+(k.choose 2:ℕ)*M^2*(A^2+B^2) := by
  induction k with
  | zero => simp [WallLift.U,F]
  | succ k ih =>
    rw [Nat.succ_mul,(WallLift.addF _ _ _).1,(WallLift.addF _ _ _).2,fa,fb,ih.1,ih.2,
      Nat.choose_succ_succ k 1,Nat.choose_one_right]
    push_cast
    constructor
    · linear_combination ((k.choose 2:ZMod m)*((2*A*B-A^2)*B+(A^2+B^2-(2*A*B-A^2))*A))*nil
    · linear_combination ((k.choose 2:ZMod m)*((2*A*B-A^2)*A+(A^2+B^2)*B))*nil

theorem first_order {p a d:ℕ} (prime:p.Prime) (hp:2<p) (ha:0<a) (h:Fibonacci (p^a) d) :
    WallLift.U (p^(a+2)) (p*d)=p*WallLift.U (p^(a+2)) d ∧
    WallLift.U (p^(a+2)) (p*d+1)-1=p*(WallLift.U (p^(a+2)) (d+1)-1) := by
  let m:=p^(a+2)
  let M:ZMod m:=(p^a:ℕ)
  have kill (n:ℕ) (hn:a+2≤n) : ((p^n:ℕ):ZMod m)=0 :=
    (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr (pow_dvd_pow _ hn)
  have nil : M^3=0 := by
    change (((p^a:ℕ):ZMod m))^3=0
    rw [←Nat.cast_pow,←pow_mul];apply kill;omega
  have die : (p:ZMod m)*M^2=0 := by
    change (p:ZMod m)*((p^a:ℕ):ZMod m)^2=0
    rw [←Nat.cast_pow,←Nat.cast_mul,←pow_mul,←pow_succ'];apply kill;omega
  obtain ⟨h0,h1⟩ := (state _ _).mp h
  obtain ⟨aa,ha'⟩ := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp h0
  obtain ⟨bb,hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd ((F (d+1):ℤ)-1) (p^a)).mp
    (by simpa [WallLift.U] using sub_eq_zero.mpr h1)
  let A:ZMod m:=aa;let B:ZMod m:=bb
  have fa : WallLift.U m d=M*A := by change (F d:ZMod m)=((p^a:ℕ):ZMod m)*aa;rw [ha',Nat.cast_mul]
  have fb : WallLift.U m (d+1)=1+M*B := by
    have b:=congrArg (fun x:ℤ => (x:ZMod m)) hb
    push_cast at b
    change _=1+((p^a:ℕ):ZMod m)*(bb:ZMod m)
    push_cast
    linear_combination b
  obtain ⟨q,hq⟩:=prime.dvd_choose_self (by decide : 2≠0) hp
  have value:=expand M A B nil fa fb p
  rw [hq,Nat.cast_mul] at value
  change WallLift.U m (p*d)=p*WallLift.U m d ∧ WallLift.U m (p*d+1)-1=p*(WallLift.U m (d+1)-1)
  rw [fa,fb,value.1,value.2]
  constructor
  · linear_combination ((q:ZMod m)*(2*A*B-A^2))*die
  · linear_combination ((q:ZMod m)*(A^2+B^2))*die

private theorem cancel {p:ℕ} (hp:0<p) (a:ℕ) (x:ℤ) :
    (p:ZMod (p^(a+1)))*x=0 ↔ (x:ZMod (p^a))=0 := by
  rw [←Int.cast_natCast p,←Int.cast_mul,ZMod.intCast_zmod_eq_zero_iff_dvd,ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [pow_succ',mul_dvd_mul_iff_left (by exact_mod_cast Nat.ne_of_gt hp : (p:ℤ)≠0)]

theorem faithful {p a d:ℕ} (prime:p.Prime) (hp:2<p) (ha:0<a) (h:Fibonacci (p^a) d) :
    Fibonacci (p^(a+2)) (p*d) ↔ Fibonacci (p^(a+1)) d := by
  obtain ⟨x,y⟩:=first_order prime hp ha h
  rw [state,state,x,←sub_eq_zero (b:=(1:ZMod (p^(a+2)))),y,←sub_eq_zero (b:=(1:ZMod (p^(a+1))))]
  apply and_congr
  · simpa only [Int.cast_natCast] using cancel (by omega : 0<p) (a+1) (F d)
  · simpa only [Int.cast_natCast,Int.cast_one,Int.cast_sub] using cancel (by omega : 0<p) (a+1) ((F (d+1):ℤ)-1)

theorem one_step {p a d:ℕ} (prime:p.Prime) (hp:2<p) (ha:0<a) (h:Fibonacci (p^a) d) :
    Fibonacci (p^(a+1)) (p*d) := by
  obtain ⟨x,y⟩:=first_order prime hp ha h
  let f:=ZMod.castHom (pow_dvd_pow p (show a+1≤a+2 by omega)) (ZMod (p^(a+1)))
  have xx:=congrArg f x;have yy:=congrArg f y
  simp only [WallLift.U,map_mul,map_one,map_sub,map_natCast] at xx yy
  obtain ⟨u,v⟩:=(state _ _).mp h
  apply (state _ _).mpr
  constructor
  · rw [show WallLift.U (p^(a+1)) (p*d)=_ from xx]
    simpa only [Int.cast_natCast] using (cancel (by omega : 0<p) a (F d)).mpr (by simpa only [Int.cast_natCast] using u)
  · apply sub_eq_zero.mp
    rw [show WallLift.U (p^(a+1)) (p*d+1)-1=_ from yy]
    simpa only [Int.cast_sub,Int.cast_natCast,Int.cast_one] using (cancel (by omega : 0<p) a ((F (d+1):ℤ)-1)).mpr
      (by simpa only [Int.cast_sub,Int.cast_natCast,Int.cast_one] using sub_eq_zero.mpr v)

end PowerLift
#print axioms PowerLift.faithful
#print axioms PowerLift.one_step
