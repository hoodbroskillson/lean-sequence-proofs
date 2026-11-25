import WallTransfer
namespace WallLift
open PisanoSource WallTransfer

private abbrev U (m n:ℕ) : ZMod m := F n
private theorem recF (m n : ℕ) : U m (n+2)=U m (n+1)+U m n := by
  change ((F (n+1)+F n:ℕ):ZMod m)=_
  push_cast
  rfl

private theorem addF (m a b : ℕ) :
    U m (a+b)=U m a*U m (b+1)+(U m (a+1)-U m a)*U m b ∧
    U m (a+b+1)=U m a*U m b+U m (a+1)*U m (b+1) := by
  induction b with
  | zero => norm_num [U,F]
  | succ b ih =>
    change U m (a+b+1)=U m a*U m (b+2)+(U m (a+1)-U m a)*U m (b+1) ∧
      U m (a+b+2)=U m a*U m (b+1)+U m (a+1)*U m (b+2)
    rw [recF m (a+b),recF m b,ih.1,ih.2]
    constructor <;> ring

theorem lift {m d : ℕ} (h : Fibonacci m d) : Fibonacci (m^2) (m*d) := by
  let R:=ZMod (m^2)
  let M:R:=m
  have nil : M^2=0 := by
    change (m:ZMod (m^2))^2=0
    rw [←Nat.cast_pow]
    exact ZMod.natCast_self _
  have h0 : (F d:ZMod m)=0 := by simpa [F] using (h 0 le_rfl : (F (0+d):ZMod m)=F 0)
  have h1 : (F (d+1):ZMod m)=1 := by simpa only [Nat.add_comm 1 d,show F 1=1 by rfl,Nat.cast_one] using (h 1 (by omega) : (F (1+d):ZMod m)=F 1)
  obtain ⟨aa,ha⟩ := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp h0
  obtain ⟨bb,hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd ((F (d+1):ℤ)-1) m).mp (by simpa using sub_eq_zero.mpr h1)
  let A:R:=aa;let B:R:=bb
  have fa : U (m^2) d=M*A := by change (F d:ZMod (m^2))=(m:ZMod (m^2))*aa;rw [ha,Nat.cast_mul]
  have fb : U (m^2) (d+1)=1+M*B := by
    have b:=congrArg (fun x:ℤ => (x:ZMod (m^2))) hb
    push_cast at b
    change _=1+(m:ZMod (m^2))*(bb:ZMod (m^2))
    linear_combination b
  have iterate (k:ℕ) : U (m^2) (k*d)=(k:R)*M*A ∧ U (m^2) (k*d+1)=1+(k:R)*M*B := by
    induction k with
    | zero => simp [U,F]
    | succ k ih =>
      rw [Nat.succ_mul,(addF _ _ _).1,(addF _ _ _).2,fa,fb,ih.1,ih.2]
      push_cast
      constructor
      · linear_combination ((k:R)*(2*A*B-A^2))*nil
      · linear_combination ((k:R)*(A^2+B^2))*nil
  have e:=iterate m
  change U (m^2) (m*d)=M*M*A ∧ U (m^2) (m*d+1)=1+M*M*B at e
  rw [←sq,nil,zero_mul,zero_mul,add_zero] at e
  intro n _
  change U (m^2) (n+m*d)=U (m^2) n
  rw [(addF _ _ _).1,e.1,e.2];ring

theorem descend {m q t : ℕ} (hd : m∣q) (h : Fibonacci q t) : Fibonacci m t := by
  intro n _
  have z := congrArg (ZMod.castHom hd (ZMod m)) (h n (by omega) : (F (n+t):ZMod q)=F n)
  simpa only [map_natCast] using z

theorem alternatives {p:ℕ} (prime:p.Prime) (hp:5<p) :
    WallTransfer.period (m:=p^2) (by nlinarith)=WallTransfer.period (m:=p) (by omega) ∨
    WallTransfer.period (m:=p^2) (by nlinarith)=p*WallTransfer.period (m:=p) (by omega) := by
  let d:=pi (m:=p) (by omega) (cop prime hp)
  let D:=pi (m:=p^2) (by nlinarith) ((cop prime hp).pow_right 2)
  have one:=pi_spec (m:=p) (by omega) (cop prime hp)
  have two:=pi_spec (m:=p^2) (by nlinarith) ((cop prime hp).pow_right 2)
  have pd : Fibonacci p d := (one.2 _).mpr dvd_rfl
  have pD : Fibonacci (p^2) D := (two.2 _).mpr dvd_rfl
  have low : d∣D := (one.2 _).mp (descend (by rw [sq];exact dvd_mul_right p p) pD)
  have high : D∣p*d := (two.2 _).mp (lift pd)
  obtain ⟨k,hk⟩:=low
  rw [hk,Nat.mul_comm p d] at high
  have h:= (Nat.dvd_prime prime).mp (Nat.dvd_of_mul_dvd_mul_left one.1 high)
  rw [periods (by nlinarith : 2<p^2) ((cop prime hp).pow_right 2),periods (by omega : 2<p) (cop prime hp)]
  change 3*D=3*d ∨ 3*D=p*(3*d)
  rcases h with rfl|rfl
  · left;rw [hk,Nat.mul_one]
  · right;rw [hk];ring

end WallLift
#print axioms WallLift.lift
#print axioms WallLift.alternatives
