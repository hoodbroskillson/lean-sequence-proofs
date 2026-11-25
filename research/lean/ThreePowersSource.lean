import WallTower
namespace ThreePowersSource
open WallLift PowerLift WallTransfer PisanoSource

private theorem large (k : ℕ) : 2<3^(k+1) := by
  have h:1≤3^k:=Nat.one_le_pow _ _ (by decide)
  rw [pow_succ];omega

private theorem first : pi (m:=3) (by decide) (by decide)=8 := by
  let d:=pi (m:=3) (by decide) (by decide)
  have sp:=pi_spec (m:=3) (by decide) (by decide)
  have up : Fibonacci 3 8 := (state _ _).mpr (by decide)
  have dvd : d∣8:=(sp.2 _).mp up
  have pos : 0<d:=sp.1
  have atd:=(state 3 d).mp ((sp.2 _).mpr dvd_rfl)
  have limit:=Nat.le_of_dvd (by decide : 0<8) dvd
  have rejects : ∀j:Fin 8,0<j.val → ¬((F j.val:ZMod 3)=0 ∧ (F (j.val+1):ZMod 3)=1) := by decide
  change d=8
  by_contra ne
  exact rejects ⟨d,by omega⟩ pos atd

theorem powers (k:ℕ) : period (large k)=24*3^k := by
  have stair (i:ℕ) : Fibonacci (3^(i+1)) (3^i*8) ∧ ¬Fibonacci (3^(i+2)) (3^i*8) := by
    induction i with
    | zero => simp only [Nat.zero_add,pow_one,pow_zero,one_mul,state];decide
    | succ i ih =>
      rw [pow_succ' 3 i,Nat.mul_assoc]
      exact ⟨one_step (by decide : Nat.Prime 3) (by decide) (by omega) ih.1,fun h=>
        ih.2 ((faithful (by decide) (by decide) (by omega : 0<i+1) ih.1).mp h)⟩
  let c:=Nat.Coprime.pow_right (k+1) (by decide : Nat.Coprime 5 3)
  let D:=pi (large k) c
  have tower:=pi_spec (large k) c
  have high : D∣3^k*8 := (tower.2 _).mp (stair k).1
  have has : Fibonacci (3^(k+1)) D := (tower.2 _).mpr dvd_rfl
  have low : 8∣D := by
    rw [←first,←(pi_spec (m:=3) (by decide) (by decide)).2]
    exact descend (by rw [pow_succ'];exact dvd_mul_right 3 (3^k)) has
  obtain ⟨l,eq⟩:=low
  rw [eq,Nat.mul_comm (3^k) 8] at high
  obtain ⟨j,le,hj⟩:=(Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp (Nat.dvd_of_mul_dvd_mul_left (by decide : 0<8) high)
  have jk : j=k := by
    by_contra ne
    rw [eq,hj,Nat.mul_comm] at has
    exact (stair j).2 (descend (pow_dvd_pow _ (show j+2≤k+1 by omega)) has)
  rw [periods (large k) c]
  change 3*D=24*3^k
  rw [eq,hj,jk];ring
end ThreePowersSource
#print axioms ThreePowersSource.powers
