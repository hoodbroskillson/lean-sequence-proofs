import PisanoSource
import LucasParity
namespace WallTransfer
open PisanoSource

private theorem fib_exists {m:ℕ} (hm:2<m) (hc:Nat.Coprime 5 m) : ∃t,0<t ∧ Fibonacci m t := by
  have spec:=pisano (by omega : 1<m) hc
  exact ⟨_,spec.1,(spec.2 _).mpr dvd_rfl⟩

noncomputable def pi {m:ℕ} (hm:2<m) (hc:Nat.Coprime 5 m) : ℕ := by
  classical
  exact Nat.find (fib_exists hm hc)

private theorem source_exists {m:ℕ} (hm:2<m) : ∃t,0<t ∧ ∃N, FinitePeriod.Tail m N t := by
  have bound : 0<3*LucasLeast.L (by omega : 1<m) :=
    Nat.mul_pos (by decide) (LucasLeast.least_spec _).1
  exact ⟨_,bound,5,(LucasParity.source hm 5 _).mpr (Or.inr ⟨le_rfl,dvd_rfl⟩)⟩

noncomputable def period {m:ℕ} (hm:2<m) : ℕ := by
  classical
  exact Nat.find (source_exists hm)

theorem pi_eq {m:ℕ} (hm:2<m) (hc:Nat.Coprime 5 m) : pi hm hc=LucasLeast.L (by omega : 1<m) := by
  classical
  have key:=pisano (by omega : 1<m) hc
  have mine : 0<pi hm hc ∧ Fibonacci m (pi hm hc) := Nat.find_spec (fib_exists hm hc)
  apply Nat.le_antisymm
  · exact Nat.find_min' (fib_exists hm hc) ⟨key.1,(key.2 _).mpr dvd_rfl⟩
  · exact Nat.le_of_dvd mine.1 ((key.2 _).mp mine.2)

theorem pi_spec {m:ℕ} (hm:2<m) (hc:Nat.Coprime 5 m) :
    0<pi hm hc ∧ ∀t,Fibonacci m t ↔ pi hm hc∣t := by
  simpa only [pi_eq] using pisano (by omega : 1<m) hc

theorem periods {m:ℕ} (hm:2<m) (hc:Nat.Coprime 5 m) : period hm=3*pi hm hc := by
  classical
  have key:=pisano (by omega : 1<m) hc
  rw [pi_eq]
  have src : 0<period hm ∧ ∃N,FinitePeriod.Tail m N (period hm) := Nat.find_spec (source_exists hm)
  obtain ⟨N,e⟩:=src.2
  have positive:=src.1
  apply Nat.le_antisymm
  · exact Nat.find_min' (source_exists hm) ⟨Nat.mul_pos (by decide) key.1,5,
      (LucasParity.source hm 5 _).mpr (Or.inr ⟨le_rfl,dvd_rfl⟩)⟩
  · exact Nat.le_of_dvd positive (((LucasParity.source hm N _).mp e).resolve_left (by omega)).2

theorem cop {p:ℕ} (hp:p.Prime) (h5:5<p) : Nat.Coprime 5 p :=
  (hp.coprime_iff_not_dvd.mpr (fun h => (Nat.not_le_of_lt h5) (Nat.le_of_dvd (by decide) h))).symm

theorem wall_iff {p:ℕ} (hp:p.Prime) (h5:5<p) :
    period (m:=p^2) (by nlinarith)=period (m:=p) (by omega) ↔
    pi (m:=p^2) (by nlinarith) ((cop hp h5).pow_right 2)=pi (m:=p) (by omega) (cop hp h5) := by
  rw [periods (by nlinarith : 2<p^2) ((cop hp h5).pow_right 2),
      periods (by omega : 2<p) (cop hp h5)]
  omega

end WallTransfer
#print axioms WallTransfer.wall_iff
#print axioms WallTransfer.periods
