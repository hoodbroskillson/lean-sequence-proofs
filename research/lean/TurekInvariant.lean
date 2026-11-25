import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace MexFamily
namespace FourCuts

private def crosses (s p q : ℤ) : Prop :=
  (p ≤ -(s+1) ∧ s+1 ≤ q) ∨ (q ≤ -(s+1) ∧ s+1 ≤ p)

/-- A discrepancy with opposite large letter counts forces the same obstruction
one substitution level earlier. The four incomplete blocks contribute at most 2s. -/
private theorem predecessor {s p q a b e : ℤ} (hs : 0≤s)
    (pn : p=s*(a+b)+e) (qn : q=a) (lo : -(2*s)≤e) (hi : e≤2*s)
    (danger : crosses s p q) : crosses s a b := by
  rcases danger with ⟨hp,hq⟩|⟨hq,hp⟩
  · have sum : a+b≤0 := by
      by_contra! h
      have pos : (1:ℤ)≤a+b := by omega
      have mul := (mul_le_mul_of_nonneg_left pos hs)
      linarith
    exact Or.inr ⟨by omega,by omega⟩
  · have sum : 0≤a+b := by
      by_contra! h
      have neg : a+b≤(-1:ℤ) := by omega
      have mul := (mul_le_mul_of_nonneg_left neg hs)
      linarith
    exact Or.inl ⟨by omega,by omega⟩

private def signed (a b c d : ℕ) : ℤ := (a:ℤ)+b-c-d

private theorem smaller_cut {a b c d x y v w : ℕ}
    (h : 0<a+b+c+d) (a₁:x≤a) (b₁:y≤b) (c₁:v≤c) (d₁:w≤d)
    (a₂:0<a→x<a) (b₂:0<b→y<b) (c₂:0<c→v<c) (d₂:0<d→w<d) :
    x+y+v+w<a+b+c+d := by omega

private theorem residual {s i j k l:ℕ} (a:i≤s) (b:j≤s) (c:k≤s) (d:l≤s) :
    -(2*(s:ℤ))≤signed i j k l ∧ signed i j k l≤2*(s:ℤ) := by unfold signed;omega

private theorem lift {s x k r : ℕ} {C : ℕ→ℕ} (sub : ∀n,C n≤n)
    (l : x=s*k+C k+r) (y : x-C x=C k) :
    (C x:ℤ)=(s:ℤ)*((C k:ℤ)+(k-C k:ℕ))+r := by
  rw [Nat.cast_sub (sub k)]
  have l' : (x:ℤ)=(s:ℤ)*k+C k+r := by exact_mod_cast l
  have hn : C x+C k=x := by have:=sub x; omega
  have y' : (C x:ℤ)+C k=x := by exact_mod_cast hn
  linear_combination l' + y'

private theorem no_cross {s : ℕ} {C : ℕ→ℕ} (sub : ∀n,C n≤n)
    (step : ∀n, ∃k r : ℕ, k≤n ∧ (0<n→k<n) ∧ r≤s ∧
      n=s*k+C k+r ∧ n-C n=C k) (z : ℕ) :
    ∀ a b c d, a+b+c+d=z →
      ¬crosses s (signed (C a) (C b) (C c) (C d))
        (signed (a-C a) (b-C b) (c-C c) (d-C d)) := by
  induction z using Nat.strong_induction_on with
  | h z ih =>
    intro a b c d sum bad
    by_cases zero : z=0
    · have az : a=0 := by omega
      have bz : b=0 := by omega
      have cz : c=0 := by omega
      have dz : d=0 := by omega
      simp [az,bz,cz,dz,signed,crosses] at bad
      omega
    obtain ⟨a',e₁,oa,da,ha,la,ya⟩:=step a
    obtain ⟨b',e₂,ob,db,hb,lb,yb⟩:=step b
    obtain ⟨c',e₃,oc,dc,hc,lc,yc⟩:=step c
    obtain ⟨d',e₄,od,dd,hd,ld,yd⟩:=step d
    obtain ⟨lo,hi⟩:=residual ha hb hc hd
    have positive : 0<a+b+c+d := sum.symm ▸ Nat.pos_of_ne_zero zero
    have smaller : a'+b'+c'+d'<z := sum ▸ smaller_cut positive oa ob oc od da db dc dd
    apply ih (a'+b'+c'+d') smaller a' b' c' d' rfl
    apply predecessor (e:=signed e₁ e₂ e₃ e₄) (by positivity) _ _ lo hi bad
    · unfold signed
      rw [lift sub la ya,lift sub lb yb,lift sub lc yc,lift sub ld yd]
      ring
    · simp [ya,yb,yc,yd]

/-- Any two equal-length windows in the fixed word A → A^s B, B → A^s
have A-counts differing by at most s. Only the lengths of prefix blocks are
needed to specify the word. -/
theorem characteristic_balanced {s : ℕ} {C : ℕ→ℕ} (_hs : 2≤s)
    (hsub : ∀n,C n≤n)
    (H : ∀n, ∃k r : ℕ, k≤n ∧ (0<n→k<n) ∧ r≤s ∧
      n=s*k+C k+r ∧ n-C n=C k)
    (i j k:ℕ) : C (i+k)+C j≤C (j+k)+C i+s := by
  by_contra! h
  apply no_cross hsub H _ (i+k) j (j+k) i rfl
  apply Or.inr
  unfold signed
  rw [Nat.cast_sub (hsub _),Nat.cast_sub (hsub _),Nat.cast_sub (hsub _),Nat.cast_sub (hsub _)]
  omega

end FourCuts
end MexFamily
#print axioms MexFamily.FourCuts.characteristic_balanced
