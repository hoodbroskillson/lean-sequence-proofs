import FamilyMex
open private MexFamily.mex_fills MexFamily.sets MexFamily.separate from FamilyMex
namespace MexFamily
open Nat Finset
noncomputable section
variable (q : Params)

private def rank (f : ℕ→ℕ) (n : ℕ) := n.findGreatest (fun i => f i≤n)

private theorem rank_spec {f : ℕ→ℕ} (h : StrictMono f) (zero : f 0=0) (n : ℕ) :
    f (rank f n)≤n ∧ n<f (rank f n+1) := by
  have lo:=Nat.findGreatest_spec (P:=fun i=>f i≤n) (Nat.zero_le n) (by simp [zero])
  refine ⟨lo,?_⟩
  by_contra! bad
  have ub:rank f n+1≤n := (h.id_le _).trans bad
  have v:=Nat.le_findGreatest (P:=fun i=>f i≤n) ub bad
  change rank f n+1≤rank f n at v
  omega

/-- Number of positive lower-column entries ≤n. -/
def C (n : ℕ) := rank (A q) n

theorem C_spec (n : ℕ) : A q (C q n)≤n ∧ n<A q (C q n+1) :=
  rank_spec (strictA q) (starts q).1 n

theorem C_le (n : ℕ) : C q n≤n := ((strictA q).id_le _).trans (C_spec q n).1

theorem C_mono : Monotone (C q) := by
  intro n m h
  by_contra! bad
  have p:=(strictA q).monotone (show C q m+1≤C q n by omega)
  have a:=C_spec q n
  have b:=C_spec q m
  omega

theorem C_succ (n : ℕ) : C q (n+1)≤C q n+1 := by
  by_contra! bad
  have p:=strictA q bad
  have a:=C_spec q n
  have b:=C_spec q (n+1)
  omega

private theorem partition_rank (N : ℕ) : C q N+rank (B q) N=N := by
  let b:=rank (B q) N
  have z:=rank_spec (strictB q) (starts q).2.1 N
  change B q b≤N ∧ N<B q (b+1) at z
  have a:=C_spec q N
  let u:=(range (C q N+1)).image (A q)
  let v:=(range b).image (fun i=>B q (i+1))
  have dis : Disjoint u v := by
    rw [disjoint_left]
    rintro x hu hv
    obtain ⟨i,_,rfl⟩:=mem_image.mp hu
    obtain ⟨j,_,eq⟩:=mem_image.mp hv
    exact MexFamily.separate q i (j+1) (by omega) eq.symm
  have union : range (N+1)=u∪v := by
    ext x
    rw [mem_range,mem_union]
    constructor
    · intro h
      have gr : x<A q (N+1) := lt_of_lt_of_le h ((strictA q).id_le _)
      obtain ⟨i,_,ea|eb⟩:=(mem_sets q _ _).mp (MexFamily.mex_fills (MexFamily.sets q (N+1)) gr)
      · apply Or.inl
        have i_le : i≤C q N := by by_contra! bad;have := (strictA q).monotone (show C q N+1≤i by omega);omega
        exact mem_image.mpr ⟨i,mem_range.mpr (by omega),ea.symm⟩
      · cases i with
        | zero => exact Or.inl (mem_image.mpr ⟨0,mem_range.mpr (by omega),by rw [eb,(starts q).1,(starts q).2.1]⟩)
        | succ i =>
           have i_lt : i<b := by by_contra! bad;have := (strictB q).monotone (show b+1≤i+1 by omega);omega
           exact Or.inr (mem_image.mpr ⟨i,mem_range.mpr i_lt,eb.symm⟩)
    · rintro (hu|hv)
      · obtain ⟨i,hi,rfl⟩:=mem_image.mp hu
        have v:=(strictA q).monotone (show i≤C q N by have := mem_range.mp hi;omega)
        omega
      · obtain ⟨i,hi,rfl⟩:=mem_image.mp hv
        have v:=(strictB q).monotone (show i+1≤b by have :=mem_range.mp hi;omega)
        omega
  have inj : Function.Injective (fun i:ℕ=>B q (i+1)) := fun i j e => by have := (strictB q).injective e;omega
  have card:=congrArg Finset.card union
  rw [card_range,card_union_of_disjoint dis] at card
  dsimp [u,v] at card
  rw [card_image_of_injective _ (strictA q).injective,card_image_of_injective _ inj,card_range,card_range] at card
  change C q N+b=N
  omega

/-- Cutting the characteristic word after n letters leaves r of the next s A's. -/
theorem prefix_decomposition (n : ℕ) : ∃ k r, k≤n ∧ (0<n→k<n) ∧ r≤q.s ∧
    n=q.s*k+C q k+r ∧ n-C q n=C q k := by
  let W (k : ℕ) := q.s*k+C q k
  have inc : StrictMono W := by
    intro k j lt
    have a:=C_mono q lt.le
    have b:=Nat.mul_lt_mul_of_pos_left lt (show 0<q.s by have := q.ge;omega)
    dsimp [W];omega
  let k:=rank W n
  have zero : C q 0=0 := by have := C_le q 0;omega
  have h:=rank_spec inc (show W 0=0 by simp [W,zero]) n
  change q.s*k+C q k≤n ∧ n<q.s*(k+1)+C q (k+1) at h
  have l:=C_succ q k
  have x:=Nat.mul_le_mul_right k q.ge
  have zs:=q.ge
  rw [Nat.mul_add,Nat.mul_one] at h
  refine ⟨k,n-(q.s*k+C q k),by omega,fun _=>by omega,by omega,by omega,?_⟩
  have split:=partition_rank q n
  have lo:=C_spec q k
  have b:=rank_spec (strictB q) (starts q).2.1 n
  have b1 : B q (C q k)≤n := by
    unfold B
    have :=Nat.mul_le_mul_left q.s lo.1
    omega
  have b2 : n<B q (C q k+1) := by
    unfold B
    have :=Nat.mul_le_mul_left q.s (show k+1≤A q (C q k+1) by omega)
    rw [Nat.mul_add,Nat.mul_one] at this
    omega
  have eq : rank (B q) n=C q k := by
    rcases lt_trichotomy (rank (B q) n) (C q k) with lt|eq|gt
    · have := (strictB q).monotone (show rank (B q) n+1≤C q k by omega);omega
    · exact eq
    · have := (strictB q).monotone (show C q k+1≤rank (B q) n by omega);omega
  omega

/-- The gap sequence is the characteristic A-word sampled on multiples of s. -/
theorem compress (n : ℕ) : A q n=n+C q ((n-1)/q.s) := by
  cases n with
  | zero => have c:=C_le q 0;simpa [(starts q).1] using c
  | succ n =>
    obtain ⟨k,e,bl,bu,_⟩:=bracket q (n+1) (by omega)
    unfold B at bl bu
    have a : q.s*A q k≤n := by omega
    have b : n<q.s*A q (k+1) := by omega
    have sp : 0<q.s := by have:=q.ge;omega
    have c : A q k≤n/q.s := (Nat.le_div_iff_mul_le sp).mpr (by simpa [mul_comm] using a)
    have d : n/q.s<A q (k+1) := (Nat.div_lt_iff_lt_mul sp).mpr (by simpa [mul_comm] using b)
    have m:=C_spec q (n/q.s)
    have t : C q (n/q.s)=k := by
      rcases lt_trichotomy (C q (n/q.s)) k with lt|eq|gt
      · have := (strictA q).monotone (show C q (n/q.s)+1≤k by omega);omega
      · exact eq
      · have := (strictA q).monotone (show k+1≤C q (n/q.s) by omega);omega
    simp [t,e]
end
end MexFamily
#print axioms MexFamily.prefix_decomposition
#print axioms MexFamily.compress
