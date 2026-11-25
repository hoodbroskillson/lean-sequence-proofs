import Mathlib.Data.List.Chain
namespace GapChain
/-- If every adjacent pair has an increasing relation, any two members with no intermediate member are adjacent. -/
theorem extract {R : ℕ→ℕ→Prop} (inc : ∀ {a b}, R a b → a<b) (xs : List ℕ) (hc : xs.Chain' R)
    {x y : ℕ} (hx : x∈xs) (hy : y∈xs) (lt : x<y) (no : ∀z∈xs, x<z → z<y → False) : R x y := by
  induction xs with
  | nil => simp at hx
  | cons a as ih =>
    have sorted := (List.chain'_iff_pairwise).mp (hc.imp (fun _ _ h => inc h))
    rcases List.mem_cons.mp hx with xa|xt
    · subst x
      cases as with
      | nil =>
        have := List.mem_singleton.mp hy
        omega
      | cons b bs =>
        obtain ⟨ab,hb⟩ := List.chain'_cons.mp hc
        rcases List.mem_cons.mp hy with ya|yr
        · omega
        · rcases List.mem_cons.mp yr with yb|ys
          · simpa [yb] using ab
          · have sp := (List.chain'_iff_pairwise).mp (hb.imp (fun _ _ h => inc h))
            exact False.elim (no b (by simp) (inc ab) (List.rel_of_pairwise_cons sp ys))
    · rcases List.mem_cons.mp hy with ya|yt
      · have := List.rel_of_pairwise_cons sorted xt
        omega
      · exact ih hc.tail xt yt (fun z hz hz1 hz2 => no z (List.mem_cons_of_mem _ hz) hz1 hz2)
end GapChain
#print axioms GapChain.extract
