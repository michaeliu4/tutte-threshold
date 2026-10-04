import Results.TutteThreshold.Solution.Rk
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

/-!
# Weighted rank sums

`Z M z v W = ∑_{S ⊆ E} z^{r(E)-r(S)} v^{|S|-r(S)} ∏_{f∈S} W¹ f ∏_{f∈E∖S} W⁰ f`.

With all weights `(1,1)` and `(z, v) = (x-1, y-1)` this is the Tutte polynomial.
The three evaluations used in the proof are `(z,v) = (0,0)` (bases), `(z,-1)` (axis `y=0`) and
`(-1,z)` (axis `x=0`).
-/

namespace Results.TutteThreshold

open Finset

/-- a pair of weights `(W⁰, W¹)`: `W⁰` for an element outside the subset, `W¹` for one inside -/
abbrev Wt := ℝ × ℝ

namespace RkMat

variable {ι : Type*} [DecidableEq ι]

/-- the weighted rank sum -/
noncomputable def Z (M : RkMat ι) (z v : ℝ) (W : ι → Wt) : ℝ :=
  ∑ S ∈ M.E.powerset,
    z ^ (M.r M.E - M.r S) * v ^ (S.card - M.r S) *
      ((∏ f ∈ S, (W f).2) * ∏ f ∈ M.E \ S, (W f).1)

/-- the weights of two parallel elements merged into one -/
def mergeW (v : ℝ) (a b : Wt) : Wt := (a.1 * b.1, a.2 * b.1 + a.1 * b.2 + v * a.2 * b.2)

variable (M : RkMat ι) (z v : ℝ) (W : ι → Wt)

/-! ### Auxiliary rank facts (proved from the axioms of `RkMat`) -/

/-- adding one element raises the rank by at most one -/
private lemma zs_r_insert_le {S : Finset ι} (hS : S ⊆ M.E) {f : ι} (hf : f ∈ M.E) :
    M.r (insert f S) ≤ M.r S + 1 := by
  have h1 := M.r_submod (singleton_subset_iff.2 hf) hS
  rw [← insert_eq] at h1
  have h2 := M.r_single_le hf
  omega

/-- adding a loop does not change the rank -/
private lemma zs_r_insert_loop {S : Finset ι} (hS : S ⊆ M.E) {f : ι} (hf : f ∈ M.E)
    (h0 : M.r {f} = 0) : M.r (insert f S) = M.r S := by
  have h1 := M.r_submod (singleton_subset_iff.2 hf) hS
  rw [← insert_eq] at h1
  have h2 := M.r_le_insert hS hf
  omega

/-- adding a coloop to a set avoiding it raises the rank by one -/
private lemma zs_r_insert_coloop {f : ι} (hf : f ∈ M.E) (hc : M.r (M.E.erase f) + 1 = M.r M.E)
    {S : Finset ι} (hS : S ⊆ M.E.erase f) : M.r (insert f S) = M.r S + 1 := by
  have hSE : S ⊆ M.E := hS.trans (erase_subset f M.E)
  have h1 := M.r_submod (insert_subset hf hSE) (erase_subset f M.E)
  rw [insert_union, union_eq_right.2 hS, insert_erase hf,
    insert_inter_of_notMem (notMem_erase f M.E), inter_eq_left.2 hS] at h1
  have h2 := zs_r_insert_le M hSE hf
  omega

/-- for a parallel pair `{f, g}`, adding `f` to a set containing `g` keeps the rank -/
private lemma zs_r_insert_par {f g : ι} (hf : f ∈ M.E) (hg : g ∈ M.E) (hg1 : M.r {g} = 1)
    (hfg : M.r {f, g} = 1) {S : Finset ι} (hS : S ⊆ M.E) :
    M.r (insert f (insert g S)) = M.r (insert g S) := by
  have hgS : insert g S ⊆ M.E := insert_subset hg hS
  have h1 := M.r_submod hgS (insert_subset hf (singleton_subset_iff.2 hg))
  have hu : insert g S ∪ {f, g} = insert f (insert g S) := by
    ext x; simp only [mem_union, mem_insert, mem_singleton]; tauto
  have h2 : M.r {g} ≤ M.r (insert g S ∩ {f, g}) :=
    M.r_mono (singleton_subset_iff.2 (mem_inter.2 ⟨mem_insert_self g S, by simp⟩))
      (inter_subset_left.trans hgS)
  rw [hu] at h1
  have h3 := M.r_le_insert hgS hf
  omega

/-- additivity of the rank along a separator -/
private lemma zs_sep_r_add {A : Finset ι} (hA : M.IsSep A) {S : Finset ι} (hS : S ⊆ M.E) :
    M.r S = M.r (S ∩ A) + M.r (S \ A) := by
  obtain ⟨hAE, hrA⟩ := hA
  have hXE : S ∩ A ⊆ M.E := inter_subset_left.trans hS
  have hYE : S \ A ⊆ M.E := sdiff_subset.trans hS
  have hBE : M.E \ A ⊆ M.E := sdiff_subset
  have h1 := M.r_submod (union_subset hXE hBE) hAE
  have hu1 : S ∩ A ∪ M.E \ A ∪ A = M.E := by
    ext x; have := @hAE x; have := @hS x; simp only [mem_union, mem_inter, mem_sdiff]; tauto
  have hi1 : (S ∩ A ∪ M.E \ A) ∩ A = S ∩ A := by
    ext x; simp only [mem_union, mem_inter, mem_sdiff]; tauto
  rw [hu1, hi1] at h1
  have h1' := M.r_union_le hXE hBE
  have h2 := M.r_submod (union_subset hXE hYE) hBE
  have hu2 : S ∩ A ∪ S \ A ∪ M.E \ A = S ∩ A ∪ M.E \ A := by
    ext x; have := @hS x; simp only [mem_union, mem_inter, mem_sdiff]; tauto
  have hi2 : (S ∩ A ∪ S \ A) ∩ (M.E \ A) = S \ A := by
    ext x; have := @hS x; simp only [mem_union, mem_inter, mem_sdiff]; tauto
  have hXY : S ∩ A ∪ S \ A = S := by
    ext x; simp only [mem_union, mem_inter, mem_sdiff]; tauto
  rw [hu2, hi2, hXY] at h2
  have h3 := M.r_union_le hXE hYE
  rw [hXY] at h3
  omega

/-! ### Splitting the sum at one element -/

/-- a sum over the subsets of `U` split according to the membership of `f` -/
private lemma zs_sum_split {U : Finset ι} {f : ι} (hf : f ∈ U) (F : Finset ι → ℝ) :
    ∑ S ∈ U.powerset, F S = ∑ S ∈ (U.erase f).powerset, (F S + F (insert f S)) := by
  have hnot : f ∉ U.erase f := notMem_erase f U
  rw [sum_add_distrib]
  conv_lhs => rw [← insert_erase hf, powerset_insert]
  rw [sum_union, sum_image]
  · intro S hS T hT hST
    have hS' : f ∉ S := fun h => hnot (mem_powerset.1 hS h)
    have hT' : f ∉ T := fun h => hnot (mem_powerset.1 hT h)
    calc S = (insert f S).erase f := (erase_insert hS').symm
      _ = (insert f T).erase f := by rw [hST]
      _ = T := erase_insert hT'
  · rw [disjoint_left]
    intro S hS hS2
    obtain ⟨T, _, hT⟩ := mem_image.1 hS2
    exact hnot (mem_powerset.1 hS (hT ▸ mem_insert_self f T))

/-- the sum defining `Z` split according to the membership of `f` -/
private lemma Z_split {f : ι} (hf : f ∈ M.E) :
    M.Z z v W = ∑ S ∈ (M.E.erase f).powerset,
      ((W f).1 * (z ^ (M.r M.E - M.r S) * v ^ (S.card - M.r S) *
          ((∏ g ∈ S, (W g).2) * ∏ g ∈ M.E.erase f \ S, (W g).1)) +
        (W f).2 * (z ^ (M.r M.E - M.r (insert f S)) * v ^ (S.card + 1 - M.r (insert f S)) *
          ((∏ g ∈ S, (W g).2) * ∏ g ∈ M.E.erase f \ S, (W g).1))) := by
  unfold Z
  rw [zs_sum_split hf]
  refine sum_congr rfl fun S hS => ?_
  have hfS : f ∉ S := fun h => notMem_erase f M.E (mem_powerset.1 hS h)
  have h1 : ∏ g ∈ M.E \ S, (W g).1 = (W f).1 * ∏ g ∈ M.E.erase f \ S, (W g).1 := by
    rw [erase_sdiff_comm]
    exact (mul_prod_erase _ _ (mem_sdiff.2 ⟨hf, hfS⟩)).symm
  rw [prod_insert hfS, card_insert_of_notMem hfS, sdiff_insert, ← erase_sdiff_comm, h1]
  ring

/-- `Z` of a deletion, unfolded -/
private lemma Z_del_eq (f : ι) : (M.del f).Z z v W = ∑ S ∈ (M.E.erase f).powerset,
    z ^ (M.r (M.E.erase f) - M.r S) * v ^ (S.card - M.r S) *
      ((∏ g ∈ S, (W g).2) * ∏ g ∈ M.E.erase f \ S, (W g).1) := rfl

/-! ### The weighted rank sum -/

lemma Z_congr {M N : RkMat ι} (h : Same M N) {W W' : ι → Wt} (hW : ∀ f ∈ M.E, W f = W' f) :
    M.Z z v W = N.Z z v W' := by
  unfold Z
  rw [← h.1]
  refine sum_congr rfl fun S hS => ?_
  have hSE : S ⊆ M.E := mem_powerset.1 hS
  have h1 : ∏ f ∈ S, (W f).2 = ∏ f ∈ S, (W' f).2 :=
    prod_congr rfl fun f hf => by rw [hW f (hSE hf)]
  have h2 : ∏ f ∈ M.E \ S, (W f).1 = ∏ f ∈ M.E \ S, (W' f).1 :=
    prod_congr rfl fun f hf => by rw [hW f (mem_sdiff.1 hf).1]
  rw [← h.2 S hSE, ← h.2 M.E subset_rfl, h1, h2]

lemma Z_empty (h : M.E = ∅) : M.Z z v W = 1 := by
  unfold Z
  rw [h]
  simp

/-- a loop contributes `W⁰ + v W¹` -/
lemma Z_loop {f : ι} (hf : f ∈ M.E) (h0 : M.r {f} = 0) :
    M.Z z v W = ((W f).1 + v * (W f).2) * (M.del f).Z z v W := by
  have hE : M.r (M.E.erase f) = M.r M.E := by
    have h := zs_r_insert_loop M (erase_subset f M.E) hf h0
    rw [insert_erase hf] at h
    exact h.symm
  rw [Z_split M z v W hf, Z_del_eq, mul_sum]
  refine sum_congr rfl fun S hS => ?_
  have hSE : S ⊆ M.E := (mem_powerset.1 hS).trans (erase_subset f M.E)
  have hc : S.card + 1 - M.r S = S.card - M.r S + 1 := by
    have := M.r_le_card hSE
    omega
  rw [zs_r_insert_loop M hSE hf h0, hE, hc, pow_succ]
  ring

/-- a coloop contributes `z W⁰ + W¹` -/
lemma Z_coloop {f : ι} (hf : f ∈ M.E) (hc : M.r (M.E.erase f) + 1 = M.r M.E) :
    M.Z z v W = (z * (W f).1 + (W f).2) * (M.del f).Z z v W := by
  rw [Z_split M z v W hf, Z_del_eq, mul_sum]
  refine sum_congr rfl fun S hS => ?_
  have hS' : S ⊆ M.E.erase f := mem_powerset.1 hS
  have hle : M.r S ≤ M.r (M.E.erase f) := M.r_mono hS' (erase_subset f M.E)
  have e1 : M.r M.E - M.r S = M.r (M.E.erase f) - M.r S + 1 := by omega
  have e2 : M.r M.E - (M.r S + 1) = M.r (M.E.erase f) - M.r S := by omega
  have e3 : S.card + 1 - (M.r S + 1) = S.card - M.r S := by omega
  rw [zs_r_insert_coloop M hf hc hS', e1, e2, e3, pow_succ]
  ring

/-- deletion–contraction for any matroid `N` presented with the rank function of `M/f` -/
private lemma zs_ord_gen {f : ι} (hf : f ∈ M.E) (h1 : M.r {f} = 1)
    (hc : M.r (M.E.erase f) = M.r M.E) (N : RkMat ι) (hNE : N.E = M.E.erase f)
    (hNr : ∀ S, N.r S = M.r (insert f S) - M.r {f}) :
    M.Z z v W = (W f).1 * (M.del f).Z z v W + (W f).2 * N.Z z v W := by
  have hN : N.Z z v W = ∑ S ∈ (M.E.erase f).powerset,
      z ^ ((M.r (insert f (M.E.erase f)) - M.r {f}) - (M.r (insert f S) - M.r {f})) *
        v ^ (S.card - (M.r (insert f S) - M.r {f})) *
        ((∏ g ∈ S, (W g).2) * ∏ g ∈ M.E.erase f \ S, (W g).1) := by
    unfold Z
    simp only [hNE, hNr]
  rw [Z_split M z v W hf, Z_del_eq, hN, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun S hS => ?_
  have hSE : S ⊆ M.E := (mem_powerset.1 hS).trans (erase_subset f M.E)
  have hge : 1 ≤ M.r (insert f S) := h1 ▸
    M.r_mono (singleton_subset_iff.2 (mem_insert_self f S)) (insert_subset hf hSE)
  have e1 : M.r M.E - 1 - (M.r (insert f S) - 1) = M.r M.E - M.r (insert f S) := by omega
  have e2 : S.card - (M.r (insert f S) - 1) = S.card + 1 - M.r (insert f S) := by omega
  rw [insert_erase hf, h1, hc, e1, e2]

/-- weighted deletion–contraction at an element that is neither a loop nor a coloop -/
lemma Z_ord {f : ι} (hf : f ∈ M.E) (h1 : M.r {f} = 1) (hc : M.r (M.E.erase f) = M.r M.E) :
    M.Z z v W = (W f).1 * (M.del f).Z z v W + (W f).2 * (M.con f hf).Z z v W :=
  zs_ord_gen M z v W hf h1 hc (M.con f hf) rfl fun _ => rfl

/-- duality for any matroid `N` presented with the rank function of `M*` -/
private lemma zs_dual_gen (N : RkMat ι) (hNE : N.E = M.E)
    (hNr : ∀ S, N.r S = S.card + M.r (M.E \ S) - M.r M.E) :
    N.Z z v W = M.Z v z (fun f => ((W f).2, (W f).1)) := by
  unfold Z
  simp only [hNE, hNr]
  refine sum_nbij' (fun S => M.E \ S) (fun S => M.E \ S) ?_ ?_ ?_ ?_ ?_
  · intro S _
    exact mem_powerset.2 sdiff_subset
  · intro S _
    exact mem_powerset.2 sdiff_subset
  · intro S hS
    exact Finset.sdiff_sdiff_eq_self (mem_powerset.1 hS)
  · intro S hS
    exact Finset.sdiff_sdiff_eq_self (mem_powerset.1 hS)
  · intro S hS
    have hSE : S ⊆ M.E := mem_powerset.1 hS
    have hT : M.E \ S ⊆ M.E := sdiff_subset
    have h1 := M.r_le_card hT
    have h2 := M.r_le_card hSE
    have h3 : M.r M.E ≤ M.r S + M.r (M.E \ S) := by
      have := M.r_union_le hSE hT
      rwa [union_sdiff_of_subset hSE] at this
    have h4 := M.r_le_r_E hT
    have h5 : (M.E \ S).card = M.E.card - S.card := card_sdiff_of_subset hSE
    have h6 := card_le_card hSE
    have e1 : M.E.card + 0 - M.r M.E - (S.card + M.r (M.E \ S) - M.r M.E) =
        (M.E \ S).card - M.r (M.E \ S) := by omega
    have e2 : S.card - (S.card + M.r (M.E \ S) - M.r M.E) = M.r M.E - M.r (M.E \ S) := by omega
    rw [Finset.sdiff_self, M.r_empty, e1, e2, Finset.sdiff_sdiff_eq_self hSE]
    ring

/-- duality: swap `z` and `v`, and the two weights -/
lemma Z_dual : M.dual.Z z v W = M.Z v z (fun f => ((W f).2, (W f).1)) :=
  zs_dual_gen M z v W M.dual rfl fun _ => rfl

/-! ### Products over separators and partitions -/

/-- `Z` of the restriction of `M` to `U` (no subset proof needed) -/
private noncomputable def zOn (U : Finset ι) : ℝ :=
  ∑ S ∈ U.powerset, z ^ (M.r U - M.r S) * v ^ (S.card - M.r S) *
    ((∏ f ∈ S, (W f).2) * ∏ f ∈ U \ S, (W f).1)

/-- `Z` is multiplicative over two disjoint blocks on which the rank is additive -/
private lemma zOn_union {A B : Finset ι} (hAB : Disjoint A B) (hA : A ⊆ M.E) (hB : B ⊆ M.E)
    (hadd : ∀ S ⊆ A ∪ B, M.r S = M.r (S ∩ A) + M.r (S ∩ B)) :
    zOn M z v W (A ∪ B) = zOn M z v W A * zOn M z v W B := by
  unfold zOn
  rw [sum_mul_sum, ← sum_product']
  refine sum_nbij' (fun S => (S ∩ A, S ∩ B)) (fun p => p.1 ∪ p.2) ?_ ?_ ?_ ?_ ?_
  · intro S _
    exact mem_product.2 ⟨mem_powerset.2 inter_subset_right, mem_powerset.2 inter_subset_right⟩
  · intro p hp
    obtain ⟨h1, h2⟩ := mem_product.1 hp
    exact mem_powerset.2 (union_subset_union (mem_powerset.1 h1) (mem_powerset.1 h2))
  · intro S hS
    dsimp only
    rw [← inter_union_distrib_left]
    exact inter_eq_left.2 (mem_powerset.1 hS)
  · intro p hp
    obtain ⟨h1, h2⟩ := mem_product.1 hp
    have hX : p.1 ⊆ A := mem_powerset.1 h1
    have hY : p.2 ⊆ B := mem_powerset.1 h2
    refine Prod.ext ?_ ?_
    · dsimp only
      ext x
      have := @hX x; have := @hY x
      have : x ∈ A → x ∉ B := fun h => disjoint_left.1 hAB h
      simp only [mem_union, mem_inter]
      tauto
    · dsimp only
      ext x
      have := @hX x; have := @hY x
      have : x ∈ A → x ∉ B := fun h => disjoint_left.1 hAB h
      simp only [mem_union, mem_inter]
      tauto
  · intro S hS
    have hS' : S ⊆ A ∪ B := mem_powerset.1 hS
    have hAE : A ∪ B ⊆ M.E := union_subset hA hB
    have hdisj : Disjoint (S ∩ A) (S ∩ B) := hAB.mono inter_subset_right inter_subset_right
    have hSXY : S ∩ A ∪ S ∩ B = S := by
      rw [← inter_union_distrib_left]
      exact inter_eq_left.2 hS'
    have hrAB : M.r (A ∪ B) = M.r A + M.r B := by
      have := hadd (A ∪ B) subset_rfl
      rwa [union_inter_cancel_left, union_inter_cancel_right] at this
    have hrS := hadd S hS'
    have hcard : S.card = (S ∩ A).card + (S ∩ B).card := by
      rw [← card_union_of_disjoint hdisj, hSXY]
    have hp1 : ∏ x ∈ S, (W x).2 = (∏ x ∈ S ∩ A, (W x).2) * ∏ x ∈ S ∩ B, (W x).2 := by
      rw [← prod_union hdisj, hSXY]
    have hp0 : ∏ x ∈ (A ∪ B) \ S, (W x).1 =
        (∏ x ∈ A \ (S ∩ A), (W x).1) * ∏ x ∈ B \ (S ∩ B), (W x).1 := by
      rw [sdiff_inter_self_right, sdiff_inter_self_right, union_sdiff_distrib,
        prod_union (hAB.mono sdiff_subset sdiff_subset)]
    have hXA : M.r (S ∩ A) ≤ M.r A := M.r_mono inter_subset_right hA
    have hYB : M.r (S ∩ B) ≤ M.r B := M.r_mono inter_subset_right hB
    have hX := M.r_le_card (inter_subset_right.trans hA : S ∩ A ⊆ M.E)
    have hY := M.r_le_card (inter_subset_right.trans hB : S ∩ B ⊆ M.E)
    have e1 : M.r (A ∪ B) - M.r S = (M.r A - M.r (S ∩ A)) + (M.r B - M.r (S ∩ B)) := by omega
    have e2 : S.card - M.r S = ((S ∩ A).card - M.r (S ∩ A)) + ((S ∩ B).card - M.r (S ∩ B)) := by
      omega
    dsimp only
    rw [e1, e2, hp1, hp0, pow_add, pow_add]
    ring

/-- `Z` is multiplicative over a partition into blocks on which the rank is additive -/
private lemma zOn_biUnion (P : Finset (Finset ι)) (hsub : ∀ K ∈ P, K ⊆ M.E)
    (hdisj : (P : Set (Finset ι)).PairwiseDisjoint id)
    (hadd : ∀ S ⊆ P.biUnion id, M.r S = ∑ K ∈ P, M.r (S ∩ K)) :
    zOn M z v W (P.biUnion id) = ∏ K ∈ P, zOn M z v W K := by
  induction P using Finset.induction_on with
  | empty =>
    unfold zOn
    simp [M.r_empty]
  | insert K P hK ih =>
    have hdisj' : (P : Set (Finset ι)).PairwiseDisjoint id :=
      hdisj.subset (coe_subset.2 (subset_insert K P))
    have hsub' : ∀ K' ∈ P, K' ⊆ M.E := fun K' hK' => hsub K' (mem_insert_of_mem hK')
    have hKP : Disjoint K (P.biUnion id) := by
      refine (disjoint_biUnion_right K P id).2 fun K' hK' => ?_
      have hne : K ≠ K' := fun h => hK (h ▸ hK')
      exact hdisj (mem_coe.2 (mem_insert_self K P)) (mem_coe.2 (mem_insert_of_mem hK')) hne
    have hU : (insert K P).biUnion id = K ∪ P.biUnion id := biUnion_insert
    have haddP : ∀ S ⊆ P.biUnion id, M.r S = ∑ K' ∈ P, M.r (S ∩ K') := by
      intro S hS
      have hSK : S ∩ K = ∅ := disjoint_iff_inter_eq_empty.1 (hKP.symm.mono_left hS)
      have := hadd S (hS.trans (hU ▸ subset_union_right))
      rwa [sum_insert hK, hSK, M.r_empty, zero_add] at this
    have hPE : P.biUnion id ⊆ M.E := biUnion_subset.2 hsub'
    rw [hU, prod_insert hK, zOn_union M z v W hKP (hsub K (mem_insert_self K P)) hPE,
      ih hsub' hdisj' haddP]
    intro S hS
    rw [hadd S (hU ▸ hS), sum_insert hK, haddP (S ∩ P.biUnion id) inter_subset_right]
    congr 1
    refine sum_congr rfl fun K' hK' => ?_
    have hK'U : K' ⊆ P.biUnion id := subset_biUnion_of_mem id hK'
    rw [inter_assoc, inter_eq_right.2 hK'U]

/-- direct sum along a separator: `Z` is multiplicative -/
lemma Z_sep {A : Finset ι} (hA : M.IsSep A) :
    M.Z z v W = (M.restrict A hA.1).Z z v W * (M.restrict (M.E \ A) Finset.sdiff_subset).Z z v W := by
  have hU : A ∪ (M.E \ A) = M.E := union_sdiff_of_subset hA.1
  have h1 : M.Z z v W = zOn M z v W (A ∪ (M.E \ A)) := by rw [hU]; rfl
  rw [h1, zOn_union M z v W disjoint_sdiff hA.1 sdiff_subset]
  · rfl
  · intro S hS
    rw [hU] at hS
    have h2 : S ∩ (M.E \ A) = S \ A := by
      ext x; have := @hS x; simp only [mem_inter, mem_sdiff]; tauto
    rw [h2]
    exact zs_sep_r_add M hA hS

/-- merging two parallel elements: delete one and merge the weights -/
lemma Z_par {f g : ι} (h : M.ParPair f g) :
    M.Z z v W = (M.del g).Z z v (Function.update W f (mergeW v (W f) (W g))) := by
  obtain ⟨hf, hg, hne, hf1, hg1, hfg⟩ := h
  have hgf : M.r {g, f} = 1 := by rw [pair_comm]; exact hfg
  have hfE' : f ∈ M.E.erase g := mem_erase.2 ⟨hne, hf⟩
  have hE : M.r (M.E.erase g) = M.r M.E := by
    have h := zs_r_insert_par M hg hf hf1 hgf (erase_subset g M.E)
    rw [insert_eq_of_mem hfE', insert_erase hg] at h
    exact h.symm
  rw [Z_split M z v W hg, zs_sum_split hfE', Z_split (M.del g) z v _ hfE']
  simp only [del_E, del_r]
  refine sum_congr rfl fun S hS => ?_
  have hS'' : S ⊆ (M.E.erase g).erase f := mem_powerset.1 hS
  have hfS : f ∉ S := fun h => notMem_erase f _ (hS'' h)
  have hSE : S ⊆ M.E := hS''.trans ((erase_subset _ _).trans (erase_subset _ _))
  have hP1 : ∏ x ∈ M.E.erase g \ S, (W x).1 =
      (W f).1 * ∏ x ∈ (M.E.erase g).erase f \ S, (W x).1 := by
    rw [erase_sdiff_comm (M.E.erase g) S f]
    exact (mul_prod_erase _ _ (mem_sdiff.2 ⟨hfE', hfS⟩)).symm
  have hP2 : M.E.erase g \ insert f S = (M.E.erase g).erase f \ S := by
    rw [sdiff_insert, ← erase_sdiff_comm]
  have hW1 : ∏ x ∈ S, (Function.update W f (mergeW v (W f) (W g)) x).2 = ∏ x ∈ S, (W x).2 :=
    prod_congr rfl fun x hx => by
      have hxf : x ≠ f := fun h => hfS (h ▸ hx)
      rw [Function.update_of_ne hxf]
  have hW0 : ∏ x ∈ (M.E.erase g).erase f \ S, (Function.update W f (mergeW v (W f) (W g)) x).1 =
      ∏ x ∈ (M.E.erase g).erase f \ S, (W x).1 :=
    prod_congr rfl fun x hx => by
      have hxf : x ≠ f := fun h => notMem_erase f _ (h ▸ (mem_sdiff.1 hx).1)
      rw [Function.update_of_ne hxf]
  have hr2 : M.r (insert g (insert f S)) = M.r (insert f S) :=
    zs_r_insert_par M hg hf hf1 hgf hSE
  have hr1 : M.r (insert g S) = M.r (insert f S) := by
    rw [← zs_r_insert_par M hf hg hg1 hfg hSE, insert_comm, hr2]
  have hle : M.r (insert f S) ≤ S.card + 1 := by
    have := M.r_le_card (insert_subset hf hSE)
    rwa [card_insert_of_notMem hfS] at this
  have e : S.card + 1 + 1 - M.r (insert f S) = S.card + 1 - M.r (insert f S) + 1 := by omega
  rw [hP1, hP2, prod_insert hfS, card_insert_of_notMem hfS, hW1, hW0, Function.update_self,
    hr1, hr2, hE, e, pow_succ]
  simp only [mergeW]
  ring

/-- product over a partition into classes on which the rank is additive -/
lemma Z_partition (P : Finset (Finset ι)) (hsub : ∀ K ∈ P, K ⊆ M.E)
    (hdisj : (P : Set (Finset ι)).PairwiseDisjoint id) (hcov : P.biUnion id = M.E)
    (hadd : ∀ S ⊆ M.E, M.r S = ∑ K ∈ P, M.r (S ∩ K)) :
    M.Z z v W = ∏ K ∈ P.attach, (M.restrict K.1 (hsub K.1 K.2)).Z z v W := by
  have h1 : M.Z z v W = zOn M z v W (P.biUnion id) := by rw [hcov]; rfl
  rw [h1, zOn_biUnion M z v W P hsub hdisj fun S hS => hadd S (hcov ▸ hS)]
  exact (prod_attach P (fun K => zOn M z v W K)).symm

end RkMat

end Results.TutteThreshold
