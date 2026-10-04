import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Finite matroids by rank function (proof layer)

The proof layer works with matroids presented by their rank function on a finite ground set.
Nothing here is part of the trusted statement layer; `Solution/Bridge.lean` connects Mathlib's
`Matroid` to this structure.
-/

namespace Results.TutteThreshold

open Finset

/-- A finite matroid given by its rank function.  `r` is only meaningful on subsets of `E`. -/
structure RkMat (ι : Type*) [DecidableEq ι] where
  E : Finset ι
  r : Finset ι → ℕ
  r_mono : ∀ ⦃S T : Finset ι⦄, S ⊆ T → T ⊆ E → r S ≤ r T
  r_submod : ∀ ⦃S T : Finset ι⦄, S ⊆ E → T ⊆ E → r (S ∪ T) + r (S ∩ T) ≤ r S + r T
  r_le_card : ∀ ⦃S : Finset ι⦄, S ⊆ E → r S ≤ S.card

namespace RkMat

variable {ι : Type*} [DecidableEq ι]

/-! ### Basic consequences of the axioms -/

lemma r_empty (M : RkMat ι) : M.r ∅ = 0 := by
  have := M.r_le_card (S := ∅) (Finset.empty_subset _)
  simpa using this

lemma r_union_le (M : RkMat ι) {S T : Finset ι} (hS : S ⊆ M.E) (hT : T ⊆ M.E) :
    M.r (S ∪ T) ≤ M.r S + M.r T := by
  have := M.r_submod hS hT
  omega

/-- adding one element raises the rank by at most one -/
lemma r_insert_le (M : RkMat ι) {S : Finset ι} (hS : S ⊆ M.E) {f : ι} (hf : f ∈ M.E) :
    M.r (insert f S) ≤ M.r S + 1 := by
  have h1 := M.r_union_le (singleton_subset_iff.2 hf) hS
  have h2 := M.r_le_card (singleton_subset_iff.2 hf)
  rw [← insert_eq] at h1
  rw [card_singleton] at h2
  omega

lemma r_le_insert (M : RkMat ι) {S : Finset ι} (hS : S ⊆ M.E) {f : ι} (hf : f ∈ M.E) :
    M.r S ≤ M.r (insert f S) :=
  M.r_mono (Finset.subset_insert _ _) (Finset.insert_subset hf hS)

lemma r_single_le (M : RkMat ι) {f : ι} (hf : f ∈ M.E) : M.r {f} ≤ 1 := by
  have := M.r_le_card (S := {f}) (by simpa using hf)
  simpa using this

lemma r_le_r_E (M : RkMat ι) {S : Finset ι} (hS : S ⊆ M.E) : M.r S ≤ M.r M.E :=
  M.r_mono hS (subset_refl _)

/-- `r(E) ≤ |S| + r(E \ S)`; in particular the truncated subtraction in `dual` is exact. -/
lemma rk_r_E_le_card_add (M : RkMat ι) {S : Finset ι} (hS : S ⊆ M.E) :
    M.r M.E ≤ S.card + M.r (M.E \ S) := by
  have h1 := M.r_union_le hS (sdiff_subset : M.E \ S ⊆ M.E)
  rw [union_sdiff_of_subset hS] at h1
  have h2 := M.r_le_card hS
  omega

/-- removing the elements of `S \ T` lowers the rank by at most `|S \ T|` -/
lemma rk_r_le_add_card_sdiff (M : RkMat ι) {S T : Finset ι} (hS : S ⊆ M.E) (hTS : T ⊆ S) :
    M.r S ≤ M.r T + (S \ T).card := by
  have hST : S \ T ⊆ M.E := sdiff_subset.trans hS
  have h1 := M.r_union_le (hTS.trans hS) hST
  rw [union_sdiff_of_subset hTS] at h1
  have h2 := M.r_le_card hST
  omega

/-- `r{f} ≤ r(S ∪ {f})` -/
lemma rk_r_single_le_insert (M : RkMat ι) {S : Finset ι} (hS : S ⊆ M.E) {f : ι}
    (hf : f ∈ M.E) : M.r {f} ≤ M.r (insert f S) :=
  M.r_mono (singleton_subset_iff.2 (mem_insert_self f S)) (insert_subset hf hS)

/-- adding a loop does not change the rank -/
lemma rk_r_insert_of_loop (M : RkMat ι) {S : Finset ι} (hS : S ⊆ M.E) {f : ι} (hf : f ∈ M.E)
    (h0 : M.r {f} = 0) : M.r (insert f S) = M.r S := by
  have h1 := M.r_union_le (singleton_subset_iff.2 hf) hS
  rw [← insert_eq] at h1
  have h2 := M.r_le_insert hS hf
  omega

/-- adding a coloop to a set not containing it raises the rank by one -/
lemma rk_r_insert_of_coloop (M : RkMat ι) {S : Finset ι} (hS : S ⊆ M.E) {f : ι} (hfS : f ∉ S)
    (hf : f ∈ M.E) (hc : M.r (M.E.erase f) + 1 = M.r M.E) : M.r (insert f S) = M.r S + 1 := by
  have h1 := M.r_submod (insert_subset hf hS) (erase_subset f M.E)
  have e1 : insert f S ∪ M.E.erase f = M.E := by grind
  have e2 : insert f S ∩ M.E.erase f = S := by grind
  rw [e1, e2] at h1
  have h2 := M.r_insert_le hS hf
  omega

private lemma card_add_r_compl_mono (M : RkMat ι) {S T : Finset ι} (hST : S ⊆ T)
    (hT : T ⊆ M.E) : S.card + M.r (M.E \ S) ≤ T.card + M.r (M.E \ T) := by
  have hsub : M.E \ T ⊆ M.E \ S := sdiff_subset_sdiff (subset_refl _) hST
  have h1 := M.rk_r_le_add_card_sdiff (sdiff_subset : M.E \ S ⊆ M.E) hsub
  rw [card_sdiff_of_subset hsub, card_sdiff_of_subset (hST.trans hT),
    card_sdiff_of_subset hT] at h1
  have h2 := card_le_card hST
  have h3 := card_le_card hT
  omega

/-! ### Minors, restriction and dual -/

/-- Deletion of one element (same rank function, smaller ground set). -/
def del (M : RkMat ι) (f : ι) : RkMat ι where
  E := M.E.erase f
  r := M.r
  r_mono := fun _ _ hST hT => M.r_mono hST (hT.trans (Finset.erase_subset _ _))
  r_submod := fun _ _ hS hT =>
    M.r_submod (hS.trans (Finset.erase_subset _ _)) (hT.trans (Finset.erase_subset _ _))
  r_le_card := fun _ hS => M.r_le_card (hS.trans (Finset.erase_subset _ _))

/-- Restriction to a subset of the ground set. -/
def restrict (M : RkMat ι) (A : Finset ι) (hA : A ⊆ M.E) : RkMat ι where
  E := A
  r := M.r
  r_mono := fun _ _ hST hT => M.r_mono hST (hT.trans hA)
  r_submod := fun _ _ hS hT => M.r_submod (hS.trans hA) (hT.trans hA)
  r_le_card := fun _ hS => M.r_le_card (hS.trans hA)

/-- Contraction of one element of the ground set: `r'(S) = r(S ∪ {f}) - r({f})`. -/
def con (M : RkMat ι) (f : ι) (hf : f ∈ M.E) : RkMat ι where
  E := M.E.erase f
  r := fun S => M.r (insert f S) - M.r {f}
  r_mono := by
    intro S T hST hT
    have hTE : insert f T ⊆ M.E := insert_subset hf (hT.trans (erase_subset f M.E))
    exact Nat.sub_le_sub_right (M.r_mono (insert_subset_insert f hST) hTE) _
  r_submod := by
    intro S T hS hT
    have hSE : S ⊆ M.E := hS.trans (erase_subset f M.E)
    have hTE : T ⊆ M.E := hT.trans (erase_subset f M.E)
    have h1 := M.r_submod (insert_subset hf hSE) (insert_subset hf hTE)
    rw [← insert_union_distrib, ← insert_inter_distrib] at h1
    have h2 := M.rk_r_single_le_insert (union_subset hSE hTE) hf
    have h3 := M.rk_r_single_le_insert (inter_subset_left.trans hSE : S ∩ T ⊆ M.E) hf
    have h4 := M.rk_r_single_le_insert hSE hf
    have h5 := M.rk_r_single_le_insert hTE hf
    omega
  r_le_card := by
    intro S hS
    have hSE : S ⊆ M.E := hS.trans (erase_subset f M.E)
    have h1 := M.r_union_le (singleton_subset_iff.2 hf) hSE
    rw [← insert_eq] at h1
    have h2 := M.r_le_card hSE
    omega

/-- The dual matroid: `r*(S) = |S| + r(E \ S) - r(E)` (for `S ⊆ E`). -/
def dual (M : RkMat ι) : RkMat ι where
  E := M.E
  r := fun S => S.card + M.r (M.E \ S) - M.r M.E
  r_mono := by
    intro S T hST hT
    exact Nat.sub_le_sub_right (M.card_add_r_compl_mono hST hT) _
  r_submod := by
    intro S T hS hT
    have h1 := M.r_submod (sdiff_subset : M.E \ S ⊆ M.E) (sdiff_subset : M.E \ T ⊆ M.E)
    rw [← sdiff_inter_distrib_right, ← sdiff_union_distrib] at h1
    have h2 := card_union_add_card_inter S T
    have h3 := M.rk_r_E_le_card_add (union_subset hS hT)
    have h4 := M.rk_r_E_le_card_add (inter_subset_left.trans hS : S ∩ T ⊆ M.E)
    have h5 := M.rk_r_E_le_card_add hS
    have h6 := M.rk_r_E_le_card_add hT
    omega
  r_le_card := by
    intro S hS
    have := M.r_le_r_E (sdiff_subset : M.E \ S ⊆ M.E)
    omega

@[simp] lemma del_E (M : RkMat ι) (f : ι) : (M.del f).E = M.E.erase f := rfl
@[simp] lemma del_r (M : RkMat ι) (f : ι) (S : Finset ι) : (M.del f).r S = M.r S := rfl
@[simp] lemma restrict_E (M : RkMat ι) (A : Finset ι) (hA : A ⊆ M.E) : (M.restrict A hA).E = A := rfl
@[simp] lemma restrict_r (M : RkMat ι) (A : Finset ι) (hA : A ⊆ M.E) (S : Finset ι) :
    (M.restrict A hA).r S = M.r S := rfl
@[simp] lemma con_E (M : RkMat ι) (f : ι) (hf : f ∈ M.E) : (M.con f hf).E = M.E.erase f := rfl
@[simp] lemma con_r (M : RkMat ι) (f : ι) (hf : f ∈ M.E) (S : Finset ι) :
    (M.con f hf).r S = M.r (insert f S) - M.r {f} := rfl
@[simp] lemma dual_E (M : RkMat ι) : M.dual.E = M.E := rfl
@[simp] lemma dual_r (M : RkMat ι) (S : Finset ι) :
    M.dual.r S = S.card + M.r (M.E \ S) - M.r M.E := rfl

/-- `M` and `N` have the same ground set and the same rank function on subsets of it. -/
def Same (M N : RkMat ι) : Prop := M.E = N.E ∧ ∀ S ⊆ M.E, M.r S = N.r S

lemma Same.refl (M : RkMat ι) : Same M M := ⟨rfl, fun _ _ => rfl⟩
lemma Same.symm {M N : RkMat ι} (h : Same M N) : Same N M :=
  ⟨h.1.symm, fun S hS => (h.2 S (h.1 ▸ hS)).symm⟩
lemma Same.trans {M N P : RkMat ι} (h : Same M N) (h' : Same N P) : Same M P :=
  ⟨h.1.trans h'.1, fun S hS => (h.2 S hS).trans (h'.2 S (h.1 ▸ hS))⟩

/-- the dual of the dual is the matroid itself -/
lemma dual_dual_same (M : RkMat ι) : Same M.dual.dual M := by
  refine ⟨rfl, fun S hS => ?_⟩
  have hS' : S ⊆ M.E := hS
  have h1 := M.rk_r_E_le_card_add (sdiff_subset : M.E \ S ⊆ M.E)
  rw [Finset.sdiff_sdiff_eq_self hS'] at h1
  have h2 := card_sdiff_add_card_eq_card hS'
  have h3 := M.r_le_card (subset_refl M.E)
  simp only [dual_r, dual_E, Finset.sdiff_sdiff_eq_self hS', Finset.sdiff_self, M.r_empty]
  omega

/-- dual of contraction is deletion of the dual -/
lemma con_dual_same (M : RkMat ι) (f : ι) (hf : f ∈ M.E) :
    Same (M.con f hf).dual (M.dual.del f) := by
  refine ⟨rfl, fun S hS => ?_⟩
  have hS' : S ⊆ M.E.erase f := hS
  have hSE : S ⊆ M.E := hS'.trans (erase_subset f M.E)
  have hfS : f ∉ S := fun h => by simpa using hS' h
  have e1 : insert f (M.E.erase f \ S) = M.E \ S := by
    rw [← insert_sdiff_of_notMem _ hfS, insert_erase hf]
  have h1 := M.rk_r_E_le_card_add hSE
  have h2 : M.r {f} ≤ M.r (M.E \ S) :=
    M.r_mono (singleton_subset_iff.2 (mem_sdiff.2 ⟨hf, hfS⟩)) sdiff_subset
  have h3 : M.r {f} ≤ M.r M.E := M.r_mono (singleton_subset_iff.2 hf) (subset_refl _)
  simp only [dual_r, con_r, con_E, del_r, insert_erase hf, e1]
  omega

/-- dual of deletion is contraction of the dual (`f` is an element of `E`). -/
lemma del_dual_same (M : RkMat ι) (f : ι) (hf : f ∈ M.E) :
    Same (M.del f).dual (M.dual.con f hf) := by
  refine ⟨rfl, fun S hS => ?_⟩
  have hS' : S ⊆ M.E.erase f := hS
  have hfS : f ∉ S := fun h => by simpa using hS' h
  have e1 : M.E \ insert f S = M.E.erase f \ S := by grind
  have h1 := (M.del f).rk_r_E_le_card_add (S := S) hS'
  simp only [del_r, del_E] at h1
  have h2 := M.r_insert_le (erase_subset f M.E) hf
  have h3 := M.r_le_insert (erase_subset f M.E) hf
  rw [insert_erase hf] at h2 h3
  have h4 := M.r_mono (sdiff_subset : M.E.erase f \ S ⊆ M.E.erase f) (erase_subset f M.E)
  simp only [dual_r, con_r, del_r, del_E, card_insert_of_notMem hfS, card_singleton,
    sdiff_singleton_eq_erase, e1]
  omega

/-! ### Elements, admissibility, separators, parallel pairs -/

/-- no loops and no coloops -/
def Admissible (M : RkMat ι) : Prop :=
  ∀ f ∈ M.E, M.r {f} = 1 ∧ M.r (M.E.erase f) = M.r M.E

/-- `A` is a separator: the matroid is the direct sum of the restrictions to `A` and `E \ A`. -/
def IsSep (M : RkMat ι) (A : Finset ι) : Prop := A ⊆ M.E ∧ M.r A + M.r (M.E \ A) = M.r M.E

/-- `f`, `g` are two distinct non-loops that are parallel -/
def ParPair (M : RkMat ι) (f g : ι) : Prop :=
  f ∈ M.E ∧ g ∈ M.E ∧ f ≠ g ∧ M.r {f} = 1 ∧ M.r {g} = 1 ∧ M.r {f, g} = 1

/-- `f`, `g` form a series pair (a two-element cocircuit): a parallel pair of the dual -/
def SerPair (M : RkMat ι) (f g : ι) : Prop := M.dual.ParPair f g

/-! ### Helper facts on parallel and series pairs -/

/-- being a parallel pair is symmetric -/
lemma ParPair.rk_symm {M : RkMat ι} {f g : ι} (h : M.ParPair f g) : M.ParPair g f := by
  obtain ⟨hf, hg, hne, h1, h2, h3⟩ := h
  exact ⟨hg, hf, hne.symm, h2, h1, by rw [pair_comm]; exact h3⟩

/-- if `f ∈ S` and `f, g` are parallel, adding `g` to `S` does not change the rank -/
lemma ParPair.rk_r_insert_eq {M : RkMat ι} {f g : ι} (h : M.ParPair f g) {S : Finset ι}
    (hS : S ⊆ M.E) (hfS : f ∈ S) : M.r (insert g S) = M.r S := by
  obtain ⟨hf, hg, -, h1, -, h3⟩ := h
  have hs := M.r_submod hS (insert_subset hf (singleton_subset_iff.2 hg))
  have e1 : S ∪ {f, g} = insert g S := by grind
  rw [e1, h3] at hs
  have hm : M.r {f} ≤ M.r (S ∩ {f, g}) :=
    M.r_mono (by grind) (inter_subset_left.trans hS : S ∩ {f, g} ⊆ M.E)
  have hm2 := M.r_le_insert hS hg
  omega

private lemma serPair_iff_aux {M : RkMat ι} (h : M.Admissible) {f g : ι} :
    M.SerPair f g ↔ (f ∈ M.E ∧ g ∈ M.E ∧ f ≠ g ∧ M.r (M.E \ {f, g}) + 1 = M.r M.E) := by
  unfold SerPair ParPair
  simp only [dual_r, dual_E]
  constructor
  · rintro ⟨hf, hg, hne, -, -, h3⟩
    refine ⟨hf, hg, hne, ?_⟩
    have h4 := M.rk_r_E_le_card_add
      (insert_subset hf (singleton_subset_iff.2 hg) : ({f, g} : Finset ι) ⊆ M.E)
    rw [card_pair hne] at h3 h4
    omega
  · rintro ⟨hf, hg, hne, h3⟩
    refine ⟨hf, hg, hne, ?_, ?_, ?_⟩
    · rw [card_singleton, sdiff_singleton_eq_erase, (h f hf).2]
      omega
    · rw [card_singleton, sdiff_singleton_eq_erase, (h g hg).2]
      omega
    · rw [card_pair hne]
      omega

/-! ### Statements used by the other modules (frozen interface) -/

lemma Admissible.dual {M : RkMat ι} (h : M.Admissible) : M.dual.Admissible := by
  intro f hf
  have hf' : f ∈ M.E := hf
  obtain ⟨h1, h2⟩ := h f hf'
  have hc := card_erase_add_one hf'
  have hr := M.r_le_card (subset_refl M.E)
  simp only [dual_r, dual_E, card_singleton, sdiff_singleton_eq_erase, Finset.sdiff_self,
    sdiff_erase_self hf', h1, h2, M.r_empty]
  omega

/-- a nonempty admissible matroid has at least two elements -/
lemma Admissible.two_le_card {M : RkMat ι} (h : M.Admissible) (hne : M.E.Nonempty) :
    2 ≤ M.E.card := by
  obtain ⟨f, hf⟩ := hne
  obtain ⟨h1, h2⟩ := h f hf
  by_contra hlt
  have hc := card_erase_add_one hf
  have he : M.E.erase f = ∅ := card_eq_zero.1 (by omega)
  rw [he, M.r_empty] at h2
  have h3 := M.r_mono (singleton_subset_iff.2 hf) (subset_refl M.E)
  omega

/-- separator additivity: for a separator `A`, ranks add on every subset -/
lemma IsSep.r_add {M : RkMat ι} {A : Finset ι} (hA : M.IsSep A) {S : Finset ι} (hS : S ⊆ M.E) :
    M.r S = M.r (S ∩ A) + M.r (S \ A) := by
  obtain ⟨hAE, hsum⟩ := hA
  have hX : S ∩ A ⊆ M.E := inter_subset_left.trans hS
  have hY : S \ A ⊆ M.E := sdiff_subset.trans hS
  have hB : M.E \ A ⊆ M.E := sdiff_subset
  -- `X ∪ B` and `A` (union `E`, intersection `X`), with `X = S ∩ A`, `B = E \ A`
  have s1 := M.r_submod (union_subset hX hB) hAE
  have e1 : S ∩ A ∪ M.E \ A ∪ A = M.E := by grind
  have e2 : (S ∩ A ∪ M.E \ A) ∩ A = S ∩ A := by grind
  rw [e1, e2] at s1
  -- `X ∪ Y` and `B` (union `X ∪ B`, intersection `Y`), with `Y = S \ A`
  have s2 := M.r_submod (union_subset hX hY) hB
  have e3 : S ∩ A ∪ S \ A ∪ M.E \ A = S ∩ A ∪ M.E \ A := by grind
  have e4 : (S ∩ A ∪ S \ A) ∩ (M.E \ A) = S \ A := by grind
  have e5 : S ∩ A ∪ S \ A = S := by grind
  rw [e3, e4, e5] at s2
  have u1 := M.r_union_le hX hB
  have u2 := M.r_union_le hX hY
  rw [e5] at u2
  omega

lemma IsSep.compl {M : RkMat ι} {A : Finset ι} (hA : M.IsSep A) :
    M.IsSep (M.E \ A) := by
  obtain ⟨hAE, hsum⟩ := hA
  refine ⟨sdiff_subset, ?_⟩
  rw [Finset.sdiff_sdiff_eq_self hAE]
  omega

lemma isSep_dual_iff {M : RkMat ι} {A : Finset ι} : M.dual.IsSep A ↔ M.IsSep A := by
  unfold IsSep
  rw [dual_E]
  refine and_congr_right fun hA => ?_
  have h1 := M.rk_r_E_le_card_add hA
  have h2 := M.rk_r_E_le_card_add (sdiff_subset : M.E \ A ⊆ M.E)
  rw [Finset.sdiff_sdiff_eq_self hA] at h2
  have h3 := card_sdiff_add_card_eq_card hA
  have h4 := M.r_union_le hA (sdiff_subset : M.E \ A ⊆ M.E)
  rw [union_sdiff_of_subset hA] at h4
  have h5 := M.r_le_card (subset_refl M.E)
  simp only [dual_r, Finset.sdiff_sdiff_eq_self hA, Finset.sdiff_self, M.r_empty]
  omega

/-- restriction of an admissible matroid to a separator is admissible -/
lemma Admissible.restrict_sep {M : RkMat ι} (h : M.Admissible) {A : Finset ι} (hA : M.IsSep A) :
    (M.restrict A hA.1).Admissible := by
  intro f hf
  have hf' : f ∈ A := hf
  have hAE : A ⊆ M.E := hA.1
  obtain ⟨h1, h2⟩ := h f (hAE hf')
  simp only [restrict_r, restrict_E]
  refine ⟨h1, ?_⟩
  have hadd := hA.r_add (erase_subset f M.E)
  have e1 : M.E.erase f ∩ A = A.erase f := by grind
  have e2 : M.E.erase f \ A = M.E \ A := by grind
  rw [e1, e2, h2] at hadd
  have := hA.2
  omega

/-- deleting an element that lies in no series pair keeps admissibility -/
lemma Admissible.del {M : RkMat ι} (h : M.Admissible) {f : ι} (hf : f ∈ M.E)
    (hs : ∀ g, ¬ M.SerPair f g) : (M.del f).Admissible := by
  intro g hg
  have hg' : g ∈ M.E.erase f := hg
  have hgf : g ≠ f := ne_of_mem_erase hg'
  have hgE : g ∈ M.E := mem_of_mem_erase hg'
  simp only [del_r, del_E]
  refine ⟨(h g hgE).1, ?_⟩
  have h2 := (h f hf).2
  have hsub : (M.E.erase f).erase g ⊆ M.E := (erase_subset _ _).trans (erase_subset _ _)
  have hle1 := M.r_mono (erase_subset g (M.E.erase f)) (erase_subset f M.E)
  have hle2 := M.r_insert_le hsub hgE
  rw [insert_erase hg'] at hle2
  have e : M.E \ {f, g} = (M.E.erase f).erase g := by grind
  by_contra hne
  exact hs g ((serPair_iff_aux h).2 ⟨hf, hgE, hgf.symm, by rw [e]; omega⟩)

/-- contracting an element that lies in no parallel pair keeps admissibility -/
lemma Admissible.con {M : RkMat ι} (h : M.Admissible) {f : ι} (hf : f ∈ M.E)
    (hp : ∀ g, ¬ M.ParPair f g) : (M.con f hf).Admissible := by
  intro g hg
  have hg' : g ∈ M.E.erase f := hg
  have hgf : g ≠ f := ne_of_mem_erase hg'
  have hgE : g ∈ M.E := mem_of_mem_erase hg'
  obtain ⟨hf1, -⟩ := h f hf
  obtain ⟨hg1, hg2⟩ := h g hgE
  simp only [con_r, con_E]
  constructor
  · have hle := M.r_insert_le (singleton_subset_iff.2 hgE) hf
    have hge := M.rk_r_single_le_insert (singleton_subset_iff.2 hgE) hf
    have hne : M.r {f, g} ≠ 1 := fun h1 => hp g ⟨hf, hgE, hgf.symm, hf1, hg1, h1⟩
    omega
  · have e : insert f ((M.E.erase f).erase g) = M.E.erase g := by grind
    rw [e, insert_erase hf, hg2]

/-- deleting one member of a parallel pair that is not a separator keeps admissibility -/
lemma Admissible.del_par {M : RkMat ι} (h : M.Admissible) {f g : ι} (hfg : M.ParPair f g)
    (hns : ¬ M.IsSep {f, g}) : (M.del g).Admissible := by
  intro k hk
  have hk' : k ∈ M.E.erase g := hk
  have hkE : k ∈ M.E := mem_of_mem_erase hk'
  have hfE : f ∈ M.E := hfg.1
  have hgE : g ∈ M.E := hfg.2.1
  have hne : f ≠ g := hfg.2.2.1
  simp only [del_r, del_E]
  refine ⟨(h k hkE).1, ?_⟩
  rw [(h g hgE).2]
  have hsub : (M.E.erase g).erase k ⊆ M.E := (erase_subset _ _).trans (erase_subset _ _)
  by_cases hkf : k = f
  · -- a rank drop at `f` would make `{f, g}` a separator
    subst k
    have hle1 := M.r_mono (erase_subset f (M.E.erase g)) (erase_subset g M.E)
    have hle2 := M.r_insert_le hsub hfE
    rw [insert_erase hk'] at hle2
    rw [(h g hgE).2] at hle1 hle2
    by_contra hdrop
    apply hns
    refine ⟨insert_subset hfE (singleton_subset_iff.2 hgE), ?_⟩
    have e : M.E \ {f, g} = (M.E.erase g).erase f := by grind
    rw [e, hfg.2.2.2.2.2]
    omega
  · -- `f` stays in `(E \ g) \ k`, so adding `g` back does not raise the rank
    have hfS : f ∈ (M.E.erase g).erase k := by grind
    have h3 := hfg.rk_r_insert_eq hsub hfS
    have e : insert g ((M.E.erase g).erase k) = M.E.erase k := by grind
    rw [e, (h k hkE).2] at h3
    exact h3.symm

/-- rank facts for a parallel pair: adding `f`, `g` or both to any set not containing them
gives the same rank -/
lemma ParPair.r_eq {M : RkMat ι} {f g : ι} (h : M.ParPair f g) {S : Finset ι}
    (hS : S ⊆ M.E) (hf : f ∉ S) (hg : g ∉ S) :
    M.r (insert f S) = M.r (insert g S) ∧ M.r (insert f (insert g S)) = M.r (insert f S) := by
  obtain ⟨hfE, hgE, hne, h1, h2, h3⟩ := h
  have hfg : ({f, g} : Finset ι) ⊆ M.E := insert_subset hfE (singleton_subset_iff.2 hgE)
  have hfgS : insert f (insert g S) ⊆ M.E := insert_subset hfE (insert_subset hgE hS)
  -- submodularity with `{f, g}`: `insert f S ∩ {f, g} = {f}` and `insert g S ∩ {f, g} = {g}`
  have sf := M.r_submod (insert_subset hfE hS) hfg
  have sg := M.r_submod (insert_subset hgE hS) hfg
  have ef1 : insert f S ∪ {f, g} = insert f (insert g S) := by grind
  have ef2 : insert f S ∩ {f, g} = {f} := by grind
  have eg1 : insert g S ∪ {f, g} = insert f (insert g S) := by grind
  have eg2 : insert g S ∩ {f, g} = {g} := by grind
  rw [ef1, ef2, h1, h3] at sf
  rw [eg1, eg2, h2, h3] at sg
  have mf := M.r_mono (insert_subset_insert f (subset_insert g S)) hfgS
  have mg := M.r_mono (subset_insert f (insert g S)) hfgS
  omega

/-- element `f` is in no two-element circuit and no two-element cocircuit -/
def ClassFree (M : RkMat ι) (f : ι) : Prop := (∀ g, ¬ M.ParPair f g) ∧ (∀ g, ¬ M.SerPair f g)

/-- admissible and `E = {f, g}` forces a parallel pair of rank one -/
lemma Admissible.pair_of_card_two {M : RkMat ι} (h : M.Admissible) {f g : ι} (hfg : f ≠ g)
    (hE : M.E = {f, g}) : M.ParPair f g ∧ M.r M.E = 1 := by
  have hfE : f ∈ M.E := by rw [hE]; exact mem_insert_self f {g}
  have hgE : g ∈ M.E := by rw [hE]; exact mem_insert_of_mem (mem_singleton_self g)
  obtain ⟨hf1, hf2⟩ := h f hfE
  have hg1 := (h g hgE).1
  have e : M.E.erase f = {g} := by rw [hE]; exact erase_insert (notMem_singleton.2 hfg)
  rw [e, hg1] at hf2
  refine ⟨⟨hfE, hgE, hfg, hf1, hg1, ?_⟩, hf2.symm⟩
  rw [← hE]
  exact hf2.symm

/-- in an admissible matroid an element of a non-separating parallel pair is not a loop of the
contraction, and in a series pair ... (see `Induction`): `SerPair` is equivalent to a rank drop -/
lemma SerPair_iff {M : RkMat ι} (h : M.Admissible) {f g : ι} :
    M.SerPair f g ↔ (f ∈ M.E ∧ g ∈ M.E ∧ f ≠ g ∧ M.r (M.E \ {f, g}) + 1 = M.r M.E) :=
  serPair_iff_aux h

end RkMat

end Results.TutteThreshold
