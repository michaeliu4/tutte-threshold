import Results.TutteThreshold.Solution.StepsA
import Results.TutteThreshold.Solution.StepsB

/-!
# The main induction on weighted skeletons (assembly)

`Claim x M ℓ`: `c(x)^{h} ≤ c(x)² ρ(M,ℓ)` where `h = ∑ size`.  The statement `main_P`: the claim
holds for every nonempty admissible rank matroid with labels in `Lab.OK` (the seven profiles and
the big parallel/series classes) and `2 ≤ x ≤ x_*` (`x³ ≤ 9(x-1)`).

The proof is by strong induction on `h + |E|` with the following cases
(see `BLUEPRINT.md`): big label (`step_big_p`, `step_big_s`), an element in no two-element
circuit or cocircuit (`step_branch`), `E = {f,g}` (`step_closing`), a separator (`step_sep`), a
parallel pair (`step_par`), a series pair (the dual of `step_par`).
-/

namespace Results.TutteThreshold

open Finset

variable {ι : Type*} [DecidableEq ι]

namespace Induction

/-! ### The measure `hsum + |E|` and the labelling conditions -/

/-- changing the label of one element of the ground set -/
lemma hsum_update {M : RkMat ι} {ℓ : ι → Lab} {f : ι} (hf : f ∈ M.E) (l : Lab) :
    hsum M (Function.update ℓ f l) + (ℓ f).size = hsum M ℓ + l.size := by
  have h1 : l.size + ∑ g ∈ M.E.erase f, (ℓ g).size = hsum M (Function.update ℓ f l) := by
    rw [hsum, ← Finset.add_sum_erase _ _ hf, Function.update_self]
    congr 1
    exact Finset.sum_congr rfl fun g hg => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hg)]
  have h2 : (ℓ f).size + ∑ g ∈ M.E.erase f, (ℓ g).size = hsum M ℓ :=
    Finset.add_sum_erase M.E (fun g => (ℓ g).size) hf
  omega

lemma hsum_del {M : RkMat ι} (ℓ : ι → Lab) {f : ι} (hf : f ∈ M.E) :
    hsum (M.del f) ℓ + (ℓ f).size = hsum M ℓ :=
  Finset.sum_erase_add M.E (fun g => (ℓ g).size) hf

lemma hsum_con {M : RkMat ι} (ℓ : ι → Lab) {f : ι} (hf : f ∈ M.E) :
    hsum (M.con f hf) ℓ + (ℓ f).size = hsum M ℓ :=
  Finset.sum_erase_add M.E (fun g => (ℓ g).size) hf

lemma hsum_restrict_le {M : RkMat ι} (ℓ : ι → Lab) {A : Finset ι} (hA : A ⊆ M.E) :
    hsum (M.restrict A hA) ℓ ≤ hsum M ℓ :=
  Finset.sum_le_sum_of_subset hA

lemma goodLab_mono {M N : RkMat ι} {ℓ : ι → Lab} (hg : GoodLab M ℓ) (h : N.E ⊆ M.E) :
    GoodLab N ℓ :=
  fun g hg' => hg g (h hg')

lemma goodLab_update {M : RkMat ι} {ℓ : ι → Lab} (hg : GoodLab M ℓ) (f : ι) {l : Lab}
    (hl : l.OK) : GoodLab M (Function.update ℓ f l) := by
  intro g hg'
  by_cases h : g = f
  · subst h
    rw [Function.update_self]
    exact hl
  · rw [Function.update_of_ne h]
    exact hg g hg'

/-- removing two edges from a big class leaves a profile or a big class -/
lemma ok_sub_two {k : ℕ} (hk : 4 ≤ k) : (Lab.p (k - 2)).OK ∧ (Lab.s (k - 2)).OK := by
  rcases (show k - 2 = 2 ∨ k - 2 = 3 ∨ 4 ≤ k - 2 by omega) with h | h | h
  · rw [h]
    exact ⟨Or.inl (by decide), Or.inl (by decide)⟩
  · rw [h]
    exact ⟨Or.inl (by decide), Or.inl (by decide)⟩
  · exact ⟨Or.inr ⟨k - 2, h, Or.inl rfl⟩, Or.inr ⟨k - 2, h, Or.inr rfl⟩⟩

lemma le_three {x : ℝ} (hxs : x ^ 3 ≤ 9 * (x - 1)) : x ≤ 3 := by
  by_contra h
  push Not at h
  nlinarith [mul_pos (mul_pos (by linarith : (0:ℝ) < x) (by linarith : (0:ℝ) < x - 3))
    (by linarith : (0:ℝ) < x + 3)]

/-! ### The induction step -/

/-- the induction hypothesis: the claim for all labelled matroids of measure `< n` -/
private def IH (x : ℝ) (ι : Type*) [DecidableEq ι] (n : ℕ) : Prop :=
  ∀ (M : RkMat ι) (ℓ : ι → Lab), hsum M ℓ + M.E.card < n → GoodLab M ℓ → M.Admissible →
    M.E.Nonempty → Claim x M ℓ

/-- a parallel pair that is not a separator (used for `M` and, for series pairs, for `M*`) -/
private lemma par_case {x : ℝ} (hx2 : 2 ≤ x) (hxs : x ^ 3 ≤ 9 * (x - 1)) {n : ℕ}
    (ih : IH x ι n) {M : RkMat ι} {ℓ : ι → Lab} (hn : hsum M ℓ + M.E.card ≤ n)
    (hg : GoodLab M ℓ) (hM : M.Admissible) {f g : ι} (hpair : M.ParPair f g)
    (hns : ¬ M.IsSep {f, g}) (hf : ℓ f ∈ Lab.H) (hg' : ℓ g ∈ Lab.H) : Claim x M ℓ := by
  obtain ⟨hfE, hgE, hfg, -, -, -⟩ := id hpair
  have hfE' : f ∈ (M.del g).E := Finset.mem_erase.2 ⟨hfg, hfE⟩
  have hdel : (M.del g).Admissible := hM.del_par hpair hns
  have hgd : GoodLab (M.del g) ℓ := goodLab_mono hg (Finset.erase_subset _ _)
  -- the measure of `M ∖ g` with a new label at `f` of at most the merged size
  have hmu : ∀ l : Lab, l.size ≤ (ℓ f).size + (ℓ g).size →
      hsum (M.del g) (Function.update ℓ f l) + (M.del g).E.card < n := by
    intro l hl
    have h1 := hsum_update hfE' l (ℓ := ℓ)
    have h2 := hsum_del ℓ hgE
    have h3 : (M.del g).E.card + 1 = M.E.card := Finset.card_erase_add_one hgE
    omega
  refine step_par hx2 hxs hg hM hpair hns hf hg' ?_ ?_
  · intro l hl
    obtain ⟨-, hsz, hok⟩ := parClass_label hx2 hf hg' hl
    exact ih _ _ (hmu l hsz.le) (goodLab_update hgd f hok) hdel ⟨f, hfE'⟩
  · intro terms ht t htm
    obtain ⟨-, -, hlab⟩ := parClass_repl hx2 (le_three hxs) hf hg' ht
    obtain ⟨hH, hsz⟩ := hlab t htm
    exact ih _ _ (hmu t.lab hsz.le) (goodLab_update hgd f (Or.inl hH)) hdel ⟨f, hfE'⟩

/-- one step of the induction -/
private lemma step {x : ℝ} (hx2 : 2 ≤ x) (hxs : x ^ 3 ≤ 9 * (x - 1)) {M : RkMat ι}
    {ℓ : ι → Lab} (ih : IH x ι (hsum M ℓ + M.E.card)) (hg : GoodLab M ℓ) (hM : M.Admissible)
    (hne : M.E.Nonempty) : Claim x M ℓ := by
  -- 1. a big label
  by_cases hbig : ∃ f ∈ M.E, (ℓ f).Big
  · obtain ⟨f, hf, k, hk, hpk | hsk⟩ := hbig
    · refine step_big_p hx2 hxs hg hM hf hk hpk
        (ih _ _ ?_ (goodLab_update hg f (ok_sub_two hk).1) hM hne)
      have := hsum_update hf (Lab.p (k - 2)) (ℓ := ℓ)
      rw [hpk] at this
      simp only [Lab.size] at this
      omega
    · refine step_big_s hx2 hxs hg hM hf hk hsk
        (ih _ _ ?_ (goodLab_update hg f (ok_sub_two hk).2) hM hne)
      have := hsum_update hf (Lab.s (k - 2)) (ℓ := ℓ)
      rw [hsk] at this
      simp only [Lab.size] at this
      omega
  have hH : ∀ f ∈ M.E, ℓ f ∈ Lab.H :=
    fun f hf => (hg f hf).resolve_right fun hb => hbig ⟨f, hf, hb⟩
  have h2 := hM.two_le_card hne
  -- 2. an element in no parallel and no series pair
  by_cases hcf : ∃ f ∈ M.E, M.ClassFree f
  · obtain ⟨f, hf, hpf, hsf⟩ := hcf
    obtain ⟨h1, hc⟩ := hM f hf
    have hcard : (M.E.erase f).card + 1 = M.E.card := Finset.card_erase_add_one hf
    have hne' : (M.E.erase f).Nonempty := Finset.card_pos.1 (by omega)
    have hgf : GoodLab (M.del f) ℓ := goodLab_mono hg (Finset.erase_subset _ _)
    refine step_branch hx2 hxs hg hf h1 hc (hH f hf) (ih _ _ ?_ hgf (hM.del hf hsf) hne')
      (ih _ _ ?_ hgf (hM.con hf hpf) hne')
    · have := hsum_del ℓ hf
      simp only [RkMat.del_E]
      omega
    · have := hsum_con ℓ hf
      simp only [RkMat.con_E]
      omega
  -- 3. every element has a mate
  obtain ⟨f, hf⟩ := hne
  have hmate : ∃ g, M.ParPair f g ∨ M.SerPair f g := by
    by_contra hcon
    exact hcf ⟨f, hf, fun g hp => hcon ⟨g, Or.inl hp⟩, fun g hs => hcon ⟨g, Or.inr hs⟩⟩
  obtain ⟨g, hfg'⟩ := hmate
  have hgE : g ∈ M.E ∧ f ≠ g := by
    rcases hfg' with h | h
    · exact ⟨h.2.1, h.2.2.1⟩
    · exact ⟨h.2.1, h.2.2.1⟩
  -- 3a. `E = {f, g}`
  by_cases hE : M.E = {f, g}
  · exact step_closing hx2 hxs hg hM hgE.2 hE (hH f hf) (hH g hgE.1)
  -- 3b. `{f, g}` is a separator
  by_cases hsep : M.IsSep {f, g}
  · have hsub : ({f, g} : Finset ι) ⊂ M.E :=
      Finset.ssubset_iff_subset_ne.2 ⟨hsep.1, Ne.symm hE⟩
    have hpos : ({f, g} : Finset ι).Nonempty := ⟨f, Finset.mem_insert_self _ _⟩
    have hc1 := Finset.card_lt_card hsub
    have hc2 := Finset.card_lt_card (Finset.sdiff_ssubset hsep.1 hpos)
    have hne2 : (M.E \ {f, g}).Nonempty :=
      Finset.sdiff_nonempty.2 fun h => hE (Finset.Subset.antisymm h hsep.1)
    refine step_sep hx2 hxs hsep
      (ih _ _ ?_ (goodLab_mono hg hsep.1) (hM.restrict_sep hsep) hpos)
      (ih _ _ ?_ (goodLab_mono hg Finset.sdiff_subset) (hM.restrict_sep hsep.compl) hne2)
    · have := hsum_restrict_le ℓ hsep.1
      simp only [RkMat.restrict_E]
      omega
    · have := hsum_restrict_le ℓ (Finset.sdiff_subset (s := M.E) (t := {f, g}))
      simp only [RkMat.restrict_E]
      omega
  -- 3c. a parallel pair that is not a separator
  rcases hfg' with hpar | hser
  · exact par_case hx2 hxs ih le_rfl hg hM hpar hsep (hH f hf) (hH g hgE.1)
  -- 3d. a series pair: the parallel case in the dual (same measure)
  · refine (claim_dual hx2 M ℓ).1 (par_case hx2 hxs ih ?_ hg.dual hM.dual hser
      (fun h => hsep (RkMat.isSep_dual_iff.1 h)) (Lab.dual_mem_H (hH f hf))
      (Lab.dual_mem_H (hH g hgE.1)))
    rw [hsum_dual, RkMat.dual_E]

end Induction

/-- the weighted-skeleton theorem -/
theorem main_P {x : ℝ} (hx2 : 2 ≤ x) (hxs : x ^ 3 ≤ 9 * (x - 1)) (M : RkMat ι) (ℓ : ι → Lab)
    (hg : GoodLab M ℓ) (hM : M.Admissible) (hne : M.E.Nonempty) : Claim x M ℓ := by
  suffices H : ∀ n : ℕ, ∀ (M : RkMat ι) (ℓ : ι → Lab), hsum M ℓ + M.E.card = n →
      GoodLab M ℓ → M.Admissible → M.E.Nonempty → Claim x M ℓ from H _ M ℓ rfl hg hM hne
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M ℓ hn hg hM hne
    subst hn
    exact Induction.step hx2 hxs (fun M' ℓ' h => ih _ h M' ℓ' rfl) hg hM hne

end Results.TutteThreshold
