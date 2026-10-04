import Results.TutteThreshold.Solution.IndDefs

/-!
# Induction steps B: separators, the closing case, parallel pairs
-/

namespace Results.TutteThreshold

open Finset

variable {ι : Type*} [DecidableEq ι]

/-! ### Auxiliary facts -/

/-- multiplying two claims: `a ≤ c² ρ₁`, `b ≤ c² ρ₂` give `a b ≤ c² ρ₁ ρ₂` (`0 < c ≤ 1`) -/
lemma StepsB.mul_claim {c a b ρ₁ ρ₂ : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (h1 : a ≤ c ^ 2 * ρ₁) (h2 : b ≤ c ^ 2 * ρ₂) : a * b ≤ c ^ 2 * (ρ₁ * ρ₂) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hc21 : c ^ 2 ≤ 1 := pow_le_one₀ hc0.le hc1
  have hρ₁ : 0 ≤ ρ₁ := by
    by_contra h
    rw [not_le] at h
    have := mul_neg_of_pos_of_neg hc2 h
    linarith
  have hρ₂ : 0 ≤ ρ₂ := by
    by_contra h
    rw [not_le] at h
    have := mul_neg_of_pos_of_neg hc2 h
    linarith
  calc a * b ≤ (c ^ 2 * ρ₁) * (c ^ 2 * ρ₂) := mul_le_mul h1 h2 hb (ha.trans h1)
    _ = c ^ 2 * (c ^ 2 * (ρ₁ * ρ₂)) := by ring
    _ ≤ c ^ 2 * (1 * (ρ₁ * ρ₂)) := by gcongr
    _ = c ^ 2 * (ρ₁ * ρ₂) := by ring

/-- `x ≤ x_*` (in the form `x³ ≤ 9(x-1)`) forces `x ≤ 3` -/
lemma StepsB.le_three {x : ℝ} (hxs : x ^ 3 ≤ 9 * (x - 1)) : x ≤ 3 := by
  by_contra h
  rw [not_le] at h
  nlinarith [mul_pos (mul_pos (by linarith : (0 : ℝ) < x - 3) (by linarith : (0 : ℝ) < x))
    (by linarith : (0 : ℝ) < x + 3)]

/-- a skeleton whose ground set is a single element of rank one (a coloop):
its three sums are the coordinates `T`, `A`, `B` of that element -/
lemma StepsB.single {x : ℝ} (hx : x ≠ 0) (S : Skel ι) {f : ι} (hE : S.M.E = {f})
    (h1 : S.M.r {f} = 1) :
    S.Zb = (S.c f).T ∧ S.Za x = (S.c f).A ∧ S.Zc x = (S.c f).B := by
  have hf : f ∈ S.M.E := by rw [hE]; exact Finset.mem_singleton_self f
  have herase : S.M.E.erase f = ∅ := by rw [hE]; exact Finset.erase_singleton f
  have hcol : S.M.r (S.M.E.erase f) + 1 = S.M.r S.M.E := by
    rw [herase, RkMat.r_empty, hE, h1]
  have hemp : (S.M.del f).E = ∅ := herase
  refine ⟨?_, ?_, ?_⟩
  · unfold Skel.Zb
    rw [RkMat.Z_coloop _ _ _ _ hf hcol, RkMat.Z_empty _ _ _ _ hemp]
    simp [Coord.wb]
  · unfold Skel.Za
    rw [RkMat.Z_coloop _ _ _ _ hf hcol, RkMat.Z_empty _ _ _ _ hemp]
    simp only [Coord.wa]
    field_simp
    ring
  · unfold Skel.Zc
    rw [RkMat.Z_coloop _ _ _ _ hf hcol, RkMat.Z_empty _ _ _ _ hemp]
    simp only [Coord.wc]
    field_simp
    ring

/-- the skeleton obtained by deleting `g` and giving `f` the coordinates of a label `l` is the
labelled skeleton of `M ∖ g` with the label of `f` changed to `l` -/
lemma StepsB.lskel_update (x : ℝ) (M : RkMat ι) (ℓ : ι → Lab) (f g : ι) (l : Lab) :
    ((lskel x M ℓ).del g).upd f (l.coord x) = lskel x (M.del g) (Function.update ℓ f l) := by
  unfold lskel Skel.del Skel.upd
  congr 1
  funext y
  by_cases hy : y = f
  · subst hy
    simp
  · simp [Function.update_of_ne hy]

/-- the number of real edges after deleting `g` and relabelling `f` by `l` -/
lemma StepsB.hsum_update {M : RkMat ι} {ℓ : ι → Lab} {f g : ι} (hfE : f ∈ M.E) (hgE : g ∈ M.E)
    (hfg : f ≠ g) (l : Lab) :
    hsum (M.del g) (Function.update ℓ f l) + (ℓ f).size + (ℓ g).size = hsum M ℓ + l.size := by
  unfold hsum
  have hf' : f ∈ M.E.erase g := Finset.mem_erase.mpr ⟨hfg, hfE⟩
  have e1 : (ℓ g).size + ∑ y ∈ M.E.erase g, (ℓ y).size = ∑ y ∈ M.E, (ℓ y).size :=
    Finset.add_sum_erase _ (fun y => (ℓ y).size) hgE
  have e2 : (ℓ f).size + ∑ y ∈ (M.E.erase g).erase f, (ℓ y).size =
      ∑ y ∈ M.E.erase g, (ℓ y).size :=
    Finset.add_sum_erase _ (fun y => (ℓ y).size) hf'
  have e3 : (Function.update ℓ f l f).size +
      ∑ y ∈ (M.E.erase g).erase f, (Function.update ℓ f l y).size =
      ∑ y ∈ M.E.erase g, (Function.update ℓ f l y).size :=
    Finset.add_sum_erase _ (fun y => (Function.update ℓ f l y).size) hf'
  have e4 : ∑ y ∈ (M.E.erase g).erase f, (Function.update ℓ f l y).size =
      ∑ y ∈ (M.E.erase g).erase f, (ℓ y).size := by
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hy)]
  rw [Function.update_self, e4] at e3
  rw [RkMat.del_E]
  omega

/-! ### The three steps -/

/-- a separator: product of two claims -/
theorem step_sep {x : ℝ} (hx2 : 2 ≤ x) (hxs : x ^ 3 ≤ 9 * (x - 1)) {M : RkMat ι}
    {ℓ : ι → Lab} {A : Finset ι} (hA : M.IsSep A)
    (h1 : Claim x (M.restrict A hA.1) ℓ)
    (h2 : Claim x (M.restrict (M.E \ A) Finset.sdiff_subset) ℓ) : Claim x M ℓ := by
  unfold Claim at h1 h2 ⊢
  have hrho : (lskel x M ℓ).rho x = (lskel x (M.restrict A hA.1) ℓ).rho x *
      (lskel x (M.restrict (M.E \ A) Finset.sdiff_subset) ℓ).rho x :=
    Skel.rho_sep x (lskel x M ℓ) hA
  have hh : hsum M ℓ = hsum (M.restrict A hA.1) ℓ +
      hsum (M.restrict (M.E \ A) Finset.sdiff_subset) ℓ := by
    unfold hsum
    rw [RkMat.restrict_E, RkMat.restrict_E, add_comm]
    exact (Finset.sum_sdiff hA.1).symm
  have hc0 := Ctx.cc_pos hx2
  rw [hrho, hh, pow_add]
  exact StepsB.mul_claim hc0 (Ctx.cc_le_one hx2 hxs) (by positivity) (by positivity) h1 h2

/-- the base case `U_{1,2}` with two profiles -/
theorem step_closing {x : ℝ} (hx2 : 2 ≤ x) (hxs : x ^ 3 ≤ 9 * (x - 1)) {M : RkMat ι}
    {ℓ : ι → Lab} (hg : GoodLab M ℓ) (hM : M.Admissible) {f g : ι} (hfg : f ≠ g)
    (hE : M.E = {f, g}) (hf : ℓ f ∈ Lab.H) (hg' : ℓ g ∈ Lab.H) : Claim x M ℓ := by
  obtain ⟨hpair, -⟩ := hM.pair_of_card_two hfg hE
  have hx0 : x ≠ 0 := by linarith
  have hc0 := Ctx.cc_pos hx2
  have hc1 := Ctx.cc_le_one hx2 hxs
  -- the composite coordinates of the pair
  have hvf := Lab.coord_valid hx2 (hg f hpair.1).size_pos
  have hvg := Lab.coord_valid hx2 (hg g hpair.2.1).size_pos
  have hT : 0 < (Coord.par x ((ℓ f).coord x) ((ℓ g).coord x)).T := by
    simp only [Coord.par]
    have := mul_pos hvf.1 hvg.2.1
    have := mul_pos hvf.2.1 hvg.1
    linarith
  -- merging `g` into `f` leaves a single coloop carrying the composite coordinates
  have hmerge : (lskel x M ℓ).rho x = (((lskel x M ℓ).del g).upd f
      (Coord.par x ((ℓ f).coord x) ((ℓ g).coord x))).rho x :=
    Skel.rho_par_merge x (lskel x M ℓ) hx2 hpair
  have hE' : (((lskel x M ℓ).del g).upd f
      (Coord.par x ((ℓ f).coord x) ((ℓ g).coord x))).M.E = {f} := by
    show M.E.erase g = {f}
    rw [hE, Finset.erase_insert_of_ne hfg, Finset.erase_singleton]
    rfl
  obtain ⟨hZb, hZa, hZc⟩ := StepsB.single hx0 _ hE' hpair.2.2.2.1
  have hcf : (((lskel x M ℓ).del g).upd f
      (Coord.par x ((ℓ f).coord x) ((ℓ g).coord x))).c f =
      Coord.par x ((ℓ f).coord x) ((ℓ g).coord x) := Function.update_self _ _ _
  rw [hcf] at hZb hZa hZc
  have hrho : 1 ≤ (lskel x M ℓ).rho x := by
    rw [hmerge, Skel.rho, hZa, hZb, hZc, one_le_div (by positivity)]
    exact closing_ok hx2 hxs hf hg'
  -- `h ≥ 2`
  have hh : 2 ≤ hsum M ℓ := by
    unfold hsum
    rw [hE, Finset.sum_pair hfg]
    have := Lab.size_pos_of_mem_H hf
    have := Lab.size_pos_of_mem_H hg'
    omega
  unfold Claim
  calc cc x ^ hsum M ℓ ≤ cc x ^ 2 := pow_le_pow_of_le_one hc0.le hc1 hh
    _ = cc x ^ 2 * 1 := (mul_one _).symm
    _ ≤ cc x ^ 2 * (lskel x M ℓ).rho x := by gcongr

/-- a parallel pair that is not a separator: recognition or joint replacement -/
theorem step_par {x : ℝ} (hx2 : 2 ≤ x) (hxs : x ^ 3 ≤ 9 * (x - 1)) {M : RkMat ι}
    {ℓ : ι → Lab} (hg : GoodLab M ℓ) (hM : M.Admissible) {f g : ι} (hpair : M.ParPair f g)
    (hns : ¬ M.IsSep {f, g}) (hf : ℓ f ∈ Lab.H) (hg' : ℓ g ∈ Lab.H)
    (hrec : ∀ l, parClass (ℓ f) (ℓ g) = ParRes.label l →
      Claim x (M.del g) (Function.update ℓ f l))
    (hrep : ∀ terms, parClass (ℓ f) (ℓ g) = ParRes.repl terms →
      ∀ t ∈ terms, Claim x (M.del g) (Function.update ℓ f t.lab)) : Claim x M ℓ := by
  have hfE : f ∈ M.E := hpair.1
  have hgE : g ∈ M.E := hpair.2.1
  have hfg : f ≠ g := hpair.2.2.1
  have hc0 := Ctx.cc_pos hx2
  have hc1 := Ctx.cc_le_one hx2 hxs
  have hmerge : (lskel x M ℓ).rho x = (((lskel x M ℓ).del g).upd f
      (Coord.par x ((ℓ f).coord x) ((ℓ g).coord x))).rho x :=
    Skel.rho_par_merge x (lskel x M ℓ) hx2 hpair
  cases hcl : parClass (ℓ f) (ℓ g) with
  | label l =>
    -- recognition: the composite is the label `l`, with the same number of real edges
    obtain ⟨hPl, hsz, -⟩ := parClass_label hx2 hf hg' hcl
    have h := hrec l hcl
    unfold Claim at h ⊢
    have hh : hsum (M.del g) (Function.update ℓ f l) = hsum M ℓ := by
      have := StepsB.hsum_update (ℓ := ℓ) hfE hgE hfg l
      omega
    rw [hmerge, hPl, StepsB.lskel_update]
    rw [hh] at h
    exact h
  | repl terms =>
    -- joint replacement in the exterior `M ∖ g` at `f`
    obtain ⟨hok, hne, hterms⟩ := parClass_repl hx2 (StepsB.le_three hxs) hf hg' hcl
    have hadm := hM.del_par hpair hns
    have hfE' : f ∈ ((lskel x M ℓ).del g).M.E := Finset.mem_erase.mpr ⟨hfg, hfE⟩
    obtain ⟨hr1, hrc⟩ := hadm f hfE'
    have hval : ((lskel x M ℓ).del g).AllValid x := fun y hy =>
      Lab.coord_valid hx2 (hg y (Finset.mem_of_mem_erase hy)).size_pos
    have hRok := Skel.ctx_ok x ((lskel x M ℓ).del g) hx2 hval hfE' hr1 hrc
    have hupd := Skel.upd_eq x ((lskel x M ℓ).del g) hfE' hr1 hrc
    have hvf := Lab.coord_valid hx2 (Lab.size_pos_of_mem_H hf)
    have hvg := Lab.coord_valid hx2 (Lab.size_pos_of_mem_H hg')
    have hN : 0 < (Coord.par x ((ℓ f).coord x) ((ℓ g).coord x)).T ∧
        0 < (Coord.par x ((ℓ f).coord x) ((ℓ g).coord x)).F := by
      simp only [Coord.par]
      have := mul_pos hvf.1 hvg.2.1
      have := mul_pos hvf.2.1 hvg.1
      exact ⟨by linarith, mul_pos hvf.2.1 hvg.2.1⟩
    have hc2 : 0 < cc x ^ 2 := by positivity
    -- every replacement term has ratio at least `γ = c^h / c²`
    have hγ : ∀ t ∈ terms, cc x ^ hsum M ℓ / cc x ^ 2 ≤
        (Skel.ctx x ((lskel x M ℓ).del g) f hfE').rho x (t.lab.coord x) := by
      intro t ht
      have h := hrep terms hcl t ht
      unfold Claim at h
      rw [← StepsB.lskel_update, hupd] at h
      have hle : hsum (M.del g) (Function.update ℓ f t.lab) ≤ hsum M ℓ := by
        have := StepsB.hsum_update (ℓ := ℓ) hfE hgE hfg t.lab
        have := (hterms t ht).2
        omega
      rw [div_le_iff₀ hc2, mul_comm]
      exact (pow_le_pow_of_le_one hc0.le hc1 hle).trans h
    have key := Ctx.replace_alg hx2 hRok hN hok
      (fun t ht => Lab.size_pos_of_mem_H (hterms t ht).1) (by positivity) hγ hne
    unfold Claim
    rw [hmerge, hupd]
    rw [div_le_iff₀ hc2, mul_comm] at key
    exact key

end Results.TutteThreshold
