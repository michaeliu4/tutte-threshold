import Results.TutteThreshold.Solution.IndDefs

/-!
# Induction steps A: big classes and the branch step
-/

namespace Results.TutteThreshold

open Finset

variable {ι : Type*} [DecidableEq ι]

namespace StepsA

/-- labels in `Lab.OK` carry valid coordinates -/
lemma allValid {x : ℝ} (hx : 2 ≤ x) {M : RkMat ι} {ℓ : ι → Lab} (hg : GoodLab M ℓ) :
    (lskel x M ℓ).AllValid x :=
  fun f hf => Lab.coord_valid hx (hg f hf).size_pos

/-- changing the label of one element changes `hsum` by the difference of the two sizes -/
lemma hsum_update {M : RkMat ι} (ℓ : ι → Lab) {f : ι} (hf : f ∈ M.E) (l : Lab) :
    hsum M (Function.update ℓ f l) + (ℓ f).size = hsum M ℓ + l.size := by
  have h : ∑ g ∈ M.E.erase f, (Function.update ℓ f l g).size = ∑ g ∈ M.E.erase f, (ℓ g).size :=
    Finset.sum_congr rfl fun g hg => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hg)]
  unfold hsum
  rw [← Finset.add_sum_erase _ _ hf, ← Finset.add_sum_erase _ _ hf, Function.update_self, h]
  omega

lemma hsum_del {M : RkMat ι} (ℓ : ι → Lab) {f : ι} (hf : f ∈ M.E) :
    hsum (M.del f) ℓ + (ℓ f).size = hsum M ℓ :=
  Finset.sum_erase_add _ _ hf

lemma hsum_con {M : RkMat ι} (ℓ : ι → Lab) {f : ι} (hf : f ∈ M.E) :
    hsum (M.con f hf) ℓ + (ℓ f).size = hsum M ℓ :=
  hsum_del ℓ hf

/-- changing the label of one element updates the coordinates of that element -/
lemma lskel_update (x : ℝ) (M : RkMat ι) (ℓ : ι → Lab) (f : ι) (l : Lab) :
    lskel x M (Function.update ℓ f l) = (lskel x M ℓ).upd f (l.coord x) := by
  simp only [lskel, Skel.upd, Skel.mk.injEq, true_and]
  funext g
  exact Function.apply_update (fun _ l => Lab.coord x l) ℓ f l g

/-- the common form of the two big steps: the label of `f` is replaced by a label with two real
edges fewer whose closure ratio is smaller by at least the factor `x²/4` in every context -/
private lemma step_big {x : ℝ} (hx2 : 2 ≤ x) (hxs : x ^ 3 ≤ 9 * (x - 1)) {M : RkMat ι}
    {ℓ : ι → Lab} (hg : GoodLab M ℓ) (hM : M.Admissible) {f : ι} (hf : f ∈ M.E) {l : Lab}
    (hl : l.size + 2 = (ℓ f).size)
    (hred : ∀ R : Ctx, R.Ok x → x ^ 2 / 4 * R.rho x (l.coord x) ≤ R.rho x ((ℓ f).coord x))
    (h : Claim x M (Function.update ℓ f l)) : Claim x M ℓ := by
  obtain ⟨h1, hc⟩ := hM f hf
  have hred' := hred _ (Skel.ctx_ok x (lskel x M ℓ) hx2 (allValid hx2 hg) hf h1 hc)
  have hh : hsum M ℓ = hsum M (Function.update ℓ f l) + 2 := by
    have := hsum_update ℓ hf l
    omega
  unfold Claim at h ⊢
  rw [lskel_update, Skel.upd_eq x (lskel x M ℓ) hf h1 hc] at h
  rw [Skel.rho_ctx x (lskel x M ℓ) hf h1 hc, hh, pow_add]
  have hc0 := Ctx.cc_pos hx2
  have hq0 : 0 < cc x ^ 2 := pow_pos hc0 2
  have hq1 : cc x ^ 2 ≤ 1 := pow_le_one₀ hc0.le (Ctx.cc_le_one hx2 hxs)
  have hA : 0 < cc x ^ hsum M (Function.update ℓ f l) := pow_pos hc0 _
  -- the ratio after the reduction is positive, by the claim for the reduced labelling
  have hρ : 0 ≤ ((lskel x M ℓ).ctx x f hf).rho x (l.coord x) :=
    (pos_of_mul_pos_right (hA.trans_le h) hq0.le).le
  have hx4 : 1 ≤ x ^ 2 / 4 := by nlinarith
  calc cc x ^ hsum M (Function.update ℓ f l) * cc x ^ 2
      ≤ cc x ^ hsum M (Function.update ℓ f l) := mul_le_of_le_one_right hA.le hq1
    _ ≤ cc x ^ 2 * ((lskel x M ℓ).ctx x f hf).rho x (l.coord x) := h
    _ ≤ cc x ^ 2 * (x ^ 2 / 4 * ((lskel x M ℓ).ctx x f hf).rho x (l.coord x)) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hρ hx4) hq0.le
    _ ≤ cc x ^ 2 * ((lskel x M ℓ).ctx x f hf).rho x ((ℓ f).coord x) :=
        mul_le_mul_of_nonneg_left hred' hq0.le

end StepsA

open StepsA

/-- a parallel class with at least four real edges loses a factor `x²/4` when two are removed -/
theorem step_big_p {x : ℝ} (hx2 : 2 ≤ x) (hxs : x ^ 3 ≤ 9 * (x - 1)) {M : RkMat ι}
    {ℓ : ι → Lab} (hg : GoodLab M ℓ) (hM : M.Admissible) {f : ι} (hf : f ∈ M.E) {k : ℕ}
    (hk : 4 ≤ k) (hℓ : ℓ f = Lab.p k)
    (h : Claim x M (Function.update ℓ f (Lab.p (k - 2)))) : Claim x M ℓ := by
  refine step_big hx2 hxs hg hM hf ?_ (fun R hR => ?_) h
  · rw [hℓ]
    show k - 2 + 2 = k
    omega
  · rw [hℓ]
    exact Ctx.reduce_p hx2 hR hk

theorem step_big_s {x : ℝ} (hx2 : 2 ≤ x) (hxs : x ^ 3 ≤ 9 * (x - 1)) {M : RkMat ι}
    {ℓ : ι → Lab} (hg : GoodLab M ℓ) (hM : M.Admissible) {f : ι} (hf : f ∈ M.E) {k : ℕ}
    (hk : 4 ≤ k) (hℓ : ℓ f = Lab.s k)
    (h : Claim x M (Function.update ℓ f (Lab.s (k - 2)))) : Claim x M ℓ := by
  refine step_big hx2 hxs hg hM hf ?_ (fun R hR => ?_) h
  · rw [hℓ]
    show k - 2 + 2 = k
    omega
  · rw [hℓ]
    exact Ctx.reduce_s hx2 hR hk

/-- branch step at an element of a profile label, neither a loop nor a coloop, both branches
satisfy the claim -/
theorem step_branch {x : ℝ} (hx2 : 2 ≤ x) (hxs : x ^ 3 ≤ 9 * (x - 1)) {M : RkMat ι}
    {ℓ : ι → Lab} (hg : GoodLab M ℓ) {f : ι} (hf : f ∈ M.E) (h1 : M.r {f} = 1)
    (hc : M.r (M.E.erase f) = M.r M.E) (hl : ℓ f ∈ Lab.H)
    (hdel : Claim x (M.del f) ℓ) (hcon : Claim x (M.con f hf) ℓ) : Claim x M ℓ := by
  have hq0 : 0 < cc x ^ 2 := pow_pos (Ctx.cc_pos hx2) 2
  -- both branches have ratio at least `γ = c^{h'} / c²`, where `h' = h - size f`
  have hγ : 0 < cc x ^ hsum (M.del f) ℓ / cc x ^ 2 := div_pos (pow_pos (Ctx.cc_pos hx2) _) hq0
  have hd : cc x ^ hsum (M.del f) ℓ / cc x ^ 2 ≤ ((lskel x M ℓ).del f).rho x := by
    rw [div_le_iff₀ hq0, mul_comm]
    exact hdel
  have hn : cc x ^ hsum (M.del f) ℓ / cc x ^ 2 ≤ ((lskel x M ℓ).con f hf).rho x := by
    rw [div_le_iff₀ hq0, mul_comm]
    exact hcon
  have hloss := Ctx.loss_label hx2 hxs
    (Skel.good_of_branches x (lskel x M ℓ) hx2 (allValid hx2 hg) hf h1 hc hγ hd hn) hl
  unfold Claim
  rw [Skel.rho_ctx x (lskel x M ℓ) hf h1 hc, ← hsum_del ℓ hf, pow_add]
  calc cc x ^ hsum (M.del f) ℓ * cc x ^ (ℓ f).size
      = cc x ^ 2 * (cc x ^ hsum (M.del f) ℓ / cc x ^ 2 * cc x ^ (ℓ f).size) := by
        rw [div_mul_eq_mul_div, mul_div_cancel₀ _ hq0.ne']
    _ ≤ cc x ^ 2 * ((lskel x M ℓ).ctx x f hf).rho x ((ℓ f).coord x) :=
        mul_le_mul_of_nonneg_left hloss hq0.le

end Results.TutteThreshold
