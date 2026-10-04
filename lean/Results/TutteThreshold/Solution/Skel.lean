import Results.TutteThreshold.Solution.Lab
import Results.TutteThreshold.Solution.Posit

/-!
# Weighted skeletons

A skeleton is a rank matroid `M` with one coordinate vector per element.  Its three weighted sums
are `Zb` (bases), `Za` (axis `y = 0`) and `Zc` (axis `x = 0`), and its ratio is `Za * Zc / Zb ^ 2`.
-/

namespace Results.TutteThreshold

open Finset

structure Skel (ι : Type*) [DecidableEq ι] where
  M : RkMat ι
  c : ι → Coord

namespace Skel

variable {ι : Type*} [DecidableEq ι]

noncomputable def Zb (S : Skel ι) : ℝ := S.M.Z 0 0 (fun f => (S.c f).wb)
noncomputable def Za (x : ℝ) (S : Skel ι) : ℝ := S.M.Z (x - 1) (-1) (fun f => (S.c f).wa x)
noncomputable def Zc (x : ℝ) (S : Skel ι) : ℝ := S.M.Z (-1) (x - 1) (fun f => (S.c f).wc x)
noncomputable def rho (x : ℝ) (S : Skel ι) : ℝ := S.Za x * S.Zc x / S.Zb ^ 2

def del (S : Skel ι) (f : ι) : Skel ι := ⟨S.M.del f, S.c⟩
def con (S : Skel ι) (f : ι) (hf : f ∈ S.M.E) : Skel ι := ⟨S.M.con f hf, S.c⟩
def dual (S : Skel ι) : Skel ι := ⟨S.M.dual, fun f => (S.c f).dual⟩
def restrict (S : Skel ι) (A : Finset ι) (hA : A ⊆ S.M.E) : Skel ι := ⟨S.M.restrict A hA, S.c⟩
def upd (S : Skel ι) (f : ι) (p : Coord) : Skel ι := ⟨S.M, Function.update S.c f p⟩

/-- every element carries valid coordinates -/
def AllValid (x : ℝ) (S : Skel ι) : Prop := ∀ f ∈ S.M.E, (S.c f).Valid x

/-- the exterior context at an element `f` -/
noncomputable def ctx (x : ℝ) (S : Skel ι) (f : ι) (hf : f ∈ S.M.E) : Ctx :=
  ⟨(S.del f).Zb, (S.con f hf).Zb, (S.del f).Za x, (S.con f hf).Za x, (S.con f hf).Zc x,
    (S.del f).Zc x⟩

/-! ### Congruence: the sums only see the coordinates of the elements of the ground set -/

/-- `Zb` only depends on the rank function on `E` and on the coordinates of the elements of `E` -/
lemma Zb_congr {S T : Skel ι} (hM : S.M.Same T.M) (hc : ∀ f ∈ S.M.E, S.c f = T.c f) :
    S.Zb = T.Zb :=
  RkMat.Z_congr 0 0 hM fun f hf => congrArg Coord.wb (hc f hf)

/-- `Za` only depends on the rank function on `E` and on the coordinates of the elements of `E` -/
lemma Za_congr (x : ℝ) {S T : Skel ι} (hM : S.M.Same T.M) (hc : ∀ f ∈ S.M.E, S.c f = T.c f) :
    S.Za x = T.Za x :=
  RkMat.Z_congr _ _ hM fun f hf => congrArg (Coord.wa x) (hc f hf)

/-- `Zc` only depends on the rank function on `E` and on the coordinates of the elements of `E` -/
lemma Zc_congr (x : ℝ) {S T : Skel ι} (hM : S.M.Same T.M) (hc : ∀ f ∈ S.M.E, S.c f = T.c f) :
    S.Zc x = T.Zc x :=
  RkMat.Z_congr _ _ hM fun f hf => congrArg (Coord.wc x) (hc f hf)

/-- the ratio only depends on the rank function on `E` and on the coordinates of the elements
of `E` -/
lemma rho_congr (x : ℝ) {S T : Skel ι} (hM : S.M.Same T.M) (hc : ∀ f ∈ S.M.E, S.c f = T.c f) :
    S.rho x = T.rho x := by
  rw [rho, rho, Zb_congr hM hc, Za_congr x hM hc, Zc_congr x hM hc]

variable (x : ℝ) (S : Skel ι)

lemma Zb_dual : S.dual.Zb = S.Zb := by
  show S.M.dual.Z 0 0 (fun f => (S.c f).dual.wb) = S.M.Z 0 0 (fun f => (S.c f).wb)
  rw [RkMat.Z_dual]
  simp only [Coord.wb_dual]

lemma Za_dual : S.dual.Za x = S.Zc x := by
  show S.M.dual.Z (x - 1) (-1) (fun f => (S.c f).dual.wa x) =
    S.M.Z (-1) (x - 1) (fun f => (S.c f).wc x)
  rw [RkMat.Z_dual]
  simp only [Coord.wa_dual]

lemma Zc_dual : S.dual.Zc x = S.Za x := by
  show S.M.dual.Z (-1) (x - 1) (fun f => (S.c f).dual.wc x) =
    S.M.Z (x - 1) (-1) (fun f => (S.c f).wa x)
  rw [RkMat.Z_dual]
  simp only [Coord.wc_dual]

lemma rho_dual : S.dual.rho x = S.rho x := by
  rw [rho, rho, Zb_dual, Za_dual, Zc_dual, mul_comm (S.Zc x)]

lemma AllValid.dual (h : S.AllValid x) : S.dual.AllValid x := fun f hf => (h f hf).dual

lemma AllValid.del (h : S.AllValid x) (f : ι) : (S.del f).AllValid x :=
  fun g hg => h g (Finset.mem_of_mem_erase hg)

lemma AllValid.con (h : S.AllValid x) {f : ι} (hf : f ∈ S.M.E) : (S.con f hf).AllValid x :=
  fun g hg => h g (Finset.mem_of_mem_erase hg)

lemma AllValid.restrict (h : S.AllValid x) {A : Finset ι} (hA : A ⊆ S.M.E) :
    (S.restrict A hA).AllValid x :=
  fun g hg => h g (hA hg)

lemma Zb_pos (hx : 2 ≤ x) (h : S.AllValid x) : 0 < S.Zb :=
  -- `hx` belongs to the uniform interface; positivity of the base weights suffices
  have _ := hx
  RkMat.Zb_pos S.M _ fun f hf => (h f hf).wb_pos

lemma Za_nonneg (hx : 2 ≤ x) (h : S.AllValid x) : 0 ≤ S.Za x :=
  RkMat.Z_nonneg_alpha S.M (x - 1) _ (by linarith) fun f hf => (h f hf).wa_range hx

lemma Zc_nonneg (hx : 2 ≤ x) (h : S.AllValid x) : 0 ≤ S.Zc x :=
  RkMat.Z_nonneg_beta S.M (x - 1) _ (by linarith) fun f hf => (h f hf).wc_range hx

/-- deletion–contraction at an ordinary element, in coordinates -/
lemma ord_eq {f : ι} (hf : f ∈ S.M.E) (h1 : S.M.r {f} = 1)
    (hc : S.M.r (S.M.E.erase f) = S.M.r S.M.E) :
    S.Zb = (S.ctx x f hf).b (S.c f) ∧ S.Za x = (S.ctx x f hf).al x (S.c f) ∧
      S.Zc x = (S.ctx x f hf).be x (S.c f) := by
  refine ⟨RkMat.Z_ord S.M 0 0 (fun g => (S.c g).wb) hf h1 hc, ?_, ?_⟩
  · have key : S.Za x = ((S.c f).A + (S.c f).I) / x * (S.del f).Za x +
        ((S.c f).A - (x - 1) * (S.c f).I) / x * (S.con f hf).Za x :=
      RkMat.Z_ord S.M (x - 1) (-1) (fun g => (S.c g).wa x) hf h1 hc
    rw [key]
    show _ = ((S.del f).Za x * ((S.c f).A + (S.c f).I) +
      (S.con f hf).Za x * ((S.c f).A - (x - 1) * (S.c f).I)) / x
    ring
  · have key : S.Zc x = ((S.c f).C - (x - 1) * (S.c f).B) / x * (S.del f).Zc x +
        ((S.c f).C + (S.c f).B) / x * (S.con f hf).Zc x :=
      RkMat.Z_ord S.M (-1) (x - 1) (fun g => (S.c g).wc x) hf h1 hc
    rw [key]
    show _ = ((S.del f).Zc x * ((S.c f).C - (x - 1) * (S.c f).B) +
      (S.con f hf).Zc x * ((S.c f).C + (S.c f).B)) / x
    ring

lemma rho_ctx {f : ι} (hf : f ∈ S.M.E) (h1 : S.M.r {f} = 1)
    (hc : S.M.r (S.M.E.erase f) = S.M.r S.M.E) :
    S.rho x = (S.ctx x f hf).rho x (S.c f) := by
  obtain ⟨hb, ha, hc'⟩ := S.ord_eq x hf h1 hc
  rw [rho, Ctx.rho, hb, ha, hc']

/-- the exterior context of valid weights satisfies the monotonicity hypotheses -/
lemma ctx_ok (hx : 2 ≤ x) (h : S.AllValid x) {f : ι} (hf : f ∈ S.M.E) (h1 : S.M.r {f} = 1)
    (hc : S.M.r (S.M.E.erase f) = S.M.r S.M.E) : (S.ctx x f hf).Ok x := by
  have hz : (0 : ℝ) ≤ x - 1 := by linarith
  have hd : (S.del f).AllValid x := AllValid.del x S h f
  have hc' : (S.con f hf).AllValid x := AllValid.con x S h hf
  exact
    { hT := Zb_pos x _ hx hd
      hF := Zb_pos x _ hx hc'
      hA := Za_nonneg x _ hx hd
      hI := Za_nonneg x _ hx hc'
      hB := Zc_nonneg x _ hx hd
      hC := Zc_nonneg x _ hx hc'
      h3 := RkMat.nbc_alpha S.M (x - 1) (fun g => (S.c g).wa x) hz hf h1 hc
        fun g hg _ => (h g hg).wa_range hx
      h4 := RkMat.nbc_beta S.M (x - 1) (fun g => (S.c g).wc x) hz hf h1 hc
        fun g hg _ => (h g hg).wc_range hx }

/-- both branches have ratio at least `γ` ⟹ the branch hypotheses hold -/
lemma good_of_branches (hx : 2 ≤ x) (h : S.AllValid x) {f : ι} (hf : f ∈ S.M.E)
    (h1 : S.M.r {f} = 1) (hc : S.M.r (S.M.E.erase f) = S.M.r S.M.E) {γ : ℝ} (hγ : 0 < γ)
    (hdel : γ ≤ (S.del f).rho x) (hcon : γ ≤ (S.con f hf).rho x) :
    (S.ctx x f hf).Good x γ := by
  have hok := S.ctx_ok x hx h hf h1 hc
  have hT : 0 < (S.del f).Zb := hok.hT
  have hF : 0 < (S.con f hf).Zb := hok.hF
  rw [rho, le_div_iff₀ (pow_pos hT 2)] at hdel
  rw [rho, le_div_iff₀ (pow_pos hF 2)] at hcon
  exact
    { hγ := hγ, hT := hok.hT, hF := hok.hF, hI := hok.hI, hB := hok.hB
      h1 := hdel, h2 := hcon, h3 := hok.h3, h4 := hok.h4 }

/-- updating the coordinate of `f` to `p` updates the weights of `f` to `w p` -/
private lemma update_wt (w : Coord → Wt) (c : ι → Coord) (f : ι) (p : Coord) :
    Function.update (fun k => w (c k)) f (w p) = fun k => w (Function.update c f p k) := by
  funext k
  by_cases hk : k = f
  · subst hk
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hk, Function.update_of_ne hk]

/-- merging two parallel elements into one with the composite coordinates -/
lemma par_merge (hx : 2 ≤ x) {f g : ι} (h : S.M.ParPair f g) :
    S.Zb = ((S.del g).upd f (Coord.par x (S.c f) (S.c g))).Zb ∧
    S.Za x = ((S.del g).upd f (Coord.par x (S.c f) (S.c g))).Za x ∧
    S.Zc x = ((S.del g).upd f (Coord.par x (S.c f) (S.c g))).Zc x := by
  have hx0 : x ≠ 0 := (show (0 : ℝ) < x by linarith).ne'
  refine ⟨(RkMat.Z_par S.M 0 0 (fun k => (S.c k).wb) h).trans ?_,
    (RkMat.Z_par S.M (x - 1) (-1) (fun k => (S.c k).wa x) h).trans ?_,
    (RkMat.Z_par S.M (-1) (x - 1) (fun k => (S.c k).wc x) h).trans ?_⟩
  · rw [← Coord.wb_par x, update_wt Coord.wb]; rfl
  · rw [← Coord.wa_par hx0, update_wt (Coord.wa x)]; rfl
  · rw [← Coord.wc_par hx0, update_wt (Coord.wc x)]; rfl

lemma rho_par_merge (hx : 2 ≤ x) {f g : ι} (h : S.M.ParPair f g) :
    S.rho x = ((S.del g).upd f (Coord.par x (S.c f) (S.c g))).rho x := by
  obtain ⟨hb, ha, hc⟩ := S.par_merge x hx h
  rw [rho, rho, hb, ha, hc]

/-- multiplicativity along a separator -/
lemma rho_sep {A : Finset ι} (hA : S.M.IsSep A) :
    S.rho x = (S.restrict A hA.1).rho x * (S.restrict (S.M.E \ A) Finset.sdiff_subset).rho x := by
  have hb : S.Zb = (S.restrict A hA.1).Zb * (S.restrict (S.M.E \ A) Finset.sdiff_subset).Zb :=
    RkMat.Z_sep S.M 0 0 (fun f => (S.c f).wb) hA
  have ha : S.Za x =
      (S.restrict A hA.1).Za x * (S.restrict (S.M.E \ A) Finset.sdiff_subset).Za x :=
    RkMat.Z_sep S.M (x - 1) (-1) (fun f => (S.c f).wa x) hA
  have hc : S.Zc x =
      (S.restrict A hA.1).Zc x * (S.restrict (S.M.E \ A) Finset.sdiff_subset).Zc x :=
    RkMat.Z_sep S.M (-1) (x - 1) (fun f => (S.c f).wc x) hA
  rw [rho, rho, rho, hb, ha, hc]
  ring

private lemma ctx_upd_aux {f : ι} (hf : f ∈ S.M.E) (p : Coord) :
    (S.upd f p).ctx x f hf = S.ctx x f hf := by
  have key : ∀ g ∈ S.M.E.erase f, Function.update S.c f p g = S.c g :=
    fun g hg => Function.update_of_ne (Finset.ne_of_mem_erase hg) _ _
  show Ctx.mk _ _ _ _ _ _ = Ctx.mk _ _ _ _ _ _
  congr 1
  · exact Zb_congr (RkMat.Same.refl _) key
  · exact Zb_congr (RkMat.Same.refl _) key
  · exact Za_congr x (RkMat.Same.refl _) key
  · exact Za_congr x (RkMat.Same.refl _) key
  · exact Zc_congr x (RkMat.Same.refl _) key
  · exact Zc_congr x (RkMat.Same.refl _) key

/-- changing the coordinates of one element: the closure formulas of the exterior apply -/
lemma upd_eq {f : ι} (hf : f ∈ S.M.E) (h1 : S.M.r {f} = 1)
    (hc : S.M.r (S.M.E.erase f) = S.M.r S.M.E) (p : Coord) :
    (S.upd f p).rho x = (S.ctx x f hf).rho x p := by
  rw [rho_ctx x (S.upd f p) hf h1 hc, ctx_upd_aux x S hf p]
  show (S.ctx x f hf).rho x (Function.update S.c f p f) = _
  rw [Function.update_self]

lemma ctx_upd {f : ι} (hf : f ∈ S.M.E) (p : Coord) :
    (S.upd f p).ctx x f hf = S.ctx x f hf := ctx_upd_aux x S hf p

end Skel

end Results.TutteThreshold
