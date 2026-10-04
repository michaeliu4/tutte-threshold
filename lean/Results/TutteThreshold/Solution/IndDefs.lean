import Results.TutteThreshold.Solution.Cert
import Results.TutteThreshold.Solution.AlgReduce
import Results.TutteThreshold.Solution.Skel

/-!
# Definitions for the main induction

`Claim x M ℓ`: `c(x)^{h} ≤ c(x)² ρ(M,ℓ)` where `h = ∑ size`.
-/

namespace Results.TutteThreshold

open Finset

variable {ι : Type*} [DecidableEq ι]

/-- the skeleton of a labelled matroid -/
noncomputable def lskel (x : ℝ) (M : RkMat ι) (ℓ : ι → Lab) : Skel ι := ⟨M, fun f => (ℓ f).coord x⟩

/-- the number of real edges -/
def hsum (M : RkMat ι) (ℓ : ι → Lab) : ℕ := ∑ f ∈ M.E, (ℓ f).size

/-- the induction claim -/
def Claim (x : ℝ) (M : RkMat ι) (ℓ : ι → Lab) : Prop :=
  cc x ^ hsum M ℓ ≤ cc x ^ 2 * (lskel x M ℓ).rho x

def GoodLab (M : RkMat ι) (ℓ : ι → Lab) : Prop := ∀ f ∈ M.E, (ℓ f).OK

lemma GoodLab.dual {M : RkMat ι} {ℓ : ι → Lab} (h : GoodLab M ℓ) :
    GoodLab M.dual (fun f => (ℓ f).dual) :=
  fun f hf => Lab.dual_OK (h f hf)

lemma hsum_dual (M : RkMat ι) (ℓ : ι → Lab) : hsum M.dual (fun f => (ℓ f).dual) = hsum M ℓ := by
  unfold hsum
  exact Finset.sum_congr rfl fun f _ => Lab.size_dual (ℓ f)

/-- the skeleton of the dual labelling of the dual matroid is the dual skeleton -/
private lemma lskel_dual_eq (x : ℝ) (M : RkMat ι) (ℓ : ι → Lab) :
    lskel x M.dual (fun f => (ℓ f).dual) = (lskel x M ℓ).dual := by
  simp only [lskel, Skel.dual, Lab.coord_dual]

lemma lskel_dual {x : ℝ} (M : RkMat ι) (ℓ : ι → Lab) :
    (lskel x M.dual (fun f => (ℓ f).dual)).rho x = (lskel x M ℓ).rho x := by
  rw [lskel_dual_eq, Skel.rho_dual]

/-- the claim is invariant under duality -/
lemma claim_dual {x : ℝ} (hx : 2 ≤ x) (M : RkMat ι) (ℓ : ι → Lab) :
    Claim x M.dual (fun f => (ℓ f).dual) ↔ Claim x M ℓ := by
  -- `hx` belongs to the frozen interface; the equivalence holds for every `x`
  have _ := hx
  unfold Claim
  rw [hsum_dual, lskel_dual]

end Results.TutteThreshold
