import Results.TutteThreshold.Defs
import Results.TutteThreshold.Solution.Components
import Results.TutteThreshold.Solution.Thresh
import Results.TutteThreshold.Solution.DoublingStruct
import Results.TutteThreshold.Solution.Asymp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Main theorems

The same statements as `Challenge.lean`, proved from the modules of `Solution/`.
-/

open Matroid Filter Topology

namespace Results.TutteThreshold

theorem thm_1_2 {xs : ℝ} (hxs : IsGreatest {t : ℝ | t ^ 3 - 9 * t + 9 = 0} xs)
    {α : Type*} (M : Matroid α) [M.Finite] (hM : IsAdmissible M) {x : ℝ}
    (hx : x ∈ Set.Icc 2 xs) :
    cFun x ^ ((M.E.ncard : ℤ) - 2 * (numComponents M : ℤ)) ≤ rho M x :=
  thm_1_2_core hx.1 (cube_le_of_le_xs hxs hx.1 hx.2) M hM

theorem thm_1_1_sufficiency {xs : ℝ} (hxs : IsGreatest {t : ℝ | t ^ 3 - 9 * t + 9 = 0} xs)
    {α : Type*} (M : Matroid α) [M.Finite] (hM : IsAdmissible M) : 1 ≤ rho M xs := by
  have h2 : 2 < xs := (xs_facts hxs).1
  have := thm_1_2 hxs M hM (x := xs) ⟨h2.le, le_refl _⟩
  rwa [cFun_xs hxs, one_zpow] at this

theorem thm_1_1 {xs : ℝ} (hxs : IsGreatest {t : ℝ | t ^ 3 - 9 * t + 9 = 0} xs) :
    IsLeast {a : ℝ | 0 ≤ a ∧
      ∀ (α : Type) (M : Matroid α) [M.Finite], IsAdmissible M → 1 ≤ rho M a} xs := by
  have h2 : 2 < xs := (xs_facts hxs).1
  refine ⟨⟨by linarith, fun α M _ hM => thm_1_1_sufficiency hxs M hM⟩, ?_⟩
  rintro a ⟨ha0, ha⟩
  by_contra hlt
  rw [not_le] at hlt
  by_cases ha2 : a < 2
  · have := ha (Fin 2) (uniformMatroid 1 2) admissible_uniform_one_two
    rw [rho_uniform_one_two] at this
    nlinarith
  · rw [not_lt] at ha2
    obtain ⟨k, hk, hlt1⟩ := exists_rhoK_lt_one ha2 (cube_lt_of_lt_xs hxs ha2 hlt)
    have := ha _ (doubling k) (doubling_structure k hk).2.1
    rw [rho_doubling] at this
    linarith

theorem thm_1_3_structure (k : ℕ) (hk : 1 ≤ k) :
    numComponents (doubling k) = 1 ∧ IsAdmissible (doubling k) ∧
      (doubling k).E.ncard = 6 * k :=
  doubling_structure k hk

theorem thm_1_3_asymptotic {xs : ℝ} (hxs : IsGreatest {t : ℝ | t ^ 3 - 9 * t + 9 = 0} xs) :
    ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → ∀ x ∈ Set.Icc 2 xs,
      |rho (doubling k) x / (4 * Real.pi / 3 * k * cFun x ^ (6 * k)) - 1| ≤ C / k := by
  obtain ⟨C, hC⟩ := rhoK_asymptotic
  refine ⟨C, fun k hk x hx => ?_⟩
  rw [rho_doubling]
  exact hC k hk x hx.1 (cube_le_of_le_xs hxs hx.1 hx.2)

theorem thm_1_3_limit {xs : ℝ} (hxs : IsGreatest {t : ℝ | t ^ 3 - 9 * t + 9 = 0} xs) {x : ℝ}
    (hx : x ∈ Set.Icc 2 xs) :
    Tendsto (fun k : ℕ => rho (doubling k) x ^ (1 / (6 * (k : ℝ)))) atTop (𝓝 (cFun x)) := by
  simp_rw [rho_doubling]
  exact rhoK_root_limit hx.1 (cube_le_of_le_xs hxs hx.1 hx.2)

end Results.TutteThreshold
