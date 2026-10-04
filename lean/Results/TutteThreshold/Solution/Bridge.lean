import Results.TutteThreshold.Defs
import Results.TutteThreshold.Solution.Skel

/-!
# From Mathlib's `Matroid` to rank matroids

`toRk M` is the rank matroid of a finite Mathlib matroid.  `tutte M x y` is the weighted rank sum
with all weights `(1,1)`, and admissibility transfers.
-/

open Matroid

namespace Results.TutteThreshold

variable {α : Type*}

/-! ### The natural-number rank of a matroid of finite rank -/

/-- every set has finite rank, so `rk` recovers `eRk` -/
lemma Bridge.cast_rk (M : Matroid α) [M.RankFinite] (X : Set α) :
    ((rk M X : ℕ) : ℕ∞) = M.eRk X :=
  ENat.coe_toNat (eRk_ne_top_iff.2 (M.isRkFinite_set X))

lemma Bridge.rk_mono (M : Matroid α) [M.RankFinite] {X Y : Set α} (h : X ⊆ Y) :
    rk M X ≤ rk M Y := by
  have := M.eRk_mono h
  rw [← Bridge.cast_rk, ← Bridge.cast_rk] at this
  exact_mod_cast this

lemma Bridge.rk_submod (M : Matroid α) [M.RankFinite] (X Y : Set α) :
    rk M (X ∪ Y) + rk M (X ∩ Y) ≤ rk M X + rk M Y := by
  have := M.eRk_inter_add_eRk_union_le X Y
  rw [← Bridge.cast_rk, ← Bridge.cast_rk, ← Bridge.cast_rk, ← Bridge.cast_rk] at this
  have h : rk M (X ∩ Y) + rk M (X ∪ Y) ≤ rk M X + rk M Y := by exact_mod_cast this
  omega

lemma Bridge.rk_le_card (M : Matroid α) [M.RankFinite] (S : Finset α) :
    rk M (S : Set α) ≤ S.card := by
  have := M.eRk_le_encard (S : Set α)
  rw [← Bridge.cast_rk, Set.encard_coe_eq_coe_finsetCard] at this
  exact_mod_cast this

lemma Bridge.rk_ground (M : Matroid α) : rk M M.E = M.eRank.toNat := by
  rw [rk, eRk_ground]

/-- the rank matroid of a finite matroid -/
noncomputable def toRk (M : Matroid α) [M.Finite] [DecidableEq α] : RkMat α where
  E := M.ground_finite.toFinset
  r := fun S => rk M (S : Set α)
  r_mono := fun _ _ h _ => Bridge.rk_mono M (Finset.coe_subset.2 h)
  r_submod := fun S T _ _ => by
    simpa only [Finset.coe_union, Finset.coe_inter] using Bridge.rk_submod M (S : Set α) T
  r_le_card := fun S _ => Bridge.rk_le_card M S

lemma toRk_E (M : Matroid α) [M.Finite] [DecidableEq α] :
    (toRk M).E = M.ground_finite.toFinset := rfl

lemma toRk_r (M : Matroid α) [M.Finite] [DecidableEq α] (S : Finset α) :
    (toRk M).r S = rk M (S : Set α) := rfl

lemma Bridge.mem_toRk_E (M : Matroid α) [M.Finite] [DecidableEq α] {e : α} :
    e ∈ (toRk M).E ↔ e ∈ M.E := by
  rw [toRk_E, Set.Finite.mem_toFinset]

lemma Bridge.toRk_r_E (M : Matroid α) [M.Finite] [DecidableEq α] :
    (toRk M).r (toRk M).E = M.eRank.toNat := by
  rw [toRk_r, toRk_E, Set.Finite.coe_toFinset, Bridge.rk_ground]

/-- the Tutte polynomial is the weighted rank sum with unit weights -/
lemma tutte_eq_Z (M : Matroid α) [M.Finite] [DecidableEq α] (x y : ℝ) :
    tutte M x y = (toRk M).Z (x - 1) (y - 1) (fun _ => ((1 : ℝ), (1 : ℝ))) := by
  rw [tutte, RkMat.Z, Bridge.toRk_r_E, toRk_E]
  refine Finset.sum_congr rfl fun S _ => ?_
  simp only [toRk_r, Finset.prod_const_one, mul_one]

/-! ### Loops, coloops and admissibility -/

lemma Bridge.isLoop_iff (M : Matroid α) [M.Finite] [DecidableEq α] {e : α} (he : e ∈ M.E) :
    M.IsLoop e ↔ (toRk M).r {e} = 0 := by
  rw [toRk_r, Finset.coe_singleton, rk]
  by_cases hl : M.IsLoop e
  · simp only [hl, hl.eRk_eq, true_iff]
    rfl
  · simp only [hl, ((not_isLoop_iff he).1 hl).eRk_eq, false_iff]
    exact one_ne_zero

lemma Bridge.isColoop_iff (M : Matroid α) [M.Finite] [DecidableEq α] {e : α} (he : e ∈ M.E) :
    M.IsColoop e ↔ (toRk M).r ((toRk M).E.erase e) < (toRk M).r (toRk M).E := by
  rw [toRk_r, toRk_r, toRk_E, Finset.coe_erase, Set.Finite.coe_toFinset]
  have hd := M.eRk_dual_add_eRank {e} (Set.singleton_subset_iff.2 he)
  rw [Set.encard_singleton, ← eRk_ground, ← Bridge.cast_rk M M.E,
    ← Bridge.cast_rk M (M.E \ {e})] at hd
  by_cases hl : M.IsColoop e
  · rw [IsLoop.eRk_eq (M := M✶) hl, zero_add] at hd
    have : rk M M.E = rk M (M.E \ {e}) + 1 := by exact_mod_cast hd
    simp only [hl, true_iff]
    omega
  · rw [((not_isLoop_iff (M := M✶) he).1 hl).eRk_eq] at hd
    have : 1 + rk M M.E = rk M (M.E \ {e}) + 1 := by exact_mod_cast hd
    simp only [hl, false_iff, not_lt]
    omega

/-- admissibility of a finite matroid is admissibility of its rank matroid -/
lemma Bridge.isAdmissible_iff (M : Matroid α) [M.Finite] [DecidableEq α] :
    IsAdmissible M ↔ (toRk M).Admissible := by
  constructor
  · intro hM f hf
    have hf' := (Bridge.mem_toRk_E M).1 hf
    have h0 : (toRk M).r {f} ≠ 0 := fun h => hM.1 f ((Bridge.isLoop_iff M hf').2 h)
    have h1 : (toRk M).r {f} ≤ 1 := by
      simpa using (toRk M).r_le_card (Finset.singleton_subset_iff.2 hf)
    have hlt : ¬ (toRk M).r ((toRk M).E.erase f) < (toRk M).r (toRk M).E :=
      fun h => hM.2 f ((Bridge.isColoop_iff M hf').2 h)
    have hle := (toRk M).r_mono (Finset.erase_subset f (toRk M).E) subset_rfl
    exact ⟨by omega, by omega⟩
  · intro h
    refine ⟨fun e he => ?_, fun e he => ?_⟩
    · have := (h e ((Bridge.mem_toRk_E M).2 he.mem_ground)).1
      rw [(Bridge.isLoop_iff M he.mem_ground).1 he] at this
      exact zero_ne_one this
    · have h2 := (h e ((Bridge.mem_toRk_E M).2 he.mem_ground)).2
      have := (Bridge.isColoop_iff M he.mem_ground).1 he
      omega

lemma admissible_toRk (M : Matroid α) [M.Finite] [DecidableEq α] (hM : IsAdmissible M) :
    (toRk M).Admissible :=
  (Bridge.isAdmissible_iff M).1 hM

/-! ### The ratio -/

/-- the three weight pairs of a single edge are `(1, 1)` -/
lemma Bridge.wts_p1 {x : ℝ} (hx : x ≠ 0) :
    (Lab.coord x (Lab.p 1)).wb = (1, 1) ∧ (Lab.coord x (Lab.p 1)).wa x = (1, 1) ∧
      (Lab.coord x (Lab.p 1)).wc x = (1, 1) := by
  simp [Lab.coord, Lab.pk, Coord.wb, Coord.wa, Coord.wc, hx]

/-- the ratio of a finite matroid is the ratio of the skeleton with every element a single edge -/
lemma rho_eq_lskel (M : Matroid α) [M.Finite] [DecidableEq α] {x : ℝ} (hx : 2 ≤ x) :
    rho M x = (Skel.mk (toRk M) (fun _ => Lab.coord x (Lab.p 1))).rho x := by
  obtain ⟨hb, ha, hc⟩ := Bridge.wts_p1 (x := x) (by linarith)
  simp only [rho, Skel.rho, Skel.Za, Skel.Zc, Skel.Zb, hb, ha, hc, tutte_eq_Z]
  norm_num

lemma card_toRk (M : Matroid α) [M.Finite] [DecidableEq α] :
    (toRk M).E.card = M.E.ncard :=
  (Set.ncard_eq_toFinset_card M.E M.ground_finite).symm

end Results.TutteThreshold
