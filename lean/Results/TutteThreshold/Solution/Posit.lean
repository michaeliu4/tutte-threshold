import Results.TutteThreshold.Solution.Zsum
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
# Positivity of weighted rank sums and the weighted broken-circuit inequality

Weights of "α-type" satisfy `0 ≤ W¹ ≤ W⁰`; weights of "β-type" satisfy `0 ≤ W⁰ ≤ W¹`.
Throughout `z ≥ 0` (in the application `z = x - 1 ≥ 1`).
-/

namespace Results.TutteThreshold

open Finset

namespace RkMat

variable {ι : Type*} [DecidableEq ι] (M : RkMat ι) (z : ℝ) (W : ι → Wt)

/-! ### Loops, coloops and ordinary elements -/

/-- every element is a loop, a coloop or neither -/
lemma posit_trichotomy {f : ι} (hf : f ∈ M.E) :
    M.r {f} = 0 ∨ M.r (M.E.erase f) + 1 = M.r M.E ∨
      (M.r {f} = 1 ∧ M.r (M.E.erase f) = M.r M.E) := by
  have h1 := M.r_single_le hf
  have h2 := M.r_le_r_E (Finset.erase_subset f M.E)
  have h3 := M.r_insert_le (Finset.erase_subset f M.E) hf
  rw [Finset.insert_erase hf] at h3
  omega

/-- adding a loop does not change the rank -/
lemma posit_r_insert_loop {f : ι} (hf : f ∈ M.E) (h0 : M.r {f} = 0) {S : Finset ι}
    (hS : S ⊆ M.E) : M.r (insert f S) = M.r S := by
  have h := M.r_submod (S := {f}) (T := S) (Finset.singleton_subset_iff.2 hf) hS
  rw [← Finset.insert_eq] at h
  have := M.r_le_insert hS hf
  omega

/-- adding a coloop `f` raises the rank of every subset of `E ∖ f` by one -/
lemma posit_r_insert_coloop {f : ι} (hf : f ∈ M.E) (hc : M.r (M.E.erase f) + 1 = M.r M.E)
    {S : Finset ι} (hS : S ⊆ M.E.erase f) : M.r (insert f S) = M.r S + 1 := by
  have hS' : S ⊆ M.E := hS.trans (Finset.erase_subset _ _)
  have h := M.r_submod (S := insert f S) (T := M.E.erase f) (Finset.insert_subset hf hS')
    (Finset.erase_subset _ _)
  rw [Finset.insert_union, Finset.union_eq_right.2 hS, Finset.insert_erase hf,
    Finset.insert_inter_of_notMem (Finset.notMem_erase f M.E), Finset.inter_eq_left.2 hS] at h
  have := M.r_insert_le hS' hf
  omega

/-! ### Positivity -/

/-- α-type weights give a nonnegative sum on the axis `y = 0` -/
lemma Z_nonneg_alpha (hz : 0 ≤ z) (hW : ∀ f ∈ M.E, 0 ≤ (W f).2 ∧ (W f).2 ≤ (W f).1) :
    0 ≤ M.Z z (-1) W := by
  suffices h : ∀ n : ℕ, ∀ N : RkMat ι, N.E.card = n →
      (∀ f ∈ N.E, 0 ≤ (W f).2 ∧ (W f).2 ≤ (W f).1) → 0 ≤ N.Z z (-1) W from h _ M rfl hW
  intro n
  induction n with
  | zero =>
    intro N hn _
    rw [N.Z_empty z (-1) W (Finset.card_eq_zero.1 hn)]
    exact zero_le_one
  | succ n ih =>
    intro N hn hWN
    obtain ⟨f, hf⟩ : N.E.Nonempty := by rw [← Finset.card_pos, hn]; omega
    have hn' : (N.E.erase f).card = n := by
      have := Finset.card_erase_of_mem hf
      omega
    have hWd : ∀ g ∈ N.E.erase f, 0 ≤ (W g).2 ∧ (W g).2 ≤ (W g).1 :=
      fun g hg => hWN g (Finset.mem_of_mem_erase hg)
    have ihd := ih (N.del f) hn' hWd
    obtain ⟨h0f, h1f⟩ := hWN f hf
    rcases N.posit_trichotomy hf with h0 | hc | ⟨h1, hc⟩
    · rw [N.Z_loop z (-1) W hf h0]
      exact mul_nonneg (by linarith) ihd
    · rw [N.Z_coloop z (-1) W hf hc]
      exact mul_nonneg (add_nonneg (mul_nonneg hz (h0f.trans h1f)) h0f) ihd
    · rw [N.Z_ord z (-1) W hf h1 hc]
      exact add_nonneg (mul_nonneg (h0f.trans h1f) ihd) (mul_nonneg h0f (ih (N.con f hf) hn' hWd))

/-- positive weights give a positive number of (weighted) bases -/
lemma Zb_pos (hW : ∀ f ∈ M.E, 0 < (W f).1 ∧ 0 < (W f).2) : 0 < M.Z 0 0 W := by
  suffices h : ∀ n : ℕ, ∀ N : RkMat ι, N.E.card = n →
      (∀ f ∈ N.E, 0 < (W f).1 ∧ 0 < (W f).2) → 0 < N.Z 0 0 W from h _ M rfl hW
  intro n
  induction n with
  | zero =>
    intro N hn _
    rw [N.Z_empty 0 0 W (Finset.card_eq_zero.1 hn)]
    exact zero_lt_one
  | succ n ih =>
    intro N hn hWN
    obtain ⟨f, hf⟩ : N.E.Nonempty := by rw [← Finset.card_pos, hn]; omega
    have hn' : (N.E.erase f).card = n := by
      have := Finset.card_erase_of_mem hf
      omega
    have hWd : ∀ g ∈ N.E.erase f, 0 < (W g).1 ∧ 0 < (W g).2 :=
      fun g hg => hWN g (Finset.mem_of_mem_erase hg)
    have ihd := ih (N.del f) hn' hWd
    obtain ⟨h0f, h1f⟩ := hWN f hf
    rcases N.posit_trichotomy hf with h0 | hc | ⟨h1, hc⟩
    · rw [N.Z_loop 0 0 W hf h0]
      exact mul_pos (by linarith) ihd
    · rw [N.Z_coloop 0 0 W hf hc]
      exact mul_pos (by linarith) ihd
    · rw [N.Z_ord 0 0 W hf h1 hc]
      exact add_pos (mul_pos h0f ihd) (mul_pos h1f (ih (N.con f hf) hn' hWd))

/-! ### The weighted broken-circuit sum `a₁` -/

/-- `a₁(M, e)`: the weighted sum over the subsets `S ⊆ E ∖ e` whose closure contains `e` -/
noncomputable def positA1 (e : ι) : ℝ :=
  ∑ S ∈ (M.E.erase e).powerset,
    if M.r (insert e S) = M.r S then
      z ^ (M.r M.E - M.r S) * (-1 : ℝ) ^ (S.card - M.r S) *
        ((∏ g ∈ S, (W g).2) * ∏ g ∈ M.E.erase e \ S, (W g).1)
    else 0

/-- splitting `a₁(M, e)` along an element `f ≠ e`: the subsets avoiding `f` give
`a₁(M ∖ f, e)` (up to the factor `z ^ (r E - r (E ∖ f)) W⁰ f`) -/
lemma positA1_split {e f : ι} (hf : f ∈ M.E) (hfe : f ≠ e) :
    M.positA1 z W e = z ^ (M.r M.E - M.r (M.E.erase f)) * (W f).1 * (M.del f).positA1 z W e +
      ∑ T ∈ ((M.E.erase f).erase e).powerset,
        if M.r (insert e (insert f T)) = M.r (insert f T) then
          z ^ (M.r M.E - M.r (insert f T)) * (-1 : ℝ) ^ (T.card + 1 - M.r (insert f T)) *
            ((W f).2 * (∏ g ∈ T, (W g).2) * ∏ g ∈ (M.E.erase f).erase e \ T, (W g).1)
        else 0 := by
  have hD : M.E.erase e = insert f ((M.E.erase f).erase e) := by
    rw [Finset.erase_right_comm, Finset.insert_erase (Finset.mem_erase.2 ⟨hfe, hf⟩)]
  have hfD : f ∉ (M.E.erase f).erase e := fun h =>
    Finset.notMem_erase f M.E (Finset.mem_of_mem_erase h)
  unfold positA1
  simp only [del_E, del_r]
  rw [hD, Finset.sum_powerset_insert hfD, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro T hT
    rw [Finset.mem_powerset] at hT
    have hfT : f ∉ T := fun h => hfD (hT h)
    rw [Finset.insert_sdiff_of_notMem _ hfT,
      Finset.prod_insert (fun h => hfD (Finset.sdiff_subset h))]
    have hTE : T ⊆ M.E.erase f := hT.trans (Finset.erase_subset _ _)
    have h1 : M.r T ≤ M.r (M.E.erase f) := M.r_mono hTE (Finset.erase_subset _ _)
    have h2 : M.r (M.E.erase f) ≤ M.r M.E := M.r_le_r_E (Finset.erase_subset _ _)
    rw [show M.r M.E - M.r T = (M.r M.E - M.r (M.E.erase f)) + (M.r (M.E.erase f) - M.r T) by
      omega, pow_add]
    split_ifs <;> ring
  · apply Finset.sum_congr rfl
    intro T hT
    rw [Finset.mem_powerset] at hT
    have hfT : f ∉ T := fun h => hfD (hT h)
    rw [Finset.insert_sdiff_insert, Finset.sdiff_insert_of_notMem hfD, Finset.prod_insert hfT,
      Finset.card_insert_of_notMem hfT]

/-- `a₁` when `f ≠ e` is a loop -/
lemma positA1_loop {e f : ι} (hf : f ∈ M.E) (hfe : f ≠ e) (he : e ∈ M.E) (h0 : M.r {f} = 0) :
    M.positA1 z W e = ((W f).1 - (W f).2) * (M.del f).positA1 z W e := by
  have hrE : M.r (M.E.erase f) = M.r M.E := by
    have := M.posit_r_insert_loop hf h0 (Finset.erase_subset f M.E)
    rw [Finset.insert_erase hf] at this
    exact this.symm
  rw [M.positA1_split z W hf hfe, hrE, Nat.sub_self, pow_zero, one_mul, sub_mul, sub_eq_add_neg]
  congr 1
  unfold positA1
  simp only [del_E, del_r]
  rw [← neg_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  rw [Finset.mem_powerset] at hT
  have hTE : T ⊆ M.E := hT.trans ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
  have heE : insert e T ⊆ M.E := Finset.insert_subset he hTE
  rw [Finset.insert_comm e f T, M.posit_r_insert_loop hf h0 heE, M.posit_r_insert_loop hf h0 hTE,
    hrE]
  have hc := M.r_le_card hTE
  rw [show T.card + 1 - M.r T = (T.card - M.r T) + 1 by omega, pow_succ]
  split_ifs <;> ring

/-- `a₁` when `f ≠ e` is a coloop -/
lemma positA1_coloop {e f : ι} (hf : f ∈ M.E) (hfe : f ≠ e) (he : e ∈ M.E)
    (hc : M.r (M.E.erase f) + 1 = M.r M.E) :
    M.positA1 z W e = (z * (W f).1 + (W f).2) * (M.del f).positA1 z W e := by
  rw [M.positA1_split z W hf hfe, show M.r M.E - M.r (M.E.erase f) = 1 by omega, pow_one, add_mul]
  congr 1
  unfold positA1
  simp only [del_E, del_r]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  rw [Finset.mem_powerset] at hT
  have hTf : T ⊆ M.E.erase f := hT.trans (Finset.erase_subset _ _)
  have heTf : insert e T ⊆ M.E.erase f :=
    Finset.insert_subset (Finset.mem_erase.2 ⟨hfe.symm, he⟩) hTf
  rw [Finset.insert_comm e f T, M.posit_r_insert_coloop hf hc heTf,
    M.posit_r_insert_coloop hf hc hTf]
  have h1 : M.r T ≤ M.r (M.E.erase f) := M.r_mono hTf (Finset.erase_subset _ _)
  rw [show M.r M.E - (M.r T + 1) = M.r (M.E.erase f) - M.r T by omega, Nat.add_sub_add_right]
  by_cases h : M.r (insert e T) = M.r T
  · rw [if_pos (by rw [h]), if_pos h]
    ring
  · rw [if_neg (by omega), if_neg h]
    ring

/-- `a₁` when `f ≠ e` is neither a loop nor a coloop -/
lemma positA1_ord_rec {e f : ι} (hf : f ∈ M.E) (hfe : f ≠ e) (he : e ∈ M.E) (h1 : M.r {f} = 1)
    (hc : M.r (M.E.erase f) = M.r M.E) :
    M.positA1 z W e =
      (W f).1 * (M.del f).positA1 z W e + (W f).2 * (M.con f hf).positA1 z W e := by
  rw [M.positA1_split z W hf hfe, hc, Nat.sub_self, pow_zero, one_mul]
  congr 1
  unfold positA1
  simp only [con_E, con_r]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  rw [Finset.mem_powerset] at hT
  rw [Finset.insert_erase hf, h1, Finset.insert_comm f e T]
  have hTE : T ⊆ M.E := hT.trans ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
  have hfT : insert f T ⊆ M.E := Finset.insert_subset hf hTE
  have a1 : 1 ≤ M.r (insert f T) :=
    h1 ▸ M.r_mono (Finset.singleton_subset_iff.2 (Finset.mem_insert_self f T)) hfT
  have a2 : M.r (insert f T) ≤ M.r M.E := M.r_le_r_E hfT
  have a3 : M.r (insert f T) ≤ T.card + 1 :=
    (M.r_le_card hfT).trans (Finset.card_insert_le _ _)
  have a4 : M.r (insert f T) ≤ M.r (insert e (insert f T)) := M.r_le_insert hfT he
  rw [show M.r M.E - 1 - (M.r (insert f T) - 1) = M.r M.E - M.r (insert f T) by omega,
    show T.card - (M.r (insert f T) - 1) = T.card + 1 - M.r (insert f T) by omega]
  by_cases h : M.r (insert e (insert f T)) = M.r (insert f T)
  · rw [if_pos h, if_pos (by omega)]
    ring
  · rw [if_neg h, if_neg (by omega)]
    ring

/-- `a₁ ≥ 0` for α-type weights (on the elements other than `e`) -/
lemma positA1_nonneg (hz : 0 ≤ z) {e : ι} (he : e ∈ M.E)
    (hW : ∀ g ∈ M.E, g ≠ e → 0 ≤ (W g).2 ∧ (W g).2 ≤ (W g).1) : 0 ≤ M.positA1 z W e := by
  suffices h : ∀ n : ℕ, ∀ N : RkMat ι, e ∈ N.E → (N.E.erase e).card = n →
      (∀ g ∈ N.E, g ≠ e → 0 ≤ (W g).2 ∧ (W g).2 ≤ (W g).1) → 0 ≤ N.positA1 z W e from
    h _ M he rfl hW
  intro n
  induction n with
  | zero =>
    intro N _ hn _
    unfold positA1
    rw [Finset.card_eq_zero.1 hn, Finset.powerset_empty, Finset.sum_singleton]
    split_ifs
    · simp only [r_empty, Finset.card_empty, Nat.sub_zero, pow_zero, mul_one,
        Finset.prod_empty, Finset.empty_sdiff]
      exact pow_nonneg hz _
    · exact le_refl 0
  | succ n ih =>
    intro N heN hn hWN
    obtain ⟨f, hf'⟩ : (N.E.erase e).Nonempty := by rw [← Finset.card_pos, hn]; omega
    obtain ⟨hfe, hf⟩ := Finset.mem_erase.1 hf'
    have hn' : ((N.E.erase f).erase e).card = n := by
      rw [Finset.erase_right_comm]
      have := Finset.card_erase_of_mem hf'
      omega
    have heD : e ∈ N.E.erase f := Finset.mem_erase.2 ⟨Ne.symm hfe, heN⟩
    have hWd : ∀ g ∈ N.E.erase f, g ≠ e → 0 ≤ (W g).2 ∧ (W g).2 ≤ (W g).1 :=
      fun g hg hge => hWN g (Finset.mem_of_mem_erase hg) hge
    have ihd := ih (N.del f) heD hn' hWd
    obtain ⟨h0f, h1f⟩ := hWN f hf hfe
    rcases N.posit_trichotomy hf with h0 | hc | ⟨h1, hc⟩
    · rw [N.positA1_loop z W hf hfe heN h0]
      exact mul_nonneg (by linarith) ihd
    · rw [N.positA1_coloop z W hf hfe heN hc]
      exact mul_nonneg (add_nonneg (mul_nonneg hz (h0f.trans h1f)) h0f) ihd
    · rw [N.positA1_ord_rec z W hf hfe heN h1 hc]
      exact add_nonneg (mul_nonneg (h0f.trans h1f) ihd)
        (mul_nonneg h0f (ih (N.con f hf) heD hn' hWd))

/-- for an element `e` that is neither a loop nor a coloop:
`Z(M ∖ e) - z Z(M / e) = (z + 1) a₁(M, e)` on the axis `y = 0` -/
lemma positA1_eq {e : ι} (he : e ∈ M.E) (h1 : M.r {e} = 1) (hc : M.r (M.E.erase e) = M.r M.E) :
    (M.del e).Z z (-1) W - z * (M.con e he).Z z (-1) W = (z + 1) * M.positA1 z W e := by
  unfold Z positA1
  simp only [del_E, del_r, con_E, con_r]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.mem_powerset] at hS
  rw [hc, h1, Finset.insert_erase he]
  have hSE : S ⊆ M.E := hS.trans (Finset.erase_subset _ _)
  have heS : insert e S ⊆ M.E := Finset.insert_subset he hSE
  have a1 : M.r S ≤ M.r (insert e S) := M.r_le_insert hSE he
  have a2 : M.r (insert e S) ≤ M.r S + 1 := M.r_insert_le hSE he
  have a3 : 1 ≤ M.r (insert e S) :=
    h1 ▸ M.r_mono (Finset.singleton_subset_iff.2 (Finset.mem_insert_self e S)) heS
  have a4 : M.r (insert e S) ≤ M.r M.E := M.r_le_r_E heS
  have a5 : M.r S ≤ S.card := M.r_le_card hSE
  by_cases h : M.r (insert e S) = M.r S
  · rw [if_pos h, h, show M.r M.E - 1 - (M.r S - 1) = M.r M.E - M.r S by omega,
      show S.card - (M.r S - 1) = (S.card - M.r S) + 1 by omega, pow_succ]
    ring
  · rw [if_neg h]
    have h' : M.r (insert e S) = M.r S + 1 := by omega
    rw [h', show M.r M.E - 1 - (M.r S + 1 - 1) = M.r M.E - 1 - M.r S by omega, Nat.add_sub_cancel,
      show M.r M.E - M.r S = (M.r M.E - 1 - M.r S) + 1 by omega, pow_succ]
    ring

/-- weighted broken-circuit inequality on the axis `y = 0`:
for an element `f` that is neither a loop nor a coloop,
`z · Z(M/f) ≤ Z(M∖f)`. -/
lemma nbc_alpha (hz : 0 ≤ z) {f : ι} (hf : f ∈ M.E) (h1 : M.r {f} = 1)
    (hc : M.r (M.E.erase f) = M.r M.E)
    (hW : ∀ g ∈ M.E, g ≠ f → 0 ≤ (W g).2 ∧ (W g).2 ≤ (W g).1) :
    z * (M.con f hf).Z z (-1) W ≤ (M.del f).Z z (-1) W := by
  have h := M.positA1_eq z W hf h1 hc
  have h' := mul_nonneg (by linarith : (0 : ℝ) ≤ z + 1) (M.positA1_nonneg z W hz hf hW)
  linarith

/-- β-type weights give a nonnegative sum on the axis `x = 0` (needs `z ≥ 0`) -/
lemma Z_nonneg_beta (hz : 0 ≤ z) (hW : ∀ f ∈ M.E, 0 ≤ (W f).1 ∧ (W f).1 ≤ (W f).2) :
    0 ≤ M.Z (-1) z W := by
  have h := M.dual.Z_nonneg_alpha z (fun f => ((W f).2, (W f).1)) hz (fun f hf => hW f hf)
  rwa [Z_dual] at h

/-- weighted broken-circuit inequality on the axis `x = 0`:
`z · Z_β(M∖f) ≤ Z_β(M/f)` -/
lemma nbc_beta (hz : 0 ≤ z) {f : ι} (hf : f ∈ M.E) (h1 : M.r {f} = 1)
    (hc : M.r (M.E.erase f) = M.r M.E)
    (hW : ∀ g ∈ M.E, g ≠ f → 0 ≤ (W g).1 ∧ (W g).1 ≤ (W g).2) :
    z * (M.del f).Z (-1) z W ≤ (M.con f hf).Z (-1) z W := by
  have hpos : 0 < M.E.card := Finset.card_pos.2 ⟨f, hf⟩
  have hd1 : M.dual.r {f} = 1 := by
    rw [dual_r, Finset.card_singleton, Finset.sdiff_singleton_eq_erase, hc]
    omega
  have hdc : M.dual.r (M.dual.E.erase f) = M.dual.r M.dual.E := by
    rw [dual_r, dual_r, dual_E, Finset.sdiff_erase_self hf, Finset.sdiff_self, r_empty, h1,
      Finset.card_erase_of_mem hf]
    omega
  have key := M.dual.nbc_alpha z (fun g => ((W g).2, (W g).1)) hz hf hd1 hdc
    (fun g hg hgf => hW g hg hgf)
  have e1 : (M.del f).Z (-1) z W = (M.dual.con f hf).Z z (-1) (fun g => ((W g).2, (W g).1)) := by
    rw [← Z_congr z (-1) (M.del_dual_same f hf) (fun _ _ => rfl), Z_dual]
  have e2 : (M.con f hf).Z (-1) z W = (M.dual.del f).Z z (-1) (fun g => ((W g).2, (W g).1)) := by
    rw [← Z_congr z (-1) (M.con_dual_same f hf) (fun _ _ => rfl), Z_dual]
  rw [e1, e2]
  exact key

end RkMat

end Results.TutteThreshold
