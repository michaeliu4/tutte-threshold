import Results.TutteThreshold.Solution.Bridge
import Results.TutteThreshold.Solution.Induction

/-!
# Connected components and Theorem 1.2

The classes of the circuit relation partition the ground set, the rank is additive over them, and
`Z` (hence `ρ`) is multiplicative; each class carries an admissible restriction with `|K| ≥ 2`.

Additivity: the union of bases of the pieces `S ∩ K` is independent, since a circuit inside it
lies in one class `K` and hence inside the basis of `S ∩ K`; the other inequality is
subadditivity.  Theorem 1.2: `main_P` on every class (all labels `p 1`), multiplied over the
classes with `Z_partition`.
-/

open Matroid

namespace Results.TutteThreshold

variable {α : Type*}

/-! ### Rank additivity over a family of blocks containing every circuit -/

/-- subadditivity of the rank over a finite family of pieces of `S` -/
lemma Components.eRk_biUnion_le [DecidableEq α] (M : Matroid α) (P : Finset (Finset α))
    (S : Finset α) :
    M.eRk ↑(P.biUnion (fun K => S ∩ K)) ≤ ∑ K ∈ P, M.eRk ↑(S ∩ K) := by
  induction P using Finset.induction_on with
  | empty => simp
  | insert K P hK ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hK, Finset.coe_union]
    exact (M.eRk_union_le_eRk_add_eRk _ _).trans (by gcongr)

/-- the rank is additive over a disjoint family of blocks covering `S` such that a circuit
meeting a block lies inside it -/
lemma Components.rk_eq_sum [DecidableEq α] (M : Matroid α) [M.Finite] (P : Finset (Finset α))
    (hdisj : (P : Set (Finset α)).PairwiseDisjoint id)
    (hcirc : ∀ C, M.IsCircuit C → ∀ K ∈ P, ∀ e ∈ C, e ∈ K → C ⊆ ↑K)
    (S : Finset α) (hSE : ↑S ⊆ M.E) (hSP : S ⊆ P.biUnion id) :
    rk M ↑S = ∑ K ∈ P, rk M ↑(S ∩ K) := by
  have hJ : ∀ K : Finset α, ∃ J : Finset α, M.IsBasis' ↑J ↑(S ∩ K) := fun K =>
    (M.isRkFinite_of_finite (S ∩ K).finite_toSet).exists_finset_isBasis'
  choose J hJ using hJ
  have hJsub : ∀ K, J K ⊆ S ∩ K := fun K => Finset.coe_subset.mp (hJ K).subset
  have hJrk : ∀ K, M.eRk ↑(S ∩ K) = (J K).card := fun K => by
    rw [← (hJ K).encard_eq_eRk, Set.encard_coe_eq_coe_finsetCard]
  have hrkJ : ∑ K ∈ P, rk M ↑(S ∩ K) = ∑ K ∈ P, (J K).card :=
    Finset.sum_congr rfl fun K _ => by rw [rk, hJrk, ENat.toNat_coe]
  -- the union of the bases of the blocks is independent
  have hIdisj : (P : Set (Finset α)).PairwiseDisjoint J := fun K hK K' hK' hne =>
    (hdisj hK hK' hne).mono ((hJsub K).trans Finset.inter_subset_right)
      ((hJsub K').trans Finset.inter_subset_right)
  have hIS : P.biUnion J ⊆ S :=
    Finset.biUnion_subset.mpr fun K _ => (hJsub K).trans Finset.inter_subset_left
  have hIind : M.Indep ↑(P.biUnion J) := by
    by_contra hdep
    obtain ⟨C, hCI, hC⟩ :=
      ((not_indep_iff ((Finset.coe_subset.mpr hIS).trans hSE)).mp hdep).exists_isCircuit_subset
    obtain ⟨e, heC⟩ := hC.nonempty
    obtain ⟨K₀, hK₀, heK₀⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp (hCI heC))
    have hCK : C ⊆ ↑K₀ :=
      hcirc C hC K₀ hK₀ e heC (Finset.mem_inter.mp (hJsub K₀ heK₀)).2
    refine hC.not_indep ((hJ K₀).indep.subset fun d hd => ?_)
    obtain ⟨K₁, hK₁, hdK₁⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp (hCI hd))
    by_cases h : K₁ = K₀
    · exact h ▸ hdK₁
    · exact absurd (hCK hd) (Finset.disjoint_left.mp (hdisj hK₁ hK₀ h)
        (Finset.mem_inter.mp (hJsub K₁ hdK₁)).2)
  have hIrk : M.eRk ↑(P.biUnion J) = (P.biUnion J).card := by
    rw [hIind.eRk_eq_encard, Set.encard_coe_eq_coe_finsetCard]
  rw [hrkJ]
  apply le_antisymm
  · have hS : P.biUnion (fun K => S ∩ K) = S := by
      rw [← Finset.inter_biUnion]
      exact Finset.inter_eq_left.mpr hSP
    have h := Components.eRk_biUnion_le M P S
    rw [hS] at h
    simp_rw [hJrk] at h
    rw [← Nat.cast_sum] at h
    simpa only [rk, ENat.toNat_coe] using ENat.toNat_le_toNat h (ENat.coe_ne_top _)
  · rw [← Finset.card_biUnion hIdisj]
    have h := ENat.toNat_le_toNat (M.eRk_mono (Finset.coe_subset.mpr hIS))
      (eRk_ne_top_iff.mpr (M.isRkFinite_set _))
    rwa [hIrk, ENat.toNat_coe] at h

/-! ### The component classes -/

/-- the elements of the ground set in a given class of the circuit relation -/
def Components.blockSet (M : Matroid α) (k : Quot (componentRel M)) : Set α :=
  {f | ∃ hf : f ∈ M.E, Quot.mk (componentRel M) ⟨f, hf⟩ = k}

lemma Components.blockSet_subset (M : Matroid α) (k : Quot (componentRel M)) :
    Components.blockSet M k ⊆ M.E :=
  fun _ ⟨hf, _⟩ => hf

/-- the elements of the ground set in a given class of the circuit relation, as a finset -/
noncomputable def Components.block (M : Matroid α) [M.Finite] (k : Quot (componentRel M)) :
    Finset α :=
  (M.ground_finite.subset (Components.blockSet_subset M k)).toFinset

lemma Components.mem_block {M : Matroid α} [M.Finite] {k : Quot (componentRel M)} {f : α} :
    f ∈ Components.block M k ↔ ∃ hf : f ∈ M.E, Quot.mk (componentRel M) ⟨f, hf⟩ = k :=
  Set.Finite.mem_toFinset _

lemma Components.block_subset (M : Matroid α) [M.Finite] (k : Quot (componentRel M)) :
    Components.block M k ⊆ M.ground_finite.toFinset :=
  fun _ hf => (Set.Finite.mem_toFinset _).mpr (Components.mem_block.mp hf).1

lemma Components.block_nonempty (M : Matroid α) [M.Finite] (k : Quot (componentRel M)) :
    (Components.block M k).Nonempty := by
  obtain ⟨⟨e, he⟩, rfl⟩ := Quot.exists_rep k
  exact ⟨e, Components.mem_block.mpr ⟨he, rfl⟩⟩

lemma Components.block_eq_of_mem {M : Matroid α} [M.Finite] {k : Quot (componentRel M)} {e : α}
    (he : e ∈ Components.block M k) :
    ∃ he' : e ∈ M.E, k = Quot.mk (componentRel M) ⟨e, he'⟩ := by
  obtain ⟨he', h⟩ := Components.mem_block.mp he
  exact ⟨he', h.symm⟩

lemma Components.block_injective (M : Matroid α) [M.Finite] :
    Function.Injective (Components.block M) := by
  intro k k' h
  obtain ⟨e, he⟩ := Components.block_nonempty M k
  obtain ⟨he₁, h₁⟩ := Components.block_eq_of_mem he
  obtain ⟨he₂, h₂⟩ := Components.block_eq_of_mem (h ▸ he)
  exact h₁.trans h₂.symm

lemma Components.block_disjoint (M : Matroid α) [M.Finite] {k k' : Quot (componentRel M)}
    (hne : k ≠ k') : Disjoint (Components.block M k) (Components.block M k') := by
  refine Finset.disjoint_left.mpr fun e he he' => hne ?_
  obtain ⟨he₁, h₁⟩ := Components.block_eq_of_mem he
  obtain ⟨he₂, h₂⟩ := Components.block_eq_of_mem he'
  exact h₁.trans h₂.symm

/-- a circuit meeting a class lies inside it -/
lemma Components.circuit_subset_block {M : Matroid α} [M.Finite] {C : Set α}
    (hC : M.IsCircuit C) {k : Quot (componentRel M)} {e : α} (heC : e ∈ C)
    (hek : e ∈ Components.block M k) : C ⊆ ↑(Components.block M k) := by
  intro d hd
  obtain ⟨he, rfl⟩ := Components.block_eq_of_mem hek
  refine Finset.mem_coe.mpr (Components.mem_block.mpr ⟨hC.subset_ground hd, ?_⟩)
  exact (Quot.sound ⟨C, hC, heC, hd⟩).symm

/-- the component classes: a partition of the ground set on which the rank is additive -/
theorem exists_partition (M : Matroid α) [M.Finite] [DecidableEq α] :
    ∃ P : Finset (Finset α), (∀ K ∈ P, K ⊆ (toRk M).E) ∧
      ((P : Set (Finset α)).PairwiseDisjoint id) ∧ P.biUnion id = (toRk M).E ∧
      (∀ K ∈ P, K.Nonempty) ∧
      (∀ S ⊆ (toRk M).E, (toRk M).r S = ∑ K ∈ P, (toRk M).r (S ∩ K)) ∧
      P.card = numComponents M := by
  have := M.ground_finite.to_subtype
  let _ : Fintype (Quot (componentRel M)) := Fintype.ofFinite _
  have hsub : ∀ K ∈ Finset.univ.image (Components.block M), K ⊆ (toRk M).E := by
    intro K hK
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hK
    exact Components.block_subset M k
  have hdisj : ((Finset.univ.image (Components.block M) : Finset (Finset α)) :
      Set (Finset α)).PairwiseDisjoint id := by
    intro K hK K' hK' hne
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hK)
    obtain ⟨k', -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hK')
    exact Components.block_disjoint M fun h => hne (congrArg _ h)
  have hcov : (Finset.univ.image (Components.block M)).biUnion id = (toRk M).E := by
    refine Finset.Subset.antisymm (Finset.biUnion_subset.mpr hsub) fun e he => ?_
    have he' : e ∈ M.E := (Set.Finite.mem_toFinset _).mp he
    exact Finset.mem_biUnion.mpr ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ
      (Quot.mk (componentRel M) ⟨e, he'⟩)), Components.mem_block.mpr ⟨he', rfl⟩⟩
  refine ⟨_, hsub, hdisj, hcov, ?_, ?_, ?_⟩
  · intro K hK
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hK
    exact Components.block_nonempty M k
  · intro S hS
    refine Components.rk_eq_sum M _ hdisj ?_ S
      (fun e he => (Set.Finite.mem_toFinset _).mp (hS (Finset.mem_coe.mp he))) (hcov ▸ hS)
    intro C hC K hK e heC heK
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hK
    exact Components.circuit_subset_block hC heC heK
  · rw [Finset.card_image_of_injective _ (Components.block_injective M), Finset.card_univ,
      numComponents, Nat.card_eq_fintype_card]

/-! ### Theorem 1.2 -/

/-- a block of a partition on which the rank is additive is a separator -/
lemma Components.isSep_of_mem {ι : Type*} [DecidableEq ι] (N : RkMat ι) (P : Finset (Finset ι))
    (hsub : ∀ K ∈ P, K ⊆ N.E) (hdisj : (P : Set (Finset ι)).PairwiseDisjoint id)
    (hadd : ∀ S ⊆ N.E, N.r S = ∑ K ∈ P, N.r (S ∩ K)) {K : Finset ι} (hK : K ∈ P) :
    N.IsSep K := by
  refine ⟨hsub K hK, ?_⟩
  rw [hadd K (hsub K hK), hadd (N.E \ K) Finset.sdiff_subset, hadd N.E subset_rfl,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun K' hK' => ?_
  by_cases h : K' = K
  · subst h
    rw [Finset.inter_self, Finset.sdiff_inter_self, Finset.inter_eq_right.mpr (hsub K' hK'),
      N.r_empty, add_zero]
  · have hd : Disjoint K K' := hdisj hK hK' (Ne.symm h)
    rw [Finset.disjoint_iff_inter_eq_empty.mp hd, N.r_empty, zero_add,
      Finset.inter_eq_right.mpr (hsub K' hK'),
      Finset.inter_eq_right.mpr (Finset.subset_sdiff.mpr ⟨hsub K' hK', hd.symm⟩)]

/-- Theorem 1.2 for `2 ≤ x` with `x³ ≤ 9 (x-1)` -/
theorem thm_1_2_core {x : ℝ} (hx2 : 2 ≤ x) (hxs : x ^ 3 ≤ 9 * (x - 1)) (M : Matroid α)
    [M.Finite] (hM : IsAdmissible M) :
    cFun x ^ ((M.E.ncard : ℤ) - 2 * (numComponents M : ℤ)) ≤ rho M x := by
  classical
  obtain ⟨P, hsub, hdisj, hcov, hne, hadd, hcard⟩ := exists_partition M
  set N := toRk M
  set ℓ : α → Lab := fun _ => Lab.p 1
  -- the claim on every class
  have hclaim : ∀ K (hK : K ∈ P),
      cc x ^ K.card ≤ cc x ^ 2 * (lskel x (N.restrict K (hsub K hK)) ℓ).rho x := by
    intro K hK
    have h := main_P hx2 hxs (N.restrict K (hsub K hK)) ℓ (fun _ _ => Or.inl (by decide))
      ((admissible_toRk M hM).restrict_sep (Components.isSep_of_mem N P hsub hdisj hadd hK))
      (hne K hK)
    have hh : hsum (N.restrict K (hsub K hK)) ℓ = K.card := by
      simp only [hsum, RkMat.restrict_E, ℓ, Lab.size, Finset.sum_const, smul_eq_mul, mul_one]
    rwa [Claim, hh] at h
  -- `ρ` is the product of the ratios of the classes
  have hrho :
      rho M x = ∏ K ∈ P.attach, (lskel x (N.restrict K.1 (hsub K.1 K.2)) ℓ).rho x := by
    rw [rho_eq_lskel M hx2]
    simp only [Skel.rho, Skel.Za, Skel.Zc, Skel.Zb]
    rw [RkMat.Z_partition N _ _ _ P hsub hdisj hcov hadd,
      RkMat.Z_partition N _ _ _ P hsub hdisj hcov hadd,
      RkMat.Z_partition N _ _ _ P hsub hdisj hcov hadd,
      ← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
    rfl
  have hcc : 0 < cc x := Real.sqrt_pos.mpr (div_pos (by positivity) (by linarith))
  have hprod : cc x ^ M.E.ncard ≤ cc x ^ (2 * numComponents M) * rho M x := by
    have h1 : ∏ K ∈ P.attach, cc x ^ K.1.card ≤
        ∏ K ∈ P.attach, (cc x ^ 2 * (lskel x (N.restrict K.1 (hsub K.1 K.2)) ℓ).rho x) :=
      Finset.prod_le_prod (fun K _ => pow_nonneg hcc.le _) (fun K _ => hclaim K.1 K.2)
    have h2 : ∑ K ∈ P, K.card = M.E.ncard := by
      rw [← card_toRk M, ← hcov, Finset.card_biUnion hdisj]
      rfl
    rw [Finset.prod_mul_distrib, ← hrho, Finset.prod_const, Finset.card_attach,
      Finset.prod_pow_eq_pow_sum, Finset.sum_attach P Finset.card, h2, ← pow_mul, hcard] at h1
    exact h1
  show cc x ^ _ ≤ _
  rw [show (M.E.ncard : ℤ) - 2 * (numComponents M : ℤ) =
      ((M.E.ncard : ℕ) : ℤ) - ((2 * numComponents M : ℕ) : ℤ) by push_cast; ring,
    zpow_sub₀ hcc.ne', zpow_natCast, zpow_natCast, div_le_iff₀ (pow_pos hcc _), mul_comm]
  exact hprod

end Results.TutteThreshold
