import Results.TutteThreshold.Solution.Doubling

/-!
# Structure of `N_k` and the matroid `U_{1,2}`
-/

open Matroid

namespace Results.TutteThreshold

open Finset

namespace DoublingStruct

private lemma uniform_indep_iff (r n : ℕ) (I : Set (Fin n)) :
    (uniformMatroid r n).Indep I ↔ I.ncard ≤ r := Iff.rfl

private lemma uniform_ground (r n : ℕ) : (uniformMatroid r n).E = Set.univ := rfl

private lemma ground_eq (k : ℕ) : (doubling k).E = Set.univ := rfl

private lemma indep_iff (k : ℕ) (I : Set (Fin (3 * k) × Fin 2)) :
    (doubling k).Indep I ↔ (Prod.fst '' I).ncard ≤ 2 * k ∧ Set.InjOn Prod.fst I := Iff.rfl

/-- a parallel class `{(i,0),(i,1)}` is a circuit of `N_k` -/
private lemma pair_isCircuit (k : ℕ) (hk : 1 ≤ k) (i : Fin (3 * k)) :
    (doubling k).IsCircuit {(i, 0), (i, 1)} := by
  rw [isCircuit_iff_forall_ssubset]
  refine ⟨⟨?_, Set.subset_univ _⟩, fun I hI => ?_⟩
  · rw [indep_iff]
    rintro ⟨-, hinj⟩
    have h01 : ((i, 0) : Fin (3 * k) × Fin 2) = (i, 1) := hinj (by simp) (by simp) rfl
    simp at h01
  · have hcard : I.ncard ≤ 1 := by
      have := Set.ncard_lt_ncard hI
      rw [Set.ncard_pair (by simp)] at this
      omega
    rw [indep_iff]
    exact ⟨(Set.ncard_image_le (Set.toFinite I)).trans (hcard.trans (by omega)),
      (Set.ncard_le_one_iff_subsingleton.1 hcard).injOn _⟩

/-- a set on which `Prod.fst` is injective with `2k+1` image points is a circuit of `N_k` -/
private lemma isCircuit_of_injOn (k : ℕ) (C : Set (Fin (3 * k) × Fin 2))
    (hinj : Set.InjOn Prod.fst C) (hC : (Prod.fst '' C).ncard = 2 * k + 1) :
    (doubling k).IsCircuit C := by
  rw [isCircuit_iff_forall_ssubset]
  refine ⟨⟨?_, Set.subset_univ _⟩, fun I hI => ?_⟩
  · rw [indep_iff]
    rintro ⟨h, -⟩
    omega
  · rw [indep_iff]
    have hIinj : Set.InjOn Prod.fst I := hinj.mono hI.subset
    refine ⟨?_, hIinj⟩
    rw [hIinj.ncard_image]
    have := Set.ncard_lt_ncard hI
    rw [← hinj.ncard_image, hC] at this
    omega

private lemma fin_two_cases : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide

private lemma mem_pair {k : ℕ} (i : Fin (3 * k)) (a : Fin 2) :
    (i, a) ∈ ({(i, 0), (i, 1)} : Set (Fin (3 * k) × Fin 2)) := by
  rcases fin_two_cases a with rfl | rfl <;> simp

/-- the two elements of a parallel class lie in a common circuit -/
private lemma rel_pair (k : ℕ) (hk : 1 ≤ k) (i : Fin (3 * k)) (a b : Fin 2) :
    ∃ C, (doubling k).IsCircuit C ∧ (i, a) ∈ C ∧ (i, b) ∈ C :=
  ⟨_, pair_isCircuit k hk i, mem_pair i a, mem_pair i b⟩

/-- `(i,0)` and `(j,0)` lie in a common circuit: lift a `(2k+1)`-set `D ∋ i, j` by `(·, 0)` -/
private lemma rel_fst (k : ℕ) (hk : 1 ≤ k) (i j : Fin (3 * k)) :
    ∃ C, (doubling k).IsCircuit C ∧ (i, 0) ∈ C ∧ (j, 0) ∈ C := by
  obtain ⟨D, hsub, -, hcard⟩ := Finset.exists_subsuperset_card_eq (s := {i, j})
    (t := Finset.univ) (n := 2 * k + 1) (Finset.subset_univ _)
    ((Finset.card_le_two).trans (by omega)) (by rw [Finset.card_univ, Fintype.card_fin]; omega)
  refine ⟨(fun d => (d, (0 : Fin 2))) '' (D : Set (Fin (3 * k))),
    isCircuit_of_injOn k _ ?_ ?_, ⟨i, ?_, rfl⟩, ⟨j, ?_, rfl⟩⟩
  · rintro _ ⟨d, -, rfl⟩ _ ⟨d', -, rfl⟩ h
    simp only at h
    rw [h]
  · rw [Set.image_image]
    simpa using hcard
  · exact hsub (by simp)
  · exact hsub (by simp)

private lemma numComponents_eq (k : ℕ) (hk : 1 ≤ k) : numComponents (doubling k) = 1 := by
  have h3 : 0 < 3 * k := by omega
  let p : (doubling k).E := ⟨(⟨0, h3⟩, 0), Set.mem_univ _⟩
  have key : ∀ x : (doubling k).E, Quot.mk (componentRel (doubling k)) x = Quot.mk _ p := by
    rintro ⟨⟨i, a⟩, hx⟩
    have hi0 : ((i, 0) : Fin (3 * k) × Fin 2) ∈ (doubling k).E := Set.mem_univ _
    calc Quot.mk _ ⟨(i, a), hx⟩ = Quot.mk (componentRel (doubling k)) ⟨(i, 0), hi0⟩ :=
          Quot.sound (rel_pair k hk i a 0)
      _ = Quot.mk _ p := Quot.sound (rel_fst k hk i ⟨0, h3⟩)
  unfold numComponents
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun q₁ q₂ => ?_⟩, ⟨Quot.mk _ p⟩⟩
  induction q₁ using Quot.ind
  induction q₂ using Quot.ind
  exact (key _).trans (key _).symm

private lemma admissible (k : ℕ) (hk : 1 ≤ k) : IsAdmissible (doubling k) := by
  refine ⟨fun e he => he.dep.not_indep ?_, fun e he => ?_⟩
  · rw [indep_iff, Set.image_singleton, Set.ncard_singleton]
    exact ⟨by omega, Set.injOn_singleton _ _⟩
  · obtain ⟨i, a⟩ := e
    exact (pair_isCircuit k hk i).not_isColoop_of_mem (mem_pair i a) he

end DoublingStruct

/-- `N_k` is connected, admissible and has `6k` elements -/
lemma doubling_structure (k : ℕ) (hk : 1 ≤ k) :
    numComponents (doubling k) = 1 ∧ IsAdmissible (doubling k) ∧
      (doubling k).E.ncard = 6 * k := by
  refine ⟨DoublingStruct.numComponents_eq k hk, DoublingStruct.admissible k hk, ?_⟩
  rw [DoublingStruct.ground_eq, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin]
  ring

/-- `T_{U_{1,2}}(x,y) = x + y` -/
lemma tutte_uniform_one_two (x y : ℝ) : tutte (uniformMatroid 1 2) x y = x + y := by
  have hE : (uniformMatroid 1 2).ground_finite.toFinset = Finset.univ := by
    ext e
    simp [DoublingStruct.uniform_ground]
  have hr : (uniformMatroid 1 2).eRank.toNat = 1 := by
    rw [← eRk_ground, DoublingStruct.uniform_ground, eRk_uniformMatroid]
    simp
  unfold tutte
  rw [hE, hr, Finset.powerset_univ,
    show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [rk, eRk_uniformMatroid]
  ring

/-- `U_{1,2}` has no loops and no coloops -/
lemma admissible_uniform_one_two : IsAdmissible (uniformMatroid 1 2) := by
  have hC : (uniformMatroid 1 2).IsCircuit Set.univ := by
    rw [isCircuit_iff_forall_ssubset]
    refine ⟨⟨?_, subset_refl _⟩, fun I hI => ?_⟩
    · rw [DoublingStruct.uniform_indep_iff]
      simp [Set.ncard_univ]
    · rw [DoublingStruct.uniform_indep_iff]
      have := Set.ncard_lt_ncard hI
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at this
      omega
  refine ⟨fun e he => he.dep.not_indep ?_,
    fun e he => hC.not_isColoop_of_mem (Set.mem_univ e) he⟩
  rw [DoublingStruct.uniform_indep_iff, Set.ncard_singleton]

/-- `ρ_x(U_{1,2}) = x² / 4` -/
lemma rho_uniform_one_two (x : ℝ) : rho (uniformMatroid 1 2) x = x ^ 2 / 4 := by
  rw [rho, tutte_uniform_one_two, tutte_uniform_one_two, tutte_uniform_one_two]
  ring

end Results.TutteThreshold
