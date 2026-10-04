import Results.TutteThreshold.Defs
import Results.TutteThreshold.Solution.Closed

/-!
# The matroids `N_k` and `U_{1,2}`

Ranks in `uniformMatroid` and in the doubling (`Matroid.comap`), the closed form of the Tutte
polynomial of `N_k`, and its structure (connected, admissible, `6k` elements).
-/

open Matroid

namespace Results.TutteThreshold

open Finset

lemma eRk_uniformMatroid (r n : ℕ) (S : Set (Fin n)) :
    (uniformMatroid r n).eRk S = min (r : ℕ∞) S.encard := by
  have hindep : ∀ I, (uniformMatroid r n).Indep I ↔ I.ncard ≤ r := fun I => Iff.rfl
  apply le_antisymm
  · refine le_min ?_ (eRk_le_encard _ _)
    rw [eRk_le_iff]
    intro I _ hI
    rw [hindep] at hI
    rw [← (Set.toFinite I).cast_ncard_eq]
    exact_mod_cast hI
  · rw [le_eRk_iff]
    obtain ⟨I, hIS, hIcard⟩ := Set.exists_subset_encard_eq (min_le_right (r : ℕ∞) S.encard)
    refine ⟨I, hIS, ?_, hIcard⟩
    rw [hindep]
    have : (I.ncard : ℕ∞) ≤ r := by
      rw [(Set.toFinite I).cast_ncard_eq, hIcard]
      exact min_le_left _ _
    exact_mod_cast this

lemma rk_doubling (k : ℕ) (S : Finset (Fin (3 * k) × Fin 2)) :
    rk (doubling k) (S : Set (Fin (3 * k) × Fin 2)) = min (2 * k) (S.image Prod.fst).card := by
  rw [rk, doubling, eRk_comap, eRk_uniformMatroid, ← coe_image,
    Set.encard_coe_eq_coe_finsetCard, ← (Nat.mono_cast (α := ℕ∞)).map_min, ENat.toNat_coe]

private lemma doubling_sum_powerset_insert {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    {s : Finset α} {a : α} (ha : a ∉ s) (f : Finset α → β) :
    ∑ t ∈ (insert a s).powerset, f t =
      ∑ t ∈ s.powerset, f t + ∑ t ∈ s.powerset, f (insert a t) := by
  rw [powerset_insert, sum_union, sum_image]
  · intro t ht u hu htu
    rw [← erase_insert (notMem_mono (mem_powerset.1 ht) ha),
      ← erase_insert (notMem_mono (mem_powerset.1 hu) ha), htu]
  · rw [disjoint_left]
    intro t ht ht'
    obtain ⟨u, -, rfl⟩ := mem_image.1 ht'
    exact ha (mem_powerset.1 ht (mem_insert_self a u))

private lemma doubling_sum_powerset_card {β M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (x : Finset β) :
    ∑ m ∈ x.powerset, f m.card = ∑ m ∈ range (x.card + 1), x.card.choose m • f m := by
  trans ∑ m ∈ range (x.card + 1), ∑ j ∈ x.powerset with j.card = m, f j.card
  · refine (sum_fiberwise_of_maps_to (fun y hy => ?_) _).symm
    rw [mem_range, Nat.lt_succ_iff]
    exact card_le_card (mem_powerset.1 hy)
  · refine sum_congr rfl fun y _ => ?_
    rw [← card_powersetCard, ← sum_const]
    refine sum_congr powersetCard_eq_filter.symm fun z hz => ?_
    rw [(mem_powersetCard.1 hz).2]

/-- Subsets `S` of `s × Fin 2` grouped by their projection `U ⊆ s`: the fibre over `U` contributes
`(2 + w)^|U|`, since each element of `U` is covered by one of its two copies or by both
(`1 + 1 + w`). -/
lemma doubling_sum_powerset {α R : Type*} [DecidableEq α] [CommSemiring R] (w : R)
    (s : Finset α) (g : ℕ → R) :
    ∑ S ∈ (s ×ˢ (univ : Finset (Fin 2))).powerset,
        g (S.image Prod.fst).card * w ^ (S.card - (S.image Prod.fst).card) =
      ∑ U ∈ s.powerset, g U.card * (2 + w) ^ U.card := by
  induction s using Finset.induction_on generalizing g with
  | empty => simp
  | insert a s ha ih =>
    have hprod : (insert a s) ×ˢ (univ : Finset (Fin 2)) =
        insert (a, 0) (insert (a, 1) (s ×ˢ univ)) := by
      ext ⟨i, j⟩
      obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
      all_goals simp
    have h1 : (a, (1 : Fin 2)) ∉ s ×ˢ (univ : Finset (Fin 2)) := by simp [ha]
    have h0 : (a, (0 : Fin 2)) ∉ insert (a, 1) (s ×ˢ (univ : Finset (Fin 2))) := by simp [ha]
    have hG : ∑ U ∈ s.powerset, g (insert a U).card * (2 + w) ^ (insert a U).card =
        ∑ U ∈ s.powerset, (fun u => (2 + w) * g (u + 1)) U.card * (2 + w) ^ U.card := by
      refine sum_congr rfl fun U hU => ?_
      rw [card_insert_of_notMem (notMem_mono (mem_powerset.1 hU) ha), pow_succ]
      ring
    rw [hprod, doubling_sum_powerset_insert h0, doubling_sum_powerset_insert h1,
      doubling_sum_powerset_insert h1, doubling_sum_powerset_insert ha, hG, ← ih g,
      ← ih (fun u => (2 + w) * g (u + 1)), add_assoc, ← sum_add_distrib, ← sum_add_distrib]
    congr 1
    refine sum_congr rfl fun t ht => ?_
    have hts : t ⊆ s ×ˢ univ := mem_powerset.1 ht
    have hat : ∀ j : Fin 2, (a, j) ∉ t := fun j h => ha (mem_product.1 (hts h)).1
    have haπ : a ∉ t.image Prod.fst := by
      rw [mem_image]
      rintro ⟨⟨i, j⟩, h, rfl⟩
      exact hat j h
    have h01 : (a, (0 : Fin 2)) ∉ insert (a, 1) t := by
      rw [mem_insert, not_or]
      exact ⟨by simp, hat 0⟩
    have hle : (t.image Prod.fst).card ≤ t.card := card_image_le
    simp only [image_insert, insert_idem, card_insert_of_notMem haπ, card_insert_of_notMem (hat 0),
      card_insert_of_notMem (hat 1), card_insert_of_notMem h01]
    rw [show t.card + 1 - ((t.image Prod.fst).card + 1) = t.card - (t.image Prod.fst).card by omega,
      show t.card + 1 + 1 - ((t.image Prod.fst).card + 1) =
        t.card - (t.image Prod.fst).card + 1 by omega, pow_succ]
    ring

/-- `doubling_sum_powerset` over all subsets of `α × Fin 2`, grouped by the size of the
projection -/
lemma doubling_sum_univ {α R : Type*} [Fintype α] [DecidableEq α] [CommSemiring R] (w : R)
    (g : ℕ → R) :
    ∑ S ∈ (univ : Finset (α × Fin 2)).powerset,
        g (S.image Prod.fst).card * w ^ (S.card - (S.image Prod.fst).card) =
      ∑ u ∈ range (Fintype.card α + 1), ((Fintype.card α).choose u : R) * (g u * (2 + w) ^ u) := by
  rw [← univ_product_univ, doubling_sum_powerset, doubling_sum_powerset_card
    (fun u => g u * (2 + w) ^ u), card_univ]
  simp only [nsmul_eq_mul]

/-- closed form of the Tutte polynomial of `N_k` -/
lemma tutte_doubling (k : ℕ) (x y : ℝ) :
    tutte (doubling k) x y =
      ∑ u ∈ range (3 * k + 1), (Nat.choose (3 * k) u : ℝ) * (x - 1) ^ (2 * k - min (2 * k) u) *
        (y - 1) ^ (u - min (2 * k) u) * (1 + y) ^ u := by
  have hE : (doubling k).E = Set.univ := rfl
  have hfin : (doubling k).ground_finite.toFinset = univ := Set.Finite.toFinset_eq_univ.2 hE
  have himage : (univ : Finset (Fin (3 * k) × Fin 2)).image Prod.fst = univ :=
    eq_univ_of_forall fun i => mem_image.2 ⟨(i, 0), mem_univ _, rfl⟩
  have hrank : (doubling k).eRank.toNat = 2 * k := by
    have h := rk_doubling k univ
    rw [coe_univ, himage, card_univ, Fintype.card_fin] at h
    rw [eRank_def, hE, ← rk, h]
    omega
  have key : ∀ S : Finset (Fin (3 * k) × Fin 2),
      (x - 1) ^ (2 * k - min (2 * k) (S.image Prod.fst).card) *
          (y - 1) ^ (S.card - min (2 * k) (S.image Prod.fst).card) =
        (fun u => (x - 1) ^ (2 * k - min (2 * k) u) * (y - 1) ^ (u - min (2 * k) u))
            (S.image Prod.fst).card * (y - 1) ^ (S.card - (S.image Prod.fst).card) := by
    intro S
    have hle : (S.image Prod.fst).card ≤ S.card := card_image_le
    rw [show S.card - min (2 * k) (S.image Prod.fst).card = (S.card - (S.image Prod.fst).card) +
      ((S.image Prod.fst).card - min (2 * k) (S.image Prod.fst).card) by omega, pow_add]
    ring
  rw [tutte, hfin, hrank]
  simp only [rk_doubling]
  rw [sum_congr rfl fun S _ => key S, doubling_sum_univ (y - 1)
    (fun u => (x - 1) ^ (2 * k - min (2 * k) u) * (y - 1) ^ (u - min (2 * k) u)), Fintype.card_fin]
  refine sum_congr rfl fun u _ => ?_
  rw [show (2 : ℝ) + (y - 1) = 1 + y by ring]
  ring

lemma tutte_doubling_x0 (k : ℕ) (x : ℝ) : tutte (doubling k) x 0 = Ak k x := by
  rw [tutte_doubling, Ak]
  refine sum_congr rfl fun u _ => ?_
  rw [zero_sub, add_zero, one_pow, mul_one]

lemma tutte_doubling_0x (k : ℕ) (x : ℝ) : tutte (doubling k) 0 x = Bk k x := by
  rw [tutte_doubling, Bk]
  simp only [zero_sub]

lemma tutte_doubling_11 (k : ℕ) : tutte (doubling k) 1 1 = bk k := by
  rw [tutte_doubling, sum_eq_single (2 * k)]
  · rw [min_self, Nat.sub_self, pow_zero, bk,
      Nat.choose_symm_of_eq_add (show 3 * k = 2 * k + k by ring), pow_mul]
    norm_num
    ring
  · intro u _ hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · rw [sub_self, zero_pow (by omega : 2 * k - min (2 * k) u ≠ 0)]
      ring
    · rw [sub_self, zero_pow (by omega : u - min (2 * k) u ≠ 0)]
      ring
  · intro h
    exact absurd (mem_range.2 (by omega)) h

lemma rho_doubling (k : ℕ) (x : ℝ) : rho (doubling k) x = rhoK k x := by
  rw [rho, rhoK, tutte_doubling_x0, tutte_doubling_0x, tutte_doubling_11]

end Results.TutteThreshold
