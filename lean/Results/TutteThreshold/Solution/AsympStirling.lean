import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Stirling's formula for `C(3k,k)`

With `s n = Stirling.stirlingSeq n = n! / (√(2n) (n/e)^n)`, the ratio of `C(3k,k)` to
`(√3 / (2 √(π k))) (27/4)^k` is `√π s(3k) / (s k · s(2k))` (`AsympStirling.choose_ratio`).
Mathlib gives `√π ≤ s n`; telescoping Robbins' bound `log s m - log s (m+1) ≤ 1/(12 m (m+1))`
to the limit gives `log s n ≤ log √π + 1/(12 n)` (`AsympStirling.log_stirlingSeq_le`).  So the
logarithm `u` of the ratio lies in `[-1/(8k), 1/(36k)]`, and `|e^u - 1| ≤ 2|u|` gives `1/(4k)`.
-/

namespace Results.TutteThreshold

open Finset Filter Topology

section

open Real

/-- Robbins' stepwise bound `log s_m - log s_{m+1} ≤ 1/(12 m (m+1))`, telescoped to the limit
`log √π`: `log s_n ≤ log √π + 1/(12 n)`. -/
lemma AsympStirling.log_stirlingSeq_le {n : ℕ} (hn : n ≠ 0) :
    log (Stirling.stirlingSeq n) ≤ log √π + 1 / (12 * n) := by
  set v : ℕ → ℝ := fun m => log (Stirling.stirlingSeq (m + 1)) - 1 / 12 * (1 / ((m : ℝ) + 1))
    with hv
  have hmono : Monotone v := by
    refine monotone_nat_of_le_succ fun m => ?_
    have h := Stirling.log_stirlingSeq_sdiff_le (m + 1)
    have e : (1 : ℝ) / (12 * ((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) + 1)) =
        1 / 12 * (1 / ((m : ℝ) + 1)) - 1 / 12 * (1 / (((m + 1 : ℕ) : ℝ) + 1)) := by
      push_cast
      field_simp
      ring
    simp only [hv]
    linarith
  have hlim : Tendsto v atTop (𝓝 (log √π)) := by
    have h1 : Tendsto (fun m : ℕ => log (Stirling.stirlingSeq (m + 1))) atTop (𝓝 (log √π)) :=
      (Stirling.tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat 1)).log
        (by positivity)
    have h2 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 12 : ℝ)
    have h3 := h1.sub h2
    rw [mul_zero, sub_zero] at h3
    exact h3
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
  have hle := hmono.ge_of_tendsto hlim m
  simp only [hv] at hle
  have e : (1 : ℝ) / (12 * ((m + 1 : ℕ) : ℝ)) = 1 / 12 * (1 / ((m : ℝ) + 1)) := by
    push_cast
    field_simp
  rw [e]
  linarith

/-- `n! = s_n √(2n) (n/e)^n` for `n ≠ 0` (definition of `Stirling.stirlingSeq`). -/
lemma AsympStirling.factorial_eq {n : ℕ} (hn : n ≠ 0) :
    (Nat.factorial n : ℝ) = Stirling.stirlingSeq n * (√(2 * n) * (n / exp 1) ^ n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have h : 0 < √(2 * (n : ℝ)) * (n / exp 1) ^ n := by positivity
  rw [Stirling.stirlingSeq, div_mul_cancel₀ _ h.ne']

/-- The Stirling ratio of `C(3k,k)`:
`C(3k,k) / ((√3/(2√(πk))) (27/4)^k) = √π s_{3k} / (s_k s_{2k})`. -/
lemma AsympStirling.choose_ratio {k : ℕ} (hk : k ≠ 0) :
    (Nat.choose (3 * k) k : ℝ) / (√3 / (2 * √(π * k)) * (27 / 4 : ℝ) ^ k) =
      √π * Stirling.stirlingSeq (3 * k) /
        (Stirling.stirlingSeq k * Stirling.stirlingSeq (2 * k)) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  rw [Nat.cast_choose ℝ (by omega : k ≤ 3 * k), show 3 * k - k = 2 * k by omega,
    AsympStirling.factorial_eq (by omega : 3 * k ≠ 0), AsympStirling.factorial_eq hk,
    AsympStirling.factorial_eq (by omega : 2 * k ≠ 0)]
  push_cast
  have e1 : √(2 * (3 * (k : ℝ))) = √2 * √3 * √k := by
    rw [show 2 * (3 * (k : ℝ)) = 2 * 3 * k by ring, sqrt_mul (by positivity),
      sqrt_mul (by positivity)]
  have e2 : √(2 * (k : ℝ)) = √2 * √k := sqrt_mul (by positivity) _
  have e3 : √(2 * (2 * (k : ℝ))) = 2 * √k := by
    rw [show 2 * (2 * (k : ℝ)) = 2 ^ 2 * k by ring, sqrt_mul (by positivity),
      sqrt_sq (by positivity)]
  have e4 : √(π * k) = √π * √k := sqrt_mul (by positivity) _
  have p1 : ((3 * (k : ℝ)) / exp 1) ^ (3 * k) = 27 ^ k * ((k / exp 1) ^ k) ^ 3 := by
    rw [pow_mul, show (3 * (k : ℝ) / exp 1) ^ 3 = 27 * (k / exp 1) ^ 3 by ring, mul_pow,
      ← pow_mul, ← pow_mul, mul_comm 3 k]
  have p3 : ((2 * (k : ℝ)) / exp 1) ^ (2 * k) = 4 ^ k * ((k / exp 1) ^ k) ^ 2 := by
    rw [pow_mul, show (2 * (k : ℝ) / exp 1) ^ 2 = 4 * (k / exp 1) ^ 2 by ring, mul_pow,
      ← pow_mul, ← pow_mul, mul_comm 2 k]
  rw [e1, e2, e3, e4, p1, p3, div_pow (27 : ℝ) 4 k]
  have hq : 0 < ((k : ℝ) / exp 1) ^ k := by positivity
  have hs1 : 0 < Stirling.stirlingSeq k :=
    lt_of_lt_of_le (by positivity) (Stirling.sqrt_pi_le_stirlingSeq hk)
  have hs2 : 0 < Stirling.stirlingSeq (2 * k) :=
    lt_of_lt_of_le (by positivity) (Stirling.sqrt_pi_le_stirlingSeq (by omega))
  have hsk : 0 < √(k : ℝ) := by positivity
  have h2 : 0 < √(2 : ℝ) := by positivity
  have h3 : 0 < √(3 : ℝ) := by positivity
  have hπ : 0 < √π := by positivity
  field_simp

/-- `choose_stirling` with the explicit constant `1/4`. -/
lemma AsympStirling.choose_stirling_quarter (k : ℕ) (hk : 1 ≤ k) :
    |(Nat.choose (3 * k) k : ℝ) / (√3 / (2 * √(π * k)) * (27 / 4 : ℝ) ^ k) - 1| ≤ 1 / 4 / k := by
  have hk0 : k ≠ 0 := by omega
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hs (n : ℕ) (hn : n ≠ 0) : 0 < Stirling.stirlingSeq n :=
    lt_of_lt_of_le (by positivity) (Stirling.sqrt_pi_le_stirlingSeq hn)
  have lo (n : ℕ) (hn : n ≠ 0) : log √π ≤ log (Stirling.stirlingSeq n) :=
    log_le_log (by positivity) (Stirling.sqrt_pi_le_stirlingSeq hn)
  have lo1 := lo k hk0
  have lo2 := lo (2 * k) (by omega)
  have lo3 := lo (3 * k) (by omega)
  have hi1 := AsympStirling.log_stirlingSeq_le hk0
  have hi2 := AsympStirling.log_stirlingSeq_le (n := 2 * k) (by omega)
  have hi3 := AsympStirling.log_stirlingSeq_le (n := 3 * k) (by omega)
  push_cast at hi2 hi3
  set u := log √π + log (Stirling.stirlingSeq (3 * k)) - log (Stirling.stirlingSeq k)
    - log (Stirling.stirlingSeq (2 * k)) with hu
  have hR : √π * Stirling.stirlingSeq (3 * k) /
      (Stirling.stirlingSeq k * Stirling.stirlingSeq (2 * k)) = exp u := by
    rw [hu, exp_sub, exp_sub, exp_add, exp_log (by positivity), exp_log (hs _ (by omega)),
      exp_log (hs _ hk0), exp_log (hs _ (by omega)), div_div]
  have e2 : (1 : ℝ) / (12 * (2 * k)) = 1 / (24 * k) := by ring
  have e3 : (1 : ℝ) / (12 * (3 * k)) = 1 / (36 * k) := by ring
  have hu1 : u ≤ 1 / (8 * k) := by
    have : (1 : ℝ) / (36 * k) ≤ 1 / (8 * k) := by gcongr; norm_num
    linarith
  have hu2 : -(1 / (8 * k)) ≤ u := by
    have : (1 : ℝ) / (12 * k) + 1 / (24 * k) = 1 / (8 * k) := by ring
    linarith
  have habs : |u| ≤ 1 / (8 * k) := abs_le.mpr ⟨hu2, hu1⟩
  have habs1 : |u| ≤ 1 := habs.trans (by rw [div_le_one (by positivity)]; linarith)
  rw [AsympStirling.choose_ratio hk0, hR]
  calc |exp u - 1| ≤ 2 * |u| := abs_exp_sub_one_le habs1
    _ ≤ 2 * (1 / (8 * k)) := by gcongr
    _ = 1 / 4 / k := by ring

end

/-- Stirling for `C(3k,k)`: `C(3k,k) = (√3 / (2 √(π k))) (27/4)^k (1 + O(1/k))` -/
lemma choose_stirling : ∃ K : ℝ, ∀ k : ℕ, 1 ≤ k →
    |(Nat.choose (3 * k) k : ℝ) / (Real.sqrt 3 / (2 * Real.sqrt (Real.pi * k)) * (27 / 4 : ℝ) ^ k)
      - 1| ≤ K / k :=
  ⟨1 / 4, AsympStirling.choose_stirling_quarter⟩

end Results.TutteThreshold
