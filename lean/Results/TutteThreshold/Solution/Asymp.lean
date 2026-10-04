import Results.TutteThreshold.Solution.AsympAB
import Results.TutteThreshold.Solution.AsympStirling
import Results.TutteThreshold.Solution.Coord

/-!
# Asymptotics of `ρ_x(N_k)` (Theorem 1.3 and the necessity of `x*`)

Pure real analysis on the closed forms `Ak`, `Bk`, `bk`.
Hypotheses: `2 ≤ x` and `x³ ≤ 9 (x - 1)` (i.e. `x ≤ x*`).
-/

namespace Results.TutteThreshold

open Finset Filter Topology

/-! ### Elementary facts on `L(x) = x³/(x-1)` and `c(x)` -/

private lemma asymp_eight_le_Lx {x : ℝ} (hx : 2 ≤ x) : 8 ≤ Lx x := by
  have h1 : 0 < x - 1 := by linarith
  rw [Lx, le_div_iff₀ h1]
  nlinarith [mul_nonneg (sub_nonneg.2 hx) (by nlinarith : (0 : ℝ) ≤ x ^ 2 + 2 * x - 4)]

private lemma asymp_cc_sq {x : ℝ} (hx : 2 ≤ x) : cc x ^ 2 = Lx x / 9 := by
  have h1 : 0 < x - 1 := by linarith
  rw [cc, Real.sq_sqrt (div_nonneg (pow_nonneg (by linarith) 3) (by linarith)), Lx, div_div,
    mul_comm]

private lemma asymp_cc_pos {x : ℝ} (hx : 2 ≤ x) : 0 < cc x := by
  have h1 : 0 < x - 1 := by linarith
  exact Real.sqrt_pos.2 (div_pos (pow_pos (by linarith) 3) (by linarith))

/-- `c(x)^{6k} = (L^k)³ / 729^k` -/
private lemma asymp_cc_pow {x : ℝ} (hx : 2 ≤ x) (k : ℕ) :
    cc x ^ (6 * k) = (Lx x ^ k) ^ 3 / 729 ^ k := by
  have h729 : (729 : ℝ) ^ k = 9 ^ (3 * k) := by rw [pow_mul]; norm_num
  rw [show 6 * k = 2 * (3 * k) by ring, pow_mul, asymp_cc_sq hx, div_pow, h729, ← pow_mul,
    mul_comm k 3]

/-! ### Relative errors of `Ak`, `Bk` -/

/-- `|A_k / L^k - 1| ≤ (27/32)^k` -/
private lemma asymp_A {x : ℝ} (hx : 2 ≤ x) (k : ℕ) :
    |Ak k x / Lx x ^ k - 1| ≤ (27 / 32 : ℝ) ^ k := by
  have hL := asymp_eight_le_Lx hx
  have hLk : 0 < Lx x ^ k := pow_pos (by linarith) k
  rw [div_sub_one hLk.ne', abs_div, abs_of_pos hLk, div_le_iff₀ hLk]
  calc |Ak k x - Lx x ^ k| ≤ (27 / 4 : ℝ) ^ k := Ak_approx hx k
    _ = (27 / 32 : ℝ) ^ k * 8 ^ k := by rw [← mul_pow]; norm_num
    _ ≤ (27 / 32 : ℝ) ^ k * Lx x ^ k := by gcongr

/-- `|B_k / L^{2k} - 1| ≤ 2 (243/256)^k` -/
private lemma asymp_B {x : ℝ} (hx : 2 ≤ x) (k : ℕ) :
    |Bk k x / Lx x ^ (2 * k) - 1| ≤ 2 * (243 / 256 : ℝ) ^ k := by
  have hL := asymp_eight_le_Lx hx
  have hLk : 0 < Lx x ^ (2 * k) := pow_pos (by linarith) _
  have h1 : 0 < x - 1 := by linarith
  have h8 : 8 * (x + 1) ≤ 3 * Lx x := by
    rw [Lx, mul_div_assoc', le_div_iff₀ h1]
    nlinarith [mul_nonneg (sub_nonneg.2 hx) (by nlinarith : (0 : ℝ) ≤ 3 * x ^ 2 - 2 * x - 4)]
  have hq : 27 * (x + 1) ^ 2 / 4 ≤ 243 / 256 * Lx x ^ 2 := by
    nlinarith [mul_le_mul h8 h8 (by linarith) (by linarith)]
  rw [div_sub_one hLk.ne', abs_div, abs_of_pos hLk, div_le_iff₀ hLk]
  calc |Bk k x - Lx x ^ (2 * k)| ≤ 2 * (27 * (x + 1) ^ 2 / 4 : ℝ) ^ k := Bk_approx hx k
    _ ≤ 2 * (243 / 256 * Lx x ^ 2) ^ k := by gcongr
    _ = 2 * (243 / 256 : ℝ) ^ k * Lx x ^ (2 * k) := by rw [mul_pow, pow_mul]; ring

/-- `(243/256)^k ≤ 19/k` (Bernoulli) -/
private lemma asymp_theta {k : ℕ} (hk : 1 ≤ k) : (243 / 256 : ℝ) ^ k ≤ 19 / k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h := one_add_mul_le_pow (a := (13 / 243 : ℝ)) (by norm_num) k
  have hprod : (243 / 256 : ℝ) ^ k * (1 + 13 / 243) ^ k = 1 := by rw [← mul_pow]; norm_num
  have hθ : 0 ≤ (243 / 256 : ℝ) ^ k := by positivity
  rw [le_div_iff₀ hk0]
  nlinarith [mul_le_mul_of_nonneg_left h hθ]

/-! ### The normalized ratio -/

/-- the Stirling ratio `C(3k,k) / ((√3 / (2 √(π k))) (27/4)^k)` -/
private noncomputable def asymp_s (k : ℕ) : ℝ :=
  (Nat.choose (3 * k) k : ℝ) / (Real.sqrt 3 / (2 * Real.sqrt (Real.pi * k)) * (27 / 4 : ℝ) ^ k)

private lemma asymp_s_pos {k : ℕ} (hk : 1 ≤ k) : 0 < asymp_s k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hC : (0 : ℝ) < Nat.choose (3 * k) k := by exact_mod_cast Nat.choose_pos (by omega)
  unfold asymp_s
  have := Real.pi_pos
  positivity

/-- `ρ_k / ((4π/3) k c^{6k}) = (A_k / L^k) (B_k / L^{2k}) / s_k²` -/
private lemma asymp_ratio_eq {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : 2 ≤ x) :
    rhoK k x / (4 * Real.pi / 3 * k * cc x ^ (6 * k)) =
      (Ak k x / Lx x ^ k) * (Bk k x / Lx x ^ (2 * k)) / asymp_s k ^ 2 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hL : 0 < Lx x := by linarith [asymp_eight_le_Lx hx]
  have hC : (0 : ℝ) < Nat.choose (3 * k) k := by exact_mod_cast Nat.choose_pos (by omega)
  have hpi := Real.pi_pos
  have hP : (Real.sqrt 3 / (2 * Real.sqrt (Real.pi * k)) * (27 / 4 : ℝ) ^ k) ^ 2 =
      3 * 729 ^ k / (4 * Real.pi * k * 16 ^ k) := by
    have h27 : ((27 / 4 : ℝ) ^ k) ^ 2 = 729 ^ k / 16 ^ k := by
      rw [← pow_mul, mul_comm k 2, pow_mul, ← div_pow]
      norm_num
    rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by positivity), h27]
    ring
  have hbk : bk k ^ 2 = 16 ^ k * (Nat.choose (3 * k) k : ℝ) ^ 2 := by
    rw [bk, mul_pow, ← pow_mul, mul_comm k 2, pow_mul]
    norm_num
  have hL2 : Lx x ^ (2 * k) = (Lx x ^ k) ^ 2 := by rw [mul_comm, pow_mul]
  have h729 : (0 : ℝ) < 729 ^ k := by positivity
  have h16 : (0 : ℝ) < 16 ^ k := by positivity
  have hLk : 0 < Lx x ^ k := pow_pos hL k
  rw [asymp_s, div_pow, hP, rhoK, hbk, asymp_cc_pow hx, hL2]
  field_simp

/-! ### Two elementary estimates -/

private lemma asymp_err_small {a b s : ℝ} (ha : |a - 1| ≤ 1) (hb : |b - 1| ≤ 2) (hs : 0 < s) :
    |a * b / s ^ 2 - 1| ≤ 6 / s ^ 2 + 1 := by
  have h1 : |a| ≤ 2 := by
    have := abs_sub_abs_le_abs_sub a 1
    rw [abs_one] at this
    linarith
  have h2 : |b| ≤ 3 := by
    have := abs_sub_abs_le_abs_sub b 1
    rw [abs_one] at this
    linarith
  have hs2 : 0 < s ^ 2 := by positivity
  calc |a * b / s ^ 2 - 1| ≤ |a * b / s ^ 2| + |1| := abs_sub _ _
    _ = |a| * |b| / s ^ 2 + 1 := by rw [abs_div, abs_mul, abs_of_pos hs2, abs_one]
    _ ≤ 6 / s ^ 2 + 1 := by
      gcongr
      nlinarith [abs_nonneg a, abs_nonneg b]

private lemma asymp_err_large {a b s θ e : ℝ} (ha : |a - 1| ≤ θ) (hb : |b - 1| ≤ 2 * θ)
    (hθ : θ ≤ 1) (hs : |s - 1| ≤ e) (he : e ≤ 1 / 2) :
    |a * b / s ^ 2 - 1| ≤ 20 * θ + 10 * e := by
  have hs1 : 1 / 2 ≤ s := by linarith [(abs_le.1 hs).1]
  have hs2 : s ≤ 3 / 2 := by linarith [(abs_le.1 hs).2]
  have hθ0 : 0 ≤ θ := (abs_nonneg _).trans ha
  have he0 : 0 ≤ e := (abs_nonneg _).trans hs
  have hsq : 0 < s ^ 2 := by positivity
  have hpq : |(a - 1) * (b - 1)| ≤ 2 * θ := by
    rw [abs_mul]
    nlinarith [abs_nonneg (a - 1), abs_nonneg (b - 1)]
  have hr : |(s - 1) * (s + 1)| ≤ 5 / 2 * e := by
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < s + 1)]
    nlinarith [abs_nonneg (s - 1)]
  have key : a * b - s ^ 2 = (a - 1) * (b - 1) + (a - 1) + (b - 1) - (s - 1) * (s + 1) := by ring
  have hnum : |a * b - s ^ 2| ≤ 5 * θ + 5 / 2 * e := by
    rw [key]
    calc |(a - 1) * (b - 1) + (a - 1) + (b - 1) - (s - 1) * (s + 1)|
        ≤ |(a - 1) * (b - 1) + (a - 1) + (b - 1)| + |(s - 1) * (s + 1)| := abs_sub _ _
      _ ≤ |(a - 1) * (b - 1)| + |a - 1| + |b - 1| + |(s - 1) * (s + 1)| := by
        gcongr
        exact abs_add_three _ _ _
      _ ≤ 2 * θ + θ + 2 * θ + 5 / 2 * e := by gcongr
      _ = 5 * θ + 5 / 2 * e := by ring
  have hs4 : 1 / 4 ≤ s ^ 2 := by nlinarith
  have := mul_le_mul_of_nonneg_left hs4 (by linarith : (0 : ℝ) ≤ 20 * θ + 10 * e)
  rw [div_sub_one hsq.ne', abs_div, abs_of_pos hsq, div_le_iff₀ hsq]
  linarith

/-! ### The three theorems -/

/-- the asymptotic formula for `ρ_x(N_k)`, uniformly in `x` -/
theorem rhoK_asymptotic : ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → ∀ x : ℝ, 2 ≤ x → x ^ 3 ≤ 9 * (x - 1) →
    |rhoK k x / (4 * Real.pi / 3 * k * cc x ^ (6 * k)) - 1| ≤ C / k := by
  obtain ⟨K, hK⟩ := choose_stirling
  have hK0 : 0 ≤ K := by
    have := hK 1 le_rfl
    rw [Nat.cast_one, div_one] at this
    exact (abs_nonneg _).trans this
  set N : ℕ := ⌈2 * K⌉₊ + 1 with hN
  set M : ℝ := ∑ j ∈ range N, (j : ℝ) * (6 / asymp_s j ^ 2 + 1) with hM
  have hM0 : ∀ j ∈ range N, 0 ≤ (j : ℝ) * (6 / asymp_s j ^ 2 + 1) := fun j _ => by positivity
  have hMnn : 0 ≤ M := Finset.sum_nonneg hM0
  refine ⟨M + 380 + 10 * K, fun k hk x hx _ => ?_⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [asymp_ratio_eq hk hx]
  have hA := asymp_A hx k
  have hB := asymp_B hx k
  have hs : 0 < asymp_s k := asymp_s_pos hk
  have hθ := asymp_theta hk
  have hα : (27 / 32 : ℝ) ^ k ≤ (243 / 256) ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
  have hθ1 : (243 / 256 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  by_cases hkN : k < N
  · have hsmall := asymp_err_small (hA.trans (hα.trans hθ1)) (hB.trans (by linarith)) hs
    have hle : (k : ℝ) * (6 / asymp_s k ^ 2 + 1) ≤ M :=
      Finset.single_le_sum hM0 (Finset.mem_range.2 hkN)
    rw [le_div_iff₀ hk0]
    calc |(Ak k x / Lx x ^ k) * (Bk k x / Lx x ^ (2 * k)) / asymp_s k ^ 2 - 1| * k
        ≤ (6 / asymp_s k ^ 2 + 1) * k := by gcongr
      _ ≤ M + 380 + 10 * K := by linarith
  · have hNk : (N : ℝ) ≤ k := by exact_mod_cast not_lt.1 hkN
    have hceil : 2 * K ≤ (⌈2 * K⌉₊ : ℝ) := Nat.le_ceil _
    have hKk : K / k ≤ 1 / 2 := by
      rw [div_le_iff₀ hk0]
      rw [hN] at hNk
      push_cast at hNk
      linarith
    have hlarge := asymp_err_large (hA.trans hα) hB hθ1 (hK k hk) hKk
    calc _ ≤ 20 * (243 / 256 : ℝ) ^ k + 10 * (K / k) := hlarge
      _ ≤ 20 * (19 / k) + 10 * (K / k) := by gcongr
      _ = (380 + 10 * K) / k := by ring
      _ ≤ (M + 380 + 10 * K) / k := by gcongr; linarith

/-- for `k ≥ 1`, `ρ_k` is `(4π/3) k c^{6k}` times a factor `r` with `|r - 1| ≤ C/k` -/
private lemma asymp_rhoK_eq {C : ℝ}
    (hC : ∀ k : ℕ, 1 ≤ k → ∀ x : ℝ, 2 ≤ x → x ^ 3 ≤ 9 * (x - 1) →
      |rhoK k x / (4 * Real.pi / 3 * k * cc x ^ (6 * k)) - 1| ≤ C / k)
    {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : 2 ≤ x) (hxs : x ^ 3 ≤ 9 * (x - 1)) :
    ∃ r : ℝ, |r - 1| ≤ C / k ∧ rhoK k x = 4 * Real.pi / 3 * k * cc x ^ (6 * k) * r := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hD : 0 < 4 * Real.pi / 3 * k * cc x ^ (6 * k) := by
    have := Real.pi_pos
    have := asymp_cc_pos hx
    positivity
  exact ⟨_, hC k hk x hx hxs, (mul_div_cancel₀ _ hD.ne').symm⟩

/-- the `6k`-th root limit -/
theorem rhoK_root_limit {x : ℝ} (hx : 2 ≤ x) (hxs : x ^ 3 ≤ 9 * (x - 1)) :
    Tendsto (fun k : ℕ => rhoK k x ^ (1 / (6 * (k : ℝ)))) atTop (𝓝 (cc x)) := by
  obtain ⟨C, hC⟩ := rhoK_asymptotic
  have hc := asymp_cc_pos hx
  have hpi2 := Real.two_le_pi
  have hpi4 := Real.pi_le_four
  -- `(9k)^{1/(6k)} → 1`
  have h9 : Tendsto (fun k : ℕ => (9 * (k : ℝ)) ^ (1 / (6 * (k : ℝ)))) atTop (𝓝 1) := by
    have h1 := (tendsto_rpow_div_mul_add (3 / 2) 1 0 (by norm_num)).comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 9))
    refine h1.congr fun k => ?_
    simp only [Function.comp_apply]
    congr 1
    ring
  have hup : Tendsto (fun k : ℕ => (9 * (k : ℝ)) ^ (1 / (6 * (k : ℝ))) * cc x) atTop
      (𝓝 (cc x)) := by
    simpa using h9.mul_const (cc x)
  -- eventually the correction factor lies in `[1/2, 3/2]`
  have hev : ∀ᶠ k : ℕ in atTop, 1 ≤ k ∧ C / k ≤ 1 / 2 := by
    obtain ⟨n, hn⟩ := exists_nat_gt (2 * C)
    refine eventually_atTop.2 ⟨max n 1, fun k hk => ⟨le_of_max_le_right hk, ?_⟩⟩
    have hk1 : 1 ≤ k := le_of_max_le_right hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have hnk : (n : ℝ) ≤ k := by exact_mod_cast le_of_max_le_left hk
    rw [div_le_iff₀ hk0]
    linarith
  -- the exponent `1/(6k)` undoes the power `6k`
  have hroot : ∀ k : ℕ, 1 ≤ k → (cc x ^ (6 * k)) ^ (1 / (6 * (k : ℝ))) = cc x := by
    intro k hk
    have : (1 / (6 * (k : ℝ))) = ((6 * k : ℕ) : ℝ)⁻¹ := by push_cast; ring
    rw [this, Real.pow_rpow_inv_natCast hc.le (by omega)]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [hev] with k ⟨hk, hCk⟩
    obtain ⟨r, hr, hrho⟩ := asymp_rhoK_eq hC hk hx hxs
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hr1 : 1 / 2 ≤ r := by linarith [(abs_le.1 hr).1]
    have hpow : 0 < cc x ^ (6 * k) := pow_pos hc _
    have hle : cc x ^ (6 * k) ≤ rhoK k x := by
      have h1 : 2 * 1 ≤ Real.pi * k := mul_le_mul hpi2 hk1 (by norm_num) (by linarith)
      have h2 : 8 / 3 * (1 / 2) ≤ 4 * Real.pi / 3 * k * r :=
        mul_le_mul (by linarith) hr1 (by norm_num) (by positivity)
      have h3 := mul_le_mul_of_nonneg_right (h2.trans' (by norm_num : (1 : ℝ) ≤ 8 / 3 * (1 / 2)))
        hpow.le
      rw [hrho]
      linarith
    calc cc x = (cc x ^ (6 * k)) ^ (1 / (6 * (k : ℝ))) := (hroot k hk).symm
      _ ≤ rhoK k x ^ (1 / (6 * (k : ℝ))) :=
        Real.rpow_le_rpow hpow.le hle (by positivity)
  · filter_upwards [hev] with k ⟨hk, hCk⟩
    obtain ⟨r, hr, hrho⟩ := asymp_rhoK_eq hC hk hx hxs
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hr1 : 1 / 2 ≤ r := by linarith [(abs_le.1 hr).1]
    have hr2 : r ≤ 3 / 2 := by linarith [(abs_le.1 hr).2]
    have hpow : 0 < cc x ^ (6 * k) := pow_pos hc _
    have hpos : 0 ≤ rhoK k x := by
      rw [hrho]
      have : 0 < 4 * Real.pi / 3 * k * r := by positivity
      positivity
    have hle : rhoK k x ≤ 9 * k * cc x ^ (6 * k) := by
      have h1 : Real.pi * r ≤ 4 * (3 / 2) := mul_le_mul hpi4 hr2 (by linarith) (by norm_num)
      have h2 := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ k)
      have h3 : 4 * Real.pi / 3 * k * r ≤ 9 * k := by linarith
      have h4 := mul_le_mul_of_nonneg_right h3 hpow.le
      rw [hrho]
      linarith
    calc rhoK k x ^ (1 / (6 * (k : ℝ))) ≤ (9 * k * cc x ^ (6 * k)) ^ (1 / (6 * (k : ℝ))) :=
        Real.rpow_le_rpow hpos hle (by positivity)
      _ = (9 * (k : ℝ)) ^ (1 / (6 * (k : ℝ))) * cc x := by
        rw [Real.mul_rpow (by positivity) hpow.le, hroot k hk]

/-- below the threshold the ratio of `N_k` is eventually below one -/
theorem exists_rhoK_lt_one {x : ℝ} (hx : 2 ≤ x) (hlt : x ^ 3 < 9 * (x - 1)) :
    ∃ k : ℕ, 1 ≤ k ∧ rhoK k x < 1 := by
  obtain ⟨C, hC⟩ := rhoK_asymptotic
  have hc := asymp_cc_pos hx
  have h1 : 0 < x - 1 := by linarith
  have hc1 : cc x < 1 := by
    rw [cc, Real.sqrt_lt' one_pos, one_pow, div_lt_one (by linarith)]
    exact hlt
  set q := cc x ^ 6 with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := pow_lt_one₀ hc.le hc1 (by norm_num)
  have hlim : Tendsto (fun k : ℕ => 4 * Real.pi / 3 * ((k : ℝ) * q ^ k + C * q ^ k)) atTop
      (𝓝 0) := by
    have := (tendsto_self_mul_const_pow_of_lt_one hq0 hq1).add
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul C)
    simpa using this.const_mul (4 * Real.pi / 3)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually_lt_const one_pos)
  refine ⟨max N 1, le_max_right _ _, ?_⟩
  set k := max N 1 with hkdef
  have hk : 1 ≤ k := le_max_right _ _
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨r, hr, hrho⟩ := asymp_rhoK_eq hC hk hx hlt.le
  have hr2 : r ≤ 1 + C / k := by linarith [(abs_le.1 hr).2]
  have hpow : cc x ^ (6 * k) = q ^ k := by rw [hq, pow_mul]
  have hD : 0 ≤ 4 * Real.pi / 3 * k * q ^ k := by
    have := Real.pi_pos
    positivity
  calc rhoK k x = 4 * Real.pi / 3 * k * q ^ k * r := by rw [hrho, hpow]
    _ ≤ 4 * Real.pi / 3 * k * q ^ k * (1 + C / k) := by gcongr
    _ = 4 * Real.pi / 3 * ((k : ℝ) * q ^ k + C * q ^ k) := by field_simp
    _ < 1 := hN k (le_max_left _ _)

end Results.TutteThreshold
