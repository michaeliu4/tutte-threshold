import Results.TutteThreshold.Solution.Closed
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Field

/-!
# Bounds on `Ak` and `Bk`

Elementary finite sums (binomial theorem and a Markov-type bound for the lower tail of
`∑ C(3k,u)`); hypotheses `2 ≤ x`.
-/

namespace Results.TutteThreshold

open Finset

/-- `∑_u C(3k,u) 2^u = 27^k` (binomial theorem) -/
lemma AsympAB_sum_choose_two_pow (k : ℕ) :
    ∑ u ∈ range (3 * k + 1), (Nat.choose (3 * k) u : ℝ) * 2 ^ u = (27 : ℝ) ^ k := by
  have h := (add_pow (2 : ℝ) 1 (3 * k)).symm
  simp only [one_pow, mul_one] at h
  rw [show (27 : ℝ) = (2 + 1) ^ 3 by norm_num, ← pow_mul, ← h]
  exact sum_congr rfl fun u _ => mul_comm _ _

/-- `L^k = ∑_u C(3k,u) z^{2k-u}` with `z = x - 1`, the power `z^{2k-u}` written as
`z^{3k-u} / z^k` -/
lemma AsympAB_sum_Lk (x : ℝ) (k : ℕ) :
    ∑ u ∈ range (3 * k + 1),
        (Nat.choose (3 * k) u : ℝ) * ((x - 1) ^ (3 * k - u) / (x - 1) ^ k) = Lx x ^ k := by
  have h := add_pow (1 : ℝ) (x - 1) (3 * k)
  simp only [one_pow, one_mul, show (1 : ℝ) + (x - 1) = x by ring] at h
  rw [Lx, div_pow, ← pow_mul, h, sum_div]
  exact sum_congr rfl fun u _ => by ring

/-- `L^{2k} = ∑_u C(3k,u) z^{u-2k} (1+x)^u` with `z = x - 1` (as `1 + z (1+x) = x²`), the power
`z^{u-2k}` written as `z^u / z^{2k}` -/
lemma AsympAB_sum_L2k (x : ℝ) (k : ℕ) :
    ∑ u ∈ range (3 * k + 1),
        (Nat.choose (3 * k) u : ℝ) * ((x - 1) ^ u * (1 + x) ^ u / (x - 1) ^ (2 * k)) =
      Lx x ^ (2 * k) := by
  have h := add_pow ((x - 1) * (1 + x)) 1 (3 * k)
  simp only [one_pow, mul_one, mul_pow, show (x - 1) * (1 + x) + 1 = x ^ 2 by ring] at h
  rw [Lx, div_pow, ← pow_mul, show 3 * (2 * k) = 2 * (3 * k) by ring, pow_mul x 2, h, sum_div]
  exact sum_congr rfl fun u _ => by ring

/-- termwise comparison of `Ak` with `L^k` -/
private lemma Ak_term {z : ℝ} (hz : 1 ≤ z) {k u : ℕ} :
    |(Nat.choose (3 * k) u : ℝ) * z ^ (2 * k - min (2 * k) u) * (-1 : ℝ) ^ (u - min (2 * k) u) -
        (Nat.choose (3 * k) u : ℝ) * (z ^ (3 * k - u) / z ^ k)| ≤
      (Nat.choose (3 * k) u : ℝ) * 2 ^ u / 4 ^ k := by
  have hz0 : 0 < z := by linarith
  have hC : (0 : ℝ) ≤ Nat.choose (3 * k) u := Nat.cast_nonneg _
  rcases le_or_gt u (2 * k) with h | h
  · have hq : z ^ (3 * k - u) / z ^ k = z ^ (2 * k - u) := by
      rw [div_eq_iff (pow_pos hz0 k).ne', ← pow_add]
      congr 1
      omega
    rw [min_eq_right h, Nat.sub_self, pow_zero, mul_one, hq, sub_self, abs_zero]
    positivity
  · rw [min_eq_left h.le, Nat.sub_self, pow_zero, mul_one, ← mul_sub, abs_mul, Nat.abs_cast]
    have hq0 : 0 ≤ z ^ (3 * k - u) / z ^ k := by positivity
    have hq1 : z ^ (3 * k - u) / z ^ k ≤ 1 :=
      (div_le_one (pow_pos hz0 k)).mpr (pow_le_pow_right₀ hz (by omega))
    have habs : |(-1 : ℝ) ^ (u - 2 * k) - z ^ (3 * k - u) / z ^ k| ≤ 2 := by
      rcases neg_one_pow_eq_or ℝ (u - 2 * k) with h1 | h1 <;> rw [h1, abs_le] <;>
        constructor <;> linarith
    have h2 : (2 : ℝ) * 4 ^ k ≤ 2 ^ u := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_succ']
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    calc (Nat.choose (3 * k) u : ℝ) * |(-1 : ℝ) ^ (u - 2 * k) - z ^ (3 * k - u) / z ^ k|
        ≤ (Nat.choose (3 * k) u : ℝ) * 2 := mul_le_mul_of_nonneg_left habs hC
      _ ≤ (Nat.choose (3 * k) u : ℝ) * 2 ^ u / 4 ^ k := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left ((le_div_iff₀ (by positivity)).mpr h2) hC

/-- termwise comparison of `Bk` with `L^{2k}` -/
private lemma Bk_term {z w : ℝ} (hz : 1 ≤ z) (hw : 2 ≤ w) {k u : ℕ} :
    |(Nat.choose (3 * k) u : ℝ) * (-1 : ℝ) ^ (2 * k - min (2 * k) u) *
          z ^ (u - min (2 * k) u) * w ^ u -
        (Nat.choose (3 * k) u : ℝ) * (z ^ u * w ^ u / z ^ (2 * k))| ≤
      2 * w ^ (2 * k) / 4 ^ k * ((Nat.choose (3 * k) u : ℝ) * 2 ^ u) := by
  have hz0 : 0 < z := by linarith
  have hw0 : 0 < w := by linarith
  have hC : (0 : ℝ) ≤ Nat.choose (3 * k) u := Nat.cast_nonneg _
  rcases le_or_gt (2 * k) u with h | h
  · have hq : z ^ u * w ^ u / z ^ (2 * k) = z ^ (u - 2 * k) * w ^ u := by
      rw [div_eq_iff (pow_pos hz0 _).ne', mul_right_comm, ← pow_add]
      congr 2
      omega
    rw [min_eq_left h, Nat.sub_self, pow_zero, mul_one, hq, ← mul_assoc, sub_self, abs_zero]
    positivity
  · have e : (Nat.choose (3 * k) u : ℝ) * (-1 : ℝ) ^ (2 * k - u) * z ^ (u - u) * w ^ u -
        (Nat.choose (3 * k) u : ℝ) * (z ^ u * w ^ u / z ^ (2 * k)) =
        ((Nat.choose (3 * k) u : ℝ) * w ^ u) *
          ((-1 : ℝ) ^ (2 * k - u) - z ^ u / z ^ (2 * k)) := by
      rw [Nat.sub_self, pow_zero]
      ring
    rw [min_eq_right h.le, e, abs_mul, abs_of_nonneg (by positivity)]
    have hq0 : 0 ≤ z ^ u / z ^ (2 * k) := by positivity
    have hq1 : z ^ u / z ^ (2 * k) ≤ 1 :=
      (div_le_one (pow_pos hz0 _)).mpr (pow_le_pow_right₀ hz h.le)
    have habs : |(-1 : ℝ) ^ (2 * k - u) - z ^ u / z ^ (2 * k)| ≤ 2 := by
      rcases neg_one_pow_eq_or ℝ (2 * k - u) with h1 | h1 <;> rw [h1, abs_le] <;>
        constructor <;> linarith
    have key : w ^ u * 4 ^ k ≤ w ^ (2 * k) * 2 ^ u := by
      have h4 : (4 : ℝ) ^ k = 2 ^ u * 2 ^ (2 * k - u) := by
        rw [← pow_add, show u + (2 * k - u) = 2 * k by omega, pow_mul]
        norm_num
      have hw' : w ^ (2 * k) = w ^ u * w ^ (2 * k - u) := by
        rw [← pow_add, show u + (2 * k - u) = 2 * k by omega]
      have h22 : (2 : ℝ) ^ (2 * k - u) ≤ w ^ (2 * k - u) :=
        pow_le_pow_left₀ (by norm_num) hw _
      rw [h4, hw']
      calc w ^ u * (2 ^ u * 2 ^ (2 * k - u)) = (w ^ u * 2 ^ u) * 2 ^ (2 * k - u) := by ring
        _ ≤ (w ^ u * 2 ^ u) * w ^ (2 * k - u) :=
          mul_le_mul_of_nonneg_left h22 (by positivity)
        _ = w ^ u * w ^ (2 * k - u) * 2 ^ u := by ring
    calc (Nat.choose (3 * k) u : ℝ) * w ^ u * |(-1 : ℝ) ^ (2 * k - u) - z ^ u / z ^ (2 * k)|
        ≤ (Nat.choose (3 * k) u : ℝ) * w ^ u * 2 :=
          mul_le_mul_of_nonneg_left habs (by positivity)
      _ ≤ 2 * w ^ (2 * k) / 4 ^ k * ((Nat.choose (3 * k) u : ℝ) * 2 ^ u) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        have := mul_le_mul_of_nonneg_left key (mul_nonneg zero_le_two hC)
        linarith

/-- `A_k = L(x)^k (1 + O(θ^k))`, explicitly `|A_k - L^k| ≤ (27/4)^k` -/
lemma Ak_approx {x : ℝ} (hx : 2 ≤ x) (k : ℕ) : |Ak k x - Lx x ^ k| ≤ (27 / 4 : ℝ) ^ k := by
  have hz : (1 : ℝ) ≤ x - 1 := by linarith
  rw [← AsympAB_sum_Lk x k, Ak, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ u ∈ range (3 * k + 1), (Nat.choose (3 * k) u : ℝ) * 2 ^ u / 4 ^ k :=
        sum_le_sum fun u _ => Ak_term hz
    _ = (27 / 4 : ℝ) ^ k := by rw [← sum_div, AsympAB_sum_choose_two_pow, div_pow]

/-- `B_k = L(x)^{2k} + E`, `|E| ≤ 2 (27 (x+1)² / 4)^k` -/
lemma Bk_approx {x : ℝ} (hx : 2 ≤ x) (k : ℕ) :
    |Bk k x - Lx x ^ (2 * k)| ≤ 2 * (27 * (x + 1) ^ 2 / 4 : ℝ) ^ k := by
  have hz : (1 : ℝ) ≤ x - 1 := by linarith
  have hw : (2 : ℝ) ≤ 1 + x := by linarith
  rw [← AsympAB_sum_L2k x k, Bk, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ u ∈ range (3 * k + 1),
          2 * (1 + x) ^ (2 * k) / 4 ^ k * ((Nat.choose (3 * k) u : ℝ) * 2 ^ u) :=
        sum_le_sum fun u _ => Bk_term hz hw
    _ = 2 * (27 * (x + 1) ^ 2 / 4 : ℝ) ^ k := by
        rw [← mul_sum, AsympAB_sum_choose_two_pow, div_pow, mul_pow, ← pow_mul, add_comm x 1]
        ring

end Results.TutteThreshold
