import Results.TutteThreshold.Defs

/-!
# The threshold `x*`

`x*` is the largest real root of `x³ - 9x + 9`; it lies in `(2, 9/4)`.  On `[2, x*]` the cubic
inequality `x³ ≤ 9 (x - 1)` holds, that is `c(x) ≤ 1` (strictly below `1` on `[2, x*)`), and
`c(x*) = 1`.
-/

namespace Results.TutteThreshold

/-- The cubic `t³ - 9t + 9` has a root greater than `2` (intermediate value theorem on
`[2, 9/4]`: `f 2 = -1 < 0 < 9/64 = f (9/4)`). -/
private lemma thresh_exists_root : ∃ r : ℝ, 2 < r ∧ r ^ 3 - 9 * r + 9 = 0 := by
  have hcont : ContinuousOn (fun t : ℝ => t ^ 3 - 9 * t + 9) (Set.Icc 2 (9 / 4)) := by
    fun_prop
  have h0 : (0 : ℝ) ∈ Set.Icc ((fun t : ℝ => t ^ 3 - 9 * t + 9) 2)
      ((fun t : ℝ => t ^ 3 - 9 * t + 9) (9 / 4)) := by
    constructor <;> norm_num
  obtain ⟨r, ⟨hr2, -⟩, hr⟩ := intermediate_value_Icc (by norm_num) hcont h0
  refine ⟨r, lt_of_le_of_ne hr2 ?_, hr⟩
  rintro rfl
  norm_num at hr

/-- `t³ - 9t + 9` is increasing on `[2, ∞)`:
`f b - f a = (b - a) (a² + ab + b² - 9)` and `a² + ab + b² ≥ 12` there. -/
private lemma thresh_cubic_mono {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    a ^ 3 - 9 * a + 9 ≤ b ^ 3 - 9 * b + 9 := by
  have hq : 0 ≤ a ^ 2 + a * b + b ^ 2 - 9 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 hab) hq]

/-- `t³ - 9t + 9` is strictly increasing on `[2, ∞)`. -/
private lemma thresh_cubic_strictMono {a b : ℝ} (ha : 2 ≤ a) (hab : a < b) :
    a ^ 3 - 9 * a + 9 < b ^ 3 - 9 * b + 9 := by
  have hq : 0 < a ^ 2 + a * b + b ^ 2 - 9 := by nlinarith
  nlinarith [mul_pos (sub_pos.2 hab) hq]

/-- The greatest root `x*` of `t³ - 9t + 9` lies in `(2, 9/4)` and satisfies `x*³ = 9 (x* - 1)`. -/
lemma xs_facts {xs : ℝ} (h : IsGreatest {t : ℝ | t ^ 3 - 9 * t + 9 = 0} xs) :
    2 < xs ∧ xs < 9 / 4 ∧ xs ^ 3 = 9 * (xs - 1) := by
  have hroot : xs ^ 3 - 9 * xs + 9 = 0 := h.1
  obtain ⟨r, hr2, hr⟩ := thresh_exists_root
  have h2 : 2 < xs := lt_of_lt_of_le hr2 (h.2 hr)
  refine ⟨h2, ?_, by linarith⟩
  by_contra hcon
  have h94 := thresh_cubic_mono (by norm_num) (not_lt.1 hcon)
  norm_num at h94
  linarith

/-- `x³ ≤ 9 (x - 1)` on `[2, x*]`. -/
lemma cube_le_of_le_xs {xs : ℝ} (h : IsGreatest {t : ℝ | t ^ 3 - 9 * t + 9 = 0} xs) {x : ℝ}
    (hx : 2 ≤ x) (hxs : x ≤ xs) : x ^ 3 ≤ 9 * (x - 1) := by
  have hroot : xs ^ 3 - 9 * xs + 9 = 0 := h.1
  linarith [thresh_cubic_mono hx hxs]

/-- `x³ < 9 (x - 1)` on `[2, x*)`. -/
lemma cube_lt_of_lt_xs {xs : ℝ} (h : IsGreatest {t : ℝ | t ^ 3 - 9 * t + 9 = 0} xs) {x : ℝ}
    (hx : 2 ≤ x) (hxs : x < xs) : x ^ 3 < 9 * (x - 1) := by
  have hroot : xs ^ 3 - 9 * xs + 9 = 0 := h.1
  linarith [thresh_cubic_strictMono hx hxs]

/-- `c(x*) = √(x*³ / (9 (x* - 1))) = 1`. -/
lemma cFun_xs {xs : ℝ} (h : IsGreatest {t : ℝ | t ^ 3 - 9 * t + 9 = 0} xs) : cFun xs = 1 := by
  obtain ⟨h2, -, h3⟩ := xs_facts h
  have hne : 9 * (xs - 1) ≠ 0 := by
    have : 0 < xs - 1 := by linarith
    positivity
  rw [cFun, h3, div_self hne, Real.sqrt_one]

end Results.TutteThreshold
