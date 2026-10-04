import Results.TutteThreshold.Solution.Lab

/-!
# Loss factors for a retained profile

For an exterior context `R` satisfying the branch hypotheses (`Ctx.Good x γ`), closing a profile
`l ∈ {ε, P₂, S₂, P₃, S₃, D, E}` loses at most the factor `c(x)^{size l}`:
`γ · c(x)^{size l} ≤ ρ(R[l])` for `2 ≤ x ≤ x_*` (here `x ≤ x_*` is expressed as `x³ ≤ 9(x-1)`).

Proof (no derivatives).  Put `z = x - 1`, `P = γT²`, `Q = γF²`, `Z = AC`, `Y = IB`.  The branch
hypotheses give `P ≤ AB`, `Q ≤ IC`, `z max(P,Q) ≤ Z` and `PQ ≤ ZY`.  For `0 ≤ c ≤ s z²` the
identity `zZ (z(sZ + cY) - s z² P - c Q) = z (Z - zP)(s z Z - c Q) + c z² (ZY - PQ)` gives
`s z² P + c Q ≤ z (sZ + cY)` and the same with `P, Q` exchanged (`AlgLoss.mono_bound`; this is the
monotonicity of `Z ↦ sZ + cPQ/Z` above `z max(P,Q)`).  Each closing value `αβ` is then bounded below
by a quadratic form in `T, F`; the remaining inequality is `(T - F)` (resp. `(F - T)`) times a
nonnegative linear form.  `S₂, S₃, E` follow from `P₂, P₃, D` by duality.
-/

namespace Results.TutteThreshold

namespace AlgLoss

/-- `2w ≤ u + v` from `w² ≤ uv` (arithmetic–geometric mean) -/
lemma two_mul_le_add {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (h : w ^ 2 ≤ u * v) :
    2 * w ≤ u + v := by
  nlinarith [sq_nonneg (u - v)]

/-- the monotonicity step of the loss lemma, without division -/
lemma mono_bound {z s c P Q Z Y : ℝ} (hz : 1 ≤ z) (hs : 0 ≤ s) (hc : 0 ≤ c)
    (hsc : c ≤ s * z ^ 2) (hQ : 0 ≤ Q) (hZ : 0 < Z) (hZP : z * P ≤ Z) (hZQ : z * Q ≤ Z)
    (hYZ : P * Q ≤ Z * Y) :
    s * z ^ 2 * P + c * Q ≤ z * (s * Z + c * Y) := by
  have h1 : 0 ≤ s * z * Z - c * Q := by
    linarith [mul_le_mul_of_nonneg_left hZQ (by positivity : 0 ≤ s * z),
      mul_le_mul_of_nonneg_right hsc hQ]
  have h2 : 0 ≤ z * Z * (z * (s * Z + c * Y) - s * z ^ 2 * P - c * Q) := by
    have e : z * Z * (z * (s * Z + c * Y) - s * z ^ 2 * P - c * Q) =
        z * (Z - z * P) * (s * z * Z - c * Q) + c * z ^ 2 * (Z * Y - P * Q) := by ring
    rw [e]
    exact add_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) h1)
      (mul_nonneg (by positivity) (by linarith))
  have := nonneg_of_mul_nonneg_right h2 (by positivity)
  linarith

/-- the consequences of the branch hypotheses used by the loss lemma: for `0 ≤ c ≤ s (x-1)²`,
`s (x-1)² max(γT², γF²) + c min(γT², γF²) ≤ (x-1) (s AC + c IB)` (both orders) -/
lemma good_key {x γ : ℝ} (hx : 2 ≤ x) {R : Ctx} (hR : R.Good x γ) {s c : ℝ} (hs : 0 ≤ s)
    (hc : 0 ≤ c) (hsc : c ≤ s * (x - 1) ^ 2) :
    s * (x - 1) ^ 2 * (γ * R.T ^ 2) + c * (γ * R.F ^ 2) ≤
        (x - 1) * (s * (R.A * R.C) + c * (R.I * R.B)) ∧
      s * (x - 1) ^ 2 * (γ * R.F ^ 2) + c * (γ * R.T ^ 2) ≤
        (x - 1) * (s * (R.A * R.C) + c * (R.I * R.B)) := by
  obtain ⟨hγ, hT, hF, hI, hB, h1, h2, h3, h4⟩ := hR
  have hz : 1 ≤ x - 1 := by linarith
  have hA : 0 ≤ R.A := le_trans (mul_nonneg (by linarith) hI) h3
  have hC : 0 ≤ R.C := le_trans (mul_nonneg (by linarith) hB) h4
  have hP : 0 < γ * R.T ^ 2 := by positivity
  have hQ : 0 < γ * R.F ^ 2 := by positivity
  -- `z P ≤ z AB ≤ AC` and `z Q ≤ z IC ≤ AC`
  have hZP : (x - 1) * (γ * R.T ^ 2) ≤ R.A * R.C := by
    linarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ x - 1),
      mul_le_mul_of_nonneg_left h4 hA]
  have hZQ : (x - 1) * (γ * R.F ^ 2) ≤ R.A * R.C := by
    linarith [mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ x - 1),
      mul_le_mul_of_nonneg_right h3 hC]
  -- `PQ ≤ (AB)(IC) = (AC)(IB)`
  have hYZ : (γ * R.T ^ 2) * (γ * R.F ^ 2) ≤ (R.A * R.C) * (R.I * R.B) := by
    have := mul_le_mul h1 h2 hQ.le (le_trans hP.le h1)
    linarith
  have hZ : 0 < R.A * R.C := lt_of_lt_of_le (by positivity) hZP
  refine ⟨mono_bound hz hs hc hsc hQ.le hZ hZP hZQ hYZ,
    mono_bound hz hs hc hsc hP.le hZ hZQ hZP ?_⟩
  linarith

/-- closing a single edge -/
lemma rho_p1 {x : ℝ} (hx : x ≠ 0) (R : Ctx) :
    R.rho x (Lab.coord x (Lab.p 1)) = (R.A + R.I) * (R.B + R.C) / (R.T + R.F) ^ 2 := by
  have hs : ∑ i ∈ Finset.range (1 - 1), x ^ (i + 1) = 0 := by simp
  have hal : R.al x (Lab.coord x (Lab.p 1)) = R.A + R.I := by
    simp only [Ctx.al, Lab.coord, Lab.pk]
    rw [div_eq_iff hx]
    ring
  have hbe : R.be x (Lab.coord x (Lab.p 1)) = R.B + R.C := by
    simp only [Ctx.be, Lab.coord, Lab.pk]
    rw [hs, div_eq_iff hx]
    ring
  have hb : R.b (Lab.coord x (Lab.p 1)) = R.T + R.F := by
    simp only [Ctx.b, Lab.coord, Lab.pk]
    push_cast
    ring
  rw [Ctx.rho, hal, hbe, hb]

/-- closing two parallel edges -/
lemma rho_p2 {x : ℝ} (hx : x ≠ 0) (R : Ctx) :
    R.rho x (Lab.coord x (Lab.p 2)) =
      (R.A + R.I) * (R.B + (1 + x) * R.C) / (R.T + 2 * R.F) ^ 2 := by
  have hs : ∑ i ∈ Finset.range (2 - 1), x ^ (i + 1) = x := by simp
  have hal : R.al x (Lab.coord x (Lab.p 2)) = R.A + R.I := by
    simp only [Ctx.al, Lab.coord, Lab.pk]
    rw [div_eq_iff hx]
    ring
  have hbe : R.be x (Lab.coord x (Lab.p 2)) = R.B + (1 + x) * R.C := by
    simp only [Ctx.be, Lab.coord, Lab.pk]
    rw [hs, div_eq_iff hx]
    ring
  have hb : R.b (Lab.coord x (Lab.p 2)) = R.T + 2 * R.F := by
    simp only [Ctx.b, Lab.coord, Lab.pk]
    push_cast
    ring
  rw [Ctx.rho, hal, hbe, hb]

/-- closing three parallel edges -/
lemma rho_p3 {x : ℝ} (hx : x ≠ 0) (R : Ctx) :
    R.rho x (Lab.coord x (Lab.p 3)) =
      (R.A + R.I) * (R.B + (1 + x + x ^ 2) * R.C) / (R.T + 3 * R.F) ^ 2 := by
  have hs : ∑ i ∈ Finset.range (3 - 1), x ^ (i + 1) = x + x ^ 2 := by
    simp [Finset.sum_range_succ]
  have hal : R.al x (Lab.coord x (Lab.p 3)) = R.A + R.I := by
    simp only [Ctx.al, Lab.coord, Lab.pk]
    rw [div_eq_iff hx]
    ring
  have hbe : R.be x (Lab.coord x (Lab.p 3)) = R.B + (1 + x + x ^ 2) * R.C := by
    simp only [Ctx.be, Lab.coord, Lab.pk]
    rw [hs, div_eq_iff hx]
    ring
  have hb : R.b (Lab.coord x (Lab.p 3)) = R.T + 3 * R.F := by
    simp only [Ctx.b, Lab.coord, Lab.pk]
    push_cast
    ring
  rw [Ctx.rho, hal, hbe, hb]

/-- closing the profile `D` -/
lemma rho_d {x : ℝ} (hx : x ≠ 0) (R : Ctx) :
    R.rho x (Lab.coord x Lab.d) =
      ((x + 1) * R.A + R.I) * ((x + 1) ^ 2 * R.C + (2 * x + 1) * R.B) /
        (16 * (R.T + R.F) ^ 2) := by
  have hal : R.al x (Lab.coord x Lab.d) = (x + 1) * R.A + R.I := by
    simp only [Ctx.al, Lab.coord]
    rw [div_eq_iff hx]
    ring
  have hbe : R.be x (Lab.coord x Lab.d) = (x + 1) ^ 2 * R.C + (2 * x + 1) * R.B := by
    simp only [Ctx.be, Lab.coord]
    rw [div_eq_iff hx]
    ring
  have hb : R.b (Lab.coord x Lab.d) = 4 * (R.T + R.F) := by
    simp only [Ctx.b, Lab.coord]
    ring
  rw [Ctx.rho, hal, hbe, hb]
  ring

/-- the factor of `P₃` is at least one: `x⁴ - 16x + 16 = (x-2)(x³+2x²+4x-8)` -/
lemma one_le_lam_p3 {x : ℝ} (hx : 2 ≤ x) : 1 ≤ x ^ 4 / (16 * (x - 1)) := by
  have hz : 0 < x - 1 := by linarith
  have hx3 : (2 : ℝ) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hx 3
  rw [le_div_iff₀ (by positivity)]
  linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 2)
    (by nlinarith : (0 : ℝ) ≤ x ^ 3 + 2 * x ^ 2 + 4 * x - 8)]

/-- the factor of `D` dominates `c(x)⁴`: `λ_D / c⁴ = 81 (x³-1) / (64 x³)` and `17 x³ ≥ 81` -/
lemma cc_pow_four_le {x : ℝ} (hx : 2 ≤ x) :
    cc x ^ 4 ≤ x ^ 3 * (x ^ 2 + x + 1) / (64 * (x - 1)) := by
  have hz : 0 < x - 1 := by linarith
  have hx3 : (2 : ℝ) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hx 3
  have hc : cc x ^ 2 = x ^ 3 / (9 * (x - 1)) := Real.sq_sqrt (by positivity)
  rw [show cc x ^ 4 = (cc x ^ 2) ^ 2 by ring, hc, div_pow,
    div_le_div_iff₀ (by positivity) (by positivity)]
  linarith [mul_nonneg (by positivity : (0 : ℝ) ≤ x ^ 3 * (x - 1))
    (by linarith : (0 : ℝ) ≤ 17 * x ^ 3 - 81)]

end AlgLoss

namespace Ctx

/-- `c(x)² = x³ / (9 (x-1))` and `0 < c(x) ≤ 1` on `2 ≤ x`, `x³ ≤ 9(x-1)` -/
lemma cc_sq {x : ℝ} (hx : 2 ≤ x) : cc x ^ 2 = x ^ 3 / (9 * (x - 1)) := by
  have hz : 0 < x - 1 := by linarith
  exact Real.sq_sqrt (by positivity)
lemma cc_pos {x : ℝ} (hx : 2 ≤ x) : 0 < cc x := by
  have hz : 0 < x - 1 := by linarith
  exact Real.sqrt_pos.mpr (by positivity)
lemma cc_le_one {x : ℝ} (hx : 2 ≤ x) (hxs : x ^ 3 ≤ 9 * (x - 1)) : cc x ≤ 1 := by
  have hz : 0 < x - 1 := by linarith
  exact Real.sqrt_le_one.mpr ((div_le_one (by positivity)).mpr hxs)

/-- the single-edge case: no loss (Cauchy–Schwarz) -/
theorem loss_p1 {x γ : ℝ} (hx : 2 ≤ x) {R : Ctx} (hR : R.Good x γ) :
    γ ≤ R.rho x (Lab.coord x (Lab.p 1)) := by
  obtain ⟨hγ, hT, hF, hI, hB, h1, h2, h3, h4⟩ := hR
  rw [AlgLoss.rho_p1 (by positivity) R, le_div_iff₀ (by positivity)]
  have hA : 0 ≤ R.A := le_trans (mul_nonneg (by linarith) hI) h3
  have hC : 0 ≤ R.C := le_trans (mul_nonneg (by linarith) hB) h4
  -- `AC · IB = AB · IC ≥ (γTF)²`, hence `AC + IB ≥ 2γTF`
  have hprod : (γ * R.T * R.F) ^ 2 ≤ (R.A * R.C) * (R.I * R.B) := by
    have := mul_le_mul h1 h2 (by positivity) (le_trans (by positivity) h1)
    linarith
  have := AlgLoss.two_mul_le_add (mul_nonneg hA hC) (mul_nonneg hI hB) hprod
  linarith

/-- two parallel edges: the loss factor is exactly `c(x)²` -/
theorem loss_p2 {x γ : ℝ} (hx : 2 ≤ x) {R : Ctx} (hR : R.Good x γ) :
    γ * (x ^ 3 / (9 * (x - 1))) ≤ R.rho x (Lab.coord x (Lab.p 2)) := by
  have hz : 0 < x - 1 := by linarith
  obtain ⟨k1, k2⟩ := AlgLoss.good_key hx hR (s := 1 + x) (c := 1) (by linarith) zero_le_one
    (by nlinarith)
  obtain ⟨hγ, hT, hF, hI, hB, h1, h2, h3, h4⟩ := hR
  rw [AlgLoss.rho_p2 (by positivity) R, le_div_iff₀ (by positivity),
    show γ * (x ^ 3 / (9 * (x - 1))) * (R.T + 2 * R.F) ^ 2 =
      γ * x ^ 3 * (R.T + 2 * R.F) ^ 2 / (9 * (x - 1)) by ring, div_le_iff₀ (by positivity)]
  have e1 := mul_le_mul_of_nonneg_left h1 hz.le
  have e2 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ (x - 1) * (1 + x))
  rcases le_total R.F R.T with hTF | hTF
  · -- `9 ((x-1) T² + F²) - x (T + 2F)² = (T - F)((8x-9)(T-F) + (12x-18)F)`
    have hq : 0 ≤ (R.T - R.F) * ((8 * x - 9) * (R.T - R.F) + (12 * x - 18) * R.F) :=
      mul_nonneg (by linarith)
        (add_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_nonneg (by linarith) hF.le))
    have := mul_nonneg (by positivity : 0 ≤ γ * x ^ 2) hq
    linarith
  · -- `9 T² + 9 (x²-1) F² - x² (T + 2F)² = (F - T)((5x²-9)(F-T) + (6x²-18)T)`
    have hq : 0 ≤ (R.F - R.T) * ((5 * x ^ 2 - 9) * (R.F - R.T) + (6 * x ^ 2 - 18) * R.T) :=
      mul_nonneg (by linarith)
        (add_nonneg (mul_nonneg (by nlinarith) (by linarith)) (mul_nonneg (by nlinarith) hT.le))
    have := mul_nonneg (by positivity : 0 ≤ γ * x) hq
    linarith

/-- three parallel edges: the loss factor is `x⁴ / (16 (x-1)) ≥ 1` -/
theorem loss_p3 {x γ : ℝ} (hx : 2 ≤ x) {R : Ctx} (hR : R.Good x γ) :
    γ * (x ^ 4 / (16 * (x - 1))) ≤ R.rho x (Lab.coord x (Lab.p 3)) := by
  have hz : 0 < x - 1 := by linarith
  obtain ⟨k1, k2⟩ := AlgLoss.good_key hx hR (s := 1 + x + x ^ 2) (c := 1) (by positivity)
    zero_le_one (by nlinarith)
  obtain ⟨hγ, hT, hF, hI, hB, h1, h2, h3, h4⟩ := hR
  rw [AlgLoss.rho_p3 (by positivity) R, le_div_iff₀ (by positivity),
    show γ * (x ^ 4 / (16 * (x - 1))) * (R.T + 3 * R.F) ^ 2 =
      γ * x ^ 4 * (R.T + 3 * R.F) ^ 2 / (16 * (x - 1)) by ring, div_le_iff₀ (by positivity)]
  have e1 := mul_le_mul_of_nonneg_left h1 hz.le
  have e2 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ (x - 1) * (1 + x + x ^ 2))
  rcases le_total R.F R.T with hTF | hTF
  · -- `16 ((x-1) T² + F²) - x (T + 3F)² = (T - F)((15x-16)(T-F) + (24x-32)F)`
    have hq : 0 ≤ (R.T - R.F) * ((15 * x - 16) * (R.T - R.F) + (24 * x - 32) * R.F) :=
      mul_nonneg (by linarith)
        (add_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_nonneg (by linarith) hF.le))
    have := mul_nonneg (by positivity : 0 ≤ γ * x ^ 3) hq
    linarith
  · -- `16 T² + 16 (x³-1) F² - x³ (T + 3F)² = (F - T)((7x³-16)(F-T) + (8x³-32)T)`
    have hx3 : (2 : ℝ) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hx 3
    have hq : 0 ≤ (R.F - R.T) * ((7 * x ^ 3 - 16) * (R.F - R.T) + (8 * x ^ 3 - 32) * R.T) :=
      mul_nonneg (by linarith)
        (add_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_nonneg (by linarith) hT.le))
    have := mul_nonneg (by positivity : 0 ≤ γ * x) hq
    linarith

/-- the profile `D` -/
theorem loss_d {x γ : ℝ} (hx : 2 ≤ x) {R : Ctx} (hR : R.Good x γ) :
    γ * (x ^ 3 * (x ^ 2 + x + 1) / (64 * (x - 1))) ≤ R.rho x (Lab.coord x Lab.d) := by
  have hz : 0 < x - 1 := by linarith
  have hsc : 2 * x + 1 ≤ (x + 1) ^ 3 * (x - 1) ^ 2 := by
    have : 1 ≤ (x - 1) ^ 2 := by nlinarith
    calc 2 * x + 1 ≤ (x + 1) ^ 3 := by nlinarith [sq_nonneg (x + 1)]
      _ ≤ (x + 1) ^ 3 * (x - 1) ^ 2 := le_mul_of_one_le_right (by positivity) this
  obtain ⟨k1, k2⟩ := AlgLoss.good_key hx hR (s := (x + 1) ^ 3) (c := 2 * x + 1) (by positivity)
    (by positivity) hsc
  obtain ⟨hγ, hT, hF, hI, hB, h1, h2, h3, h4⟩ := hR
  rw [AlgLoss.rho_d (by positivity) R, le_div_iff₀ (by positivity),
    show γ * (x ^ 3 * (x ^ 2 + x + 1) / (64 * (x - 1))) * (16 * (R.T + R.F) ^ 2) =
      γ * x ^ 3 * (x ^ 2 + x + 1) * (16 * (R.T + R.F) ^ 2) / (64 * (x - 1)) by ring,
    div_le_iff₀ (by positivity)]
  have e1 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ (x - 1) * (x + 1) * (2 * x + 1))
  have e2 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ (x - 1) * (x + 1) ^ 2)
  rcases le_total R.F R.T with hTF | hTF
  · -- `4 ((x²-1) T² + F²) - x² (T + F)² = (T - F)((3x²-4)(T-F) + (4x²-8)F)`
    have hq : 0 ≤ (R.T - R.F) * ((3 * x ^ 2 - 4) * (R.T - R.F) + (4 * x ^ 2 - 8) * R.F) :=
      mul_nonneg (by linarith)
        (add_nonneg (mul_nonneg (by nlinarith) (by linarith)) (mul_nonneg (by nlinarith) hF.le))
    have := mul_nonneg (by positivity : 0 ≤ γ * x * (x ^ 2 + x + 1)) hq
    linarith
  · -- `4 (2x+1) T² + 4 (x+1)² (x-1) F² - x (x²+x+1) (T + F)²`
    -- `= (F - T)((3x³+3x²-5x-4)(F-T) + (4x³+4x²-12x-8)T)`
    have ha : 0 ≤ 3 * x ^ 3 + 3 * x ^ 2 - 5 * x - 4 := by nlinarith
    have hb : 0 ≤ 4 * x ^ 3 + 4 * x ^ 2 - 12 * x - 8 := by nlinarith
    have hq : 0 ≤ (R.F - R.T) * ((3 * x ^ 3 + 3 * x ^ 2 - 5 * x - 4) * (R.F - R.T) +
        (4 * x ^ 3 + 4 * x ^ 2 - 12 * x - 8) * R.T) :=
      mul_nonneg (by linarith)
        (add_nonneg (mul_nonneg ha (by linarith)) (mul_nonneg hb hT.le))
    have := mul_nonneg (by positivity : 0 ≤ γ * x ^ 2) hq
    linarith

/-- the loss lemma in the form used by the induction -/
theorem loss_label {x γ : ℝ} (hx : 2 ≤ x) (hxs : x ^ 3 ≤ 9 * (x - 1)) {R : Ctx}
    (hR : R.Good x γ) {l : Lab} (hl : l ∈ Lab.H) :
    γ * cc x ^ l.size ≤ R.rho x (Lab.coord x l) := by
  have hx0 : x ≠ 0 := by positivity
  have hc0 := cc_pos hx
  have hc1 := cc_le_one hx hxs
  have hγ := hR.hγ
  have hRd := hR.dual
  simp only [Lab.H, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- `ε`
    calc γ * cc x ^ (Lab.p 1).size = γ * cc x := by simp [Lab.size]
      _ ≤ γ * 1 := mul_le_mul_of_nonneg_left hc1 hγ.le
      _ = γ := mul_one γ
      _ ≤ _ := loss_p1 hx hR
  · -- `P₂`
    rw [show (Lab.p 2).size = 2 from rfl, cc_sq hx]
    exact loss_p2 hx hR
  · -- `S₂ = P₂*`
    rw [show (Lab.s 2).size = 2 from rfl, cc_sq hx,
      show Lab.coord x (Lab.s 2) = (Lab.coord x (Lab.p 2)).dual from rfl,
      show R = R.dual.dual from rfl, rho_dual hx0]
    exact loss_p2 hx hRd
  · -- `P₃`
    rw [show (Lab.p 3).size = 3 from rfl]
    calc γ * cc x ^ 3 ≤ γ * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hc0.le hc1) hγ.le
      _ ≤ γ * (x ^ 4 / (16 * (x - 1))) :=
          mul_le_mul_of_nonneg_left (AlgLoss.one_le_lam_p3 hx) hγ.le
      _ ≤ _ := loss_p3 hx hR
  · -- `S₃ = P₃*`
    rw [show (Lab.s 3).size = 3 from rfl,
      show Lab.coord x (Lab.s 3) = (Lab.coord x (Lab.p 3)).dual from rfl,
      show R = R.dual.dual from rfl, rho_dual hx0]
    calc γ * cc x ^ 3 ≤ γ * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hc0.le hc1) hγ.le
      _ ≤ γ * (x ^ 4 / (16 * (x - 1))) :=
          mul_le_mul_of_nonneg_left (AlgLoss.one_le_lam_p3 hx) hγ.le
      _ ≤ _ := loss_p3 hx hRd
  · -- `D`
    rw [show Lab.d.size = 4 from rfl]
    calc γ * cc x ^ 4 ≤ γ * (x ^ 3 * (x ^ 2 + x + 1) / (64 * (x - 1))) :=
          mul_le_mul_of_nonneg_left (AlgLoss.cc_pow_four_le hx) hγ.le
      _ ≤ _ := loss_d hx hR
  · -- `E = D*`
    rw [show Lab.ee.size = 4 from rfl,
      show Lab.coord x Lab.ee = (Lab.coord x Lab.d).dual from rfl,
      show R = R.dual.dual from rfl, rho_dual hx0]
    calc γ * cc x ^ 4 ≤ γ * (x ^ 3 * (x ^ 2 + x + 1) / (64 * (x - 1))) :=
          mul_le_mul_of_nonneg_left (AlgLoss.cc_pow_four_le hx) hγ.le
      _ ≤ _ := loss_d hx hRd

end Ctx

end Results.TutteThreshold
