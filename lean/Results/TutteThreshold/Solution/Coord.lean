import Results.TutteThreshold.Solution.Zsum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Ring.GeomSum

/-!
# Pointed-matroid coordinates, profiles and weights

For fixed `x` put `z = x - 1`.  A pointed patch has six coordinates `(T,F,A,I,C,B)`:
`T = b(L∖e)`, `F = b(L/e)`, `A = T_{L∖e}(x,0)`, `I = T_{L/e}(x,0)`, `C = T_{L/e}(0,x)`,
`B = T_{L∖e}(0,x)`.  Inside a weighted rank sum the patch acts on an element through three weight
pairs (bases, axis `y = 0`, axis `x = 0`).
-/

namespace Results.TutteThreshold

structure Coord where
  T : ℝ
  F : ℝ
  A : ℝ
  I : ℝ
  C : ℝ
  B : ℝ

namespace Coord

/-- weights for the evaluation at `(1,1)` (number of bases) -/
def wb (c : Coord) : ℝ × ℝ := (c.F, c.T)

/-- weights for the evaluation on the axis `y = 0` -/
noncomputable def wa (x : ℝ) (c : Coord) : ℝ × ℝ :=
  ((c.A + c.I) / x, (c.A - (x - 1) * c.I) / x)

/-- weights for the evaluation on the axis `x = 0` -/
noncomputable def wc (x : ℝ) (c : Coord) : ℝ × ℝ :=
  ((c.C - (x - 1) * c.B) / x, (c.C + c.B) / x)

/-- duality: `(T,F,A,I,C,B) ↦ (F,T,C,B,A,I)` -/
def dual (c : Coord) : Coord := ⟨c.F, c.T, c.C, c.B, c.A, c.I⟩

@[simp] lemma dual_dual (c : Coord) : c.dual.dual = c := rfl

/-- coordinates of the parallel composition (equivalently of the two-sum of the two patches
closed by a common element: `T = b(J)`, `A = T_J(x,0)`, `B = T_J(0,x)`) -/
noncomputable def par (x : ℝ) (c d : Coord) : Coord where
  T := c.T * d.F + c.F * d.T
  F := c.F * d.F
  A := (c.A * d.A + c.A * d.I + c.I * d.A - (x - 1) * c.I * d.I) / x
  I := c.I * d.I
  C := c.C * d.C
  B := (c.C * d.C + c.C * d.B + c.B * d.C - (x - 1) * c.B * d.B) / x

/-- validity: the hypotheses under which the weights are admissible and positive -/
def Valid (x : ℝ) (c : Coord) : Prop :=
  0 < c.T ∧ 0 < c.F ∧ 0 ≤ c.I ∧ 0 ≤ c.B ∧ (x - 1) * c.I ≤ c.A ∧ (x - 1) * c.B ≤ c.C

end Coord

/-- the six numbers of an exterior context (a skeleton with a distinguished element removed or
contracted) -/
structure Ctx where
  T : ℝ
  F : ℝ
  A : ℝ
  I : ℝ
  C : ℝ
  B : ℝ

namespace Ctx

def dual (R : Ctx) : Ctx := ⟨R.F, R.T, R.C, R.B, R.A, R.I⟩

/-- number of bases of the closure of the patch `p` in the exterior `R` -/
def b (R : Ctx) (p : Coord) : ℝ := p.F * R.T + p.T * R.F

/-- axis `y = 0` value of the closure -/
noncomputable def al (x : ℝ) (R : Ctx) (p : Coord) : ℝ :=
  (R.A * (p.A + p.I) + R.I * (p.A - (x - 1) * p.I)) / x

/-- axis `x = 0` value of the closure -/
noncomputable def be (x : ℝ) (R : Ctx) (p : Coord) : ℝ :=
  (R.B * (p.C - (x - 1) * p.B) + R.C * (p.C + p.B)) / x

/-- the ratio of the closure -/
noncomputable def rho (x : ℝ) (R : Ctx) (p : Coord) : ℝ :=
  R.al x p * R.be x p / (R.b p) ^ 2

/-- the hypotheses of a branch step: both branches have ratio at least `γ`, plus the broken
circuit inequalities -/
structure Good (x γ : ℝ) (R : Ctx) : Prop where
  hγ : 0 < γ
  hT : 0 < R.T
  hF : 0 < R.F
  hI : 0 ≤ R.I
  hB : 0 ≤ R.B
  h1 : γ * R.T ^ 2 ≤ R.A * R.B
  h2 : γ * R.F ^ 2 ≤ R.I * R.C
  h3 : (x - 1) * R.I ≤ R.A
  h4 : (x - 1) * R.B ≤ R.C

end Ctx

/-- the scaling constant `c(x) = √(x³ / (9 (x-1)))` -/
noncomputable def cc (x : ℝ) : ℝ := Real.sqrt (x ^ 3 / (9 * (x - 1)))

namespace Coord

/-! ### Identities for the weights (frozen interface) -/

lemma par_comm {x : ℝ} (c d : Coord) : par x c d = par x d c := by
  simp only [par, Coord.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring⟩

lemma wb_par (x : ℝ) (c d : Coord) : (par x c d).wb = RkMat.mergeW 0 c.wb d.wb := by
  refine Prod.ext rfl ?_
  simp only [wb, par, RkMat.mergeW]
  ring

lemma wa_par {x : ℝ} (hx : x ≠ 0) (c d : Coord) :
    (par x c d).wa x = RkMat.mergeW (-1) (c.wa x) (d.wa x) := by
  simp only [wa, par, RkMat.mergeW, Prod.mk.injEq]
  constructor <;> field_simp <;> ring

lemma wc_par {x : ℝ} (hx : x ≠ 0) (c d : Coord) :
    (par x c d).wc x = RkMat.mergeW (x - 1) (c.wc x) (d.wc x) := by
  simp only [wc, par, RkMat.mergeW, Prod.mk.injEq]
  constructor <;> field_simp <;> ring

lemma wb_dual (c : Coord) : c.dual.wb = (c.wb.2, c.wb.1) := rfl

lemma wa_dual (x : ℝ) (c : Coord) : c.dual.wa x = ((c.wc x).2, (c.wc x).1) := rfl

lemma wc_dual (x : ℝ) (c : Coord) : c.dual.wc x = ((c.wa x).2, (c.wa x).1) := rfl

lemma Valid.dual {x : ℝ} {c : Coord} (h : c.Valid x) : c.dual.Valid x := by
  obtain ⟨hT, hF, hI, hB, hA, hC⟩ := h
  exact ⟨hF, hT, hB, hI, hC, hA⟩

lemma Valid.wb_pos {x : ℝ} {c : Coord} (h : c.Valid x) : 0 < c.wb.1 ∧ 0 < c.wb.2 :=
  ⟨h.2.1, h.1⟩

lemma Valid.wa_range {x : ℝ} (hx : 2 ≤ x) {c : Coord} (h : c.Valid x) :
    0 ≤ (c.wa x).2 ∧ (c.wa x).2 ≤ (c.wa x).1 := by
  obtain ⟨-, -, hI, -, hA, -⟩ := h
  have hx0 : 0 < x := by linarith
  refine ⟨div_nonneg (by linarith) hx0.le, div_le_div_of_nonneg_right ?_ hx0.le⟩
  nlinarith [mul_nonneg hx0.le hI]

lemma Valid.wc_range {x : ℝ} (hx : 2 ≤ x) {c : Coord} (h : c.Valid x) :
    0 ≤ (c.wc x).1 ∧ (c.wc x).1 ≤ (c.wc x).2 := by
  obtain ⟨-, -, -, hB, -, hC⟩ := h
  have hx0 : 0 < x := by linarith
  refine ⟨div_nonneg (by linarith) hx0.le, div_le_div_of_nonneg_right ?_ hx0.le⟩
  nlinarith [mul_nonneg hx0.le hB]

end Coord

namespace Ctx

/-- the hypotheses on an exterior context that make the closure formulas monotone -/
structure Ok (x : ℝ) (R : Ctx) : Prop where
  hT : 0 < R.T
  hF : 0 < R.F
  hA : 0 ≤ R.A
  hI : 0 ≤ R.I
  hB : 0 ≤ R.B
  hC : 0 ≤ R.C
  h3 : (x - 1) * R.I ≤ R.A
  h4 : (x - 1) * R.B ≤ R.C

lemma Good.ok {x γ : ℝ} {R : Ctx} (hx : 2 ≤ x) (h : R.Good x γ) : R.Ok x :=
  ⟨h.hT, h.hF, le_trans (mul_nonneg (by linarith) h.hI) h.h3, h.hI, h.hB,
    le_trans (mul_nonneg (by linarith) h.hB) h.h4, h.h3, h.h4⟩

lemma Good.dual {x γ : ℝ} {R : Ctx} (h : R.Good x γ) : R.dual.Good x γ :=
  ⟨h.hγ, h.hF, h.hT, h.hB, h.hI, by simpa only [Ctx.dual, mul_comm R.C] using h.h2,
    by simpa only [Ctx.dual, mul_comm R.B] using h.h1, h.h4, h.h3⟩

lemma Ok.dual {x : ℝ} {R : Ctx} (h : R.Ok x) : R.dual.Ok x :=
  ⟨h.hF, h.hT, h.hC, h.hB, h.hI, h.hA, h.h4, h.h3⟩

/-- the number of bases of a closure is invariant under duality -/
lemma coord_b_dual (R : Ctx) (p : Coord) : R.dual.b p.dual = R.b p := by
  simp only [b, dual, Coord.dual]
  ring

/-- duality exchanges the two axis evaluations of a closure -/
lemma coord_al_dual (x : ℝ) (R : Ctx) (p : Coord) : R.dual.al x p.dual = R.be x p := by
  simp only [al, be, dual, Coord.dual]
  ring

/-- duality exchanges the two axis evaluations of a closure -/
lemma coord_be_dual (x : ℝ) (R : Ctx) (p : Coord) : R.dual.be x p.dual = R.al x p := by
  simp only [al, be, dual, Coord.dual]
  ring

lemma rho_dual {x : ℝ} (hx : x ≠ 0) (R : Ctx) (p : Coord) :
    R.dual.rho x p.dual = R.rho x p := by
  have _ : x ≠ 0 := hx  -- not needed: the identity holds for every `x`
  rw [rho, rho, coord_b_dual, coord_al_dual, coord_be_dual, mul_comm]

end Ctx

end Results.TutteThreshold
