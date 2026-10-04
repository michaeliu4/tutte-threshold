import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic

/-!
# Closed forms for `N_k`

With `u` the number of occupied parallel pairs,
`T_{N_k}(x,y) = ∑_u C(3k,u) (x-1)^{2k - min(2k,u)} (y-1)^{u - min(2k,u)} (1+y)^u`.
Its three evaluations used for Theorem 1.3 are `Ak` (at `(x,0)`), `Bk` (at `(0,x)`) and
`bk` (at `(1,1)`).
-/

namespace Results.TutteThreshold

open Finset

/-- `T_{N_k}(x, 0)` -/
noncomputable def Ak (k : ℕ) (x : ℝ) : ℝ :=
  ∑ u ∈ range (3 * k + 1),
    (Nat.choose (3 * k) u : ℝ) * (x - 1) ^ (2 * k - min (2 * k) u) *
      ((-1 : ℝ) ^ (u - min (2 * k) u))

/-- `T_{N_k}(0, x)` -/
noncomputable def Bk (k : ℕ) (x : ℝ) : ℝ :=
  ∑ u ∈ range (3 * k + 1),
    (Nat.choose (3 * k) u : ℝ) * ((-1 : ℝ) ^ (2 * k - min (2 * k) u)) *
      (x - 1) ^ (u - min (2 * k) u) * (1 + x) ^ u

/-- `T_{N_k}(1, 1) = 4^k C(3k, k)` -/
noncomputable def bk (k : ℕ) : ℝ := 4 ^ k * (Nat.choose (3 * k) k : ℝ)

/-- the ratio of `N_k` -/
noncomputable def rhoK (k : ℕ) (x : ℝ) : ℝ := Ak k x * Bk k x / (bk k) ^ 2

/-- `L(x) = x³/(x-1)` -/
noncomputable def Lx (x : ℝ) : ℝ := x ^ 3 / (x - 1)

end Results.TutteThreshold
