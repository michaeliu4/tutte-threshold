import Results.TutteThreshold.Solution.Lab

/-!
# Parallel classes of at least four real edges

For an exterior `R` with `Ctx.Ok`, replacing `P_k` by `P_{k-2}` (`k ≥ 4`) multiplies the ratio by at
most `x²/4`, i.e. `ρ(R[P_k]) ≥ (x²/4) ρ(R[P_{k-2}])`.  The series version follows by duality.
-/

namespace Results.TutteThreshold

namespace Ctx

/-- `B` of `P_{n+3}` in terms of `B` of `P_{n+1}`: `B_{n+3} = x + x² + x² B_{n+1}` -/
private lemma reduce_B_add_two (x : ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 2), x ^ (i + 1) =
      x + x ^ 2 + x ^ 2 * ∑ i ∈ Finset.range n, x ^ (i + 1) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.mul_sum]
  have : ∀ i ∈ Finset.range n, x ^ (i + 1 + 1 + 1) = x ^ 2 * x ^ (i + 1) := fun i _ => by ring
  rw [Finset.sum_congr rfl this]
  ring

/-- `(x - 1) B_{n+1} = x^{n+1} - x` -/
private lemma reduce_B_mul (x : ℝ) (n : ℕ) :
    (x - 1) * ∑ i ∈ Finset.range n, x ^ (i + 1) = x ^ (n + 1) - x := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, mul_add, ih]; ring

/-- comparison of two closures with the same `α`: `b ≤ 2b'` and `x² β' ≤ β` -/
private lemma reduce_key {x a c c' b b' : ℝ} (ha : 0 ≤ a) (hc' : 0 ≤ c') (hb : 0 < b)
    (hbb : b ≤ 2 * b') (hc : x ^ 2 * c' ≤ c) :
    x ^ 2 / 4 * (a * c' / b' ^ 2) ≤ a * c / b ^ 2 := by
  have hb' : 0 < b' := by linarith
  have hc0 : 0 ≤ c := le_trans (by positivity) hc
  calc x ^ 2 / 4 * (a * c' / b' ^ 2) = a * (x ^ 2 * c') / (2 * b') ^ 2 := by
        field_simp; ring
    _ ≤ a * c / (2 * b') ^ 2 := by gcongr
    _ ≤ a * c / b ^ 2 := by gcongr

/-- `ρ(R[P_k]) ≥ (x²/4) ρ(R[P_{k-2}])` for `k ≥ 4` -/
theorem reduce_p {x : ℝ} (hx : 2 ≤ x) {R : Ctx} (hR : R.Ok x) {k : ℕ} (hk : 4 ≤ k) :
    x ^ 2 / 4 * R.rho x (Lab.pk x (k - 2)) ≤ R.rho x (Lab.pk x k) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 3 := ⟨k - 3, by omega⟩
  obtain ⟨hT, hF, hA, hI, hB, hC, -, h4⟩ := hR
  have hx0 : 0 < x := by linarith
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  set s := ∑ i ∈ Finset.range n, x ^ (i + 1)
  have hs : 0 ≤ s := Finset.sum_nonneg fun i _ => by positivity
  have hsx : x ^ (n + 1) - (x - 1) * s = x := by rw [reduce_B_mul]; ring
  have e1 : Lab.pk x (n + 3) = ⟨(n + 3 : ℕ), 1, x, 0, x ^ (n + 3), x + x ^ 2 + x ^ 2 * s⟩ := by
    rw [Lab.pk, show n + 3 - 1 = n + 2 by omega, reduce_B_add_two]
  have e2 : Lab.pk x (n + 3 - 2) = ⟨(n + 1 : ℕ), 1, x, 0, x ^ (n + 1), s⟩ := by
    rw [show n + 3 - 2 = n + 1 by omega, Lab.pk, Nat.add_sub_cancel]
  rw [e1, e2]
  simp only [Ctx.rho, Ctx.al, Ctx.be, Ctx.b]
  apply reduce_key
  · simp only [add_zero, mul_zero, sub_zero]; positivity
  · rw [hsx]; positivity
  · push_cast; positivity
  · push_cast; nlinarith
  · -- `β_k - x² β_{k-2} = (1 + x)(C_R - (x - 1) B_R)`
    have : (R.B * (x ^ (n + 3) - (x - 1) * (x + x ^ 2 + x ^ 2 * s)) +
          R.C * (x ^ (n + 3) + (x + x ^ 2 + x ^ 2 * s))) / x -
        x ^ 2 * ((R.B * (x ^ (n + 1) - (x - 1) * s) + R.C * (x ^ (n + 1) + s)) / x) =
        (1 + x) * (R.C - (x - 1) * R.B) := by
      field_simp; ring
    nlinarith

/-- `ρ(R[S_k]) ≥ (x²/4) ρ(R[S_{k-2}])` for `k ≥ 4` (dual of `reduce_p`) -/
theorem reduce_s {x : ℝ} (hx : 2 ≤ x) {R : Ctx} (hR : R.Ok x) {k : ℕ} (hk : 4 ≤ k) :
    x ^ 2 / 4 * R.rho x (Lab.pk x (k - 2)).dual ≤ R.rho x (Lab.pk x k).dual := by
  have hx0 : x ≠ 0 := by positivity
  have e : ∀ p : Coord, R.rho x p.dual = R.dual.rho x p := fun p => rho_dual hx0 R.dual p
  rw [e, e]
  exact reduce_p hx hR.dual hk

end Ctx

end Results.TutteThreshold
