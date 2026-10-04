import Results.TutteThreshold.Solution.Lab

/-!
# Joint replacements

`ReplOK x N terms` says that the patch `N` is jointly replaced by the profiles of `terms` with
weights `(u, v, w)`: `w² ≤ u v`, the two basis comparisons and the four axis comparisons.
-/

namespace Results.TutteThreshold

structure ReplTerm where
  lab : Lab
  u : ℚ
  v : ℚ
  w : ℚ

/-- the conditions (weights), (trees) and (axes) of the joint replacement lemma -/
def ReplOK (x : ℝ) (N : Coord) (terms : List ReplTerm) : Prop :=
  (∀ t ∈ terms, 0 < t.u ∧ 0 < t.v ∧ 0 < t.w ∧ ((t.w : ℝ)) ^ 2 ≤ (t.u : ℝ) * t.v) ∧
  N.T ≤ (terms.map fun t => (t.w : ℝ) * (t.lab.coord x).T).sum ∧
  N.F ≤ (terms.map fun t => (t.w : ℝ) * (t.lab.coord x).F).sum ∧
  (terms.map fun t => (t.u : ℝ) * (t.lab.coord x).A).sum ≤ N.A ∧
  (terms.map fun t => (t.u : ℝ) * ((t.lab.coord x).A + (t.lab.coord x).I)).sum ≤ N.A + N.I ∧
  (terms.map fun t => (t.v : ℝ) * (t.lab.coord x).C).sum ≤ N.C ∧
  (terms.map fun t => (t.v : ℝ) * ((t.lab.coord x).C + (t.lab.coord x).B)).sum ≤ N.C + N.B

namespace Ctx

/-- Cauchy–Schwarz over a list: `γ Z_j² ≤ X_j Y_j` with `X_j, Y_j ≥ 0` gives
`γ (∑ Z_j)² ≤ (∑ X_j)(∑ Y_j)` -/
private lemma repl_cs {α : Type*} {γ : ℝ} (hγ : 0 ≤ γ) (X Y Z : α → ℝ) :
    ∀ l : List α, (∀ a ∈ l, 0 ≤ X a ∧ 0 ≤ Y a ∧ γ * Z a ^ 2 ≤ X a * Y a) →
      γ * (l.map Z).sum ^ 2 ≤ (l.map X).sum * (l.map Y).sum
  | [], _ => by simp
  | a :: l, h => by
    obtain ⟨hXa, hYa, ha⟩ := h a List.mem_cons_self
    have hl : ∀ b ∈ l, 0 ≤ X b ∧ 0 ≤ Y b ∧ γ * Z b ^ 2 ≤ X b * Y b :=
      fun b hb => h b (List.mem_cons_of_mem a hb)
    have ih := repl_cs hγ X Y Z l hl
    have hX : 0 ≤ (l.map X).sum :=
      List.sum_nonneg fun y hy => by
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
        exact (hl b hb).1
    have hY : 0 ≤ (l.map Y).sum :=
      List.sum_nonneg fun y hy => by
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
        exact (hl b hb).2.1
    simp only [List.map_cons, List.sum_cons]
    -- the cross term: `2 γ Z_a ∑ Z ≤ X_a ∑ Y + Y_a ∑ X` (AM–GM)
    have hr : (γ * Z a * (l.map Z).sum) ^ 2 ≤
        (X a * (l.map Y).sum) * ((l.map X).sum * Y a) :=
      calc (γ * Z a * (l.map Z).sum) ^ 2 = (γ * Z a ^ 2) * (γ * (l.map Z).sum ^ 2) := by ring
        _ ≤ (X a * Y a) * (γ * (l.map Z).sum ^ 2) := by gcongr
        _ ≤ (X a * Y a) * ((l.map X).sum * (l.map Y).sum) := by gcongr
        _ = (X a * (l.map Y).sum) * ((l.map X).sum * Y a) := by ring
    have h2 : 2 * (γ * Z a * (l.map Z).sum) ≤ X a * (l.map Y).sum + (l.map X).sum * Y a := by
      nlinarith [sq_nonneg (X a * (l.map Y).sum - (l.map X).sum * Y a),
        mul_nonneg hXa hY, mul_nonneg hX hYa]
    nlinarith

/-- a list sum of weighted linear combinations -/
private lemma repl_sum_lin {α : Type*} (l : List α) (c f g h : α → ℝ) (a b : ℝ)
    (hh : ∀ t ∈ l, h t = a * f t + b * g t) :
    (l.map fun t => c t * h t).sum =
      a * (l.map fun t => c t * f t).sum + b * (l.map fun t => c t * g t).sum := by
  induction l with
  | nil => simp
  | cons t l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih fun s hs => hh s (List.mem_cons_of_mem t hs), hh t List.mem_cons_self]
    ring

/-- the joint replacement lemma for terms with valid coordinates -/
private lemma replace_core {x : ℝ} (hx : 2 ≤ x) {R : Ctx} (hR : R.Ok x) {N : Coord}
    (hN : 0 < N.T ∧ 0 < N.F) {terms : List ReplTerm} (hok : ReplOK x N terms)
    (hval : ∀ t ∈ terms, Coord.Valid x (t.lab.coord x)) {γ : ℝ} (hγ : 0 < γ)
    (h : ∀ t ∈ terms, γ ≤ R.rho x (t.lab.coord x)) :
    γ ≤ R.rho x N := by
  obtain ⟨hT, hF, hA, hI, hB, hC, h3, h4⟩ := hR
  obtain ⟨hw, hNT, hNF, hNA, hNAI, hNC, hNCB⟩ := hok
  obtain ⟨hNT0, hNF0⟩ := hN
  have hx0 : 0 < x := by linarith
  -- the closure formulas as combinations with nonnegative coefficients
  have eb : ∀ p : Coord, R.b p = R.T * p.F + R.F * p.T := fun p => by unfold Ctx.b; ring
  have ea : ∀ p : Coord, R.al x p = R.I * p.A + (R.A - (x - 1) * R.I) / x * (p.A + p.I) := by
    intro p; unfold Ctx.al; field_simp; ring
  have ec : ∀ p : Coord, R.be x p = R.B * p.C + (R.C - (x - 1) * R.B) / x * (p.C + p.B) := by
    intro p; unfold Ctx.be; field_simp; ring
  have hKa : 0 ≤ (R.A - (x - 1) * R.I) / x := div_nonneg (by linarith) hx0.le
  have hKc : 0 ≤ (R.C - (x - 1) * R.B) / x := div_nonneg (by linarith) hx0.le
  -- the closures of the terms: `α_j, β_j ≥ 0` and `γ b_j² ≤ α_j β_j`
  have hterm : ∀ t ∈ terms, 0 ≤ R.al x (t.lab.coord x) ∧ 0 ≤ R.be x (t.lab.coord x) ∧
      γ * R.b (t.lab.coord x) ^ 2 ≤ R.al x (t.lab.coord x) * R.be x (t.lab.coord x) := by
    intro t ht
    obtain ⟨vT, vF, vI, vB, vA, vC⟩ := hval t ht
    have hpA : 0 ≤ (t.lab.coord x).A := by nlinarith
    have hpC : 0 ≤ (t.lab.coord x).C := by nlinarith
    have hpb : 0 < R.b (t.lab.coord x) := by rw [eb]; positivity
    refine ⟨?_, ?_, ?_⟩
    · rw [ea]
      exact add_nonneg (mul_nonneg hI hpA) (mul_nonneg hKa (add_nonneg hpA vI))
    · rw [ec]
      exact add_nonneg (mul_nonneg hB hpC) (mul_nonneg hKc (add_nonneg hpC vB))
    · have := h t ht
      unfold Ctx.rho at this
      rwa [le_div_iff₀ (by positivity)] at this
  -- (trees): `b_N ≤ ∑ w_j b_j`
  have hb : R.b N ≤ (terms.map fun t => (t.w : ℝ) * R.b (t.lab.coord x)).sum := by
    rw [repl_sum_lin terms (fun t => (t.w : ℝ)) (fun t => (t.lab.coord x).F)
      (fun t => (t.lab.coord x).T) (fun t => R.b (t.lab.coord x)) R.T R.F (fun t _ => eb _),
      eb N]
    exact add_le_add (mul_le_mul_of_nonneg_left hNF hT.le) (mul_le_mul_of_nonneg_left hNT hF.le)
  -- (axes): `∑ u_j α_j ≤ α_N` and `∑ v_j β_j ≤ β_N`
  have ha : (terms.map fun t => (t.u : ℝ) * R.al x (t.lab.coord x)).sum ≤ R.al x N := by
    rw [repl_sum_lin terms (fun t => (t.u : ℝ)) (fun t => (t.lab.coord x).A)
      (fun t => (t.lab.coord x).A + (t.lab.coord x).I) (fun t => R.al x (t.lab.coord x))
      R.I ((R.A - (x - 1) * R.I) / x) (fun t _ => ea _), ea N]
    exact add_le_add (mul_le_mul_of_nonneg_left hNA hI) (mul_le_mul_of_nonneg_left hNAI hKa)
  have hc : (terms.map fun t => (t.v : ℝ) * R.be x (t.lab.coord x)).sum ≤ R.be x N := by
    rw [repl_sum_lin terms (fun t => (t.v : ℝ)) (fun t => (t.lab.coord x).C)
      (fun t => (t.lab.coord x).C + (t.lab.coord x).B) (fun t => R.be x (t.lab.coord x))
      R.B ((R.C - (x - 1) * R.B) / x) (fun t _ => ec _), ec N]
    exact add_le_add (mul_le_mul_of_nonneg_left hNC hB) (mul_le_mul_of_nonneg_left hNCB hKc)
  -- Cauchy–Schwarz: `γ (∑ w_j b_j)² ≤ (∑ u_j α_j)(∑ v_j β_j)`
  have hcs := repl_cs hγ.le (fun t => (t.u : ℝ) * R.al x (t.lab.coord x))
    (fun t => (t.v : ℝ) * R.be x (t.lab.coord x)) (fun t => (t.w : ℝ) * R.b (t.lab.coord x))
    terms (by
      intro t ht
      obtain ⟨hu, hv, -, hwuv⟩ := hw t ht
      obtain ⟨hal, hbe, hρ⟩ := hterm t ht
      have hu' : (0 : ℝ) < t.u := by exact_mod_cast hu
      have hv' : (0 : ℝ) < t.v := by exact_mod_cast hv
      refine ⟨mul_nonneg hu'.le hal, mul_nonneg hv'.le hbe, ?_⟩
      calc γ * ((t.w : ℝ) * R.b (t.lab.coord x)) ^ 2
          = (t.w : ℝ) ^ 2 * (γ * R.b (t.lab.coord x) ^ 2) := by ring
        _ ≤ ((t.u : ℝ) * t.v) * (γ * R.b (t.lab.coord x) ^ 2) := by gcongr
        _ ≤ ((t.u : ℝ) * t.v) * (R.al x (t.lab.coord x) * R.be x (t.lab.coord x)) := by gcongr
        _ = (t.u : ℝ) * R.al x (t.lab.coord x) * ((t.v : ℝ) * R.be x (t.lab.coord x)) := by
          ring)
  have hX0 : 0 ≤ (terms.map fun t => (t.u : ℝ) * R.al x (t.lab.coord x)).sum :=
    List.sum_nonneg fun y hy => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
      exact mul_nonneg (by exact_mod_cast (hw t ht).1.le) (hterm t ht).1
  have hY0 : 0 ≤ (terms.map fun t => (t.v : ℝ) * R.be x (t.lab.coord x)).sum :=
    List.sum_nonneg fun y hy => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
      exact mul_nonneg (by exact_mod_cast (hw t ht).2.1.le) (hterm t ht).2.1
  have hbN : 0 < R.b N := by rw [eb]; positivity
  have key : γ * R.b N ^ 2 ≤ R.al x N * R.be x N :=
    calc γ * R.b N ^ 2
        ≤ γ * (terms.map fun t => (t.w : ℝ) * R.b (t.lab.coord x)).sum ^ 2 := by gcongr
      _ ≤ _ := hcs
      _ ≤ R.al x N * R.be x N := mul_le_mul ha hc hY0 (hX0.trans ha)
  unfold Ctx.rho
  rw [le_div_iff₀ (by positivity)]
  exact key

/-- the joint replacement lemma at the level of closures -/
theorem replace_alg {x : ℝ} (hx : 2 ≤ x) {R : Ctx} (hR : R.Ok x) {N : Coord}
    (hN : 0 < N.T ∧ 0 < N.F) {terms : List ReplTerm} (hok : ReplOK x N terms)
    (hlab : ∀ t ∈ terms, 1 ≤ t.lab.size) {γ : ℝ} (hγ : 0 < γ)
    (h : ∀ t ∈ terms, γ ≤ R.rho x (t.lab.coord x)) (hne : terms ≠ []) :
    γ ≤ R.rho x N := by
  -- `hne` also follows from `hN` and the tree comparison of `hok`
  obtain ⟨_, _, rfl⟩ := List.exists_cons_of_ne_nil hne
  exact replace_core hx hR hN hok (fun t ht => Lab.coord_valid hx (hlab t ht)) hγ h

end Ctx

end Results.TutteThreshold
