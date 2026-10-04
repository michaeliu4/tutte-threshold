import Results.TutteThreshold.Solution.Coord

/-!
# Profile labels

`p k` is `k` parallel real edges (`p 1` is a single edge `ε`), `s k` is a path of `k` real edges,
`d = S(P₂,P₂)` and `ee = P(S₂,S₂)`.  The seven retained profiles are
`ε, P₂, S₂, P₃, S₃, D, E`.
-/

namespace Results.TutteThreshold

inductive Lab
  | p (k : ℕ)
  | s (k : ℕ)
  | d
  | ee
  deriving DecidableEq

namespace Lab

/-- number of real edges -/
def size : Lab → ℕ
  | p k => k
  | s k => k
  | d => 4
  | ee => 4

/-- planar duality: `P_k ↔ S_k` (`k ≠ 1`; the single edge is self-dual), `D ↔ E` -/
def dual : Lab → Lab
  | p k => if k = 1 then p 1 else s k
  | s k => if k = 1 then p 1 else p k
  | d => ee
  | ee => d

/-- the seven profiles `ε, P₂, S₂, P₃, S₃, D, E` -/
def H : List Lab := [p 1, p 2, s 2, p 3, s 3, d, ee]

/-- labels with at least four real edges in one parallel or series class -/
def Big (l : Lab) : Prop := ∃ k, 4 ≤ k ∧ (l = p k ∨ l = s k)

/-- the labels occurring in the induction: the seven profiles and the big classes -/
def OK (l : Lab) : Prop := l ∈ H ∨ Big l

/-- coordinates of `k` parallel edges -/
noncomputable def pk (x : ℝ) (k : ℕ) : Coord :=
  ⟨k, 1, x, 0, x ^ k, ∑ i ∈ Finset.range (k - 1), x ^ (i + 1)⟩

/-- coordinates of a label -/
noncomputable def coord (x : ℝ) : Lab → Coord
  | p k => pk x k
  | s k => (pk x k).dual
  | d => ⟨4, 4, x ^ 2, x, x ^ 3 + x ^ 2 + x, x ^ 2⟩
  | ee => ⟨4, 4, x ^ 3 + x ^ 2 + x, x ^ 2, x ^ 2, x⟩

lemma size_dual (l : Lab) : l.dual.size = l.size := by
  cases l with
  | p k => by_cases hk : k = 1 <;> simp [dual, size, hk]
  | s k => by_cases hk : k = 1 <;> simp [dual, size, hk]
  | d => rfl
  | ee => rfl

/-- counterexample to `dual_dual`: the non-canonical single edge `s 1` is dualised to `p 1` -/
lemma lab_not_dual_dual_s_one : (s 1).dual.dual ≠ s 1 := by decide

/-- `dual` is an involution away from `s 1` -/
lemma lab_dual_dual_of_ne {l : Lab} (h : l ≠ s 1) : l.dual.dual = l := by
  cases l with
  | p k => by_cases hk : k = 1 <;> simp [dual, hk]
  | s k =>
    have hk : k ≠ 1 := by
      rintro rfl
      exact h rfl
    simp [dual, hk]
  | d => rfl
  | ee => rfl

/-- `dual` is an involution away from the non-canonical single edge `s 1` (corrected form of the
frozen `dual_dual`, which is false for `l = s 1`) -/
lemma dual_dual {l : Lab} (h : l ≠ s 1) : l.dual.dual = l := lab_dual_dual_of_ne h

/-- `dual` is an involution on the labels of the induction -/
lemma OK.lab_dual_dual {l : Lab} (h : l.OK) : l.dual.dual = l := by
  refine lab_dual_dual_of_ne ?_
  rintro rfl
  rcases h with h | ⟨k, hk, h' | h'⟩
  · simp [H] at h
  · simp at h'
  · simp only [s.injEq] at h'
    omega

lemma coord_dual (x : ℝ) (l : Lab) : l.dual.coord x = (l.coord x).dual := by
  cases l with
  | p k =>
    by_cases hk : k = 1
    · subst hk
      simp [dual, coord, pk, Coord.dual]
    · simp [dual, coord, hk]
  | s k =>
    by_cases hk : k = 1
    · subst hk
      simp [dual, coord]
    · simp [dual, coord, hk]
  | d => rfl
  | ee => rfl

/-- the coordinates of `l.dual.dual` and `l` agree for every label (including `s 1`) -/
lemma lab_coord_dual_dual (x : ℝ) (l : Lab) : l.dual.dual.coord x = l.coord x := by
  rw [coord_dual, coord_dual, Coord.dual_dual]

lemma size_pos_of_mem_H {l : Lab} (h : l ∈ H) : 1 ≤ l.size := by
  have key : ∀ l ∈ H, 1 ≤ l.size := by decide
  exact key l h

lemma dual_mem_H {l : Lab} (h : l ∈ H) : l.dual ∈ H := by
  have key : ∀ l ∈ H, l.dual ∈ H := by decide
  exact key l h

lemma dual_OK {l : Lab} (h : l.OK) : l.dual.OK := by
  rcases h with h | ⟨k, hk, rfl | rfl⟩
  · exact Or.inl (dual_mem_H h)
  · exact Or.inr ⟨k, hk, Or.inr (by simp [dual, show k ≠ 1 by omega])⟩
  · exact Or.inr ⟨k, hk, Or.inl (by simp [dual, show k ≠ 1 by omega])⟩

lemma OK.size_pos {l : Lab} (h : l.OK) : 1 ≤ l.size := by
  rcases h with h | ⟨k, hk, rfl | rfl⟩
  · exact size_pos_of_mem_H h
  · exact (show 1 ≤ k by omega)
  · exact (show 1 ≤ k by omega)

open Finset in
/-- `∑_{i<n} x^{i+1} = x ∑_{i<n} x^i` -/
lemma lab_sum_pow_succ (x : ℝ) (n : ℕ) :
    ∑ i ∈ range n, x ^ (i + 1) = x * ∑ i ∈ range n, x ^ i := by
  rw [mul_sum]
  exact sum_congr rfl fun i _ => pow_succ' x i

open Finset in
/-- telescoping: `(x - 1) ∑_{i<n} x^{i+1} = x^{n+1} - x` -/
lemma lab_sub_one_mul_sum (x : ℝ) (n : ℕ) :
    (x - 1) * ∑ i ∈ range n, x ^ (i + 1) = x ^ (n + 1) - x := by
  rw [lab_sum_pow_succ, show (x - 1) * (x * ∑ i ∈ range n, x ^ i) =
    x * ((∑ i ∈ range n, x ^ i) * (x - 1)) by ring, geom_sum_mul]
  ring

open Finset in
/-- `1 + ... + x^{m+n} = (1 + ... + x^{n-1}) + x^n (1 + ... + x^{m-1}) + x^{n+m}` -/
lemma lab_geom_split (x : ℝ) (m n : ℕ) :
    ∑ i ∈ range (m + n + 1), x ^ i =
      ∑ i ∈ range n, x ^ i + x ^ n * ∑ i ∈ range m, x ^ i + x ^ (n + m) := by
  rw [show m + n + 1 = n + (m + 1) by omega, sum_range_add, sum_range_succ, mul_sum]
  simp only [pow_add]
  ring

/-- the coordinates of a nonempty parallel class are valid -/
lemma lab_pk_valid {x : ℝ} (hx : 2 ≤ x) {k : ℕ} (hk : 1 ≤ k) : Coord.Valid x (pk x k) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hx0 : 0 ≤ x := by linarith
  dsimp only [Coord.Valid, pk]
  refine ⟨by positivity, one_pos, le_rfl, Finset.sum_nonneg fun i _ => by positivity,
    by linarith, ?_⟩
  rw [Nat.add_sub_cancel, lab_sub_one_mul_sum]
  linarith

lemma coord_valid {x : ℝ} (hx : 2 ≤ x) {l : Lab} (hl : 1 ≤ l.size) :
    Coord.Valid x (l.coord x) := by
  have hx0 : 0 ≤ x := by linarith
  cases l with
  | p k => exact lab_pk_valid hx hl
  | s k => exact (lab_pk_valid hx hl).dual
  | d =>
    dsimp only [Coord.Valid, coord]
    exact ⟨by norm_num, by norm_num, hx0, by positivity, by nlinarith, by nlinarith⟩
  | ee =>
    dsimp only [Coord.Valid, coord]
    exact ⟨by norm_num, by norm_num, by positivity, hx0, by nlinarith, by nlinarith⟩

/-- parallel composition of parallel classes adds their sizes -/
lemma par_pk {x : ℝ} (hx : x ≠ 0) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Coord.par x (pk x a) (pk x b) = pk x (a + b) := by
  obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
  have e1 : m + 1 + (n + 1) - 1 = m + n + 1 := by omega
  simp only [Coord.par, pk, Nat.add_sub_cancel, e1, Coord.mk.injEq]
  refine ⟨by push_cast; ring, by ring, by field_simp; ring, by ring, by ring, ?_⟩
  rw [lab_sum_pow_succ, lab_sum_pow_succ, lab_sum_pow_succ, lab_geom_split, div_eq_iff hx]
  set Gm := ∑ i ∈ Finset.range m, x ^ i
  set Gn := ∑ i ∈ Finset.range n, x ^ i
  rw [show (x - 1) * (x * Gm) * (x * Gn) = x ^ 2 * Gn * (Gm * (x - 1)) by ring, geom_sum_mul]
  ring

/-- `E = P(S₂, S₂)` -/
lemma par_s2_s2 {x : ℝ} (hx : x ≠ 0) :
    Coord.par x ((s 2).coord x) ((s 2).coord x) = (ee).coord x := by
  have h1 : ∑ i ∈ Finset.range (2 - 1), x ^ (i + 1) = x := by simp
  simp only [coord, pk, Coord.dual, Coord.par, Coord.mk.injEq, h1]
  refine ⟨by norm_num, by norm_num, by field_simp; ring, by ring, by ring, by field_simp; ring⟩

/-- the coordinates `wa` of a parallel class do not depend on its size -/
lemma wa_pk (x : ℝ) (hx : x ≠ 0) (k : ℕ) : (pk x k).wa x = (1, 1) := by
  simp [Coord.wa, pk, hx]

end Lab

end Results.TutteThreshold
