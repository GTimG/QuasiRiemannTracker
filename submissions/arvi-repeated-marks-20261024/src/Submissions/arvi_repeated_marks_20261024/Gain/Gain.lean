import Mathlib.Tactic

/-!
# The repeated-mark HIGH gain with one detector cutoff per amplitude class

Amplitude class `p ∈ [0,1/2)`, `K` copies of each marked slot.
Inverse witness: target `r + 2 p z ≥ x` with `z ≤ min (K S) ((Q-r)/2)`.
Plain witness:   target `y + 2 p z ≥ x` with `z ≤ min S (min (h Q) ((B Q - y)/lam))`.
-/

set_option autoImplicit false
namespace QRH.RepeatedMarks
noncomputable section

/-- Inverse threshold in class `p` with `K` copies. -/
def invThr (p K x S Q : ℝ) : ℝ := max (x - 2*p*K*S) ((x - p*Q)/(1-p))

/-- Plain threshold in class `p` (parent face `B, lam, h`). -/
def plainThr (p B lam h x S Q : ℝ) : ℝ :=
  max (x - 2*p*S) (max (x - 2*p*h*Q) ((x - 2*p*B*Q/lam)/(1 - 2*p/lam)))

theorem inv_threshold_iff {p K x S Q r : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    invThr p K x S Q ≤ r ↔ x ≤ r + 2*p*min (K*S) ((Q-r)/2) := by
  have h1p : 0 < 1 - p := by linarith
  have key : x ≤ r + 2*p*min (K*S) ((Q-r)/2) ↔
      x ≤ r + 2*p*(K*S) ∧ x ≤ r + 2*p*((Q-r)/2) := by
    rcases le_total (K*S) ((Q-r)/2) with h | h
    · rw [min_eq_left h]
      constructor
      · intro hx; exact ⟨hx, by nlinarith [mul_le_mul_of_nonneg_left h (by linarith : (0:ℝ) ≤ 2*p)]⟩
      · intro hx; exact hx.1
    · rw [min_eq_right h]
      constructor
      · intro hx; exact ⟨by nlinarith [mul_le_mul_of_nonneg_left h (by linarith : (0:ℝ) ≤ 2*p)], hx⟩
      · intro hx; exact hx.2
  rw [key, invThr, max_le_iff, div_le_iff₀ h1p]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by nlinarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by nlinarith⟩

theorem plain_threshold_iff {p B lam h x S Q y : ℝ} (hp0 : 0 ≤ p) (hlam : 2*p < lam)
    (hlam1 : 0 < lam) :
    plainThr p B lam h x S Q ≤ y ↔
      x ≤ y + 2*p*min S (min (h*Q) ((B*Q - y)/lam)) := by
  have hd : 0 < 1 - 2*p/lam := by
    rw [sub_pos, div_lt_one hlam1]; exact hlam
  have hmin : ∀ a b c : ℝ, x ≤ y + 2*p*min a (min b c) ↔
      x ≤ y + 2*p*a ∧ x ≤ y + 2*p*b ∧ x ≤ y + 2*p*c := by
    intro a b c
    have h2p : 0 ≤ 2*p := by linarith
    constructor
    · intro hx
      have ha := mul_le_mul_of_nonneg_left (min_le_left a (min b c)) h2p
      have hb := mul_le_mul_of_nonneg_left ((min_le_right a (min b c)).trans (min_le_left b c)) h2p
      have hc := mul_le_mul_of_nonneg_left ((min_le_right a (min b c)).trans (min_le_right b c)) h2p
      exact ⟨by linarith, by linarith, by linarith⟩
    · rintro ⟨ha, hb, hc⟩
      rcases le_total a (min b c) with h1 | h1
      · rw [min_eq_left h1]; exact ha
      · rw [min_eq_right h1]
        rcases le_total b c with h2 | h2
        · rw [min_eq_left h2]; exact hb
        · rw [min_eq_right h2]; exact hc
  rw [hmin, plainThr, max_le_iff, max_le_iff, div_le_iff₀ hd]
  have hlam0 : lam ≠ 0 := ne_of_gt hlam1
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by linarith, by linarith, ?_⟩
    have : x - 2*p*B*Q/lam ≤ y - y*(2*p/lam) := by linarith [show y*(1-2*p/lam) = y - y*(2*p/lam) by ring]
    have e : 2*p*((B*Q - y)/lam) = 2*p*B*Q/lam - y*(2*p/lam) := by field_simp
    linarith
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by linarith, by linarith, ?_⟩
    have e : 2*p*((B*Q - y)/lam) = 2*p*B*Q/lam - y*(2*p/lam) := by field_simp
    nlinarith


/-! ## Branches of the per-class detector -/

abbrev Branch := Fin 2 × Fin 3
def w (ν : ℝ) := 5 - 6*ν
def densityDenom (ν : ℝ) := 15 - 6*ν
def baseXi (ν : ℝ) := 10 / densityDenom ν

def invSlope (p : ℝ) : Fin 2 → ℝ := ![1, 1/(1-p)]
def invOffset (p K S Q : ℝ) : Fin 2 → ℝ := ![-(2*p*K*S), -(p*Q)/(1-p)]
def plainSlope (p lam : ℝ) : Fin 3 → ℝ := ![1, 1, 1/(1-2*p/lam)]
def plainOffset (p B lam h S Q : ℝ) : Fin 3 → ℝ :=
  ![-(2*p*S), -(2*p*h*Q), -(2*p*B*Q/lam)/(1-2*p/lam)]

def branchSlope (ν p lam : ℝ) (k : Branch) : ℝ :=
  6*ν + w ν*(invSlope p k.1 + plainSlope p lam k.2/2)
def branchOffset (ν p K B lam h S Q : ℝ) (k : Branch) : ℝ :=
  w ν*(invOffset p K S Q k.1 + plainOffset p B lam h S Q k.2/2)
def branchRoot (ν p K B lam h S Q : ℝ) (k : Branch) : ℝ :=
  (5*Q - branchOffset ν p K B lam h S Q k)/branchSlope ν p lam k

/-- The per-class detector root: the least branch root. -/
def xiP (ν p K B lam h S Q : ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (branchRoot ν p K B lam h S Q)

/-- The per-class gain `f_p`. -/
def gainP (ν p K B lam h S Q : ℝ) : ℝ :=
  (1-2*p)*ν*S + ν*(xiP ν p K B lam h S Q - baseXi ν*Q)

theorem invSlope_pos {p : ℝ} (hp : p < 1) (i : Fin 2) : 0 < invSlope p i := by
  fin_cases i
  · simp [invSlope]
  · simp only [invSlope, Matrix.cons_val_one, Matrix.head_cons]
    exact one_div_pos.mpr (by linarith)

theorem plainSlope_pos {p lam : ℝ} (hlam : 2*p < lam) (hlam1 : 0 < lam) (j : Fin 3) :
    0 < plainSlope p lam j := by
  have hd : 0 < 1 - 2*p/lam := by rw [sub_pos, div_lt_one hlam1]; exact hlam
  fin_cases j
  · simp [plainSlope]
  · simp [plainSlope]
  · simp only [plainSlope, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    exact one_div_pos.mpr hd

theorem branchSlope_pos {ν p lam : ℝ} (hν0 : 0 < ν) (hν1 : ν ≤ 3/4) (hp : p < 1)
    (hlam : 2*p < lam) (hlam1 : 0 < lam) (k : Branch) : 0 < branchSlope ν p lam k := by
  have hw : 0 < w ν := by simp only [w]; linarith
  have hi := invSlope_pos hp k.1
  have hj := plainSlope_pos hlam hlam1 k.2
  simp only [branchSlope]
  positivity

/-- At amplitude class `p = 0` every branch has root `baseXi ν * Q`, so `f_0 = ν S`. -/
theorem branchRoot_zero (ν K B lam h S Q : ℝ) (hν1 : ν ≤ 3/4) (k : Branch) :
    branchRoot ν 0 K B lam h S Q k = baseXi ν * Q := by
  have hd : densityDenom ν ≠ 0 := by simp only [densityDenom]; linarith
  have hs : branchSlope ν 0 lam k = (15 - 6*ν)/2 := by
    rcases k with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [branchSlope, invSlope, plainSlope, w] <;> ring
  have ho : branchOffset ν 0 K B lam h S Q k = 0 := by
    rcases k with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [branchOffset, invOffset, plainOffset]
  rw [branchRoot, hs, ho, baseXi]
  simp only [densityDenom] at hd ⊢
  field_simp
  ring

theorem gainP_zero (ν K B lam h S Q : ℝ) (hν1 : ν ≤ 3/4) :
    gainP ν 0 K B lam h S Q = ν*S := by
  have hall : ∀ k, branchRoot ν 0 K B lam h S Q k = baseXi ν * Q :=
    branchRoot_zero ν K B lam h S Q hν1
  have hxi : xiP ν 0 K B lam h S Q = baseXi ν * Q := by
    apply le_antisymm
    · exact (Finset.inf'_le _ (Finset.mem_univ (0, 0))).trans (le_of_eq (hall _))
    · exact Finset.le_inf' _ _ (fun k _ => le_of_eq (hall k).symm)
  rw [gainP, hxi]
  ring


/-! ## Facets: each branch gives a linear form in `(S, Q)` -/

def facetVal (ν p K B lam h S Q : ℝ) (k : Branch) : ℝ :=
  (1-2*p)*ν*S + ν*(branchRoot ν p K B lam h S Q k - baseXi ν*Q)

theorem branchOffset_linear (ν p K B lam h S Q : ℝ) (k : Branch) :
    branchOffset ν p K B lam h S Q k =
      S*branchOffset ν p K B lam h 1 0 k + Q*branchOffset ν p K B lam h 0 1 k := by
  rcases k with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [branchOffset, invOffset, plainOffset] <;> ring

theorem facetVal_linear (ν p K B lam h S Q : ℝ) (k : Branch) :
    facetVal ν p K B lam h S Q k =
      S*facetVal ν p K B lam h 1 0 k + Q*facetVal ν p K B lam h 0 1 k := by
  simp only [facetVal, branchRoot]
  rw [branchOffset_linear ν p K B lam h S Q k]
  ring

theorem gainP_eq_inf (ν p K B lam h S Q : ℝ) (hν : 0 ≤ ν) :
    gainP ν p K B lam h S Q =
      Finset.univ.inf' Finset.univ_nonempty (facetVal ν p K B lam h S Q) := by
  apply le_antisymm
  · apply Finset.le_inf'
    intro k _
    have hk : xiP ν p K B lam h S Q ≤ branchRoot ν p K B lam h S Q k :=
      Finset.inf'_le _ (Finset.mem_univ k)
    simp only [gainP, facetVal]
    nlinarith
  · obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
      (branchRoot ν p K B lam h S Q)
    have := Finset.inf'_le (s := Finset.univ) (facetVal ν p K B lam h S Q) (Finset.mem_univ k)
    simp only [gainP, xiP, facetVal] at this ⊢
    rw [hk]
    exact this


/-! ## Signs of the facet coefficients -/

/-- `w ν * (a_S S + a_Q Q)` form of `-branchOffset`: explicit S- and Q-coefficients. -/
def offS (p K lam : ℝ) (k : Branch) : ℝ :=
  ![2*p*K, 0] k.1 + ![2*p, 0, 0] k.2/2
def offQ (p B lam h : ℝ) (k : Branch) : ℝ :=
  ![0, p/(1-p)] k.1 + ![0, 2*p*h, (2*p*B/lam)/(1-2*p/lam)] k.2/2

theorem neg_branchOffset (ν p K B lam h S Q : ℝ) (k : Branch) :
    -branchOffset ν p K B lam h S Q k = w ν*(offS p K lam k*S + offQ p B lam h k*Q) := by
  rcases k with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [branchOffset, invOffset, plainOffset, offS, offQ] <;> ring

/-- Slope excess over the `p = 0` slope. -/
def slopeExcess (p lam : ℝ) (k : Branch) : ℝ :=
  ![0, p/(1-p)] k.1 + ![0, 0, (2*p/lam)/(1-2*p/lam)] k.2/2

theorem branchSlope_eq (ν p lam : ℝ) (hp : p < 1) (hlam : 2*p < lam) (hlam1 : 0 < lam)
    (k : Branch) :
    branchSlope ν p lam k = (15 - 6*ν)/2 + w ν*slopeExcess p lam k := by
  have h1 : 1 - p ≠ 0 := by linarith
  have hd : 1 - 2*p/lam ≠ 0 := by
    have : 2*p/lam < 1 := by rw [div_lt_one hlam1]; exact hlam
    linarith
  have hl2 : lam - p*2 ≠ 0 := by intro h; linarith
  have hl2' : lam - 2*p ≠ 0 := by intro h; linarith
  rcases k with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [branchSlope, invSlope, plainSlope, slopeExcess, w] <;> field_simp <;> ring


theorem offS_nonneg {p K lam : ℝ} (hp : 0 ≤ p) (hK : 0 ≤ K) (k : Branch) : 0 ≤ offS p K lam k := by
  rcases k with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp [offS] <;> positivity

/-- Per-branch comparison of the Q-offset with the slope excess. -/
theorem offQ_bounds {ν p B lam h : ℝ} (hν1 : ν ≤ 3/4) (hp0 : 0 ≤ p) (hp1 : p ≤ 1/2)
    (hB0 : 22/23 ≤ B) (hB1 : B ≤ 1) (hlam : 1 < lam) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (k : Branch) :
    10*slopeExcess p lam k ≤ (15 - 6*ν)*offQ p B lam h k ∧
      offQ p B lam h k ≤ 1/2 + slopeExcess p lam k := by
  have hlam0 : 0 < lam := by linarith
  have h2p : 2*p < lam := by linarith
  have hd : 0 < 1 - 2*p/lam := by rw [sub_pos, div_lt_one hlam0]; exact h2p
  have h1p : 0 < 1 - p := by linarith
  have he1 : 0 ≤ p/(1-p) := div_nonneg hp0 h1p.le
  have he2 : 0 ≤ (2*p/lam)/(1-2*p/lam) := div_nonneg (div_nonneg (by linarith) hlam0.le) hd.le
  have hden : 10 ≤ 15 - 6*ν := by linarith
  -- plain parts
  have hj2a : 10*((2*p/lam)/(1-2*p/lam)) ≤ (15-6*ν)*((2*p*B/lam)/(1-2*p/lam)) := by
    rw [show (2*p*B/lam)/(1-2*p/lam) = B*((2*p/lam)/(1-2*p/lam)) by field_simp]
    have hBnu : 10 ≤ (15-6*ν)*B := by nlinarith
    nlinarith
  have hj2b : (2*p*B/lam)/(1-2*p/lam) ≤ 1 + (2*p/lam)/(1-2*p/lam) := by
    have hlam' : lam ≠ 0 := ne_of_gt hlam0
    have hdl : lam - 2*p > 0 := by linarith
    have e1 : (2*p*B/lam)/(1-2*p/lam) = 2*p*B/(lam-2*p) := by field_simp
    have e2 : 1 + (2*p/lam)/(1-2*p/lam) = lam/(lam-2*p) := by field_simp; ring
    rw [e1, e2, div_le_div_iff_of_pos_right hdl]
    nlinarith
  have hph : 0 ≤ p*h := mul_nonneg hp0 hh0
  have hph1 : p*h ≤ 1/2 := by nlinarith
  have hnu : 0 ≤ 15 - 6*ν := by linarith
  rcases k with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp [slopeExcess, offQ] <;>
    (try constructor) <;>
    nlinarith [mul_le_mul_of_nonneg_right hden he1, mul_nonneg hnu hph]


/-- Standing hypotheses on the density, class and HIGH parent. -/
structure Params (ν p K B lam h : ℝ) : Prop where
  hν0 : 0 < ν
  hν1 : ν ≤ 3/4
  hp0 : 0 ≤ p
  hp1 : p ≤ 1/2
  hK : 0 ≤ K
  hB0 : 22/23 ≤ B
  hB1 : B ≤ 1
  hlam : 1 < lam
  hh0 : 0 ≤ h
  hh1 : h ≤ 1

theorem branchRoot_eq {ν p K B lam h : ℝ} (P : Params ν p K B lam h) (S Q : ℝ) (k : Branch) :
    branchRoot ν p K B lam h S Q k =
      (5*Q + w ν*(offS p K lam k*S + offQ p B lam h k*Q)) /
        ((15 - 6*ν)/2 + w ν*slopeExcess p lam k) := by
  have hs := branchSlope_eq ν p lam (by linarith [P.hp1]) (by linarith [P.hp1, P.hlam])
    (by linarith [P.hlam]) k
  have ho := neg_branchOffset ν p K B lam h S Q k
  rw [branchRoot, hs]
  congr 1
  linarith

theorem slopeExcess_nonneg {p lam : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1/2) (hlam : 1 < lam)
    (k : Branch) : 0 ≤ slopeExcess p lam k := by
  have hlam0 : 0 < lam := by linarith
  have hd : 0 < 1 - 2*p/lam := by rw [sub_pos, div_lt_one hlam0]; linarith
  have he1 : 0 ≤ p/(1-p) := div_nonneg hp0 (by linarith)
  have he2 : 0 ≤ (2*p/lam)/(1-2*p/lam) := div_nonneg (div_nonneg (by linarith) hlam0.le) hd.le
  rcases k with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp [slopeExcess] <;> positivity

theorem facet_coeffs {ν p K B lam h : ℝ} (P : Params ν p K B lam h) (k : Branch) :
    0 ≤ facetVal ν p K B lam h 1 0 k ∧ 0 ≤ facetVal ν p K B lam h 0 1 k ∧
      facetVal ν p K B lam h 0 1 k ≤ ν*(1 - baseXi ν) := by
  have hw : 0 < w ν := by simp only [w]; linarith [P.hν1]
  have hex := slopeExcess_nonneg P.hp0 P.hp1 P.hlam k
  have hden : 0 < (15 - 6*ν)/2 + w ν*slopeExcess p lam k := by
    have : 0 ≤ w ν*slopeExcess p lam k := mul_nonneg hw.le hex
    linarith [P.hν1]
  have hoS := offS_nonneg (lam := lam) P.hp0 P.hK k
  have hb := offQ_bounds P.hν1 P.hp0 P.hp1 P.hB0 P.hB1 P.hlam P.hh0 P.hh1 k
  have hD : (0:ℝ) < 15 - 6*ν := by linarith [P.hν1]
  refine ⟨?_, ?_, ?_⟩
  · simp only [facetVal, branchRoot_eq P]
    have : 0 ≤ (5*0 + w ν*(offS p K lam k*1 + offQ p B lam h k*0)) /
        ((15 - 6*ν)/2 + w ν*slopeExcess p lam k) := by
      apply div_nonneg _ hden.le
      simp; exact mul_nonneg hw.le hoS
    have h2 : 0 ≤ (1 - 2*p)*ν*1 := by nlinarith [P.hp1, P.hν0]
    nlinarith [P.hν0]
  · simp only [facetVal, branchRoot_eq P, baseXi, densityDenom]
    have key : 10/(15 - 6*ν) ≤ (5*1 + w ν*(offS p K lam k*0 + offQ p B lam h k*1)) /
        ((15 - 6*ν)/2 + w ν*slopeExcess p lam k) := by
      rw [div_le_div_iff₀ hD hden]
      have := mul_le_mul_of_nonneg_left hb.1 hw.le
      nlinarith
    nlinarith [P.hν0]
  · simp only [facetVal, branchRoot_eq P, baseXi, densityDenom]
    have key : (5*1 + w ν*(offS p K lam k*0 + offQ p B lam h k*1)) /
        ((15 - 6*ν)/2 + w ν*slopeExcess p lam k) ≤ 1 := by
      rw [div_le_one hden]
      have := mul_le_mul_of_nonneg_left hb.2 hw.le
      simp only [w] at this ⊢
      nlinarith
    nlinarith [P.hν0]



/-- One facet. -/
theorem facet_payment {A B ν S F L Q δ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hν : 0 ≤ ν)
    (hS : 0 ≤ S) (h2SF : 2 * S ≤ F) (hδ : 0 ≤ δ)
    (hSL : S ≤ L + δ) (hFQ : F ≤ Q + 2 * δ) (hL : 0 ≤ L) (hQ : 0 ≤ Q) :
    min (A * S + B * F) (ν * S) ≤ A * L + B * Q + ν * δ := by
  rcases le_total S δ with hSδ | hδS
  · -- δ ≥ S: the term ν δ already pays ν S
    have h1 : ν * S ≤ ν * δ := mul_le_mul_of_nonneg_left hSδ hν
    have h2 : 0 ≤ A * L := mul_nonneg hA hL
    have h3 : 0 ≤ B * Q := mul_nonneg hB hQ
    exact (min_le_right _ _).trans (by linarith)
  · -- δ ≤ S: monotone lower bound, affine in δ, compare with the endpoints δ = 0 and δ = S
    have h1 : A * (S - δ) ≤ A * L := mul_le_mul_of_nonneg_left (by linarith) hA
    have h2 : B * (F - 2 * δ) ≤ B * Q := mul_le_mul_of_nonneg_left (by linarith) hB
    rcases le_total (A + 2 * B) ν with hc | hc
    · -- slope condition holds: the value at δ is at least the value at 0
      have : A * S + B * F ≤ A * (S - δ) + B * (F - 2 * δ) + ν * δ := by nlinarith
      exact (min_le_left _ _).trans (by linarith)
    · -- value at δ is at least the value at S, which is B (F - 2 S) + ν S ≥ ν S
      have hval : B * (F - 2 * S) + ν * S ≤ A * (S - δ) + B * (F - 2 * δ) + ν * δ := by
        nlinarith
      have hB2 : 0 ≤ B * (F - 2 * S) := mul_nonneg hB (by linarith)
      exact (min_le_right _ _).trans (by linarith)

/-- Lemma C for an arbitrary family of facets. -/
theorem lemmaC {ι : Type*} (A B : ι → ℝ) (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j)
    {ν S F L Q δ GSF GLQ : ℝ} (hν : 0 ≤ ν)
    (hS : 0 ≤ S) (h2SF : 2 * S ≤ F) (hL : 0 ≤ L) (hQ : 0 ≤ Q) (hδ : 0 ≤ δ)
    (hSL : S ≤ L + δ) (hFQ : F ≤ Q + 2 * δ)
    (hGle : ∀ j, GSF ≤ A j * S + B j * F) (hGcap : GSF ≤ ν * S)
    (hGinf : ∀ ε > 0, ∃ j, A j * L + B j * Q ≤ GLQ + ε) :
    GSF ≤ GLQ + ν * δ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨j, hj⟩ := hGinf ((GSF - (GLQ + ν * δ)) / 2) (by linarith)
  have hf := facet_payment (hA j) (hB j) hν hS h2SF hδ hSL hFQ hL hQ
  have hmin : GSF ≤ min (A j * S + B j * F) (ν * S) := le_min (hGle j) hGcap
  linarith



/-! ## The repeated-mark gain: infimum over amplitude classes -/

def classes : Set ℝ := Set.Icc 0 (1/2)

/-- The gain `G_K(S,Q) = inf_{0 ≤ p ≤ 1/2} f_p(S,Q)`. -/
def gainK (ν K B lam h S Q : ℝ) : ℝ := sInf ((fun p => gainP ν p K B lam h S Q) '' classes)

theorem facetVal_nonneg {ν p K B lam h : ℝ} (P : Params ν p K B lam h) {S Q : ℝ}
    (hS : 0 ≤ S) (hQ : 0 ≤ Q) (k : Branch) : 0 ≤ facetVal ν p K B lam h S Q k := by
  rw [facetVal_linear]
  have hc := facet_coeffs P k
  exact add_nonneg (mul_nonneg hS hc.1) (mul_nonneg hQ hc.2.1)

theorem gainP_nonneg {ν p K B lam h : ℝ} (P : Params ν p K B lam h) {S Q : ℝ}
    (hS : 0 ≤ S) (hQ : 0 ≤ Q) : 0 ≤ gainP ν p K B lam h S Q := by
  rw [gainP_eq_inf ν p K B lam h S Q P.hν0.le]
  exact Finset.le_inf' _ _ (fun k _ => facetVal_nonneg P hS hQ k)

/-- The standing parent hypotheses, for every class. -/
structure ParentParams (ν K B lam h : ℝ) : Prop where
  hν0 : 0 < ν
  hν1 : ν ≤ 3/4
  hK : 0 ≤ K
  hB0 : 22/23 ≤ B
  hB1 : B ≤ 1
  hlam : 1 < lam
  hh0 : 0 ≤ h
  hh1 : h ≤ 1

theorem ParentParams.at {ν K B lam h : ℝ} (P : ParentParams ν K B lam h) {p : ℝ}
    (hp : p ∈ classes) : Params ν p K B lam h :=
  ⟨P.hν0, P.hν1, hp.1, hp.2, P.hK, P.hB0, P.hB1, P.hlam, P.hh0, P.hh1⟩

theorem gainK_bdd {ν K B lam h : ℝ} (P : ParentParams ν K B lam h) {S Q : ℝ}
    (hS : 0 ≤ S) (hQ : 0 ≤ Q) :
    BddBelow ((fun p => gainP ν p K B lam h S Q) '' classes) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  exact gainP_nonneg (P.at hp) hS hQ

theorem gainK_le_gainP {ν K B lam h : ℝ} (P : ParentParams ν K B lam h) {S Q p : ℝ}
    (hS : 0 ≤ S) (hQ : 0 ≤ Q) (hp : p ∈ classes) :
    gainK ν K B lam h S Q ≤ gainP ν p K B lam h S Q :=
  csInf_le (gainK_bdd P hS hQ) ⟨p, hp, rfl⟩

theorem gainK_le_nuS {ν K B lam h : ℝ} (P : ParentParams ν K B lam h) {S Q : ℝ}
    (hS : 0 ≤ S) (hQ : 0 ≤ Q) : gainK ν K B lam h S Q ≤ ν*S := by
  have h0 : (0:ℝ) ∈ classes := ⟨le_rfl, by norm_num⟩
  have := gainK_le_gainP P hS hQ h0
  rwa [gainP_zero ν K B lam h S Q P.hν1] at this

theorem gainK_nonneg {ν K B lam h : ℝ} (P : ParentParams ν K B lam h) {S Q : ℝ}
    (hS : 0 ≤ S) (hQ : 0 ≤ Q) : 0 ≤ gainK ν K B lam h S Q := by
  apply le_csInf
  · exact ⟨_, ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact gainP_nonneg (P.at hp) hS hQ

/-- **Lemma C for the repeated-mark gain** (common-width payment, reserve zero). -/
theorem gainK_payment {ν K B lam h : ℝ} (P : ParentParams ν K B lam h)
    {S F L Q δ : ℝ} (hS : 0 ≤ S) (h2SF : 2*S ≤ F) (hL : 0 ≤ L) (hQ : 0 ≤ Q) (hδ : 0 ≤ δ)
    (hSL : S ≤ L + δ) (hFQ : F ≤ Q + 2*δ) :
    gainK ν K B lam h S F ≤ gainK ν K B lam h L Q + ν*δ := by
  have hF : 0 ≤ F := by linarith
  let ι := classes × Branch
  let A : ι → ℝ := fun j => facetVal ν j.1.1 K B lam h 1 0 j.2
  let Bc : ι → ℝ := fun j => facetVal ν j.1.1 K B lam h 0 1 j.2
  have hA : ∀ j : ι, 0 ≤ A j := fun j => (facet_coeffs (P.at j.1.2) j.2).1
  have hB : ∀ j : ι, 0 ≤ Bc j := fun j => (facet_coeffs (P.at j.1.2) j.2).2.1
  apply lemmaC A Bc hA hB P.hν0.le hS h2SF hL hQ hδ hSL hFQ
  · intro j
    have h1 := gainK_le_gainP P hS hF j.1.2
    rw [gainP_eq_inf ν j.1.1 K B lam h S F P.hν0.le] at h1
    have h2 := Finset.inf'_le (s := Finset.univ) (facetVal ν j.1.1 K B lam h S F) (Finset.mem_univ j.2)
    have h3 := facetVal_linear ν j.1.1 K B lam h S F j.2
    simp only [A, Bc]
    linarith
  · exact gainK_le_nuS P hS hF
  · intro ε hε
    -- an amplitude class nearly attaining the infimum at (L,Q)
    obtain ⟨_, ⟨p, hp, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt
      (⟨_, ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩⟩ : ((fun p => gainP ν p K B lam h L Q) '' classes).Nonempty)
      (show gainK ν K B lam h L Q < gainK ν K B lam h L Q + ε by linarith)
    obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (facetVal ν p K B lam h L Q)
    refine ⟨(⟨p, hp⟩, k), ?_⟩
    have hg := gainP_eq_inf ν p K B lam h L Q P.hν0.le
    have h3 := facetVal_linear ν p K B lam h L Q k
    simp only [A, Bc]
    linarith


/-- Any facet attaining `G_K(S,Q)` within `ε`, packaged. -/
theorem gainK_near {ν K B lam h : ℝ} (P : ParentParams ν K B lam h) {S Q ε : ℝ}
    (hS : 0 ≤ S) (hQ : 0 ≤ Q) (hε : 0 < ε) :
    ∃ p ∈ classes, ∃ k : Branch, facetVal ν p K B lam h S Q k < gainK ν K B lam h S Q + ε := by
  obtain ⟨_, ⟨p, hp, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt
    (⟨_, ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩⟩ : ((fun p => gainP ν p K B lam h S Q) '' classes).Nonempty)
    (show gainK ν K B lam h S Q < gainK ν K B lam h S Q + ε by linarith)
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (facetVal ν p K B lam h S Q)
  refine ⟨p, hp, k, ?_⟩
  have hg := gainP_eq_inf ν p K B lam h S Q P.hν0.le
  rw [← hk, ← hg]
  exact hlt

/-- (P2): `ν S - G_K(S,Q)` is nondecreasing in `S`. -/
theorem gainK_width_mono {ν K B lam h : ℝ} (P : ParentParams ν K B lam h) {S L Q : ℝ}
    (hS : 0 ≤ S) (hSL : S ≤ L) (hQ : 0 ≤ Q) :
    ν*S - gainK ν K B lam h S Q ≤ ν*L - gainK ν K B lam h L Q := by
  have hL : 0 ≤ L := by linarith
  by_contra hcon
  push Not at hcon
  set ε := (ν*S - gainK ν K B lam h S Q) - (ν*L - gainK ν K B lam h L Q) with hε
  have hεpos : 0 < ε := by linarith
  obtain ⟨p, hp, k, hk⟩ := gainK_near P hS hQ (show 0 < ε/2 by linarith)
  have hc := facet_coeffs (P.at hp) k
  have hlinS := facetVal_linear ν p K B lam h S Q k
  have hlinL := facetVal_linear ν p K B lam h L Q k
  have hGL : gainK ν K B lam h L Q ≤ gainP ν p K B lam h L Q := gainK_le_gainP P hL hQ hp
  rw [gainP_eq_inf ν p K B lam h L Q P.hν0.le] at hGL
  have hGL' := hGL.trans (Finset.inf'_le (s := Finset.univ) (facetVal ν p K B lam h L Q) (Finset.mem_univ k))
  have hnuS := gainK_le_nuS P hL hQ
  -- case on the facet slope
  rcases le_total (facetVal ν p K B lam h 1 0 k) ν with hA | hA
  · have : facetVal ν p K B lam h 1 0 k * (L - S) ≤ ν*(L - S) :=
      mul_le_mul_of_nonneg_right hA (by linarith)
    nlinarith
  · -- a facet with slope ≥ ν nearly attains G_K(S,Q) ≤ ν S; then use G_K(L,Q) ≤ ν L
    have hGS0 : 0 ≤ gainK ν K B lam h S Q := gainK_nonneg P hS hQ
    have hBQ : 0 ≤ facetVal ν p K B lam h 0 1 k * Q := mul_nonneg hc.2.1 hQ
    have hGSle := gainK_le_nuS P hS hQ
    nlinarith

/-- Homogeneity of the per-class gain and of `G_K`. -/
theorem facetVal_smul (ν p K B lam h S Q D : ℝ) (k : Branch) :
    facetVal ν p K B lam h (D*S) (D*Q) k = D*facetVal ν p K B lam h S Q k := by
  rw [facetVal_linear ν p K B lam h (D*S) (D*Q) k, facetVal_linear ν p K B lam h S Q k]
  ring

theorem gainP_smul {ν p K B lam h S Q D : ℝ} (hν : 0 ≤ ν) (hD : 0 ≤ D) :
    gainP ν p K B lam h (D*S) (D*Q) = D*gainP ν p K B lam h S Q := by
  rw [gainP_eq_inf ν p K B lam h _ _ hν, gainP_eq_inf ν p K B lam h S Q hν]
  simp_rw [facetVal_smul]
  have hg : ∀ x y : ℝ, D * (x ⊓ y) = D * x ⊓ D * y := fun x y => by
    rcases le_total x y with hxy | hxy
    · rw [inf_eq_left.mpr hxy, inf_eq_left.mpr (mul_le_mul_of_nonneg_left hxy hD)]
    · rw [inf_eq_right.mpr hxy, inf_eq_right.mpr (mul_le_mul_of_nonneg_left hxy hD)]
  exact (Finset.apply_inf'_eq_inf'_comp Finset.univ_nonempty (fun x => D * x) hg).symm


/-! ## Further properties used by the source step: row monotonicity, root completion, scaling -/

/-- Monotonicity in the row width `Q` (every facet has a nonnegative `Q`-coefficient). -/
theorem gainK_mono_Q {ν K B lam h : ℝ} (P : ParentParams ν K B lam h) {S Q F : ℝ}
    (hS : 0 ≤ S) (hQ : 0 ≤ Q) (hQF : Q ≤ F) :
    gainK ν K B lam h S Q ≤ gainK ν K B lam h S F := by
  have hF : 0 ≤ F := hQ.trans hQF
  have hne : ((fun p => gainP ν p K B lam h S F) '' classes).Nonempty :=
    ⟨_, ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩⟩
  show gainK ν K B lam h S Q ≤ sInf ((fun p => gainP ν p K B lam h S F) '' classes)
  apply le_csInf hne
  rintro _ ⟨p, hp, rfl⟩
  apply (gainK_le_gainP P hS hQ hp).trans
  show gainP ν p K B lam h S Q ≤ gainP ν p K B lam h S F
  rw [gainP_eq_inf ν p K B lam h S Q P.hν0.le, gainP_eq_inf ν p K B lam h S F P.hν0.le]
  apply Finset.le_inf'
  intro k _
  apply (Finset.inf'_le _ (Finset.mem_univ k)).trans
  rw [facetVal_linear ν p K B lam h S Q k, facetVal_linear ν p K B lam h S F k]
  have hc := facet_coeffs (P.at hp) k
  nlinarith [mul_le_mul_of_nonneg_right hQF hc.2.1]

/-- Row loss: `G_K(S,F) ≤ G_K(S,q) + C_max (F - q)` for `q ≤ F`, `C_max = ν(1 - baseXi ν)`. -/
theorem gainK_row_loss {ν K B lam h : ℝ} (P : ParentParams ν K B lam h) {S q F : ℝ}
    (hS : 0 ≤ S) (hq : 0 ≤ q) (hqF : q ≤ F) :
    gainK ν K B lam h S F ≤ gainK ν K B lam h S q + ν*(1 - baseXi ν)*(F - q) := by
  have hF : 0 ≤ F := hq.trans hqF
  by_contra hcon
  push Not at hcon
  set ε := gainK ν K B lam h S F - (gainK ν K B lam h S q + ν*(1 - baseXi ν)*(F - q)) with hε
  have hεpos : 0 < ε := by linarith
  obtain ⟨p, hp, k, hk⟩ := gainK_near P hS hq hεpos
  have hc := facet_coeffs (P.at hp) k
  have hlinq := facetVal_linear ν p K B lam h S q k
  have hlinF := facetVal_linear ν p K B lam h S F k
  have hGF : gainK ν K B lam h S F ≤ facetVal ν p K B lam h S F k := by
    apply (gainK_le_gainP P hS hF hp).trans
    rw [gainP_eq_inf ν p K B lam h S F P.hν0.le]
    exact Finset.inf'_le _ (Finset.mem_univ k)
  have hm := mul_le_mul_of_nonneg_right hc.2.2 (sub_nonneg.mpr hqF)
  nlinarith

/-- `G_K(S,Q) ≤ C_max Q`, from the slot-free branch (inverse cap, width cap) at `p = 1/2`. -/
theorem gainK_le_cmax {ν K B lam h : ℝ} (P : ParentParams ν K B lam h) {S Q : ℝ}
    (hS : 0 ≤ S) (hQ : 0 ≤ Q) :
    gainK ν K B lam h S Q ≤ ν*(1 - baseXi ν)*Q := by
  have hp : (1/2:ℝ) ∈ classes := ⟨by norm_num, le_rfl⟩
  apply (gainK_le_gainP P hS hQ hp).trans
  rw [gainP_eq_inf ν (1/2) K B lam h S Q P.hν0.le]
  apply (Finset.inf'_le _ (Finset.mem_univ ((1, 1) : Branch))).trans
  rw [facetVal_linear ν (1/2) K B lam h S Q (1, 1)]
  have hc := facet_coeffs (P.at hp) (1, 1)
  -- the `S`-coefficient of this branch vanishes at `p = 1/2`
  have hA : facetVal ν (1/2) K B lam h 1 0 (1, 1) = 0 := by
    have hd : densityDenom ν ≠ 0 := by simp only [densityDenom]; linarith [P.hν1]
    simp only [facetVal, branchRoot, branchOffset, branchSlope, invOffset, plainOffset,
      invSlope, plainSlope]
    show (1 - 2*(1/2))*ν*1 + ν*((5*0 - w ν*(-((1/2)*0)/(1-1/2) + -(2*(1/2)*h*0)/2)) /
        (6*ν + w ν*(1/(1-1/2) + 1/2)) - baseXi ν*0) = 0
    ring
  rw [hA]
  nlinarith [mul_le_mul_of_nonneg_left hc.2.2 hQ]

/-- Homogeneity of `G_K`. -/
theorem gainK_smul {ν K B lam h : ℝ} (P : ParentParams ν K B lam h) {S Q D : ℝ}
    (hS : 0 ≤ S) (hQ : 0 ≤ Q) (hD : 0 ≤ D) :
    gainK ν K B lam h (D*S) (D*Q) = D*gainK ν K B lam h S Q := by
  rcases eq_or_lt_of_le hD with h0 | hpos
  · subst h0
    simp only [zero_mul]
    apply le_antisymm
    · have := gainK_le_nuS P (le_refl (0:ℝ)) (le_refl (0:ℝ)); linarith
    · exact gainK_nonneg P le_rfl le_rfl
  · have hset : ((fun p => gainP ν p K B lam h (D*S) (D*Q)) '' classes) =
        (fun x => D*x) '' ((fun p => gainP ν p K B lam h S Q) '' classes) := by
      rw [Set.image_image]
      congr 1
      funext p
      exact gainP_smul P.hν0.le hD
    have hne : ((fun p => gainP ν p K B lam h S Q) '' classes).Nonempty :=
      ⟨_, ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩⟩
    simp only [gainK]
    rw [hset]
    exact (Monotone.map_csInf_of_continuousAt (f := fun x => D*x)
      (continuous_const.mul continuous_id).continuousAt
      (fun a b hab => mul_le_mul_of_nonneg_left hab hD)
      hne (gainK_bdd P hS hQ)).symm

end
end QRH.RepeatedMarks
