import Submissions.arvi_repeated_marks_on_sil_face_20261025.Gain.Gain

/-!
# The per-class detector

For amplitude class `p` the detector cutoff is
`cutoffP = invThr p K ξ S Q + plainThr p B lam h ξ S Q / 2` at the class root `ξ = xiP`.
It satisfies the balance `6 ν ξ + (5 - 6 ν) cutoffP = 5 Q`, and
`baseXi ν Q ≤ ξ ≤ Q`, `ξ ≤ B Q`, `Q ≤ cutoffP ≤ 10 Q / 7`.
This is the per-class analogue of `High.cutoff_balance`, `High.xi_lower`, `High.xi_upper` and
`High.cutoff_bounds` (Collet), which are the case `p = 1/2`, `K = 1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace QRH.RepeatedMarks
noncomputable section

/-- The detector of class `p`. -/
def detectorP (ν p K B lam h S Q x : ℝ) : ℝ :=
  6*ν*x + w ν*(invThr p K x S Q + plainThr p B lam h x S Q/2)

/-- The detector cutoff of class `p`. -/
def cutoffP (ν p K B lam h S Q : ℝ) : ℝ :=
  invThr p K (xiP ν p K B lam h S Q) S Q + plainThr p B lam h (xiP ν p K B lam h S Q) S Q/2

def branchValueP (ν p K B lam h S Q x : ℝ) (k : Branch) : ℝ :=
  branchSlope ν p lam k*x + branchOffset ν p K B lam h S Q k

theorem inv_piece_le (p K x S Q : ℝ) (i : Fin 2) :
    invSlope p i*x + invOffset p K S Q i ≤ invThr p K x S Q := by
  fin_cases i
  · show 1*x + -(2*p*K*S) ≤ invThr p K x S Q
    exact le_of_eq_of_le (by ring) (le_max_left _ _)
  · show 1/(1-p)*x + -(p*Q)/(1-p) ≤ invThr p K x S Q
    exact le_of_eq_of_le (by ring) (le_max_right _ _)

theorem plain_piece_le (p B lam h x S Q : ℝ) (j : Fin 3) :
    plainSlope p lam j*x + plainOffset p B lam h S Q j ≤ plainThr p B lam h x S Q := by
  fin_cases j
  · show 1*x + -(2*p*S) ≤ plainThr p B lam h x S Q
    exact le_of_eq_of_le (by ring) (le_max_left _ _)
  · show 1*x + -(2*p*h*Q) ≤ plainThr p B lam h x S Q
    exact le_of_eq_of_le (by ring) ((le_max_left _ _).trans (le_max_right _ _))
  · show 1/(1-2*p/lam)*x + -(2*p*B*Q/lam)/(1-2*p/lam) ≤ plainThr p B lam h x S Q
    exact le_of_eq_of_le (by ring) ((le_max_right _ _).trans (le_max_right _ _))

theorem branchValueP_le_detectorP {ν p K B lam h S Q x : ℝ} (hν : ν ≤ 5/6) (k : Branch) :
    branchValueP ν p K B lam h S Q x k ≤ detectorP ν p K B lam h S Q x := by
  have hw : 0 ≤ w ν := by simp only [w]; linarith
  have hi := inv_piece_le p K x S Q k.1
  have hp := plain_piece_le p B lam h x S Q k.2
  have hh := mul_le_mul_of_nonneg_left (show
    invSlope p k.1*x + invOffset p K S Q k.1 +
      (plainSlope p lam k.2*x + plainOffset p B lam h S Q k.2)/2 ≤
      invThr p K x S Q + plainThr p B lam h x S Q/2 by linarith) hw
  simp only [branchValueP, branchSlope, branchOffset, detectorP]
  nlinarith

theorem inv_piece_eq (p K x S Q : ℝ) :
    ∃ i : Fin 2, invThr p K x S Q = invSlope p i*x + invOffset p K S Q i := by
  rcases le_total (x - 2*p*K*S) ((x - p*Q)/(1-p)) with hh | hh
  · refine ⟨1, ?_⟩
    rw [invThr, max_eq_right hh]
    show (x - p*Q)/(1-p) = 1/(1-p)*x + -(p*Q)/(1-p)
    ring
  · refine ⟨0, ?_⟩
    rw [invThr, max_eq_left hh]
    show x - 2*p*K*S = 1*x + -(2*p*K*S)
    ring

theorem plain_piece_eq (p B lam h x S Q : ℝ) :
    ∃ j : Fin 3, plainThr p B lam h x S Q = plainSlope p lam j*x + plainOffset p B lam h S Q j := by
  rcases le_total (x - 2*p*S) (max (x - 2*p*h*Q) ((x - 2*p*B*Q/lam)/(1 - 2*p/lam))) with hh | hh
  · rcases le_total (x - 2*p*h*Q) ((x - 2*p*B*Q/lam)/(1 - 2*p/lam)) with hc | hc
    · refine ⟨2, ?_⟩
      rw [plainThr, max_eq_right hh, max_eq_right hc]
      show (x - 2*p*B*Q/lam)/(1 - 2*p/lam) = 1/(1-2*p/lam)*x + -(2*p*B*Q/lam)/(1-2*p/lam)
      ring
    · refine ⟨1, ?_⟩
      rw [plainThr, max_eq_right hh, max_eq_left hc]
      show x - 2*p*h*Q = 1*x + -(2*p*h*Q)
      ring
  · refine ⟨0, ?_⟩
    rw [plainThr, max_eq_left hh]
    show x - 2*p*S = 1*x + -(2*p*S)
    ring

theorem detectorP_eq_branch (ν p K B lam h S Q x : ℝ) :
    ∃ k : Branch, detectorP ν p K B lam h S Q x = branchValueP ν p K B lam h S Q x k := by
  obtain ⟨i, hi⟩ := inv_piece_eq p K x S Q
  obtain ⟨j, hj⟩ := plain_piece_eq p B lam h x S Q
  refine ⟨(i, j), ?_⟩
  simp only [detectorP, branchValueP, branchSlope, branchOffset]
  rw [hi, hj]
  ring

/-- Standing hypotheses of a class. -/
structure ClassParams (ν p lam : ℝ) : Prop where
  hν0 : 1/2 ≤ ν
  hν1 : ν ≤ 3/4
  hp0 : 0 ≤ p
  hp1 : p ≤ 1/2
  hlam : 1 < lam

theorem ClassParams.slope_pos {ν p lam : ℝ} (P : ClassParams ν p lam) (k : Branch) :
    0 < branchSlope ν p lam k :=
  branchSlope_pos (by linarith [P.hν0]) P.hν1 (by linarith [P.hp1])
    (by linarith [P.hp1, P.hlam]) (by linarith [P.hlam]) k

theorem detectorP_le_iff {ν p K B lam h S Q x : ℝ} (P : ClassParams ν p lam) :
    detectorP ν p K B lam h S Q x ≤ 5*Q ↔ x ≤ xiP ν p K B lam h S Q := by
  have hb (k : Branch) : branchValueP ν p K B lam h S Q x k ≤ 5*Q ↔
      x ≤ branchRoot ν p K B lam h S Q k := by
    rw [branchRoot, le_div_iff₀ (P.slope_pos k)]
    simp only [branchValueP]
    constructor <;> intro hh <;> nlinarith
  constructor
  · intro hd
    apply Finset.le_inf'
    intro k _
    exact (hb k).mp ((branchValueP_le_detectorP (by linarith [P.hν1]) k).trans hd)
  · intro hx
    obtain ⟨k, hk⟩ := detectorP_eq_branch ν p K B lam h S Q x
    rw [hk]
    exact (hb k).mpr (hx.trans (Finset.inf'_le _ (Finset.mem_univ k)))

theorem cutoffP_balance {ν p K B lam h S Q : ℝ} (P : ClassParams ν p lam) :
    6*ν*xiP ν p K B lam h S Q + w ν*cutoffP ν p K B lam h S Q = 5*Q := by
  have hle := (detectorP_le_iff (K:=K) (B:=B) (h:=h) (S:=S) (Q:=Q) P).mpr
    (le_refl (xiP ν p K B lam h S Q))
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (branchRoot ν p K B lam h S Q)
  have hk' : xiP ν p K B lam h S Q = branchRoot ν p K B lam h S Q k := hk
  have he : branchValueP ν p K B lam h S Q (xiP ν p K B lam h S Q) k = 5*Q := by
    rw [hk']
    simp only [branchValueP, branchRoot]
    rw [mul_div_cancel₀ _ (ne_of_gt (P.slope_pos k))]
    ring
  have hge := branchValueP_le_detectorP (ν:=ν) (p:=p) (lam:=lam) (K:=K) (B:=B) (h:=h) (S:=S)
    (Q:=Q) (x:=xiP ν p K B lam h S Q) (by linarith [P.hν1]) k
  rw [he] at hge
  have := le_antisymm hle hge
  simpa only [detectorP, cutoffP] using this

/-- The class root is at least the slot-free root `baseXi ν Q`. -/
theorem xiP_lower {ν p K B lam h S Q : ℝ} (P : ClassParams ν p lam) (hK : 0 ≤ K)
    (hB : 22/23 ≤ B) (hh : 0 ≤ h) (hS : 0 ≤ S) (hQ : 0 ≤ Q) :
    baseXi ν*Q ≤ xiP ν p K B lam h S Q := by
  have hd : 0 < densityDenom ν := by simp only [densityDenom]; linarith [P.hν1]
  have hb0 : 5/6 ≤ baseXi ν := by
    rw [baseXi, le_div_iff₀ hd]; simp only [densityDenom]; linarith [P.hν0]
  have hb1 : baseXi ν ≤ 20/21 := by
    rw [baseXi, div_le_iff₀ hd]; simp only [densityDenom]; linarith [P.hν1]
  set x := baseXi ν*Q with hxdef
  have hx0 : 0 ≤ x := mul_nonneg (by linarith) hQ
  have hxQ : x ≤ Q := by nlinarith
  have hxB : x ≤ B*Q := by nlinarith
  have hp0 := P.hp0
  have hp1 := P.hp1
  have hlam0 : 0 < lam := by linarith [P.hlam]
  have h1p : 0 < 1 - p := by linarith
  have hd2 : 0 < 1 - 2*p/lam := by rw [sub_pos, div_lt_one hlam0]; linarith [P.hlam]
  have hi : invThr p K x S Q ≤ x := by
    refine max_le (by nlinarith [mul_nonneg (mul_nonneg hp0 hK) hS]) ?_
    rw [div_le_iff₀ h1p]; nlinarith
  have hpl : plainThr p B lam h x S Q ≤ x := by
    refine max_le (by nlinarith [mul_nonneg hp0 hS]) (max_le
      (by nlinarith [mul_nonneg (mul_nonneg hp0 hh) hQ]) ?_)
    rw [div_le_iff₀ hd2]
    have e : x*(1 - 2*p/lam) = x - 2*p*x/lam := by field_simp
    rw [e]
    have : 2*p*x/lam ≤ 2*p*B*Q/lam := by
      apply div_le_div_of_nonneg_right _ hlam0.le
      nlinarith
    linarith
  apply (detectorP_le_iff P).mp
  have hw : 0 ≤ w ν := by simp only [w]; linarith [P.hν1]
  have he : 6*ν*x + w ν*(x + x/2) = 5*Q := by
    have hd' : (15 - 6*ν) ≠ 0 := by linarith [P.hν1]
    have hx' : x = 10/(15 - 6*ν)*Q := by rw [hxdef, baseXi, densityDenom]
    rw [hx']
    simp only [w]
    field_simp
    ring
  simp only [detectorP]
  have ht := mul_le_mul_of_nonneg_left (show invThr p K x S Q + plainThr p B lam h x S Q/2 ≤
    x + x/2 by linarith) hw
  linarith

theorem xiP_le_of_branch {ν p K B lam h S Q y : ℝ} (P : ClassParams ν p lam) (k : Branch)
    (hk : 5*Q ≤ branchValueP ν p K B lam h S Q y k) : xiP ν p K B lam h S Q ≤ y := by
  apply (Finset.inf'_le _ (Finset.mem_univ k)).trans
  rw [branchRoot, div_le_iff₀ (P.slope_pos k)]
  simp only [branchValueP] at hk
  nlinarith

/-- The class root is at most the ambient exponent `Q` (inverse-cap / width-cap branch). -/
theorem xiP_le_Q {ν p K B lam h S Q : ℝ} (P : ClassParams ν p lam) (hh1 : h ≤ 1)
    (hQ : 0 ≤ Q) : xiP ν p K B lam h S Q ≤ Q := by
  apply xiP_le_of_branch P (1, 1)
  have hp1 := P.hp1
  have h1p : 0 < 1 - p := by linarith
  have he : branchValueP ν p K B lam h S Q Q (1, 1) = 5*Q + w ν*((1 - 2*p*h)*Q/2) := by
    show (6*ν + w ν*(1/(1-p) + 1/2))*Q + w ν*(-(p*Q)/(1-p) + -(2*p*h*Q)/2) = _
    have h1p' : (1 - p) ≠ 0 := by linarith
    simp only [w]
    field_simp
    ring
  rw [he]
  have hw : 0 ≤ w ν := by simp only [w]; linarith [P.hν1]
  have : 0 ≤ w ν*((1 - 2*p*h)*Q/2) := by
    apply mul_nonneg hw
    apply div_nonneg _ (by norm_num)
    apply mul_nonneg _ hQ
    nlinarith [P.hp0]
  linarith

/-- The class root is at most `B Q` (inverse-cap / affine branch), for `B ≥ 22/23`. -/
theorem xiP_le_BQ {ν p K B lam h S Q : ℝ} (P : ClassParams ν p lam) (hB : 22/23 ≤ B)
    (hB1 : B ≤ 1) (hQ : 0 ≤ Q) : xiP ν p K B lam h S Q ≤ B*Q := by
  apply xiP_le_of_branch P (1, 2)
  have hp0 := P.hp0
  have hp1 := P.hp1
  have hlam0 : 0 < lam := by linarith [P.hlam]
  have h1p : 0 < 1 - p := by linarith
  have hd2 : 0 < 1 - 2*p/lam := by rw [sub_pos, div_lt_one hlam0]; linarith [P.hlam]
  have hval : branchValueP ν p K B lam h S Q (B*Q) (1, 2) =
      6*ν*(B*Q) + w ν*((B - p)/(1 - p)*Q + B*Q/2) := by
    show (6*ν + w ν*(1/(1-p) + (1/(1-2*p/lam))/2))*(B*Q) +
      w ν*(-(p*Q)/(1-p) + (-(2*p*B*Q/lam)/(1-2*p/lam))/2) = _
    have hd2' : (1 - 2*p/lam) ≠ 0 := ne_of_gt hd2
    have key : (1/(1-2*p/lam)) * (1 - 2*p/lam) = 1 := one_div_mul_cancel hd2'
    have hpl : (1/(1-2*p/lam))*(B*Q) + (-(2*p*B*Q/lam)/(1-2*p/lam)) = B*Q := by
      rw [neg_div, div_eq_mul_one_div (2*p*B*Q/lam)]
      linear_combination (B*Q) * key
    linear_combination (w ν / 2) * hpl
  rw [hval]
  have hw : 0 ≤ w ν := by simp only [w]; linarith [P.hν1]
  -- (B - p)/(1-p) ≥ 2B - 1 since (B-p) - (2B-1)(1-p) = (1-B)(1-2p) ≥ 0
  have hBp : 2*B - 1 ≤ (B - p)/(1 - p) := by
    rw [le_div_iff₀ h1p]; nlinarith
  have hgate : 5 ≤ 6*ν*B + w ν*(2*B - 1 + B/2) := by
    simp only [w]; nlinarith [P.hν0, P.hν1]
  have h1 := mul_le_mul_of_nonneg_left hBp hw
  have h2 := mul_le_mul_of_nonneg_right hgate hQ
  nlinarith [mul_le_mul_of_nonneg_right h1 hQ]

/-- The class cutoff lies in `[Q, 10 Q/7]`. -/
theorem cutoffP_bounds {ν p K B lam h S Q : ℝ} (P : ClassParams ν p lam) (hK : 0 ≤ K)
    (hB : 22/23 ≤ B) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hS : 0 ≤ S) (hQ : 0 ≤ Q) :
    Q ≤ cutoffP ν p K B lam h S Q ∧ cutoffP ν p K B lam h S Q ≤ 10*Q/7 := by
  have hbal := cutoffP_balance (K:=K) (B:=B) (h:=h) (S:=S) (Q:=Q) P
  have hx0 := xiP_lower (K:=K) (S:=S) P hK hB hh0 hS hQ
  have hx1 := xiP_le_Q (K:=K) (B:=B) (S:=S) P hh1 hQ
  have hν0 := P.hν0
  have hν1 := P.hν1
  have hw : 0 < w ν := by simp only [w]; linarith
  have hd : 0 < densityDenom ν := by simp only [densityDenom]; linarith
  have hbase : densityDenom ν*baseXi ν = 10 := by
    rw [baseXi, mul_div_cancel₀ _ (ne_of_gt hd)]
  constructor
  · -- w cutoff = 5Q - 6 ν ξ ≥ (5 - 6ν) Q
    simp only [w] at hbal hw
    nlinarith
  · -- (5 - 2ν) cutoff ≤ 5 Q from ξ ≥ 10 Q/(15 - 6ν)
    have hc : 10*Q ≤ densityDenom ν*xiP ν p K B lam h S Q := by
      have := mul_le_mul_of_nonneg_left hx0 hd.le
      nlinarith [hbase]
    simp only [densityDenom, w] at hc hbal hw
    have hceil : (5 - 2*ν)*cutoffP ν p K B lam h S Q ≤ 5*Q := by nlinarith
    have hpos : 0 ≤ cutoffP ν p K B lam h S Q := by nlinarith
    nlinarith

/-- The second inverse admission: on the class root, `invThr ≥ 2 ξ - Q`. -/
theorem invThr_ge_two {p K x S Q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1/2) (hxQ : x ≤ Q) :
    2*x - Q ≤ invThr p K x S Q := by
  have h1p : 0 < 1 - p := by linarith
  apply le_trans _ (le_max_right _ _)
  rw [le_div_iff₀ h1p]
  nlinarith

/-- The count identity: `Q - ν ξ_p = ρ Q - f_p + (1-2p) ν S`. -/
theorem gainP_count_identity (ν p K B lam h S Q : ℝ) :
    Q - ν*xiP ν p K B lam h S Q =
      (1 - ν*baseXi ν)*Q - gainP ν p K B lam h S Q + (1-2*p)*ν*S := by
  simp only [gainP]
  ring

end
end QRH.RepeatedMarks
