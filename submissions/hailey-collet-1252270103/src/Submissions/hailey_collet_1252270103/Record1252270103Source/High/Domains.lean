/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.Selection

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High
noncomputable section

theorem baseXi_bounds {nu : ℝ} (hnu0 : 1/2≤nu) (hnu1 : nu≤3/4) :
    5/6≤baseXi nu ∧ baseXi nu≤20/21 := by
  have hd : 0<densityDenom nu := by dsimp [densityDenom]; linarith
  constructor
  · rw [baseXi,le_div_iff₀ hd]
    dsimp [densityDenom]
    linarith
  · rw [baseXi,div_le_iff₀ hd]
    dsimp [densityDenom]
    linarith

theorem xi_lower {nu B lam h S Q : ℝ}
    (hnu0 : 1/2≤nu) (hnu1 : nu≤3/4) (hB : 22/23≤B)
    (hlam : 1<lam) (hh : 0≤h) (hS : 0≤S) (hQ : 0≤Q) :
    baseXi nu*Q≤xi nu B lam h S Q := by
  have hb := baseXi_bounds hnu0 hnu1
  have hbaseB : baseXi nu≤B := by linarith
  have hbase1 : baseXi nu≤1 := by linarith
  have hxQ : baseXi nu*Q≤Q := by nlinarith
  have hBQ : baseXi nu*Q≤B*Q := mul_le_mul_of_nonneg_right hbaseB hQ
  have hi : inverseThreshold (baseXi nu*Q) S Q≤baseXi nu*Q :=
    max_le (by linarith) (by linarith)
  have hp : plainThreshold B lam h (baseXi nu*Q) S Q≤baseXi nu*Q := by
    refine max_le (by linarith) (max_le ?_ ?_)
    · nlinarith [mul_nonneg hh hQ]
    · apply (div_le_iff₀ (by linarith : 0<lam-1)).mpr
      nlinarith
  apply (detector_le_iff hnu0 hnu1 hlam).mp
  have hw : 0≤w nu := by dsimp [w]; linarith
  have he : 6*nu*(baseXi nu*Q)+w nu*(baseXi nu*Q+baseXi nu*Q/2)=5*Q := by
    dsimp [baseXi,densityDenom,w]
    field_simp (discharger := linarith)
    ring
  dsimp [detector]
  have ht := mul_le_mul_of_nonneg_left (show inverseThreshold (baseXi nu*Q) S Q+
    plainThreshold B lam h (baseXi nu*Q) S Q/2≤baseXi nu*Q+baseXi nu*Q/2 by linarith) hw
  linarith

theorem xi_le_of_branch_ge {nu B lam h S Q y : ℝ}
    (hnu0 : 1/2≤nu) (hnu1 : nu≤3/4) (hlam : 1<lam) (k : Branch)
    (hk : 5*Q≤branchValue nu B lam h S Q y k) : xi nu B lam h S Q≤y := by
  apply (Finset.inf'_le _ (Finset.mem_univ k)).trans
  rw [branchRoot,div_le_iff₀ (branchSlope_pos hnu0 hnu1 hlam k)]
  dsimp [branchValue] at hk
  nlinarith

theorem xi_upper {nu B lam h S Q : ℝ}
    (hnu0 : 1/2≤nu) (hnu1 : nu≤3/4) (hB : 22/23≤B)
    (hlam : 1<lam) (hQ : 0≤Q) : xi nu B lam h S Q≤B*Q := by
  apply xi_le_of_branch_ge hnu0 hnu1 hlam (1,2)
  have he : branchValue nu B lam h S Q (B*Q) (1,2)=
      (6*nu*B+w nu*(5*B/2-1))*Q := by
    norm_num [branchValue,branchSlope,branchOffset,inverseSlope,inverseOffset,
      plainSlope,plainOffset]
    field_simp (discharger := linarith)
    ring
  rw [he]
  have hw : 0<w nu := by dsimp [w]; linarith
  have hc : 0≤6*nu+5*w nu/2 := by positivity
  have hm := mul_le_mul_of_nonneg_right hB hc
  have hgate : 5≤6*nu*B+w nu*(5*B/2-1) := by
    dsimp [w] at *
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hgate hQ]

theorem xi_lt_ambient {nu B lam h S Q : ℝ}
    (hnu0 : 1/2≤nu) (hnu1 : nu≤3/4) (hlam : 1<lam)
    (hh : h<1) (hQ : 0<Q) : xi nu B lam h S Q<Q := by
  have hw : 0<w nu := by dsimp [w]; linarith
  have he : branchValue nu B lam h S Q Q (1,1)=5*Q+w nu*((1-h)*Q/2) := by
    norm_num [branchValue,branchSlope,branchOffset,inverseSlope,inverseOffset,
      plainSlope,plainOffset,w]
    ring
  have hstrict : 5*Q<branchValue nu B lam h S Q Q (1,1) := by
    rw [he]
    have ht : 0<w nu*((1-h)*Q/2) := by positivity
    linarith
  apply lt_of_le_of_lt (Finset.inf'_le _ (Finset.mem_univ (1,1)))
  rw [branchRoot,div_lt_iff₀ (branchSlope_pos hnu0 hnu1 hlam (1,1))]
  dsimp [branchValue] at hstrict
  nlinarith

theorem cutoff_bounds {nu B lam h S Q : ℝ}
    (hnu0 : 1/2≤nu) (hnu1 : nu≤3/4) (hB : 22/23≤B)
    (hlam : 1<lam) (hh0 : 0≤h) (hh1 : h<1) (hS : 0≤S) (hQ : 0<Q) :
    Q<cutoff nu B lam h S Q ∧ cutoff nu B lam h S Q≤10*Q/7 ∧
      2*Q/3≤ inverseThreshold (xi nu B lam h S Q) S Q := by
  have hx0 := xi_lower hnu0 hnu1 hB hlam hh0 hS hQ.le
  have hx1 := xi_lt_ambient (B:=B) (S:=S) hnu0 hnu1 hlam hh1 hQ
  have hb := baseXi_bounds hnu0 hnu1
  have hx56 : 5*Q/6≤xi nu B lam h S Q := by
    have := mul_le_mul_of_nonneg_right hb.1 hQ.le
    linarith
  have he := cutoff_balance (B:=B) (h:=h) (S:=S) (Q:=Q) hnu0 hnu1 hlam
  have hn : 0<nu := by linarith
  have hw : 0<w nu := by dsimp [w]; linarith
  have hstrict := mul_lt_mul_of_pos_left hx1 hn
  have hceil : (5-2*nu)*cutoff nu B lam h S Q≤5*Q := by
    have hbase : densityDenom nu*baseXi nu=10 := by
      dsimp [baseXi]
      rw [mul_div_cancel₀ _ (show densityDenom nu≠0 by dsimp [densityDenom]; linarith)]
    have hd : 0<densityDenom nu := by dsimp [densityDenom]; linarith
    have hxx := mul_le_mul_of_nonneg_left hx0 hd.le
    have hc : 10*Q≤densityDenom nu*xi nu B lam h S Q := by nlinarith [hbase]
    have hcnu := mul_le_mul_of_nonneg_left hc hn.le
    dsimp [densityDenom,w] at *
    nlinarith
  have htpos : 0<cutoff nu B lam h S Q := by
    have hcut : Q<cutoff nu B lam h S Q := by dsimp [w] at he hw; nlinarith
    exact hQ.trans hcut
  refine ⟨?_,?_,?_⟩
  · dsimp [w] at he hw
    nlinarith
  · nlinarith
  · have ht := le_max_right (xi nu B lam h S Q-S) (2*xi nu B lam h S Q-Q)
    change _≤ inverseThreshold (xi nu B lam h S Q) S Q at ht
    linarith

end
end QRH.Record1252270103Source.High
#print axioms QRH.Record1252270103Source.High.xi_lower
#print axioms QRH.Record1252270103Source.High.xi_upper
#print axioms QRH.Record1252270103Source.High.xi_lt_ambient
#print axioms QRH.Record1252270103Source.High.cutoff_bounds
