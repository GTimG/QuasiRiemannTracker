/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.CommonGain
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.Homogeneous
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High
noncomputable section

theorem rho_eq_original (nu : ℝ) : rho nu=Record12518109Gain.rho nu := by
  dsimp [rho,baseXi,densityDenom,Record12518109Gain.rho]
  rw [show (15:ℝ)-6*nu=3*(5-2*nu) by ring]
  ring

theorem branch_gain_scale (nu B lam h S Q a : ℝ) (k : Branch) :
    nu*(branchRoot nu B lam h (a*S) (a*Q) k-baseXi nu*(a*Q))=
      a*(nu*(branchRoot nu B lam h S Q k-baseXi nu*Q)) := by
  rw [branch_gain_affine,branch_gain_affine]
  ring

theorem gain_homogeneous {nu B lam h S Q a : ℝ} (hnu : 0≤nu) (ha : 0≤a) :
    gain nu B lam h (a*S) (a*Q)=a*gain nu B lam h S Q := by
  apply le_antisymm
  · obtain ⟨k,hk⟩ := gain_eq_some_branch nu B lam h S Q
    have hle := gain_le_branch (B:=B) (lam:=lam) (h:=h) (S:=a*S) (Q:=a*Q) hnu k
    rw [branch_gain_scale,←hk] at hle
    exact hle
  · obtain ⟨k,hk⟩ := gain_eq_some_branch nu B lam h (a*S) (a*Q)
    have hle := mul_le_mul_of_nonneg_left
      (gain_le_branch (B:=B) (lam:=lam) (h:=h) (S:=S) (Q:=Q) hnu k) ha
    rw [branch_gain_scale] at hk
    exact hle.trans_eq hk.symm

theorem gain_rescale {nu B lam h S F : ℝ} (hnu : 0≤nu) (hF : 0<F) :
    F*gain nu B lam h (S/F) 1=gain nu B lam h S F := by
  have hh := gain_homogeneous (B:=B) (lam:=lam) (h:=h) (S:=S/F) (Q:=1) hnu hF.le
  rw [mul_div_cancel₀ _ hF.ne',mul_one] at hh
  exact hh.symm

theorem homogeneous_power_rescale {nu B lam h S F Z : ℝ}
    (hnu : 0≤nu) (hF : 0<F) (hZ : 0≤Z) :
    (Z^F)^(rho nu+nu*(S/F)-gain nu B lam h (S/F) 1)=
      Z^(rho nu*F+nu*S-gain nu B lam h S F) := by
  rw [←Real.rpow_mul hZ]
  congr 1
  rw [←gain_rescale hnu hF]
  field_simp

/-- The ordinary child HIGH residual is the complement of the physical
power after the common source has ambient exponent `1-6*a`. This only
converts the exact six checked gates; the actual physical sum still uses
the proved coefficient/row transport. -/
theorem regular_power_gate {nu B lam h S a T fee : ℝ}
    (hn0 : 1/2≤nu) (hn1 : nu≤3/4) (hl : 1<lam)
    (hgates : ∀k : Branch,fee<1-rho nu-nu*T-a*(5-6*rho nu)+
      facet nu B lam h S (1-6*a) k) :
    rho nu*(1-6*a)+nu*T+5*a-gain nu B lam h S (1-6*a)<1-fee := by
  have hg := regular_gate_of_six hn0 hn1 hl hgates
  nlinarith

end
end QRH.Record1252270103Source.High
#print axioms QRH.Record1252270103Source.High.gain_homogeneous
#print axioms QRH.Record1252270103Source.High.homogeneous_power_rescale
#print axioms QRH.Record1252270103Source.High.regular_power_gate
