/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Convert the source gain and the four real count routes to the terminal
penalty. The negative constant face uses the actual crossing length. -/
import Candidate.C092.transport.MixedCenteredFaces
set_option autoImplicit false
noncomputable section
open QRH.Cycle090 QRH.Coverage QRH.ContactCertificate
open QRH.Cycle092.TopData QRH.Cycle092.Mixed QRH.Cycle092.ActualMixedPrice
namespace QRH.Cycle092.MixedCenteredFaces

theorem paired_center_eq {δ p g₀ g₁ : ℝ} (hJ : pairedJ δ p g₁ ≠ 0) :
    pairedCount δ p g₀ g₁ =
    1-δ*(p*(1+2*g₀)+pairedK p g₁*(2*(pairedCrossing δ p g₀ g₁/3))) := by
  rw [pairedCount_eq hJ]
  unfold pairedCrossing
  field_simp
  dsimp [pairedJ,pairedV,pairedU,pairedK]
  ring

theorem directed_parameters {r : Row} (hr : r∈rows) {point : Point} (hp : r.box.Contains point) :
    0≤(rowKLower r.box:ℝ) ∧ 0≤(rowV r.box:ℝ)/(r.box.uHi:ℝ) ∧
      point.1*((rowV r.box:ℝ)/(r.box.uHi:ℝ)) ≤ pairedV point.1 := by
  have hs := Top.shape_of_check (List.all_eq_true.mp Top.all_rows_checked r hr)
  have ht := Top.point_guards hs hp
  have hhi : (r.box.uHi:ℝ) ≤ (1/2:ℝ) := by
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using ((Rat.cast_le (K:=ℝ)).mpr hs.2.2.2.1)
  have hvhi : (r.box.vHi:ℝ) ≤ (1/2:ℝ) := by
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using ((Rat.cast_le (K:=ℝ)).mpr hs.2.2.2.2.2.2.1)
  have hlo : 0 < (r.box.uHi:ℝ) := (Rat.cast_pos.mpr hs.2.1).trans_le (hp.1.trans hp.2.1)
  have hV : 0 ≤ (rowV r.box:ℝ) := by norm_num [rowV]; linarith
  have hk : 0 ≤ (rowKLower r.box:ℝ) := by
    norm_num [rowKLower,g1Receipt]; linarith only [hvhi]
  refine ⟨hk,div_nonneg hV hlo.le,?_⟩
  have h₁ := mul_le_mul_of_nonneg_right hp.2.1 (div_nonneg hV hlo.le)
  rw [mul_div_cancel₀ _ hlo.ne'] at h₁
  apply h₁.trans
  norm_num [pairedV,rowV]; linarith only [hp.2.1]

/-- At a mixed terminal use the native counts with their own tangent mark
quotas. The preceding inverse, when needed, has its own source bound. -/
theorem terminal_centered_count {ι : Type*} (s : Finset ι) {r : Row} (hr : r∈rows)
    {point : Point} (hp : r.box.Contains point) {contact : ℝ}
    (hx : QRH.RationalInterval.Contains alphaInterval contact) (U C ξ inv z prev loss : ℝ)
    (hU : 1 ≤ U) (hC : 0≤C) (hξ : 0≤ξ) :
    let δ := point.1
    let p := point.2
    let g₀ := g0 (wValue contact)
    let g₁ := g1 (wValue contact)
    let k := pairedK p g₁
    let R := pairedCount δ p g₀ g₁
    let m := pairedCrossing δ p g₀ g₁/3
    let quota := fun w => (1-w)/2+g₀-g₁*w
    let left := ξ-(rowGamma r.box r.B:ℝ)/65536-3*witnessCollar
    3*m-ξ-3*witnessCollar ≤ inv+z →
    (s.card:ℝ) ≤ C*U^(R+loss) →
    (s.card:ℝ) ≤ C*U^(1-(δ*inv+2*(δ*p)*quota inv)+loss) →
    (s.card:ℝ) ≤ C*U^(1-(δ*(2*z)+2*(δ*p)*quota (2*z))+loss) →
    (0<left → prev ≤ 3*m-left ∧ (s.card:ℝ) ≤ C*U^(1/6+pairedV δ*prev+loss)) →
    (s.card:ℝ) ≤ C*U^(R-δ*(penalty r ξ z-k*(z-m))+loss) := by
  dsimp only
  intro hsupport hbase hinv hord hprev
  let δ := point.1
  let p := point.2
  let g₀ := g0 (wValue contact)
  let g₁ := g1 (wValue contact)
  let k := pairedK p g₁
  let m := pairedCrossing δ p g₀ g₁/3
  let frac := (rowV r.box:ℝ)/(r.box.uHi:ℝ)
  let prevGain := frac*max 0 (ξ-(rowGamma r.box r.B:ℝ)/65536-3*witnessCollar)
  have hpar := directed_parameters hr hp
  have hguard := Top.point_guards (Top.shape_of_check (List.all_eq_true.mp Top.all_rows_checked r hr)) hp
  have hk := actual_k_bounds hr hp hx
  have hmm := actual_crossing_upper hr hp hx
  have hadm := Physical.actual_contact_bounds hx
  have hJ : pairedJ δ p g₁ ≠ 0 := (Physical.admitted (g₀:=g0 (wValue contact)) (g₁:=g1 (wValue contact)) hguard.1 hguard.2.1 hguard.2.2.1 hguard.2.2.2
    (by linarith only [hadm.1]) (by linarith only [hadm.2.1])
    (by linarith only [hadm.2.2.1]) (by linarith only [hadm.2.2.2])).2.1.ne'
  have hR := paired_center_eq (g₀:=g₀) hJ
  have hv : 0 ≤ pairedV δ := by dsimp [pairedV,δ]; linarith only [hguard.2.1]
  have hpr := predecessor_count s (factor:=frac) (m:=m) hU hC hv hpar.2.2
    (show pairedCount δ p g₀ g₁=1/6+pairedV δ*(3*m) by rw [pairedCount_eq hJ]; dsimp [m]; ring)
    hbase hprev
  rw [tangent_inverse_identity] at hinv hord
  have hh := centered_count s (U:=U) (C:=C) (R:=pairedCount δ p g₀ g₁) (δ:=δ)
    (A:=p*(1+2*g₀)) (k:=k) (x:=inv) (z:=z) (m:=m) (h:=prevGain) (loss:=loss) hU hguard.1 (hpar.1.trans hk.1) hR hbase hinv (by
    dsimp only [k,p,δ,g₀,g₁,pairedK]; convert hord using 2 <;> ring) hpr
  have hc := directed_penalty (step:=0) (k:=k) (x:=inv) (z:=z) (m:=m) (M:=(rowM r.box:ℝ)+witnessCollar)
    (h:=prevGain) hpar.1 hk.1 hk.2 (hmm.trans (by unfold witnessCollar; linarith))
    hξ (by norm_num [witnessCollar] : 0≤3*witnessCollar) hsupport
  apply hh.trans
  apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU ?_) hC
  change pairedCount δ p g₀ g₁-δ*center k inv z m prevGain+loss ≤
    pairedCount δ p g₀ g₁-δ*(penalty r ξ z-k*(z-m))+loss
  change penalty r ξ z ≤ k*(z-m)+center k inv z m prevGain at hc
  nlinarith only [mul_le_mul_of_nonneg_left hc (show 0≤δ from hguard.1)]

#print axioms terminal_centered_count
end QRH.Cycle092.MixedCenteredFaces
end
