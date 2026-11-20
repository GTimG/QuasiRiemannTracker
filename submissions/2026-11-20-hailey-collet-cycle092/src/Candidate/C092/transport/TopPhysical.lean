/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.TopKernel

/-! Pointwise original-price and normalized-debit meaning of checked top rows.
The quotient signs and all box/conductor contracts remain explicit. This does
not turn the paired-count scalar into an analytic count theorem. -/
set_option autoImplicit false
set_option maxRecDepth 16384
namespace QRH.Cycle092.Top
open QRH.Cycle090 QRH.Cycle092.TopConstants QRH.Cycle092.TopData
noncomputable section

/-- The modest directed contact constants conservatively enclose the authentic endpoints. -/
theorem contact_rounding :
    g0Lower≤QRH.ContactCertificate.g0Receipt.lo ∧
    QRH.ContactCertificate.g1Receipt.hi≤g1Upper ∧
    0≤g0Lower ∧ g0Lower≤3/50 ∧ 7/100≤g1Upper ∧ g1Upper≤2/25 := by
  decide +kernel

/-- Real contact data retain all bounds used by the original paired count. -/
def ContactBounds (g₀ g₁ : ℝ) : Prop :=
  (g0Lower:ℝ)≤g₀ ∧ g₀≤3/50 ∧ 7/100≤g₁ ∧ g₁≤(g1Upper:ℝ)

theorem actual_contact {x : ℝ}
    (hx : QRH.RationalInterval.Contains QRH.ContactCertificate.alphaInterval x) :
    ContactBounds (QRH.ContactCertificate.g0 (QRH.ContactCertificate.wValue x))
      (QRH.ContactCertificate.g1 (QRH.ContactCertificate.wValue x)) := by
  have hg₀ := QRH.ContactCertificate.g0_receipt_sound hx
  have hg₁ := QRH.ContactCertificate.g1_receipt_sound hx
  have hr := QRH.Cycle092.Physical.actual_contact_bounds hx
  have h0 : (g0Lower:ℝ)≤(QRH.ContactCertificate.g0Receipt.lo:ℝ) := Rat.cast_le.mpr contact_rounding.1
  have h1 : (QRH.ContactCertificate.g1Receipt.hi:ℝ)≤(g1Upper:ℝ) := Rat.cast_le.mpr contact_rounding.2.1
  exact ⟨h0.trans hg₀.1,by linarith [hr.2.1],by linarith [hr.2.2.1],hg₁.2.trans h1⟩

/-- The refined proxy lies below the literal original capped capacity. -/
theorem capacity_lower {h : ℝ} (_hh : hLower≤h) (hh' : h≤hUpper) :
    capacityProxy h≤cappedCapacity physicalCap (h-2*QRH.Cycle090.ell) sourceCost h := by
  have hs : 0≤sourceCost ∧ sourceCost≤1/10^(30:ℕ) := by
    constructor
    · exact allowances_pos.1.le
    · have hpow : (10:ℝ)^30≤10^(260:ℕ) := pow_le_pow_right₀ (by norm_num) (by norm_num)
      have hp := one_div_le_one_div_of_le (by positivity : (0:ℝ)<10^(30:ℕ)) hpow
      exact hp
  have h1 : h≤1 := hh'.trans conductor_interval.2.2.le
  have hc : capacityProxy h≤1 := by
    norm_num [capacityProxy,QRH.Cycle090.ell,theta] at hh' ⊢
    norm_num [hUpper] at hh'
    linarith
  unfold cappedCapacity
  apply le_min
  · norm_num [capacityProxy,physicalCap,QRH.Cycle090.ell,theta] at hh' ⊢
    norm_num [hUpper] at hh'
    linarith
  · apply (le_div_iff₀ (by linarith : 0<2+10*sourceCost)).mpr
    have hsh := mul_le_mul_of_nonneg_left h1 hs.1
    have hsc := mul_le_mul_of_nonneg_left hc hs.1
    dsimp [capacityProxy] at hsc ⊢
    norm_num at hs hsc ⊢
    nlinarith

/-- The original paired count is no larger than its directed refined contact value. -/
theorem count_upper {d p g₀ g₁ : ℝ}
    (hd : 0≤d) (hd' : d≤1/2) (hp : 0≤p) (hp' : p≤1/2)
    (hg : ContactBounds g₀ g₁) :
    pairedCount d p g₀ g₁≤pairedCount d p (g0Lower:ℝ) (g1Upper:ℝ) := by
  have hq0 : (0:ℝ)≤(g0Lower:ℝ) := Rat.cast_nonneg.mpr contact_rounding.2.2.1
  have hq0' : (g0Lower:ℝ)≤3/50 := by
    simpa only [Rat.cast_div,Rat.cast_ofNat] using ((Rat.cast_le (K:=ℝ)).mpr contact_rounding.2.2.2.1)
  have hq1 : (7/100:ℝ)≤(g1Upper:ℝ) := by
    simpa only [Rat.cast_div,Rat.cast_ofNat] using ((Rat.cast_le (K:=ℝ)).mpr contact_rounding.2.2.2.2.1)
  have hq1' : (g1Upper:ℝ)≤2/25 := by
    simpa only [Rat.cast_div,Rat.cast_ofNat] using ((Rat.cast_le (K:=ℝ)).mpr contact_rounding.2.2.2.2.2)
  have ha := QRH.Cycle092.Physical.admitted hd hd' hp hp'
    (hq0.trans hg.1) hg.2.1 hg.2.2.1 (hg.2.2.2.trans hq1')
  have hb := QRH.Cycle092.Physical.admitted hd hd' hp hp' hq0 hq0' hg.2.2.1 (hg.2.2.2.trans hq1')
  have hc := QRH.Cycle092.Physical.admitted hd hd' hp hp' hq0 hq0' hq1 hq1'
  exact (pairedCount_antitone_g₀ hd (by linarith) hp hg.1 ha.2.1).trans
    (pairedCount_monotone_g₁ hd (by linarith) hp hg.2.2.2 hb.1 hb.2.1 hc.2.1)

/-- Every checked row's frozen B genuinely bounds the original Q1 top excess. -/
theorem top_budget {r : Row} (hc : check r=true) {h g₀ g₁ : ℝ} {point : QRH.Coverage.Point}
    (hh : hLower≤h) (hh' : h≤hUpper) (hp : r.box.Contains point)
    (hg : ContactBounds g₀ g₁) :
    QRH.Cycle092.Physical.price h point.1 point.2 g₀ g₁ h-theta≤(r.B:ℝ) := by
  have hs := shape_of_check hc
  have hguard := point_guards hs hp
  have hden := denominator_lower hs hp
  have hB : (0:ℝ)≤(r.B:ℝ) := Rat.cast_nonneg.mpr hs.1
  have hclear := cleared_lower hc hh hh' hp
  have hM : -(r.B:ℝ)*(denominatorLower r.box:ℝ)≤0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hden.1.le
  have hdiv := cleared_margin_nonpositive hM hclear hden.1 hden.2
  have hJ : 0<pairedJ point.1 point.2 (g1Upper:ℝ) := hden.1.trans_le hden.2
  have he := pairedCount_clear_margin (d:=point.1) (p:=point.2)
    (g₀:=(g0Lower:ℝ)) (g₁:=(g1Upper:ℝ)) (target:=theta)
    (base:=baseProxy h point.1 point.2) (h:=h) (ne_of_gt hJ)
  change cleared h point.1 point.2 = _ at he
  rw [he] at hdiv
  have hproxy : -(r.B:ℝ)≤theta-
      (baseProxy h point.1 point.2+3*h*pairedCount point.1 point.2 (g0Lower:ℝ) (g1Upper:ℝ)/4) := by
    simpa only [mul_div_cancel_right₀ _ (ne_of_gt hden.1),
      mul_div_cancel_left₀ _ (ne_of_gt hJ)] using hdiv
  have hcap := mul_le_mul_of_nonneg_left (capacity_lower hh hh')
    (mul_nonneg hguard.1 hguard.2.2.1)
  have hr := count_upper hguard.1 hguard.2.1 hguard.2.2.1 hguard.2.2.2 hg
  have hcount := mul_le_mul_of_nonneg_left hr
    (by have h0:=conductor_interval.1.le.trans hh; positivity : 0≤3*h/4)
  dsimp [QRH.Cycle092.Physical.price,baseProxy,QRH.Cycle092.Physical.ell,QRH.Cycle090.ell] at hproxy hcap ⊢
  nlinarith

/-- The normalized budget uses exactly the frozen B and Q's allocated inward debit. -/
def debit (r : Row) : ℝ := ((r.B:ℝ)+inwardDebit)/hLower

theorem rationalDebit_cast (r : Row) : (rationalDebit r:ℝ)=debit r := by
  norm_num [rationalDebit,debit,inwardDebit,hLower]

theorem rationalSlope_cast (b : QRH.Coverage.Box) :
    (rationalSlope b:ℝ)=boxSlope (b.uHi:ℝ) physicalCap := by
  norm_num [rationalSlope,boxSlope,physicalCap]

theorem normalizedDebit_eq {r : Row} (hs : Shape r) :
    normalizedDebit (r.B:ℝ) inwardDebit hLower=debit r := by
  have hB : (0:ℝ)≤(r.B:ℝ) := Rat.cast_nonneg.mpr hs.1
  simp only [normalizedDebit,debit,max_eq_right hB]

/-- Each checked row has the strict original conductor slope surplus S>q0. -/
theorem conductor_slope {r : Row} (hc : check r=true) :
    debit r<boxSlope (r.box.uHi:ℝ) physicalCap := by
  have hq := (shape_of_check hc).2.2.2.2.2.2.2.2
  have hr : (rationalDebit r:ℝ)<(rationalSlope r.box:ℝ) := Rat.cast_lt.mpr hq
  rwa [rationalDebit_cast,rationalSlope_cast] at hr

/-- The original physical Q2 bound, with positive denominator signs discharged by the row. -/
theorem normalized_physical_debit {r : Row} (hc : check r=true)
    {h g₀ g₁ D : ℝ} {point : QRH.Coverage.Point}
    (hh : hLower≤h) (hh' : h≤hUpper) (hp : r.box.Contains point)
    (hg : ContactBounds g₀ g₁) (hD : 0≤D) (hDh : D≤h) :
    positivePart (QRH.Cycle092.Physical.price h point.1 point.2 g₀ g₁ D-theta+inwardDebit)≤
      D*debit r := by
  have hs := shape_of_check hc
  have hguard := point_guards hs hp
  have hq0 : (0:ℝ)≤(g0Lower:ℝ) := Rat.cast_nonneg.mpr contact_rounding.2.2.1
  have hq1' : (g1Upper:ℝ)≤2/25 := by
    simpa only [Rat.cast_div,Rat.cast_ofNat] using ((Rat.cast_le (K:=ℝ)).mpr contact_rounding.2.2.2.2.2)
  have hj := QRH.Cycle092.Physical.admitted hguard.1 hguard.2.1 hguard.2.2.1 hguard.2.2.2
    (hq0.trans hg.1) hg.2.1 hg.2.2.1 (hg.2.2.2.trans hq1')
  have hR := pairedCount_lower hguard.1 (by linarith) hj.1 hj.2.1
  have htop := top_budget hc hh hh' hp hg
  rw [QRH.Cycle092.Physical.price_eq_conductorPrice] at htop ⊢
  have hnorm := normalized_physical_debit_Q2 hguard.1 hguard.2.2.1 hguard.2.2.2 hp.2.1
    physicalCap_admissible.1.le allowances_pos.1.le hR allowances_pos.2.2.2.2.le
    conductor_interval.1 hh hD hDh
    (by rw [normalizedDebit_eq hs]; exact (conductor_slope hc).le) htop
  simpa only [normalizedDebit_eq hs] using hnorm

end
end QRH.Cycle092.Top
#print axioms QRH.Cycle092.Top.top_budget
#print axioms QRH.Cycle092.Top.normalized_physical_debit
