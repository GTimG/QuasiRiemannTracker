/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The genuine natural capacity projects to the current top physical price. -/
import Candidate.C092.transport.NaturalPacketLowPrice
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open QRH.Cycle090 QRH.Cycle092.Direct QRH.Cycle092.SelectedNonfloor
namespace QRH.Cycle092.NaturalPacketLow
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

lemma natural_price_mono {δ p R d d' : ℝ} (hδ : 0≤δ) (hδ' : δ≤3/4)
    (hp : 0≤p) (hp' : p≤1/2) (hr : 1-δ≤R) (hdd : d≤d') :
    naturalRowPrice δ p R d ≤ naturalRowPrice δ p R d' := by
  have hcap := natural_capacity_increment hdd
  have hprod : 0≤δ*p := mul_nonneg hδ hp
  have hprod' : δ*p≤3/8 := by nlinarith [mul_le_mul_of_nonneg_left hp' hδ]
  have hcoef : 0≤3*R/4-9/100-δ*p/8 := by nlinarith
  have hw := mul_le_mul_of_nonneg_left hcap hprod
  have hn := mul_nonneg hcoef (sub_nonneg.mpr hdd)
  unfold naturalRowPrice
  nlinarith

/-- The comparison retains the actual natural min and actual upper cap.
It applies to any proved count above the unavoidable unmarked count. -/
theorem natural_price_le_native_top {δ p R d : ℝ}
    (hδ : 0≤δ) (hδ' : δ≤3/4) (hp : 0≤p) (hp' : p≤1/2) (hr : 1-δ≤R)
    (hd : d≤19/25) (hh : hLower≤Geometry.h) (hh' : Geometry.h≤hUpper)
    (hell : Geometry.ell=Physical.ell) :
    naturalRowPrice δ p R d ≤ rowPrice δ p R Geometry.h sourceCost := by
  have hy : Geometry.y=Geometry.h-2*Physical.ell := by
    unfold Geometry.h; rw [←hell]; linarith [Geometry.x_add_y]
  have hh0 : 0<Geometry.h := by norm_num [hLower] at hh;linarith
  have hΔ : 0≤Geometry.h-19/25 := by norm_num [hLower] at hh;linarith
  have hs := allowances_pos.1.le
  have hden : 0<2+10*sourceCost := by positivity
  have hkap : 0<6*kap := by have h:=q_kappa_bounds.1;linarith
  have hmin : 2*Geometry.y-(19/25:ℝ)≤19/25 := by linarith [ActualGeometry.WidenedCoreBounds.ly_coarse.2]
  have hnatural : Geometry.y-Geometry.h/2-absoluteCapacity kap (19/25)≤(Geometry.h-19/25)/2 := by
    unfold absoluteCapacity
    rw [min_eq_right hmin]
    have hb : Geometry.y-Geometry.h+19/50≤(2*Geometry.y-19/25)/(6*kap) := by
      apply (le_div_iff₀ hkap).2
      rw [hy]
      norm_num [kap,QRH.ContactCertificate.alphaHi,Physical.ell,theta,hLower,hUpper] at hh hh' ⊢
      linarith
    linarith
  have hupper : cappedCapacity physicalCap Geometry.y sourceCost Geometry.h≤Geometry.y-Geometry.h/2 := by
    apply (min_le_right _ _).trans
    apply (div_le_iff₀ hden).2
    have hg : 0≤10*Geometry.y-4*Geometry.h := by
      rw [hy]
      norm_num [Physical.ell,theta,hLower] at hh ⊢
      linarith
    nlinarith [mul_nonneg hs hg]
  have hcap := hupper.trans (by linarith [hnatural] : Geometry.y-Geometry.h/2≤
    absoluteCapacity kap (19/25)+(Geometry.h-19/25)/2)
  have hprod : 0≤δ*p := mul_nonneg hδ hp
  have hprod' : δ*p≤3/8 := by nlinarith [mul_le_mul_of_nonneg_left hp' hδ]
  have hcoef : 0≤3*R/4-9/100-δ*p/4 := by nlinarith
  have hw := mul_le_mul_of_nonneg_left hcap hprod
  have hn := mul_nonneg hcoef hΔ
  have hscaled := Physical.Selection.scaled_zero_capacity (y:=Geometry.y) (s:=sourceCost) hh0
  have htop : naturalRowPrice δ p R (19/25)≤rowPrice δ p R Geometry.h sourceCost := by
    unfold naturalRowPrice rowPrice
    rw [hscaled]
    nlinarith
  exact (natural_price_mono hδ hδ' hp hp' hr hd).trans htop

end QRH.Cycle092.NaturalPacketLow
#print axioms QRH.Cycle092.NaturalPacketLow.natural_price_le_native_top
