/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Native direct certificate at the actual conductor, with explicit source/count fees. -/
import Candidate.C092.transport.PacketJoinMean
import Candidate.C092.transport.DirectCountNativeAlgebra
import Candidate.C092.transport.DirectCertificates
import Candidate.C092.transport.SelectedNonfloorPrice
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open QRH.Record1252270103Return
open QRH.Cycle090 QRH.Cycle092.Direct QRH.Cycle092.DirectCount
open QRH.Cycle092.SelectedNonfloor QRH.Coverage
namespace QRH.Cycle092.PacketJoin
variable [Geometry.Parameters]

/-- A true native count stays above the unmarked 1-delta count. -/
theorem native_value_lower {δ p : ℝ} (hδ : 0≤δ) (hp : 0≤p) (hp' : p≤1/2)
    (hg : ∀ j:Fin 15,0<nativeGuard j sourceCost δ p) : 1-δ≤nativeValue sourceCost δ p := by
  have hn := native_data hδ hp hg
  have hc := native_cross_identity sourceCost δ p hn.Dpos hn.Jpos
  have hx := mul_le_mul_of_nonneg_left hn.crossHi (by linarith : 0≤1-p)
  have hh := mul_le_mul_of_nonneg_left (show p+(1-p)*nativeCross sourceCost δ p≤1 by linarith) hδ
  linarith

/-- Actual source-cap price is monotone up to the native certificate's top
conductor. The original count is unchanged throughout this comparison. -/
theorem native_row_price_le_top {δ p D : ℝ}
    (hδ : 0≤δ) (hδ' : δ≤3/4) (hp : 0≤p) (hp' : p≤1/2)
    (hg : ∀ j:Fin 15,0<nativeGuard j sourceCost δ p)
    (hD : 0<D) (hDh : D≤Geometry.h) :
    rowPrice δ p (nativeValue sourceCost δ p) D sourceCost ≤
      rowPrice δ p (nativeValue sourceCost δ p) Geometry.h sourceCost := by
  have hh : 0<Geometry.h := hD.trans_le hDh
  have hcD := Physical.Selection.scaled_zero_capacity (y:=Geometry.y) (s:=sourceCost) hD
  have hch := Physical.Selection.scaled_zero_capacity (y:=Geometry.y) (s:=sourceCost) hh
  have hcap := cappedCapacity_increment_le physicalCap_admissible.1.le allowances_pos.1.le hDh (y:=Geometry.y)
  have hr := native_value_lower hδ hp hp' hg
  have hdp : 0≤δ*p := mul_nonneg hδ hp
  have hdphi : δ*p≤3/8 := by nlinarith [mul_le_mul_of_nonneg_left hp' hδ]
  have hc : 0≤3*nativeValue sourceCost δ p/4-9/100-δ*p*physicalCap/2 := by
    norm_num [physicalCap]
    nlinarith
  have hweight := mul_le_mul_of_nonneg_left hcap hdp
  have hnonneg := mul_nonneg hc (sub_nonneg.mpr hDh)
  unfold rowPrice
  rw [hcD,hch]
  nlinarith

/-- A public native direct certificate supplies the real physical surplus,
without assuming a scalar price bound or a numerical count. -/
theorem native_row_price_of_certificate {c : DirectCertificate}
    (hc : c∈directCertificates) (hr : c.route=.native) (he : c.edge=3)
    {δ p D : ℝ} (hpbox : c.box.Contains (δ,p))
    (hh : hLower≤Geometry.h) (hh' : Geometry.h≤hUpper)
    (hell : Geometry.ell=Physical.ell)
    (hδ : 0≤δ) (hδ' : δ≤3/4) (hp : 0≤p) (hp' : p≤1/2)
    (hg : ∀ j:Fin 15,0<nativeGuard j sourceCost δ p)
    (hD : 0<D) (hDh : D≤Geometry.h) :
    rowPrice δ p (nativeValue sourceCost δ p) D sourceCost ≤ theta-1/2500000 := by
  have hprice := certified_original_price hc hh hh' hpbox
  rw [hr,he] at hprice
  have hy : Geometry.y=Geometry.h-2*Geometry.ell := by
    unfold Geometry.h
    linarith [Geometry.x_add_y]
  have hgeom : 0<Geometry.h := hD.trans_le hDh
  have hcap := Physical.Selection.scaled_zero_capacity (y:=Geometry.y) (s:=sourceCost) hgeom
  have heq : rowPrice δ p (nativeValue sourceCost δ p) Geometry.h sourceCost =
      originalPrice .native 3 Geometry.h δ p := by
    unfold rowPrice
    rw [hcap,hy,hell]
    rfl
  have hm := native_row_price_le_top hδ hδ' hp hp' hg hD hDh
  rw [heq] at hm
  linarith

end QRH.Cycle092.PacketJoin
#print axioms QRH.Cycle092.PacketJoin.native_row_price_of_certificate
