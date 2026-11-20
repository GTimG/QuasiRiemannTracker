/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.DirectPrices
set_option autoImplicit false
set_option maxRecDepth 16384
namespace QRH.Cycle092.Direct
open QRH.Cycle090 QRH.Coverage

structure DirectCertificate where
  route : CountRoute
  edge : Fin 4
  box : Box
  deriving DecidableEq,Repr

def directCertificateCheck (c : DirectCertificate) : Bool :=
  decide (0 ≤ c.box.uLo ∧ c.box.uLo < c.box.uHi ∧ c.box.uHi ≤ 3/4 ∧
    0 ≤ c.box.vLo ∧ c.box.vLo < c.box.vHi ∧ c.box.vHi ≤ 1/2) &&
  (QRH.Bernstein.coefficientsCheck 2 3
    (directCoefficients c.route c.edge (8175840773/10000000000) c.box) (1/1000000) &&
   QRH.Bernstein.coefficientsCheck 2 3
    (directCoefficients c.route c.edge (8175840793/10000000000) c.box) (1/1000000))

def directCertificates : List DirectCertificate := [
  ⟨.fixedS, 0, ⟨(0), (3/4), (0), (1/2)⟩⟩,
  ⟨.fixedA, 0, ⟨(0), (3/4), (0), (1/2)⟩⟩,
  ⟨.fixedS, 1, ⟨(0), (3/8), (0), (1/2)⟩⟩,
  ⟨.fixedA, 1, ⟨(0), (3/8), (0), (1/2)⟩⟩,
  ⟨.old, 1, ⟨(3/8), (3/4), (0), (1/2)⟩⟩,
  ⟨.fixedS, 2, ⟨(0), (3/8), (0), (1/2)⟩⟩,
  ⟨.fixedA, 2, ⟨(0), (3/8), (0), (1/2)⟩⟩,
  ⟨.old, 2, ⟨(3/8), (3/4), (0), (1/2)⟩⟩,
  ⟨.old, 3, ⟨(0), (3/16), (0), (1/2)⟩⟩,
  ⟨.old, 3, ⟨(3/16), (15/64), (3/16), (1/2)⟩⟩,
  ⟨.old, 3, ⟨(3/16), (9/32), (0), (3/16)⟩⟩,
  ⟨.old, 3, ⟨(15/64), (9/32), (3/16), (7/32)⟩⟩,
  ⟨.old, 3, ⟨(33/128), (9/32), (7/32), (1/4)⟩⟩,
  ⟨.old, 3, ⟨(9/32), (3/8), (0), (3/16)⟩⟩,
  ⟨.old, 3, ⟨(3/8), (3/4), (0), (1/4)⟩⟩,
  ⟨.old, 3, ⟨(15/32), (9/16), (1/4), (3/8)⟩⟩,
  ⟨.old, 3, ⟨(9/16), (3/4), (1/4), (1/2)⟩⟩,
  ⟨.fixedS, 3, ⟨(15/64), (33/128), (7/32), (1/4)⟩⟩,
  ⟨.fixedA, 3, ⟨(15/64), (33/128), (7/32), (1/4)⟩⟩,
  ⟨.fixedS, 3, ⟨(15/64), (9/32), (1/4), (5/16)⟩⟩,
  ⟨.fixedA, 3, ⟨(15/64), (9/32), (1/4), (5/16)⟩⟩,
  ⟨.native, 3, ⟨(15/64), (9/32), (5/16), (3/8)⟩⟩,
  ⟨.native, 3, ⟨(15/64), (21/64), (7/16), (1/2)⟩⟩,
  ⟨.native, 3, ⟨(15/64), (3/8), (3/8), (7/16)⟩⟩,
  ⟨.native, 3, ⟨(9/32), (3/8), (3/16), (3/8)⟩⟩,
  ⟨.native, 3, ⟨(21/64), (45/128), (15/32), (1/2)⟩⟩,
  ⟨.native, 3, ⟨(21/64), (3/8), (7/16), (15/32)⟩⟩,
  ⟨.native, 3, ⟨(3/8), (15/32), (1/4), (7/16)⟩⟩,
  ⟨.native, 3, ⟨(27/64), (15/32), (7/16), (15/32)⟩⟩,
  ⟨.native, 3, ⟨(15/32), (9/16), (3/8), (1/2)⟩⟩
]

theorem directCertificates_checked : directCertificates.all directCertificateCheck = true := by
  decide +kernel
/-- A finite certificate establishes the actual polynomial at all h and all points. -/
theorem certificate_cleared {c : DirectCertificate} (hc : directCertificateCheck c = true)
    {h : ℝ} {point : Point} (hh : hLower ≤ h) (hh' : h ≤ hUpper)
    (hp : c.box.Contains point) : 1/1000000 ≤ cleared c.route c.edge h point.1 point.2 := by
  simp only [directCertificateCheck,Bool.and_eq_true,decide_eq_true_eq] at hc
  rcases hc with ⟨⟨_,hu,_,_,hv,_⟩,hl,hh0⟩
  have hlow := direct_box_bound c.route c.edge (8175840773/10000000000) c.box (1/1000000) hu hv hl hp
  have hhigh := direct_box_bound c.route c.edge (8175840793/10000000000) c.box (1/1000000) hu hv hh0 hp
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] at hlow hhigh
  change (1/1000000 : ℝ) ≤ cleared c.route c.edge hLower point.1 point.2 at hlow
  change (1/1000000 : ℝ) ≤ cleared c.route c.edge hUpper point.1 point.2 at hhigh
  have hs := QRH.Bernstein.coordinate_mem_unit conductor_interval.2.1 hh hh'
  change 0 ≤ (h-hLower)/(hUpper-hLower) ∧ (h-hLower)/(hUpper-hLower) ≤ 1 at hs
  rw [direct_interpolation]
  have h0 := mul_le_mul_of_nonneg_left hlow (by linarith : 0 ≤ 1-(h-hLower)/(hUpper-hLower))
  have h1 := mul_le_mul_of_nonneg_left hhigh hs.1
  nlinarith

/-- All certified fixed/saved/native routes pay the original pointwise physical price. -/
theorem certified_original_price {c : DirectCertificate} (hm : c ∈ directCertificates)
    {h : ℝ} {point : Point} (hh : hLower ≤ h) (hh' : h ≤ hUpper)
    (hp : c.box.Contains point) :
    1/2500000 ≤ theta-originalPrice c.route c.edge h point.1 point.2 := by
  have hc := List.all_eq_true.mp directCertificates_checked c hm
  have hclear := certificate_cleared hc hh hh' hp
  simp only [directCertificateCheck,Bool.and_eq_true,decide_eq_true_eq] at hc
  have hd0 : (0 : ℝ) ≤ (c.box.uLo : ℝ) := Rat.cast_nonneg.mpr hc.1.1
  have hd1 : (c.box.uHi : ℝ) ≤ (3/4 : ℝ) := by
    simpa only [Rat.cast_div,Rat.cast_ofNat] using
      (Rat.cast_le.mpr hc.1.2.2.1 : (c.box.uHi : ℝ) ≤ ((3/4 : ℚ) : ℝ))
  have hp0 : (0 : ℝ) ≤ (c.box.vLo : ℝ) := Rat.cast_nonneg.mpr hc.1.2.2.2.1
  have hp1 : (c.box.vHi : ℝ) ≤ (1/2 : ℝ) := by
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
      (Rat.cast_le.mpr hc.1.2.2.2.2.2 : (c.box.vHi : ℝ) ≤ ((1/2 : ℚ) : ℝ))
  exact original_price_of_cleared _ _ hh hh' (hd0.trans hp.1) (hp.2.1.trans hd1)
    (hp0.trans hp.2.2.1) (hp.2.2.2.trans hp1) hclear

end QRH.Cycle092.Direct
#print axioms QRH.Cycle092.Direct.directCertificates_checked
#print axioms QRH.Cycle092.Direct.certified_original_price
