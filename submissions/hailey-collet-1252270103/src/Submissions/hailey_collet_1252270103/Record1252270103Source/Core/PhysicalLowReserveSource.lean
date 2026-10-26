/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The seed and both NF fee profiles pay the actual LOW price with eight
allowances remaining after four allowances of additional analytic losses. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.PhysicalLowReserve
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.PhysicalLowGuardSource
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.PhysicalLowReserve
noncomputable section
open Record1252270103Finite Record1252270103StepScalar QRH.Record1252270103Graph

def price (n low : Source) (b width rho loss mesh err errv radialRound : ℝ) : ℝ :=
  -min (sourceAReal n low b) (nodeGain n low width)+
    (n.q:ℝ)*(max (((low.B:ℝ)*rho+loss)/(low.L:ℝ)) ((low.cap:ℝ)*rho)+mesh)+
    err+errv+radialRound

theorem node_price_with_outer (K : ℚ) (n low : Source)
    (b width rho loss mesh err errv radialRound outer : ℝ)
    (hg : RealGeometry K n low b) (hn : ParentGood n) (hlow : ParentGood low)
    (he : 0≤(n.allowance:ℝ)) (hq0 : 0≤(n.q:ℝ)) (hq1 : (n.q:ℝ)≤1)
    (hw : width≤PhysicalLowGuard.step n)
    (hρ : rho≤(n.allowance:ℝ)/4) (hloss : loss≤(n.allowance:ℝ)/4)
    (hm : mesh≤(n.allowance:ℝ)/4) (herr : err≤(n.allowance:ℝ)/4)
    (herrv : errv≤(n.allowance:ℝ)/4) (hrad : radialRound≤(n.allowance:ℝ)/4)
    (houter : outer≤4*(n.allowance:ℝ)) :
    price n low b width rho loss mesh err errv radialRound+outer≤-8*(n.allowance:ℝ) := by
  have hL : 0≤(n.L:ℝ) := by exact_mod_cast (show (0:ℚ)≤n.L by linarith [hn.2.2.1])
  have hlam : 1≤(low.L:ℝ) := by exact_mod_cast hlow.2.2.1.le
  have hB0 : 0≤(low.B:ℝ) := by exact_mod_cast hlow.1.le
  have hB1 : (low.B:ℝ)≤1 := by exact_mod_cast hlow.2.1
  have hh0 : 0≤(low.cap:ℝ) := by exact_mod_cast hlow.2.2.2.1
  have hh1 : (low.cap:ℝ)≤1 := by exact_mod_cast hlow.2.2.2.2.le
  have hp := node_price_reserve K n low b width rho loss mesh err errv radialRound
    hg he hL hq0 hq1 hlam hB0 hB1 hh0 hh1 hw hρ hloss hm herr herrv hrad
  change price n low b width rho loss mesh err errv radialRound≤-12*(n.allowance:ℝ) at hp
  linarith only [hp,houter]

theorem nf_price_with_outer (n low : Source) (high : Option Source)
    (hv : SourceValid n low high) (hlow : ParentGood low) (ha : NFAccounting n)
    (b width rho loss mesh err errv radialRound outer : ℝ)
    (hb : b∈Set.Icc (crossing n low:ℝ) (n.cap:ℝ))
    (hw : width≤PhysicalLowGuard.step n)
    (hρ : rho≤(n.allowance:ℝ)/4) (hloss : loss≤(n.allowance:ℝ)/4)
    (hm : mesh≤(n.allowance:ℝ)/4) (herr : err≤(n.allowance:ℝ)/4)
    (herrv : errv≤(n.allowance:ℝ)/4) (hrad : radialRound≤(n.allowance:ℝ)/4)
    (houter : outer≤4*(n.allowance:ℝ)) :
    price n low b width rho loss mesh err errv radialRound+outer≤-8*(n.allowance:ℝ) := by
  have hq0 : 0≤(n.q:ℝ) := by
    have hq : (1/2:ℝ)≤n.q := by
      have h : (((1/2:ℚ):ℝ))≤(n.q:ℝ) := Rat.cast_le.mpr hv.2.2.2.2.2.1
      norm_num at h
      exact h
    linarith only [hq]
  have hq1 : (n.q:ℝ)≤1 := by
    have hq : (n.q:ℝ)≤3/4 := by
      have h : (n.q:ℝ)≤(((3/4:ℚ):ℝ)) := Rat.cast_le.mpr hv.2.2.2.2.2.2.1
      norm_num at h
      exact h
    linarith only [hq]
  have he : 0≤(n.allowance:ℝ) := by exact_mod_cast (nf_accounting_positive ha).1.le
  exact node_price_with_outer _ n low b width rho loss mesh err errv radialRound outer
    (nf_real_geometry n low high hv hlow hb) (parent_good_of_source_valid hv) hlow he hq0 hq1
    hw hρ hloss hm herr herrv hrad houter

theorem seed_price_with_outer (n low : Source)
    (hv : SeedSourceValid n low) (hlow : ParentGood low)
    (b width rho loss mesh err errv radialRound outer : ℝ)
    (hb : b∈Set.Icc (crossing n low:ℝ) (n.cap:ℝ))
    (hw : width≤PhysicalLowGuard.step n)
    (hρ : rho≤(n.allowance:ℝ)/4) (hloss : loss≤(n.allowance:ℝ)/4)
    (hm : mesh≤(n.allowance:ℝ)/4) (herr : err≤(n.allowance:ℝ)/4)
    (herrv : errv≤(n.allowance:ℝ)/4) (hrad : radialRound≤(n.allowance:ℝ)/4)
    (houter : outer≤4*(n.allowance:ℝ)) :
    price n low b width rho loss mesh err errv radialRound+outer≤-8*(n.allowance:ℝ) := by
  have hq0 : 0≤(n.q:ℝ) := by
    have hq : (1/2:ℝ)≤n.q := by
      have h : (((1/2:ℚ):ℝ))≤(n.q:ℝ) := Rat.cast_le.mpr hv.2.2.2.2.2.1
      norm_num at h
      exact h
    linarith only [hq]
  have hq1 : (n.q:ℝ)≤1 := by
    have hq : (n.q:ℝ)<3/4 := by
      have h : (n.q:ℝ)<(((3/4:ℚ):ℝ)) := Rat.cast_lt.mpr hv.2.2.2.2.2.2.1
      norm_num at h
      exact h
    linarith only [hq]
  exact node_price_with_outer _ n low b width rho loss mesh err errv radialRound outer
    (seed_real_geometry n low hv hlow hb) (parent_good_of_seed_valid hv) hlow
    (PhysicalLowGuard.seed_allowance_positive n low hv).le hq0 hq1
    hw hρ hloss hm herr herrv hrad houter

end
end QRH.Record1252270103Source.PhysicalLowReserve
#print axioms QRH.Record1252270103Source.PhysicalLowReserve.node_price_with_outer
#print axioms QRH.Record1252270103Source.PhysicalLowReserve.nf_price_with_outer
#print axioms QRH.Record1252270103Source.PhysicalLowReserve.seed_price_with_outer
