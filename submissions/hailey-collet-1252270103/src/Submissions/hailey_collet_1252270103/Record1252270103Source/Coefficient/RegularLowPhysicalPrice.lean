/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual modified LOW coordinates pay the exact seed/NF source reserve.
The numerical price is derived, never supplied as an analytic hypothesis. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalModifiedLowPayment
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.PhysicalLowReserveSource
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.RegularLowPhysicalPrice
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open ConcretePrimeRowBridge CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentCommonRadialData CenteredMomentSourceLiveColumn CenteredMomentSectorLocalization
open Cycle61HighGeometry Cycle61InitialMass Cycle61Moment Record12518109Natural
open Record1252270103CommonGeometry Record1252270103Finite Record1252270103StepScalar
open QRH.Record1252270103Graph QRH.Record1252270103Source.High
open QRH.Record1252270103Source.Admission OAI.SevenEighths.Record1252270103Source.Collision
open QRH.Record1252270103Source.PhysicalLowReserve
local notation "O" => HeckeFamily.O

/-- The actual scalar conclusion for all modified first columns and both
second orientations. Every remaining premise is a geometric or error bound. -/
def ModifiedNodePrice (n low : Source) (b : ℝ) : Prop :=
  ∀(ι:Type)[Fintype ι][DecidableEq ι],
  ∀(s:Input ι)(A₁ A₂ Dmark Kmark R seed:Ideal O)(Fmark:Ideal O→ℂ)
    (H Z ξ:ℝ)(hH:0<H)(bin:ℤ×(Fin 5→ℤ)),
  ∀j:FirstColumnIndex (CoupledFirst.geometryFirstSource s
    (markedSourceModifier A₁ A₂ Dmark Kmark Fmark) R seed H Z ξ hH bin),
  ∀(reflected second:Bool)(d₂:SecondInputDatum ι)(U:Finset (CommonIndex d₂.C d₂.D)),
  ∀(M A reserve width err errv c f loss rho mesh erased radial radialRound outer:ℝ),
    1<Z → 0≤width → width≤PhysicalLowGuard.step n → 0≤loss → 0≤rho →
    rho≤(n.allowance:ℝ)/4 → loss≤(n.allowance:ℝ)/4 → mesh≤(n.allowance:ℝ)/4 →
    err≤(n.allowance:ℝ)/4 → errv≤(n.allowance:ℝ)/4 → radialRound≤(n.allowance:ℝ)/4 →
    outer≤4*(n.allowance:ℝ) →
  let l:=FirstFamily.firstLabel s (markedSourceModifier A₁ A₂ Dmark Kmark Fmark)
    R seed H Z ξ hH bin j;
  let x:=childHighCoordinates (actualHighCoordinates reflected (!reflected) second l d₂.C d₂.D U
    Z M A (sourceAReal n low b) ξ reserve err) errv;
    labelC reflected l Z≤c → 0≤f →
    erased≤max 0 (max
      (b-f-((low.B:ℝ)*(sourceFReal n low b-max (labelD reflected l Z-labelC reflected l Z) 0-rho)-
        (plainBudget n b width-c+f+loss))/(low.L:ℝ))
      (b-f-(low.cap:ℝ)*(sourceFReal n low b-max (labelD reflected l Z-labelC reflected l Z) 0-rho)))+mesh →
    radial≤x 2+radialRound →
    x 0+x 1+radial-balancedGeometrySide reflected A
      (CoupledFirst.geometryExponents s (markedSourceModifier A₁ A₂ Dmark Kmark Fmark)
        R seed H Z ξ j.1.val)+(n.q:ℝ)*erased+outer≤-8*(n.allowance:ℝ)

theorem modified_node_price (K:ℚ)(n low:Source)(b:ℝ)
    (hg:RealGeometry K n low b)(hn:ParentGood n)(hlow:ParentGood low)
    (he:0≤(n.allowance:ℝ))(hq0:0≤(n.q:ℝ))(hq1:(n.q:ℝ)≤1) :
    ModifiedNodePrice n low b := by
  have hB0 : 0≤(low.B:ℝ) := by exact_mod_cast hlow.1.le
  have hB1 : (low.B:ℝ)≤1 := by exact_mod_cast hlow.2.1
  have hlam : 1<(low.L:ℝ) := by exact_mod_cast hlow.2.2.1
  have hh : 0≤(low.cap:ℝ) := by exact_mod_cast hlow.2.2.2.1
  have hL : 0≤(n.L:ℝ) := by exact_mod_cast (show (0:ℚ)≤n.L by linarith [hn.2.2.1])
  intro ι _ _ s A₁ A₂ Dmark Kmark R seed Fmark H Z ξ hH bin j reflected second d₂ U
    M A reserve width err errv c f loss rho mesh erased radial radialRound outer
    hZ hw0 hw hloss0 hrho0 hrho hloss hmesh herr herrv hround houter l x hc hf herased hrad
  have hp := GlobalPhysical.modified_low_coordinate_payment s A₁ A₂ Dmark Kmark R seed
    Fmark H Z ξ hH bin j reflected second d₂ U M A (sourceAReal n low b) reserve err errv
    (n.q:ℝ) (low.B:ℝ) (low.L:ℝ) (low.cap:ℝ) (sourceFReal n low b)
    (plainBudget n b width) b c f loss rho mesh erased (nodeGain n low width) radial radialRound
    hZ hq0 hB0 hB1 hlam hc hf hh hg.qcap_room.le
    (conservative_gain K n low b width hg).symm (conservative_weak_cap K n low b width hg hL hw0)
    hloss0 hrho0 herased hrad
  have hpaid := node_price_with_outer K n low b width rho loss mesh err errv radialRound outer
    hg hn hlow he hq0 hq1 hw hrho hloss hmesh herr herrv hround houter
  change x 0+x 1+radial-balancedGeometrySide reflected A
      (CoupledFirst.geometryExponents s (markedSourceModifier A₁ A₂ Dmark Kmark Fmark)
        R seed H Z ξ j.1.val)+(n.q:ℝ)*erased≤
    price n low b width rho loss mesh err errv radialRound at hp
  linarith only [hp,hpaid]

theorem nf_modified_node_price (n low:Source)(high:Option Source)
    (hv:SourceValid n low high)(hlow:ParentGood low)(ha:NFAccounting n)
    (b:ℝ)(hb:b∈Set.Icc (crossing n low:ℝ) (n.cap:ℝ)) :
    ModifiedNodePrice n low b := by
  have hq0 : 0≤(n.q:ℝ) := by
    have h : (((1/2:ℚ):ℝ))≤(n.q:ℝ) := Rat.cast_le.mpr hv.2.2.2.2.2.1
    norm_num at h
    linarith only [h]
  have hq1 : (n.q:ℝ)≤1 := by
    have h : (n.q:ℝ)≤(((3/4:ℚ):ℝ)) := Rat.cast_le.mpr hv.2.2.2.2.2.2.1
    norm_num at h
    linarith only [h]
  exact modified_node_price _ n low b (nf_real_geometry n low high hv hlow hb)
    (parent_good_of_source_valid hv) hlow (by exact_mod_cast (nf_accounting_positive ha).1.le) hq0 hq1

theorem seed_modified_node_price (n low:Source)
    (hv:SeedSourceValid n low)(hlow:ParentGood low)
    (b:ℝ)(hb:b∈Set.Icc (crossing n low:ℝ) (n.cap:ℝ)) :
    ModifiedNodePrice n low b := by
  have hq0 : 0≤(n.q:ℝ) := by
    have h : (((1/2:ℚ):ℝ))≤(n.q:ℝ) := Rat.cast_le.mpr hv.2.2.2.2.2.1
    norm_num at h
    linarith only [h]
  have hq1 : (n.q:ℝ)≤1 := by
    have h : (n.q:ℝ)<(((3/4:ℚ):ℝ)) := Rat.cast_lt.mpr hv.2.2.2.2.2.2.1
    norm_num at h
    linarith only [h]
  exact modified_node_price _ n low b (seed_real_geometry n low hv hlow hb)
    (parent_good_of_seed_valid hv) hlow (PhysicalLowGuard.seed_allowance_positive n low hv).le hq0 hq1

end
end QRH.Record1252270103Source.RegularLowPhysicalPrice
#print axioms QRH.Record1252270103Source.RegularLowPhysicalPrice.modified_node_price
#print axioms QRH.Record1252270103Source.RegularLowPhysicalPrice.nf_modified_node_price
#print axioms QRH.Record1252270103Source.RegularLowPhysicalPrice.seed_modified_node_price
