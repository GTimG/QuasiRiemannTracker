/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual three-allocation corner contraction and fixed collected mask. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedHighCofactorFamilyData
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedHighCoordinatesVolume
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.InitialPhysicalBounds
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.RegularResidualGeometry
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.RegularLowCollectedMask
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedRegularCanonicalGeometry
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform
open CenteredMomentCanonicalFirst Cycle61Moment Cycle61InitialMass CenteredMomentSecondHeightFamily
open CenteredMomentFiniteProfileExceptional
open OAI.SevenEighths.Record1252270103Source QRH.Record1252270103Low
open Record12518109Raw
open SelectedHighCofactorFamily
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _

variable {α:Type}[Fintype α]
def corner₁ (s:Input α)(S A:Finset (Ideal O))(corner:Bool):ℝ:=
  (if corner then s.Y₁ else s.X₁)/(newtonDivisorPair S A).1.absNorm
def corner₂ (s:Input α)(S A:Finset (Ideal O))(corner:Bool):ℝ:=
  (if corner then s.Y₂ else s.X₂)/(newtonDivisorPair S A).2.absNorm

def CornerBounds (s:Input α)(S A:Finset (Ideal O))(Z:ℝ):Prop:=
  ∀corner:Bool,0<corner₁ s S A corner ∧ 0<corner₂ s S A corner ∧
    corner₁ s S A corner≤Z ∧ corner₂ s S A corner≤Z ∧
    corner₁ s S A corner*corner₂ s S A corner≤Z ∧
    (9/4:ℝ)^2*(corner₁ s S A corner*corner₂ s S A corner)≤Z^(2:ℝ)

theorem divided_corner (x y d1 d2 Z:ℝ)(hx:0<x)(hy:0<y)(hd1:1≤d1)(hd2:1≤d2)
    (hZ:(9/4:ℝ)^2≤Z)(h1:x≤Z)(h2:y≤Z)(hp:x*y≤Z):
    0<x/d1 ∧ 0<y/d2 ∧ x/d1≤Z ∧ y/d2≤Z ∧ (x/d1)*(y/d2)≤Z ∧
      (9/4:ℝ)^2*((x/d1)*(y/d2))≤Z^(2:ℝ):=by
  have hp1:0<d1:=zero_lt_one.trans_le hd1
  have hp2:0<d2:=zero_lt_one.trans_le hd2
  have he1:x/d1≤x:=div_le_self hx.le hd1
  have he2:y/d2≤y:=div_le_self hy.le hd2
  have hprod: (x/d1)*(y/d2)≤Z:=
    (mul_le_mul he1 he2 (div_pos hy hp2).le hx.le).trans hp
  refine ⟨div_pos hx hp1,div_pos hy hp2,he1.trans h1,he2.trans h2,hprod,?_⟩
  calc
    _≤(9/4:ℝ)^2*Z:=mul_le_mul_of_nonneg_left hprod (sq_nonneg _)
    _≤Z*Z:=mul_le_mul_of_nonneg_right hZ (by nlinarith [sq_nonneg (9/4:ℝ)])
    _=Z^(2:ℝ):=by rw [Real.rpow_two];ring

theorem selected_newton_corners (s:Input α)(reflected second:Bool)(l:FirstSourceLabel)(C₂ D₂ R:Ideal O)
    (sel:Selection s reflected second l C₂ D₂ R)(Z:ℝ)(hZ:1<Z)(hZlarge:(9/4:ℝ)^2≤Z)
    (hx1:s.X₁≤Z)(hx2:s.X₂≤Z)(hy1:s.Y₁≤Z)(hy2:s.Y₂≤Z)(hprod:s.X₁*s.X₂≤Z)
    (P S A:Finset (Ideal O))(hS:S⊆P)(hA:A⊆S)(hp:∀p∈P,p≠0):
    CornerBounds sel.finalInput S A Z ∧
      corner₁ sel.finalInput S A true*corner₂ sel.finalInput S A true=
        corner₁ sel.finalInput S A false*corner₂ sel.finalInput S A false:=by
  have hc:=SelectedHighCoordinates.three_raw_and_log_corners s (if reflected then l.1.2 else l.1.1) R
    sel.B₁ sel.τ₁ sel.t₁ (if second then D₂ else C₂) sel.B₂ sel.τ₂ sel.t₂ sel.Cf sel.Bf sel.τf sel.tf Z hZ
  have hpair:=RegularLowCollectedMask.newton_pair_nonzero P S A hS hA hp
  have normone (I:Ideal O)(hI:I≠0):(1:ℝ)≤I.absNorm:=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hd1:=normone _ (mul_ne_zero_iff.mp hpair).1
  have hd2:=normone _ (mul_ne_zero_iff.mp hpair).2
  have hpx:sel.finalInput.X₁*sel.finalInput.X₂≤Z:=
    (mul_le_mul hc.1 hc.2.1 sel.finalInput.X₂_pos.le s.X₁_pos.le).trans hprod
  have hpy:sel.finalInput.Y₁*sel.finalInput.Y₂≤Z:=by rw [sel.finalInput.same_product];exact hpx
  constructor
  · intro corner;cases corner
    · exact divided_corner _ _ _ _ Z sel.finalInput.X₁_pos sel.finalInput.X₂_pos hd1 hd2 hZlarge
        (hc.1.trans hx1) (hc.2.1.trans hx2) hpx
    · exact divided_corner _ _ _ _ Z sel.finalInput.Y₁_pos sel.finalInput.Y₂_pos hd1 hd2 hZlarge
        (hc.2.2.1.trans hy1) (hc.2.2.2.1.trans hy2) hpy
  · simp only [corner₁,corner₂,ite_true,Bool.false_eq_true,ite_false,div_mul_div_comm,sel.finalInput.same_product]

theorem eventually_mask_ten (ηanchor:Character)(R₀:Ideal O)(hR₀:R₀≠0):
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀(ι:Type)[Fintype ι](s:Input ι),s.η=ηanchor→
      ∀L:Ideal O,L≠0→(L.absNorm:ℝ)≤Z^(4:ℝ)→
      ∀(P S A:Finset (Ideal O))(depth:ℕ)(amp:ℝ),S⊆P→A⊆S→S.card≤depth→
        0≤amp→(depth:ℝ)*amp<5→(∀p∈P,p≠0)→(∀p∈P,(p.absNorm:ℝ)≤Z^amp)→
      (geometryRawFixedMask s R₀*L)*((newtonDivisorPair S A).1*(newtonDivisorPair S A).2)≠0 ∧
      (((geometryRawFixedMask s R₀*L)*((newtonDivisorPair S A).1*(newtonDivisorPair S A).2)).absNorm:ℝ)≤Z^(10:ℝ):=by
  filter_upwards [RegularLowCollectedMask.eventually_collected_mask_cap ηanchor R₀ hR₀ 1 (by norm_num)] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι inst s hη L hL hLcap P S A depth amp hS hA hdepth hamp hcost hp hpool
  have hh:=hZ.2 ι s hη L hL hLcap P S A depth amp hS hA hdepth hamp hp hpool
  exact ⟨hh.1,hh.2.trans (Real.rpow_le_rpow_of_exponent_le hZ.1.le (by linarith))⟩
end
end QRH.Record1252270103Source.Admission.SelectedRegularCanonicalGeometry
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularCanonicalGeometry.divided_corner
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularCanonicalGeometry.selected_newton_corners
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularCanonicalGeometry.eventually_mask_ten
