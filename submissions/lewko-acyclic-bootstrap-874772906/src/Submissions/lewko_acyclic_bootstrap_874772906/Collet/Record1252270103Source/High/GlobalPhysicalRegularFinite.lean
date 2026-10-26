/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual selected row fibers and the full residual ideal pool preserve
one quarter of the source reserve. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalRegularFixedLoss
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.SelectedRegularFibersSelection
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedRegularAbsoluteData
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.InitialPhysicalResidualCap
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform
open CenteredMomentSecondHeightFamily CenteredMomentHeckeExpansion CenteredMomentCanonicalFirst
open CenteredMomentExceptionalAmplitudePair CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open Cycle61InitialMass Cycle61Moment OAI.SevenEighths.Record1252270103Source
open Record1252270103Second SecondRemainder Collision
open Admission.SelectedHighCofactorFamily Admission.ModifiedFibers Pool
open Admission Admission.SelectedRegularSourceData
open QRH.Record1252270103Low QRH.Record1252270103KernelMass
local notation "O"=>HeckeFamily.O
local instance regularFiniteDecidable {ι:Type*}:DecidableEq ι:=Classical.decEq _


open CenteredMomentSourceMass CenteredMomentOriginalCommonHarmonic CenteredMomentSectorLocalization CenteredMomentEnergyBands

theorem regular_finite_normalized (reserve θ Bslot Cpoint:ℝ)(N depth J:ℕ)
    (hf:PhysicalAnalytic.FixedBudget reserve 100 100 1 θ)(hslot:1≤Bslot)(hpoint:0<Cpoint):
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀{α Label:Type}[Fintype α][Fintype Label](a:Anchor α Z)(F:Family a Label),
    Fintype.card α≤N→
    Function.Injective (fun l=>FirstAllocationSelection.columnKey F.s F.modifier F.R F.seed
      (Z^F.D) Z F.ξ F.hK F.bin (F.column l))→
    (∀l,frozenCoefficient (F.stage l).B.val (F.stage l).common F.R F.s.ν F.s.W F.s.P≠0)→
    sourceRadius F.s≤Z^(2:ℝ)→
    (∀l,Z^(-(32:ℝ))≤F.Hmain l)→(∀l,F.Hmain l≤Z^(32:ℝ))→
    (∀l,frequencyRadius (F.Tsec l) Z F.ξ≤Z^(4:ℝ))→
    (∀I∈finiteColumns (Fintype.piFinset F.s.pools),(I.absNorm:ℝ)≤Z^(4:ℝ))→
    (∀i,1≤F.s.hi i)→(∀i,1≤F.s.P i)→0≤F.s.b₁→0≤F.s.b₂→
    ∀(P:Finset (Ideal O))(amp mesh:ℝ),0<amp→
    FixedCellPoolData P Z amp (amp/2) mesh θ 10 4 depth→
    (∀p∈P,∀i I,I∈F.s.slots i→¬p∣I)→2/(amp/2)≤depth→
    (9/4:ℝ)^2*(F.s.X₁*F.s.X₂)≤Z^(2:ℝ)→
    (∀i,∀p∈F.s.slots i,‖restoredSlotCoeff F.s i p‖≤Bslot)→
    (∀i,∀p∈F.s.slots i,(p.absNorm:ℝ)≤2*F.s.P i)→
    ∀(W₁ W₂:𝓢(ℝ,ℂ)),F.s.W₁=(W₁:ℝ→ℂ)→F.s.W₂=(W₂:ℝ→ℂ)→
    F.s.b₁≤9/4→F.s.b₂≤9/4→
    ∀(weight:F.Complete→ℂ)(second:Bool)(t u geometry control height:ℝ),
    0≤geometry→0≤control→1≤height→
    RegularCofactorBound F second P depth weight t u (9/4) 4
      (Cpoint*geometry*control*height^J*Z^(-(reserve/2)))→
    modifiedSecondNormalizedSum second F.datum (regularModifier F P) weight t u≤
      C*geometry*control*height^J*Z^(-(reserve/4)):=by
  obtain ⟨Ckey,hkey,efiber⟩:=Low.SelectedRegularFibers.eventual_regular_full_cost_selection
    32 32 2 2 4 1 θ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hf.positive
  obtain ⟨Cnorm,hnorm,enorm⟩:=actual_regular_normalized_newton_collection N 4 θ (θ/100)
    (by norm_num) hf.positive (div_pos hf.positive (by norm_num))
  let K:=Ckey*Cnorm*newtonMassBound depth^2*collisionProjectionCost Bslot 256 N*(2:ℝ)^N*Cpoint
  have hK:0≤K:=by dsimp [K,collisionProjectionCost];positivity
  refine ⟨1+K,by positivity,?_⟩
  filter_upwards [efiber,enorm] with Z hk hn
  refine ⟨hn.1,?_⟩
  intro α Label instα instLabel a F hN hinj hfreeze hsource hHlo hHhi hfreq hpool
    hhi hP hb1 hb2 P amp mesh hamp hcell havoid hdepth hplain hcoeff hslotnorm
    W1 W2 hW1 hW2 hb1' hb2' weight second t u geom control height hg hc hh hcof
  have hz:0<Z:=zero_lt_one.trans hn.1
  have hchild(l:Label):sourceRadius (F.input l)≤Z^(2:ℝ):=
    (InitialPhysical.child_source_radius_le F.s (F.stage l).common F.R (F.stage l).B
      (F.stage l).τ (F.stage l).t hhi hP hb1 hb2).trans hsource
  have hselect:=hk.2 a F hinj hHlo hHhi (by simpa only [one_mul] using hfreq) hchild hsource second
  have hres:∀r∈F.Rows,∀L∈secondResidualIdeals
      (fun q=>modifiedDatumBlock (F.datum q) (regularModifier F P q)) r,(L.absNorm:ℝ)≤Z^(4:ℝ):=by
    intro r hr L hL
    have hp:=SelectedRegularAbsolute.child_full_pool_cap F 4
      (SelectedRegularAbsolute.column_cap_irrel _ _ _ _ hpool) r.1.1
    exact (InitialPhysical.modified_second_residual_full_cap F.datum (regularModifier F P) r
      (Z^(4:ℝ)) (SelectedRegularAbsolute.column_cap_irrel _ _ _ _ hp) L hL).2
  have hfirst(l):((F.stage l).common.absNorm:ℝ)≤Z^(2:ℝ):=by
    have hb:=CoupledFirst.actual_geometry_norm_caps F.s F.modifier F.R F.seed (Z^F.D) Z F.ξ 2
      F.seed_sf F.zero₁ F.zero₂ hsource (F.column l).1.val
    change ((if F.reflected then (a.label (F.column l)).1.2 else (a.label (F.column l)).1.1).absNorm:ℝ)≤_
    cases he:F.reflected
    · exact (hb 0).2
    · exact (hb 1).2
  have hsecond(q:F.Complete):((if second then (F.datum q).D else (F.datum q).C).absNorm:ℝ)≤Z^(2:ℝ):=by
    have hb:=SelectedSecondKeyCaps.regular_common_caps F.slots F.input F.childModifier F.mask F.childSeed
      F.Hmain F.Tsec Z F.ξ CenteredMomentFirstAmplificationChoice.ballProfile F.childSeed_sf
      (fun _=>F.zero₁) (fun _=>F.zero₂) F.Hmain_pos F.χ₀ F.Q F.m q
    cases second
    · exact hb.1.trans (hchild q.1)
    · exact hb.2.trans (hchild q.1)
  have h:=hn.2 a F second hN hfreeze P weight t u (Ckey*Z^θ) (by positivity) hselect hres
    W1 W2 (9/4) 2 2 2 amp (amp/2) mesh θ 4 depth
    (Cpoint*geom*control*height^J*Z^(-(reserve/2))) Bslot (by positivity) hslot
    hW1 hW2 hb1' hb2' (by norm_num) (by positivity) hfirst hsecond (by norm_num at hcell ⊢;exact hcell)
    havoid hdepth hplain hP hcoeff hslotnorm hcof
  have he:=normalized_loss_reserve reserve θ hf
  calc
    _≤(Ckey*Z^θ)*Cnorm*Z^(θ+4*(θ/100))*newtonMassBound depth^2*
        (collisionProjectionCost Bslot 256 N*((2:ℝ)^N*
          (Cpoint*geom*control*height^J*Z^(-(reserve/2))))):=h
    _=K*geom*control*height^J*Z^(θ+(θ+4*(θ/100))-reserve/2):=by
      simp only [Real.rpow_sub hz,Real.rpow_add hz,Real.rpow_neg hz.le]
      dsimp [K]
      ring
    _≤K*geom*control*height^J*Z^(-(reserve/4)):=by
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn.1.le (by linarith only [he])) (by positivity)
    _≤(1+K)*geom*control*height^J*Z^(-(reserve/4)):=by gcongr;linarith
end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_finite_normalized
