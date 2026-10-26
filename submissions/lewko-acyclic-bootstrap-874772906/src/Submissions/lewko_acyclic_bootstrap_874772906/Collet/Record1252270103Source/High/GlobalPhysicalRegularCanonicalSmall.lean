/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Genuine earlier LOW and HIGH sources control the same full centered family. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalRegularSmall
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalRegularFamily
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedRegularCanonicalAbsolute
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalRegularFinite
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalRegularCofactorBridge
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedRegularCombinedPointSome
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedRegularCombinedPointNatural
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
open OAI OAI.SevenEighths
open QRH.Record1252270103Source.High
open QRH.Record1252270103Source.Admission
open QRH.Record1252270103Source.High.GlobalPhysical
open QRH.Record1252270103Low QRH.Record1252270103Restoration QRH.Record1252270103KernelMass
open ConcretePrimeRowBridge CenteredMomentSecondHeightFamily CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open Record1252270103Source Record1252270103Second
open Record1252270103Finite PhysicalScalar HighScalar Record1252270103Source.Collision
open Cycle61HighGeometry Record1252270103CommonGeometry
open CenteredMomentSecondCanonical CenteredMomentSectorLocalization CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open Record12518109Natural
open Cycle61InitialMass WeightedHigh JointHigh MarkedPlain
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Set Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentRetainedProfile
open Cycle61HighProfiles Cycle61FinalLow CenteredMomentFiniteProfileExceptional
open Cycle61HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
open CenteredMomentAllocatedChildCapacity Cycle61Moment
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentSlotRatios CenteredMomentSourceLiveColumn
open CenteredMomentChildRows RayFourExpansion HeckeInverseAmplification
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstSourceReduction ConcretePrimeRowBridge
open ProbeHighRowFamily ProbePhysical Record12518109GainWholeGeometry
open SelectedHighCofactorFamily SelectedHighCofactorCoordinates
open SelectedHighPaid Pool
local instance regularCanonicalDecEq {ι : Type*} : DecidableEq ι := Classical.decEq _
local notation "O" => HeckeFamily.O

open SelectedRegularHighPoint CenteredMomentEnergyBands
open OAI OAI.SevenEighths
open scoped Classical BigOperators ContDiff
open HeckeFamily ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondInputCapacitySource Cycle61Moment LocalMoment
open PhysicalAnalytic Record1252270103Finite
open Set Filter Admission
open High.GlobalPhysical SelectedRegularHighPoint SelectedRegularSourceData SelectedHighCofactorFamily
open SelectedRegularCombinedPoint SelectedRegularLowPoint CenteredMomentSourceMass
open CenteredMomentFirstAmplificationChoice CenteredMomentSourceMass
open Record1252270103StepScalar QRH.Record1252270103Graph CenteredMomentLogDyadic
open SelectedRegularCanonicalAbsolute
local instance regularCanonicalFinite (M:Ideal O)[NeZero M]:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

theorem regular_canonical_small {α:Type}[Fintype α]
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M ≤ H)
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(hWs:Function.support W⊆Icc (1:ℝ) 2)
    (ηanchor η₀:Character)(R₀:Ideal O)(hR₀:R₀≠0)(Q:Ideal O)
    (K:ℚ)(n low:Source)(bcell reserve θ mesh ξ width τsource Cpoint:ℝ)(N degree:ℕ)
    (controls:Finset (ℕ×ℕ))(hf:FixedBudget reserve 100 100 1 θ)
    (hg:RealGeometry K n low bcell)(hn:ParentGood n)
    (hξ:0<ξ)(hξ1:ξ ≤ 1)(hθ:0 ≤ θ)(hθ1:θ ≤ 1)
    (hpoint:0<Cpoint)(hτ:0<τsource):
    ∃Cs:ℝ,0<Cs ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀hp:RegularPointAt (α:=α) M H hH W hW hWs ηanchor η₀ R₀ hR₀ Q n low
      bcell reserve θ mesh ξ width τsource N degree controls Cpoint Z,
    ∀(hZ:1<Z)(i:Initial (α:=α) M H Z)(r:ℝ),InitialGeometry i n bcell width mesh r→
    Fintype.card α ≤ N→
    ∀(bin:ℤ×(Fin 5→ℤ))(reflected:Bool),
    let a:=i.anchor hH W hW hWs hZ ηanchor η₀ R₀ 1 hR₀ (by simp) 1 1 1 1 (fun _=>1) ξ θ bin reflected Q
    ∀{Label:Type}[Fintype Label](column:Label→a.Column)
      (hLive:∀l,column l∈firstLiveColumns
        (CoupledFirst.geometryFirstSource a.s a.modifier a.R a.seed (Z^a.D) Z a.ξ a.hK a.bin)
        (fun _=>logAnnulus))
      (alloc:∀l,actualAllocations a.s.pools (FirstFamily.columnIdeal a.reflected a.s a.modifier a.R a.seed
        (Z^a.D) Z a.ξ a.hK a.bin (column l)))
      (P:Finset (Ideal O))(ht:ℝ)(χ₀:Label→RayCharacter),
    Function.Injective (fun l=>(a.label (column l),(column l).2.1.val))→
    (∀l,frozenCoefficient (alloc l).val
      (FirstFamily.columnIdeal a.reflected a.s a.modifier a.R a.seed (Z^a.D) Z a.ξ a.hK a.bin (column l))
      a.R a.s.ν a.s.W a.s.P≠0)→
    FixedCellPoolData P Z (sourceAReal n low bcell) ((sourceAReal n low bcell)/2) mesh θ 10 4
      (cellNewtonDepth (sourceAReal n low bcell))→
    let F:=allocatedRegularFamily a column hLive alloc P (sourceAReal n low bcell) ht N χ₀
    let H0:=fun l=>(CoupledFirst.geometryFirstSource a.s a.modifier a.R a.seed (Z^a.D) Z a.ξ a.hK a.bin (column l).1).H0
    let radius:=fun l=>ExceptionalPrice.literalFirstRadius reflected Z (volume a.s) Z ξ θ (a.label (column l))
    ∀(Wa:𝓢(ℝ,ℂ))(height:ℝ),0 ≤ height→(∀j,|i.freq j| ≤ height)→
    1+|ht|+height ≤ Z^(τsource/4)→
    ∀(second:Bool)(t u:ℝ),mellinPairHeight t u ≤ Z^(τsource/4)→
    modifiedSecondNormalizedSum second F.datum (fun q=>F.childModifier q.1)
      (regularFamilyWeight F Wa (fun _=>P) H0 radius ((sourceAReal n low bcell)/2)) t u ≤ 
      Cs*geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*
        (i.p.control controls)^2*(1+|ht|+height)^degree*(mellinPairHeight t u)^degree*Z^(-(reserve/4)):=by
  have hnB:(n.B:ℝ) ≤ 1:=by exact_mod_cast hn.2.1
  have hnL:1 ≤ (n.L:ℝ):=by exact_mod_cast hn.2.2.1.le
  have hncap:(n.cap:ℝ) ≤ 1:=by exact_mod_cast hn.2.2.2.2.le
  let amp:=sourceAReal n low bcell
  have hamp:0<amp:=hg.a_pos
  have hamp1:amp ≤ 1:=hg.a_small.le.trans (by norm_num)
  obtain ⟨Cs,hCs,es⟩:=regular_small_normalized (α:=α) M H hH W hW hWs ηanchor η₀ R₀ hR₀ Q n low
    bcell reserve θ mesh ξ width τsource (initialSlotBound W hW hWs) Cpoint N (cellNewtonDepth amp)
    degree controls hf (initialSlotBound_ge_one W hW hWs) hpoint hτ hamp
  refine ⟨Cs,hCs,?_⟩
  filter_upwards [es,InitialTruncated.eventually_initial_caps N (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ) hnB hnL hncap,
    ExceptionalPrice.eventually_initial_first_geometry N (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ) ξ amp θ
      hnB hnL hncap hξ hξ1 hamp.le hamp1 hθ hθ1,allocated_frequency N,
    eventually_ge_atTop ((9/4:ℝ)^2)] with Z hs hc hgZ hfZ hlarge
  refine ⟨hs.1,?_⟩
  intro hp hZ i r hi hN bin reflected a Label _ column hLive alloc P ht χ₀ hinj hfreeze hcell F H0 radius Wa height hh hv hext second t u hpair
  have hz:=zero_lt_one.trans hZ
  have hy:1 ≤ i.Y₂:=hi.reference.symm ▸ Real.one_le_rpow hZ.le hi.r_nonneg
  have hyl:i.Y₂ ≤ i.X₁:=hi.reference.symm ▸ hi.long_left
  have hyr:i.Y₂ ≤ i.X₂:=hi.reference.symm ▸ hi.long_right
  have caps:=hc.2 hZ M H hH W hW hWs ηanchor η₀ R₀ i.θ i.w i.freq i.t₀ i.p
    i.X₁ i.X₂ i.Y₁ i.Y₂ i.hX₁ i.hX₂ i.hY₁ i.hY₂ i.same hN hi.widths_nonneg hi.face hy hyl hyr
  have geom:=hgZ.2 hZ M H hH W hW hWs ηanchor η₀ R₀ i.θ i.w i.freq i.t₀ i.p
    i.X₁ i.X₂ i.Y₁ i.Y₂ i.hX₁ i.hX₂ i.hY₁ i.hY₂ i.same hN hi.widths_nonneg hi.face hy hyl hyr
  have hgeom (l:Label):0<H0 l ∧ 0 ≤ radius l+6*amp ∧ radius l+6*amp ≤ 32 ∧
      Z^(radius l+6*amp)=F.Hmain l:=by
    have gg:=fun j=>by
      have g:=geom a.modifier reflected bin j
      exact And.intro g.1 (And.intro g.2.1 (And.intro g.2.2.1 g.2.2.2.2.2.2))
    let prop:=(fun (K:ℝ)(hK:0<K)=>∀j:FirstColumnIndex
        (CoupledFirst.geometryFirstSource a.s a.modifier a.R a.seed K Z ξ hK bin),
      0<(CoupledFirst.geometryFirstSource a.s a.modifier a.R a.seed K Z ξ hK bin j.1).H0 ∧
      let rad:=ExceptionalPrice.literalFirstRadius reflected Z (volume a.s) Z ξ θ
        (FirstFamily.firstLabel a.s a.modifier a.R a.seed K Z ξ hK bin j)
      0 ≤ rad+6*amp ∧ rad+6*amp ≤ 32 ∧
        Z^(rad+6*amp)=firstMainRadius reflected K (volume a.s) Z ξ (3*amp) θ
          (FirstFamily.firstLabel a.s a.modifier a.R a.seed K Z ξ hK bin j))
    have base:prop Z hz:=gg
    have transport (K:ℝ)(hK:0<K)(he:K=Z):prop K hK:=by subst K;exact base
    exact transport (Z^a.D) a.hK (by change Z^(1:ℝ)=Z;exact Real.rpow_one Z) (column l)
  have hHlo(l:Label):Z^(-(32:ℝ)) ≤ F.Hmain l:=by
    rw [←(hgeom l).2.2.2]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith [(hgeom l).2.1])
  have hHhi(l:Label):F.Hmain l ≤ Z^(32:ℝ):=by
    rw [←(hgeom l).2.2.2]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (hgeom l).2.2.1
  have hplain:(9/4:ℝ)^2*(F.s.X₁*F.s.X₂) ≤ Z^(2:ℝ):=by
    have hcorners:=SelectedRegularCanonicalGeometry.initial_long_corners M H hH W hW hWs Z hZ
      ηanchor η₀ R₀ i.θ i.w i.freq i.t₀ i.p i.X₁ i.X₂ i.Y₁ i.Y₂ i.hX₁ i.hX₂ i.hY₁ i.hY₂ i.same
      (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ) r hnB hnL hi.widths_nonneg hi.face hi.r_nonneg hi.long_left hi.long_right hi.reference
    calc
      _ ≤ Z*Z:=mul_le_mul hlarge hcorners.2.2.2.2 (mul_pos i.hX₁ i.hX₂).le hz.le
      _=Z^(2:ℝ):=by rw [Real.rpow_two,pow_two]
  have hcoeff(j:α)(I:Ideal O)(hI:I∈F.s.slots j):‖restoredSlotCoeff F.s j I‖ ≤ initialSlotBound W hW hWs:=
    F.s.coefficient_bound j I hI
  have hnorm(j:α)(I:Ideal O)(hI:I∈F.s.slots j):(I.absNorm:ℝ) ≤ 2*F.s.P j:=by
    exact (Collision.primePool_norm_le M H (Z^(i.w j))
      (Real.rpow_nonneg hz.le _) I hI).2
  have hfirst:Function.Injective (fun l=>FirstAllocationSelection.columnKey F.s F.modifier F.R F.seed
      (Z^F.D) Z F.ξ F.hK F.bin (F.column l)):=hinj
  have hb:=hs.2 hp hZ i r hi 1 (by simp) bin reflected F hN hfirst hfreeze caps.2.1 hHlo hHhi
    (hfZ.2 a column hLive alloc P amp ht χ₀ rfl hξ.le hξ1 hθ hamp.le)
    (SelectedRegularAbsolute.column_cap_irrel _ _ _ _ caps.2.2.2.2)
    (fun _=>by change (1:ℝ) ≤ 2;norm_num)
    (fun j=>by change 1 ≤ Z^(i.w j);exact Real.one_le_rpow hZ.le (hi.widths_nonneg j))
    (by change (0:ℝ) ≤ 9/4;norm_num) (by change (0:ℝ) ≤ 9/4;norm_num) P hcell
    (fun p hp j I hI=>hcell.avoids_canonical_slot M H (i.w j) (hi.widths_mesh j) p hp I hI)
    (node_newton_depth K n low bcell hg).2.2.1 (node_newton_depth K n low bcell hg).2.2.2.1
    hplain hcoeff hnorm (i.p.profile 0) (i.p.profile 1) Wa rfl rfl le_rfl le_rfl H0 radius
    (fun l=>(hgeom l).1) (fun l=>⟨(hgeom l).2.1,(hgeom l).2.2.1⟩)
    (fun _=>rfl) (fun _=>rfl) ht height hh hv (fun _=>rfl) hext second t u hpair
  exact hb
end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_canonical_small
