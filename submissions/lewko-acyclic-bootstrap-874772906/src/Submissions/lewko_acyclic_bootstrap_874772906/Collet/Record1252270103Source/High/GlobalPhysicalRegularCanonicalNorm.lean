/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Genuine earlier LOW and HIGH sources control the same full centered family. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalRegularCanonicalSmall
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalRegularNorm
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
local instance regularCanonicalNormDecEq {ι : Type*} : DecidableEq ι := Classical.decEq _
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
local instance regularCanonicalNormFinite (M:Ideal O)[NeZero M]:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

theorem regular_canonical_joint {α:Type}[Fintype α]
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M ≤ H)
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(hWs:Function.support W⊆Icc (1:ℝ) 2)
    (ηanchor η₀:Character)(R₀:Ideal O)(hR₀:R₀≠0)(Q:Ideal O)
    (K:ℚ)(n low:Source)(bcell reserve θ mesh ξ width τsource Cpoint:ℝ)(N degree:ℕ)
    (controls:Finset (ℕ×ℕ))(h00:(0,0)∈controls)(hf:FixedBudget reserve 100 100 1 θ)
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
    ‖∑q:F.Complete,SelectedRegularAbsolute.phase F Wa (fun _=>P) H0 radius
      ((sourceAReal n low bcell)/2) (regularFamilyKeep F) q*
      (modifiedDatumBlock (F.datum q) (F.childModifier q.1)).value ballProfile‖ ≤ 
      Cs*geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*
        (i.p.control controls)^2*(1+|ht|+height)^degree*Z^(-(reserve/8)):=by
  have hnB:(n.B:ℝ) ≤ 1:=by exact_mod_cast hn.2.1
  have hnL:1 ≤ (n.L:ℝ):=by exact_mod_cast hn.2.2.1.le
  have hncap:(n.cap:ℝ) ≤ 1:=by exact_mod_cast hn.2.2.2.2.le
  let amp:=sourceAReal n low bcell
  have hamp:0<amp:=hg.a_pos
  have hamp1:amp ≤ 1:=hg.a_small.le.trans (by norm_num)
  obtain ⟨Cs,hCs,es⟩:=regular_canonical_small (α:=α) M H hH W hW hWs ηanchor η₀ R₀ hR₀ Q
    K n low bcell reserve θ mesh ξ width τsource Cpoint N degree controls hf hg hn hξ hξ1 hθ hθ1 hpoint hτ
  obtain ⟨Ca,hCa,ea⟩:=eventually_canonical_absolute N (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ) ξ amp θ
    hnB hnL hncap hξ hξ1 hamp hamp1 hθ hθ1 W hW hWs
  obtain ⟨C,hC,en⟩:=regular_joint_of_bounded_normalized (τsource/4) 75 reserve Cs Ca N degree
    (by positivity) (by linarith [hf.tiny,hf.positive]) hCs.le hCa.le
  refine ⟨C,hC,?_⟩
  filter_upwards [es,ea,en,InitialTruncated.eventually_initial_caps N (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ) hnB hnL hncap,
    ExceptionalPrice.eventually_initial_first_geometry N (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ) ξ amp θ
      hnB hnL hncap hξ hξ1 hamp.le hamp1 hθ hθ1,allocated_frequency N] with Z hs ha hnZ hc hgZ hfZ
  refine ⟨hs.1,?_⟩
  intro hp hZ i r hi hN bin reflected a Label _ column hLive alloc P ht χ₀ hinj hfreeze hcell F H0 radius Wa height hh hv hext
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
  have hchild(l:Label):sourceRadius (F.input l) ≤ Z^(2:ℝ):=
    (InitialPhysical.child_source_radius_le F.s (F.stage l).common F.R (F.stage l).B
      (F.stage l).τ (F.stage l).t
      (fun _=>by change (1:ℝ) ≤ 2;norm_num)
      (fun j=>by change 1 ≤ Z^(i.w j);exact Real.one_le_rpow hZ.le (hi.widths_nonneg j))
      (by change (0:ℝ) ≤ 9/4;norm_num) (by change (0:ℝ) ≤ 9/4;norm_num)).trans caps.2.1
  have hsmall(second:Bool)(t u:ℝ)(hpair:(1+‖t‖)*(1+‖u‖) ≤ Z^(τsource/4)):=
    hs.2 hp hZ i r hi hN bin reflected column hLive alloc P ht χ₀ hinj hfreeze hcell Wa height hh hv hext second t u hpair
  have hab:=ha.2 hZ M H hH i ηanchor η₀ R₀ hR₀ bin reflected Q hN hi.widths_nonneg hi.face hy hyl hyr
    column hLive alloc P ht χ₀ hinj hcell.nonempty mesh θ 10 (cellNewtonDepth amp) hcell Wa
  have hcontrol:(i.p.control {(0,0)})^2 ≤ (i.p.control controls)^2:=
    pow_le_pow_left₀ (i.p.control_nonneg _) (CenteredMomentEnergyBandMonotonicity.profile_control_mono i.p
      (Finset.singleton_subset_iff.mpr h00)) 2
  have hab':secondAbsoluteBudget F.datum (fun q=>F.childModifier q.1)
      (regularFamilyWeight F Wa (fun _=>P) H0 radius (amp/2)) ≤ Ca*(i.p.control controls)^2*Z^(75:ℝ):=by
    apply hab.trans
    gcongr
  exact hnZ.2 a F caps.2.1 hHlo hHhi
    (hfZ.2 a column hLive alloc P amp ht χ₀ rfl hξ.le hξ1 hθ hamp.le) hchild
    Wa (fun _=>P) H0 radius (amp/2) ((i.p.control controls)^2) (1+|ht|+height)
    (sq_nonneg _) (by linarith [abs_nonneg ht]) hsmall hab'
end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_canonical_joint
