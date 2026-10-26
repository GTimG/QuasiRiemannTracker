/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Canonical initial data and the actual scalar/frequency LOW point gates. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalRegularLowAt
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalRegularPhase
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedRegularCanonicalGeometry
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.InitialTruncatedCaps
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.InitialPhysicalChildBounds
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.PhysicalLowGuardSource
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.RegularLowRetainedFrequency
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedRegularLowPoint
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators ContDiff SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge ConcreteTraceCRT CompletedGauss
open CenteredMomentSourceMass
open CenteredMomentEnergyBands
open CenteredMomentCommonRadialData CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSectorLocalization
open Cycle61HighGeometry Record12518109Natural
open Cycle61Moment Cycle61InitialMass LocalMoment CenteredMomentSecondHeightFamily
open CenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional CenteredMomentPrimeSlot CenteredMomentEnergyState
open OAI.SevenEighths.Record1252270103Source QRH.Record1252270103Low
open Record12518109Raw Record1252270103Finite Record1252270103StepScalar QRH.Record1252270103Graph
open SelectedSecondKeyCaps SelectedSecondNatural
open SelectedRegularSourceData SelectedHighCofactorFamily High.GlobalPhysical
local notation "O"=>HeckeFamily.O
local instance selectedLowPointDataDecEq {ι:Type*}:DecidableEq ι:=Classical.decEq _
local instance selectedLowPointDataFinite (M:Ideal O)[NeZero M]:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

structure Initial {α:Type}[Fintype α](rayM:Ideal O)[NeZero rayM]
    (H:Subgroup (O⧸rayM)ˣ)(Z:ℝ) where
  θ : α→RayQuotient.Characters rayM H
  w : α→ℝ
  freq : α→ℝ
  t₀ : ℝ
  p : Profiles (1/4) (9/4)
  X₁ : ℝ
  X₂ : ℝ
  Y₁ : ℝ
  Y₂ : ℝ
  hX₁ : 0<X₁
  hX₂ : 0<X₂
  hY₁ : 0<Y₁
  hY₂ : 0<Y₂
  same : Y₁*Y₂=X₁*X₂

namespace Initial
variable {α:Type}[Fintype α]{rayM:Ideal O}[NeZero rayM]{H:Subgroup (O⧸rayM)ˣ}{Z:ℝ}
    (i:Initial (α:=α) rayM H Z)
def input (hH:RayOrthogonality.globalUnits rayM≤H)(W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)
    (hsW:Function.support W⊆Set.Icc (1:ℝ) 2)(hZ:1<Z)(η η₀:Character)(R₀:Ideal O):Input α:=
  initialInput rayM H hH W hW hsW Z (zero_lt_one.trans hZ) η η₀ R₀ i.θ i.w i.freq i.t₀ i.p
    (by norm_num) i.X₁ i.X₂ i.Y₁ i.Y₂ i.hX₁ i.hX₂ i.hY₁ i.hY₂ i.same

def anchor (hH:RayOrthogonality.globalUnits rayM≤H)(W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)
    (hsW:Function.support W⊆Set.Icc (1:ℝ) 2)(hZ:1<Z)(η η₀:Character)(R₀ seed:Ideal O)
    (hR₀:R₀≠0)(hs:Squarefree seed)(A₁ A₂ D K:Ideal O)(Fm:Ideal O→ℂ)
    (ξ θloss:ℝ)(bin:ℤ×(Fin 5→ℤ))(reflected:Bool)(Q:Ideal O):Anchor α Z where
  s:=i.input hH W hW hsW hZ η η₀ R₀
  modifier:=Collision.markedSourceModifier A₁ A₂ D K Fm
  R:=R₀
  seed:=seed
  R_ne:=hR₀
  seed_sf:=hs
  zero₁:=initial_plain_zero i.p (by norm_num) 0
  zero₂:=initial_plain_zero i.p (by norm_num) 1
  D:=1
  ξ:=ξ
  reserve:=θloss
  hZ:=hZ
  hK:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) 1
  bin:=bin
  reflected:=reflected
  Q:=internalQ Q η₀
  m:=fixedBadMask*idealGenerator R₀
end Initial

theorem step_le_quarter (n:Source)(ha:0≤(n.allowance:ℝ))(hL:0≤(n.L:ℝ)):
    PhysicalLowGuard.step n≤(n.allowance:ℝ)/4:=by
  rw [PhysicalLowGuard.step]
  apply (div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ)<4)).mpr
  nlinarith [mul_nonneg ha hL]

theorem eventually_low_scalar (Kgraph:ℚ)(n low:Source)(b θloss ξ:ℝ)
    (hg:RealGeometry Kgraph n low b)(hn:ParentGood n)(hlow:ParentGood low)
    (ha:0<(n.allowance:ℝ))(hθ:0<θloss)(hθsmall:θloss≤(n.allowance:ℝ)/16)
    (hθstep:θloss≤PhysicalLowGuard.step n)(hξ:0<ξ)(hξstep:ξ≤PhysicalLowGuard.step n)(N:ℕ):
    ∀ᶠ Z:ℝ in atTop,1<Z ∧
      (0≤frequencyLoss Z 32 ξ ∧ frequencyLoss Z 32 ξ≤(n.allowance:ℝ)/4) ∧
      let annular:=3*(N:ℝ)*Real.logb Z 2+2*Real.logb Z (max 1 (9/4:ℝ))+2*θloss
      0≤annular ∧ annular≤(n.allowance:ℝ)/4 ∧
      ∀width:ℝ,width≤PhysicalLowGuard.step n→
        annular+(low.B:ℝ)*frequencyLoss Z 32 ξ+2*(n.allowance:ℝ)≤
          (low.B:ℝ)*sourceFReal n low b-PhysicalLowReserve.plainBudget n b width-b:=by
  have hL:0≤(n.L:ℝ):=by exact_mod_cast (lt_trans (by norm_num : (0:ℚ)<1) hn.2.2.1).le
  have hB0:0≤(low.B:ℝ):=by exact_mod_cast hlow.1.le
  have hB1:(low.B:ℝ)≤1:=by exact_mod_cast hlow.2.1
  filter_upwards [PhysicalLowGuard.eventually_geometry_guard n low N 2 (9/4) ξ ha hL hB0 hB1
    (by norm_num) hξ hξstep,PhysicalLowGuard.eventually_fixed_losses n N 2 (9/4) ξ ha (by norm_num) hξ hξstep,
    PhysicalLowGuard.eventually_logarithmic_loss N 2 (9/4) ((n.allowance:ℝ)/8) (by norm_num) (by positivity)]
      with Z hgZ hf hl
  refine ⟨hgZ.1,⟨hf.2.2.1,hf.2.2.2.trans (step_le_quarter n ha.le hL)⟩,?_,?_,?_⟩
  · linarith [hl.2.1]
  · linarith [hl.2.2]
  · intro width hw
    exact hgZ.2 Kgraph b hg (PhysicalLowReserve.plainBudget n b width) (sourceFReal n low b) b
      width θloss (frequencyLoss Z 32 ξ) θloss hθ.le hf.2.2.1 hw hθstep hf.2.2.2 hθstep
      le_rfl (by linarith [hf.2.2.1]) le_rfl


structure Scalar (Kgraph:ℚ)(n low:Source)(b θloss mesh ξ width:ℝ):Prop where
  geometry : RealGeometry Kgraph n low b
  parent : ParentGood n
  low_parent : ParentGood low
  allowance_pos : 0<(n.allowance:ℝ)
  loss_pos : 0<θloss
  loss_small : θloss≤(n.allowance:ℝ)/16
  loss_step : θloss≤PhysicalLowGuard.step n
  xi_pos : 0<ξ
  xi_loss : ξ≤θloss
  mesh_nonneg : 0≤mesh
  mesh_small : mesh≤(n.allowance:ℝ)/4
  width_nonneg : 0≤width
  width_step : width≤PhysicalLowGuard.step n

structure InitialGeometry {α:Type}[Fintype α]{M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Z:ℝ}
    (i:Initial (α:=α) M H Z)(n:Source)(b width mesh r:ℝ):Prop where
  widths_nonneg : ∀j:α,0≤Initial.w i j
  widths_mesh : ∀j:α,Initial.w i j≤mesh
  face : (globalFace (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ)).Admissible
    (length Z (Initial.X₁ i)) (length Z (Initial.X₂ i)) (∑j,Initial.w i j) 1
  cell_lower : b-width≤∑j,Initial.w i j
  cell_upper : (∑j,Initial.w i j)≤b
  r_nonneg : 0≤r
  long_left : Z^r≤Initial.X₁ i
  long_right : Z^r≤Initial.X₂ i
  reference : Initial.Y₂ i=Z^r

structure Shared {α Label Row:Type}[Fintype α][Fintype Label]{Z:ℝ}{a:Anchor α Z}{F:Family a Label}
    {rows:Finset Row}{second:Bool}(G:Selected F Row rows second)
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
    (η₀:Character)(Q:Ideal O)(hQM:Q≤M)(S A:Finset (Ideal O))(e τsource:ℝ) where
  states : rows→NaturalState Z 20 2
  fixed : ∀u,(states u).fixedModulus=internalQ Q η₀
  keep : ∀u,(states u).radial.keep (G.z u)
  select : rows→BufferIndex e
  gates : ∀u,(states u).character=G.τ u ∧
    (states u).puncture=Selection.puncture (G.sel u)*((newtonDivisorPair S A).1*(newtonDivisorPair S A).2) ∧
    (states u).width≤40 ∧
    (states u).radial.profile (‖eisEmbedding (G.z u)‖^2/(states u).radial.scale)≠0 ∧
    RetainedZeroBin M H hH (states u) η₀ ((fixed u).trans_le (inf_le_left.trans hQM))
      ((fixed u).trans_le inf_le_right) (G.z u) (keep u) e (Z^τsource) (select u) ∧
    KeyCaps (G.key u) Z 6
      (Real.logb Z ((firstSourceMissing (!F.reflected) (G.key u).val.1).absNorm:ℝ))

theorem missing_norm_from_key_caps {left:Bool}{unit:FirstSourceLabel→O}
    (key:NonzeroJointSourceLabel left 1 unit)(Z m:ℝ)(h:KeyCaps key Z 6 m):
    ((firstSourceMissing left key.val.1).absNorm:ℝ)≤Z^(6:ℝ):=by
  let I:Ideal O:=Ideal.span {jointSourceRow left 1 unit key.val}
  let H:=firstSourceMissing left key.val.1
  have hI:I≠0:=Ideal.span_singleton_eq_bot.not.mpr key.property
  have hH:H≠0:=h.2.2.2.1
  have hd:H∣I*H:=dvd_mul_left H I
  exact (CenteredMomentFirstSourceConductorCaps.divisor_norm_le H (I*H) (mul_ne_zero hI hH) hd).trans h.2.2.1



def radial {α Label Row:Type}[Fintype α][Fintype Label]{Z:ℝ}{a:Anchor α Z}{F:Family a Label}
    {rows:Finset Row}{second:Bool}(G:Selected F Row rows second)(n low:Source)(b:ℝ)(u:rows):ℝ:=
  sourceFReal n low b-max (labelD F.reflected (F.first (G.row u).val.1) Z-
    labelC F.reflected (F.first (G.row u).val.1) Z) 0-frequencyLoss Z 32 F.ξ

theorem modifier_radial {α:Type}[Fintype α]
    (n low:Source)(b:ℝ)(s:Input α)(modifier:Tuple α→ℂ)(A₁ A₂ D K R seed:Ideal O)(Fm:Ideal O→ℂ)
    (H Z ξ:ℝ)(hH:0<H)(hZ:1<Z)(bin:ℤ×(Fin 5→ℤ))
    (he:modifier=Collision.markedSourceModifier A₁ A₂ D K Fm)
    (j:FirstColumnIndex (High.CoupledFirst.geometryFirstSource s modifier R seed H Z ξ hH bin))
    (reflected second:Bool)(C₂ D₂:Ideal O)(U:Finset (CommonIndex C₂ D₂))(V reserve err errv:ℝ):
    let l:=FirstFamily.firstLabel s modifier R seed H Z ξ hH bin j
    max (labelD reflected l Z-labelC reflected l Z) 0≤labelC reflected l Z ∧
    childHighCoordinates (actualHighCoordinates reflected (!reflected) second l C₂ D₂ U Z 1 V
      (sourceAReal n low b) ξ reserve err) errv 2=
      sourceFReal n low b-max (labelD reflected l Z-labelC reflected l Z) 0-
        (frequencyLoss Z 32 ξ+reserve-err):=by
  subst modifier
  exact RegularLowRetainedRadial.modified_deficit_and_coordinate n low b s A₁ A₂ D K R seed Fm
    H Z ξ hH hZ bin j reflected second C₂ D₂ U V reserve err errv

theorem eventually_selected_frequency (θloss:ℝ)(N:ℕ)(hθ:0<θloss):
    ∀ᶠ Z:ℝ in atTop,1<Z ∧ ∀{α Label Row:Type}[Fintype α][Fintype Label]
      (a:Anchor α Z)(F:Family a Label)(rows:Finset Row)(second:Bool)(G:Selected F Row rows second)
      (n low:Source)(b:ℝ)(A₁ A₂ D K:Ideal O)(Fm:Ideal O→ℂ),
      F.D=1→F.reserve=θloss→F.modifier=Collision.markedSourceModifier A₁ A₂ D K Fm→F.ξ≤θloss→
      (∀u,F.Tsec (G.row u).val.1.1=firstMainFourierScale F.reflected (Z^F.D) (volume F.s) Z F.ξ
        (3*sourceAReal n low b) F.reserve 2 N (F.first (G.row u).val.1))→
      ∀u,max (labelD F.reflected (F.first (G.row u).val.1) Z-
        labelC F.reflected (F.first (G.row u).val.1) Z) 0≤labelC F.reflected (F.first (G.row u).val.1) Z ∧
      radial G n low b u=childHighCoordinates (actualHighCoordinates F.reflected (!F.reflected) second
        (F.first (G.row u).val.1) (G.datum u).C (G.datum u).D (G.datum u).inactive
        Z 1 (Real.logb Z (volume F.s)) (sourceAReal n low b) F.ξ θloss θloss) θloss 2 ∧
      rawFrequencyNorm (nonzeroJointSourceRow (G.key u))≤Z^(radial G n low b u):=by
  filter_upwards [FirstFamily.eventual_literal_high_frequency 2 θloss N (by norm_num) hθ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro α Label Row instα instLabel a F rows second G n low b A₁ A₂ D K Fm hD hreserve hmodifier hξ hT u
  have hrad:(G.datum u).radius=frequencyRadius
      (firstMainFourierScale F.reflected (Z^F.D) (volume F.s) Z F.ξ (3*sourceAReal n low b)
        F.reserve 2 N (FirstFamily.firstLabel F.s F.modifier F.R F.seed (Z^F.D) Z F.ξ F.hK F.bin (G.column u))) Z F.ξ:=by
    change frequencyRadius (F.Tsec (G.row u).val.1.1) Z F.ξ=_
    rw [hT u]
    rfl
  have hf:=hZ.2 F.reflected second F.s F.modifier F.R F.seed F.D F.ξ F.hK F.bin
    (G.column u) F.datum F.first (G.row u) rfl (sourceAReal n low b) F.reserve θloss hξ hrad
  have hg:=modifier_radial n low b F.s F.modifier A₁ A₂ D K F.R F.seed Fm
    (Z^F.D) Z F.ξ F.hK F.hZ F.bin hmodifier (G.column u) F.reflected second (G.datum u).C (G.datum u).D
    (G.datum u).inactive (Real.logb Z (volume F.s)) F.reserve θloss θloss
  have hg':max (labelD F.reflected (F.first (G.row u).val.1) Z-labelC F.reflected (F.first (G.row u).val.1) Z) 0≤
      labelC F.reflected (F.first (G.row u).val.1) Z ∧
      childHighCoordinates (actualHighCoordinates F.reflected (!F.reflected) second
        (F.first (G.row u).val.1) (G.datum u).C (G.datum u).D (G.datum u).inactive
        Z 1 (Real.logb Z (volume F.s)) (sourceAReal n low b) F.ξ θloss θloss) θloss 2=radial G n low b u:=by
    simpa only [Family.first,Selected.column,Anchor.label,hreserve,
      add_sub_cancel_right,radial] using hg
  refine ⟨hg'.1,hg'.2.symm,?_⟩
  change rawFrequencyNorm (nonzeroJointSourceRow (G.key u))≤Z^(
    childHighCoordinates (actualHighCoordinates F.reflected (!F.reflected) second
      (F.first (G.row u).val.1) (G.datum u).C (G.datum u).D (G.datum u).inactive
      Z F.D (Real.logb Z (volume F.s)) (sourceAReal n low b) F.ξ F.reserve θloss) θloss 2) at hf
  rw [hD,hreserve,hg'.2] at hf
  exact hf

theorem selected_common_norm_caps {α Label Row:Type}[Fintype α][Fintype Label]{Z:ℝ}{a:Anchor α Z}
    (F:Family a Label)(rows:Finset Row)(second:Bool)(G:Selected F Row rows second)
    (hsource:CenteredMomentOriginalCommonHarmonic.sourceRadius F.s≤Z^(2:ℝ))
    (hhi:∀i,1≤F.s.hi i)(hP:∀i,1≤F.s.P i)(hb₁:0≤F.s.b₁)(hb₂:0≤F.s.b₂)
    : ∀u,
      ((if F.reflected then (F.first (G.row u).val.1).1.2 else (F.first (G.row u).val.1).1.1).absNorm:ℝ)≤Z^(2:ℝ) ∧
      ((if second then (G.datum u).D else (G.datum u).C).absNorm:ℝ)≤Z^(2:ℝ):=by
  have hchild(l:Label):CenteredMomentOriginalCommonHarmonic.sourceRadius (F.input l)≤Z^(2:ℝ):=
    (InitialPhysical.child_source_radius_le F.s (F.stage l).common F.R (F.stage l).B
      (F.stage l).τ (F.stage l).t hhi hP hb₁ hb₂).trans hsource
  intro u
  constructor
  · have hc:=High.CoupledFirst.actual_geometry_norm_caps F.s F.modifier F.R F.seed (Z^F.D) Z F.ξ 2
      F.seed_sf F.zero₁ F.zero₂ hsource (G.column u).1.val
    cases hr:F.reflected
    · exact (hc 0).2
    · exact (hc 1).2
  · have hc:=SelectedSecondKeyCaps.regular_common_caps F.slots F.input F.childModifier F.mask F.childSeed
      F.Hmain F.Tsec Z F.ξ CenteredMomentFirstAmplificationChoice.ballProfile F.childSeed_sf
      (fun _=>F.zero₁) (fun _=>F.zero₂) F.Hmain_pos F.χ₀ F.Q F.m (G.row u).val.1
    cases second
    · exact hc.1.trans (hchild (G.row u).val.1.1)
    · exact hc.2.trans (hchild (G.row u).val.1.1)

theorem selected_residual_norm_cap {α Label Row:Type}[Fintype α][Fintype Label]{Z:ℝ}{a:Anchor α Z}
    (F:Family a Label)(rows:Finset Row)(second:Bool)(G:Selected F Row rows second)
    (hpool:∀I∈finiteColumns (Fintype.piFinset F.s.pools),(I.absNorm:ℝ)≤Z^(4:ℝ))
    (hL:∃r:F.Rows,G.L∈secondResidualIdeals (fun q=>(F.datum q).block) r.val):
    (G.L.absNorm:ℝ)≤Z^(4:ℝ):=by
  obtain ⟨r,hr⟩:=hL
  have hp:=SelectedRegularAbsolute.child_full_pool_cap F 4
    (SelectedRegularAbsolute.column_cap_irrel _ _ _ _ hpool) r.val.1.1
  exact (InitialPhysical.modified_second_residual_full_cap F.datum
    (fun q=>F.childModifier q.1) r.val (Z^(4:ℝ)) (SelectedRegularAbsolute.column_cap_irrel _ _ _ _ hp) G.L hr).2

end
end QRH.Record1252270103Source.Admission.SelectedRegularLowPoint
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularLowPoint.step_le_quarter
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularLowPoint.eventually_low_scalar

#print axioms QRH.Record1252270103Source.Admission.SelectedRegularLowPoint.missing_norm_from_key_caps

#print axioms QRH.Record1252270103Source.Admission.SelectedRegularLowPoint.eventually_selected_frequency

#print axioms QRH.Record1252270103Source.Admission.SelectedRegularLowPoint.modifier_radial

#print axioms QRH.Record1252270103Source.Admission.SelectedRegularLowPoint.selected_common_norm_caps

#print axioms QRH.Record1252270103Source.Admission.SelectedRegularLowPoint.selected_residual_norm_cap
