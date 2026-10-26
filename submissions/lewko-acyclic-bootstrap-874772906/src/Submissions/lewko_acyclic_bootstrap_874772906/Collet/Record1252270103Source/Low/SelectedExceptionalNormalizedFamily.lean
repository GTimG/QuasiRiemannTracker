/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The genuine corrected exceptional child estimate pays the physical block.
Only finite polynomial caps and the original character-family identity enter;
the full allocation count, frozen weights, divisor seed and row selector remain. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.SelectedExceptionalNormalizedPhysical
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.SelectedExceptionalNormalizedRows
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.SecondEffectiveScalar
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Low.SelectedExceptionalNormalized
noncomputable section
open OAI OAI.SevenEighths OAI.SevenEighths.Record1252270103Source
open Filter ExceptionalWindow
open scoped Classical BigOperators SchwartzMap
open Record1252270103Second Record1252270103GlobalSelected
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn CenteredMomentFirstSectors
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit CenteredMomentCanonicalFirst
open CenteredMomentSecondSectorColumns CenteredMomentSecondNonexceptional
open CenteredMomentSecondWholeKernel CenteredMomentSecondSectorRetained CenteredMomentSecondWindowBudget
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization CenteredMomentOriginalCommonHarmonic
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy CenteredMomentMobiusRegroup RayFourExpansion
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile CenteredMomentSourceProfileMass
open ConcretePrimeRowBridge CenteredExceptionalProfile CenteredMomentChildRows CenteredMomentSecondHeightFamily
open QRH.Record1252270103Low QRH.Record1252270103Source.High.CorrectedCentered
open QRH.Record1252270103Source.ForcedCost
local notation "O"=>ActualEisensteinCubic.O
local notation "coefficient"=>QRH.Record1252270103Source.High.CoupledFirst.coefficient
open SecondSectorDatum High.GlobalPhysical Admission.SelectedSecondNatural Cycle61InitialMass
open CenteredMomentFirstAmplificationChoice CenteredMomentEnergyChildState
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _
local instance selectedExceptionalFamilySum {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable {α:Type*} [Fintype α]


/-- Only actual support, arithmetic and polynomial-size gates for a retained
datum. In particular this structure contains no energy or physical norm bound. -/
structure ExceptionalCaps (d:SecondInputDatum α)(W₁ W₂ Φ:𝓢(ℝ,ℂ))
    (A₁ A₂ Df K Q:Ideal O)(P:Finset (Ideal O))
    (a b Z Bη BR Bfreq BH BA Bpool Bplain BD ell B H brad Lraw:ℝ)(depth:ℕ):Prop where
  profile1:d.input.W₁=(W₁:ℝ→ℂ)
  profile2:d.input.W₂=(W₂:ℝ→ℂ)
  support1:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b
  support2:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b
  scales:∀i,1≤d.input.P i
  coprime:IsCoprime Q d.C
  radial_pos:0<H
  brad_nonneg:0≤brad
  radial_nonneg:∀x,0≤(Φ x).re
  radial_support:Function.support (Φ:ℝ→ℂ)⊆Set.Iic brad
  radial_major:∀z∈d.rows,1≤(Φ (normValue z/H)).re
  character_cap:(d.input.η.modulus.absNorm:ℝ)≤Z^Bη
  frequency_cap:((Ideal.span {d.block.frequency}).absNorm:ℝ)≤Z^Bfreq
  height_cap:H≤Z^BH
  fixed_cap:(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ)*brad≤Z
  raw_pos:0<Lraw
  raw_X1:Lraw≤d.input.X₁
  raw_X2:Lraw≤d.input.X₂
  raw_Y1:Lraw≤d.input.Y₁
  raw_Y2:Lraw≤d.input.Y₂
  allocations:∀X:Ideal O,X=d.C∨X=d.D→
    ∀L∈divisorPool Finset.univ
      (fun I:sectorPool d.D d.hD.1 (finiteColumns (Fintype.piFinset d.input.pools))=>(I:Ideal O)),
    Squarefree L→∀A:actualAllocations d.input.pools X,
    frozenCoefficient A X d.R d.input.ν d.input.W d.input.P≠0→
    CorrectedAllocatedCaps d.input X d.R A W₁ W₂ b Z BA Bpool Bplain BD BR ell depth A₁ A₂ Df K L P
  residual_cap:∀I:sectorPool d.D d.hD.1 (finiteColumns (Fintype.piFinset d.input.pools)),
    ((I:Ideal O).absNorm:ℝ)≤Z^B

/-- The scalar payment after both complete common allocations and the full
artificial-divisor sum. The height profile, ratio and effective phase stay literal. -/
def datumPayment (d:SecondInputDatum α)(T:Finset (ℕ×ℕ))(W₁ W₂ Φ:𝓢(ℝ,ℂ))(Q:Ideal O)
    (Z ε εL power B δ H brad Lraw C₀ K₀ Cphys Hmass:ℝ)(J decay:ℕ):ℝ :=
  Cphys*(outerScalar d.C d.D d.K d.dyad*normalizer d.C d.D d.inactive)*
    (Hmass*Z^(δ+B*εL)*pairedPayment d.input T W₁ W₂ Φ Q d.C d.D d.inactive
      Z ε εL power Lraw brad (Real.logb Z H) C₀ K₀ J d.input.t)/
    (1+dyadicScale (d.dyad 0)*dyadicScale (d.dyad 1)/
      (dyadicScale (d.dyad 2)*dyadicScale (d.dyad 3)))^decay

/-- Exact normalization for the effective phase factor consumed by the
checked actual_second_phase_bound. No inequality or energy premise is used. -/
theorem datum_phase_payment (d:SecondInputDatum α)(w:ℂ)
    (T:Finset (ℕ×ℕ))(W₁ W₂ Φ:𝓢(ℝ,ℂ))(Q:Ideal O)
    (Z ε εL power B δ H brad Lraw C₀ K₀ Cphys Hmass:ℝ)(J decay:ℕ):
    ‖w‖*datumPayment d T W₁ W₂ Φ Q Z ε εL power B δ H brad Lraw C₀ K₀ Cphys Hmass J decay=
      (‖w‖*d.block.outside*volume d.input)*
        (Cphys*Hmass*Z^(δ+B*εL)*pairedPayment d.input T W₁ W₂ Φ Q d.C d.D d.inactive
          Z ε εL power Lraw brad (Real.logb Z H) C₀ K₀ J d.input.t/volume d.input)/
        (1+dyadicScale (d.dyad 0)*dyadicScale (d.dyad 1)/
          (dyadicScale (d.dyad 2)*dyadicScale (d.dyad 3)))^decay := by
  have hv:volume d.input≠0:=(volume_pos d.input).ne'
  change ‖w‖*datumPayment d T W₁ W₂ Φ Q Z ε εL power B δ H brad Lraw C₀ K₀ Cphys Hmass J decay=
    (‖w‖*(outerScalar d.C d.D d.K d.dyad*normalizer d.C d.D d.inactive)*volume d.input)*_/_
  unfold datumPayment
  simp only [div_eq_mul_inv]
  calc
    _=‖w‖*(outerScalar d.C d.D d.K d.dyad*normalizer d.C d.D d.inactive)*
      (volume d.input*(volume d.input)⁻¹)*
      (Cphys*Hmass*Z^(δ+B*εL)*pairedPayment d.input T W₁ W₂ Φ Q d.C d.D d.inactive
        Z ε εL power Lraw brad (Real.logb Z H) C₀ K₀ J d.input.t)*
      ((1+dyadicScale (d.dyad 0)*dyadicScale (d.dyad 1)*
        (dyadicScale (d.dyad 2)*dyadicScale (d.dyad 3))⁻¹)^decay)⁻¹ := by
          rw [mul_inv_cancel₀ hv]
          ring
    _=_:=by ring

/-- Moving original inputs and first-stage weights; no analytic bounds are
part of these data. The complete carrier is defined before the row split. -/
structure CorrectedFamilyData {Label:Type*}(slots:Label→Finset α)(W:𝓢(ℝ,ℂ))(Z:ℝ) where
  input:∀l,Input (slots l)
  W₁:Label→𝓢(ℝ,ℂ)
  W₂:Label→𝓢(ℝ,ℂ)
  A₁:Label→Ideal O
  A₂:Label→Ideal O
  frozen:Label→Ideal O
  marked:Label→Ideal O
  puncture:Label→Ideal O
  seed:Label→Ideal O
  pool:Label→Finset (Ideal O)
  seed_squarefree:∀l,Squarefree (seed l)
  zero₁:∀l,(input l).W₁ 0=0
  zero₂:∀l,(input l).W₂ 0=0
  physicalScale:Label→ℝ
  sectorScale:Label→ℝ
  energyScale:Label→ℝ
  amplitude:Label→ℝ
  mesh:ℝ
  physical_pos:∀l,0<physicalScale l
  referenceRay:Label→RayCharacter
  rowMask:O

namespace CorrectedFamilyData
variable {Label:Type*}[Fintype Label]{slots:Label→Finset α}{W:𝓢(ℝ,ℂ)}{Z:ℝ}

def modifier (f:CorrectedFamilyData slots W Z)(l:Label):Tuple (slots l)→ℂ :=
  Collision.markedSourceModifier (f.A₁ l) (f.A₂ l) (f.frozen l) (f.marked l) (poolCorrection (f.pool l))

abbrev Carrier (f:CorrectedFamilyData slots W Z):=
  CompleteFamily slots f.input f.modifier f.puncture f.seed W f.physicalScale f.sectorScale
    (fun _=>Z) (fun _=>f.mesh)

def datum (f:CorrectedFamilyData slots W Z)(Q:Ideal O)(q:f.Carrier):SecondInputDatum α :=
  exceptionalDatum slots f.input f.modifier f.puncture f.seed f.physicalScale f.sectorScale Z f.mesh W
    f.seed_squarefree f.zero₁ f.zero₂ f.physical_pos f.referenceRay Q f.rowMask q

def block (f:CorrectedFamilyData slots W Z)(Q:Ideal O)(q:f.Carrier):SecondBlockSource :=
  modifiedDatumBlock (f.datum Q q) (f.modifier q.1)

def phase (f:CorrectedFamilyData slots W Z)(Q:Ideal O)(q:f.Carrier):ℂ :=
  familyWeight slots f.input f.modifier f.puncture f.seed W f.physicalScale f.sectorScale
    (fun _=>Z) (fun _=>f.mesh) f.energyScale f.amplitude
    (fun l q z=>¬regularKeep slots f.input f.modifier f.puncture f.seed f.physicalScale
      f.sectorScale Z f.mesh f.referenceRay Q f.rowMask l q z) q

structure RadialData (f:CorrectedFamilyData slots W Z) where
  profile:f.Carrier→𝓢(ℝ,ℂ)
  scale:f.Carrier→ℝ
  upper:f.Carrier→ℝ
  rawLower:f.Carrier→ℝ

/-- The original retained ball supplies the radial data uniformly; the
reference modulus only selects rows and changes no radius. -/
def retainedRadial (f:CorrectedFamilyData slots W Z)(Q:Ideal O)
    (raw:f.Carrier→ℝ):RadialData f where
  profile:=fun _=>ballProfile
  scale:=fun q=>Cycle61FinalNatural.retainedScale (f.datum Q q).radius
    (f.datum Q q).C (f.datum Q q).D (f.datum Q q).inactive
  upper:=fun _=>2
  rawLower:=raw

theorem retainedRadial_gates (f:CorrectedFamilyData slots W Z)(Q:Ideal O)
    (raw:f.Carrier→ℝ)(q:f.Carrier):
    let rad:=f.retainedRadial Q raw
    0<rad.scale q ∧ 0≤rad.upper q ∧ (∀x,0≤(rad.profile q x).re) ∧
    Function.support (rad.profile q:ℝ→ℂ)⊆Set.Iic (rad.upper q) ∧
    ∀z∈(f.datum Q q).rows,1≤(rad.profile q (normValue z/rad.scale q)).re := by
  have hg:=exceptional_retained_majorant slots f.input f.modifier f.puncture f.seed
    f.physicalScale f.sectorScale Z f.mesh W f.seed_squarefree f.zero₁ f.zero₂ f.physical_pos
    f.referenceRay Q f.rowMask q
  exact ⟨hg.1,by norm_num [retainedRadial],ballProfile_nonneg,ball_support,hg.2⟩

theorem modulus_coprime (f:CorrectedFamilyData slots W Z)(Q:Ideal O)
    (hQR:∀l,Q∣f.puncture l)(q:f.Carrier):
    IsCoprime Q (f.datum Q q).C ∧ IsCoprime Q (f.datum Q q).D :=
  exceptional_common_coprime slots f.input f.modifier f.puncture f.seed
    f.physicalScale f.sectorScale Z f.mesh W f.seed_squarefree f.zero₁ f.zero₂ f.physical_pos
    f.referenceRay Q f.rowMask q (hQR q.1)

def Caps (f:CorrectedFamilyData slots W Z)(rad:RadialData f)(Q:Ideal O)
    (a b Bη BR Bfreq BH BA Bpool Bplain BD ell B:ℝ)(depth:ℕ):Prop :=
  ∀q,ExceptionalCaps (f.datum Q q) (f.W₁ q.1) (f.W₂ q.1) (rad.profile q)
    (f.A₁ q.1) (f.A₂ q.1) (f.frozen q.1) (f.marked q.1) Q (f.pool q.1)
    a b Z Bη BR Bfreq BH BA Bpool Bplain BD ell B (rad.scale q) (rad.upper q) (rad.rawLower q) depth

def payment (f:CorrectedFamilyData slots W Z)(rad:RadialData f)(Q:Ideal O)
    (J:Finset α→ℕ)(T:Finset α→Finset (ℕ×ℕ))(C₀ K₀ Cphys Hmass:Finset α→ℝ)
    (ε εL power B δ:ℝ)(decay:ℕ)(q:f.Carrier):ℝ :=
  datumPayment (f.datum Q q) (T (slots q.1)) (f.W₁ q.1) (f.W₂ q.1) (rad.profile q) Q
    Z ε εL power B δ (rad.scale q) (rad.upper q) (rad.rawLower q)
    (C₀ (slots q.1)) (K₀ (slots q.1)) (Cphys (slots q.1)) (Hmass (slots q.1))
    (J (slots q.1)) decay
end CorrectedFamilyData

/-- Genuine exceptional control for the complementary original complete
family, with its effective phase weight. Only the explicit nonanalytic Caps
remain at the caller. All finite-subset constants precede every moving datum. -/
theorem exceptional_complete_family_paid
    (W:𝓢(ℝ,ℂ))(decay:ℕ)
    (a b ε εL Bη BR Bfreq BH BA Bpool Bplain BD ell power B δ:ℝ)(depth:ℕ)
    (ha:0<a)(hb:0≤b)(hε:0<ε)(hεL:0<εL)
    (hBχ:0≤Bη+BR+Bfreq+BH+1)(hBA:0≤BA)(hBpool:0≤Bpool)
    (hell:0<ell)(hpower0:0≤power)(hpower:power<1/2)(hB:0≤B)(hδ:0<δ):
    ∃J:Finset α→ℕ,∃T:Finset α→Finset (ℕ×ℕ),(∀A,(0,0)∈T A) ∧
    ∀Q:Ideal O,Q≠0→Q≠⊤→Q≤Ideal.span {(72:O)}→
    ∃C₀ K₀ Cphys Hmass:Finset α→ℝ,
      (∀A,0<C₀ A ∧ 0<K₀ A ∧ 0≤Cphys A ∧ 0<Hmass A) ∧
    ∀ᶠ Z:ℝ in atTop,1<Z ∧
    ∀{Label:Type*}[Fintype Label](slots:Label→Finset α)(f:CorrectedFamilyData slots W Z),
    f.rowMask≠0→goodLambda∣f.rowMask→(2:O)∣f.rowMask→
    ∀rad:CorrectedFamilyData.RadialData f,
    f.Caps rad Q a b Bη BR Bfreq BH BA Bpool Bplain BD ell B depth→
    ‖∑q,f.phase Q q*(f.block Q q).value W‖≤
      ∑q,‖secondEffectiveWeight (f.block Q) (f.phase Q) W q‖*
        f.payment rad Q J T C₀ K₀ Cphys Hmass ε εL power B δ decay q := by
  obtain ⟨J,T,hT,hp⟩:=exceptional_finite_subset_paid (κ:=α) W decay
    a b ε εL Bη BR Bfreq BH BA Bpool Bplain BD ell power B δ depth
    ha hb hε hεL hBχ hBA hBpool hell hpower0 hpower hB hδ
  refine ⟨J,T,hT,?_⟩
  intro Q hQ0 hQ hQ72
  obtain ⟨C₀,K₀,Cphys,Hmass,hpos,hp⟩:=hp Q hQ0 hQ hQ72
  refine ⟨C₀,K₀,Cphys,Hmass,hpos,?_⟩
  filter_upwards [hp] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Label inst slots f hm hmLam hm2 rad hc
  rw [actual_second_effective_sum (f.block Q) (f.phase Q) W]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro q _
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  let d:=f.datum Q q
  have hg:=exceptional_original_gates slots f.input f.modifier f.puncture f.seed
    f.physicalScale f.sectorScale Z f.mesh W f.seed_squarefree f.zero₁ f.zero₂ f.physical_pos
    f.referenceRay Q f.rowMask q
  have hf:∀χ:RayCharacter,∀I:Ideal O,Supported I→(IsCoprime d.C I∨IsCoprime d.D I)→
      ∀v:ℝ,heightCoeff (d.τ χ) v I=heightCoeff d.input.η v I*
        idealRowHom d.block.frequency I*rayCharacter χ (primaryGenerator I):=d.family.height_eq
  have hex:∀z∈d.rows,FixedInducingRow (childCharacter d.input.η (f.referenceRay q.1)) Q f.rowMask d.block.frequency z:=
    exceptional_rows_fixed slots f.input f.modifier f.puncture f.seed f.physicalScale f.sectorScale Z f.mesh W
      f.seed_squarefree f.zero₁ f.zero₂ f.physical_pos f.referenceRay Q f.rowMask q
  have cc:=hc q
  have hh:=hZ.2 d.slots
  specialize hh (f.W₁ q.1) (f.W₂ q.1) cc.support1 cc.support2 d.input cc.profile1 cc.profile2 cc.scales
  specialize hh d.input.η d.τ d.input.t (f.A₁ q.1) (f.A₂ q.1) (f.frozen q.1) (f.marked q.1) d.R d.seed (f.pool q.1)
    d.C d.D d.hC d.hD hg.2.2.1 hg.2.2.2 d.sameSupport cc.coprime hg.1
  specialize hh d.inactive hf d.radius d.rows f.rowMask (f.referenceRay q.1) hm hmLam hm2 d.rows_ne hex
  specialize hh (rad.profile q) (rad.scale q) (rad.upper q) cc.radial_pos cc.brad_nonneg cc.radial_nonneg
    cc.radial_support cc.radial_major cc.character_cap cc.frequency_cap cc.height_cap cc.fixed_cap
  specialize hh (rad.rawLower q) cc.raw_pos cc.raw_X1 cc.raw_X2 cc.raw_Y1 cc.raw_Y2
  specialize hh cc.allocations
  specialize hh cc.residual_cap
  specialize hh d.K d.K_pos d.dyad
  exact hh
end
end QRH.Record1252270103Source.Low.SelectedExceptionalNormalized
#print axioms QRH.Record1252270103Source.Low.SelectedExceptionalNormalized.exceptional_complete_family_paid

#print axioms QRH.Record1252270103Source.Low.SelectedExceptionalNormalized.datum_phase_payment

#print axioms QRH.Record1252270103Source.Low.SelectedExceptionalNormalized.CorrectedFamilyData.retainedRadial_gates
#print axioms QRH.Record1252270103Source.Low.SelectedExceptionalNormalized.CorrectedFamilyData.modulus_coprime
