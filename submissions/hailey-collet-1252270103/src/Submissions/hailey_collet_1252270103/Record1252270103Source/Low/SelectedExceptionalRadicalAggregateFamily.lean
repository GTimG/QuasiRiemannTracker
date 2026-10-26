/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Full original second blocks inject into the actual radical mass family. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.SelectedExceptionalRadicalAggregatePrice
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Low.SelectedExceptionalRadicalAggregate
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn CenteredMomentFirstSectors CenteredMomentSecondSectorColumns
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSectorLocalization CenteredMomentSupport
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceRow CenteredMomentActiveSource
open CenteredMomentSecondBlockHarmonicMass CenteredMomentSecondBlockRadicalHarmonicMass
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate
open Cycle61InitialMass Record1252270103Second Record1252270103CommonGeometry
open OAI.SevenEighths.Record1252270103Source ExceptionalRadical
open QRH.Record1252270103Source.High
open QRH.Record1252270103Source.High.GlobalPhysical SecondSectorDatum
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentHeckeColumnWindow CenteredMomentMobiusRegroup CenteredMomentDivisorBoundary
open CenteredMomentSecondWindowBudget CenteredMomentSecondInputCapacitySource
open CenteredMomentSecondLiveBlock
open CenteredMomentFirstAmplificationChoice
open QRH.Record1252270103Low
open Low.SelectedExceptionalNormalized Low.SelectedExceptionalInitialCaps
open Low.SelectedExceptionalNormalizedMasked


variable {α Label:Type*}[Fintype α][Fintype Label]

/-- The first-label cost retains the original energy normalizer, physical
radius and first allocation; no child-volume substitution is made. -/
def firstCost {slots:Label→Finset α}{W:𝓢(ℝ,ℂ)}{Z:ℝ}
    (f:CorrectedFamilyData slots W Z)(N:ℕ)(Q:Ideal O)
    (J:Finset α→ℕ)(T:Finset α→Finset (ℕ×ℕ))(C₀ K₀ Cphys:Finset α→ℝ)
    (ε:ℝ)(raw:Label→ℝ)(l:Label):ℝ :=
  (f.amplitude l/f.energyScale l)*(f.physicalScale l/lowerFactor N 1 (1/4))*Cphys (slots l)*
    (CenteredMomentCommonExceptionalCost.frozenProfile (f.input l))^2*
    centeredProfileFactor (f.input l) (T (slots l)) (f.W₁ l) (f.W₂ l) ballProfile Q Z ε
      (499/1000) (raw l) 2 (C₀ (slots l)) (K₀ (slots l))*
    volume (f.input l)*(4*frequencyRadius (f.sectorScale l) Z f.mesh)^(1/6:ℝ)*
    (heightEnvelope (f.input l).t^(J (slots l))*profileMoment (J (slots l)))^2

lemma firstCost_nonneg {slots:Label→Finset α}{W:𝓢(ℝ,ℂ)}{Z:ℝ}
    (f:CorrectedFamilyData slots W Z)(N:ℕ)(Q:Ideal O)
    (J:Finset α→ℕ)(T:Finset α→Finset (ℕ×ℕ))(C₀ K₀ Cphys:Finset α→ℝ)
    (ε:ℝ)(raw:Label→ℝ)(ha:∀l,0≤f.amplitude l)(he:∀l,0<f.energyScale l)
    (hK:∀A,0≤K₀ A)(hp:∀A,0≤Cphys A)
    (hr:∀l,0≤frequencyRadius (f.sectorScale l) Z f.mesh)(l:Label):
    0≤firstCost f N Q J T C₀ K₀ Cphys ε raw l:=by
  have hc:=centeredProfileFactor_nonneg (f.input l) (T (slots l)) (f.W₁ l) (f.W₂ l)
    ballProfile Q Z ε (499/1000) (raw l) 2 (C₀ (slots l)) (K₀ (slots l)) (hK _) (by norm_num)
  have hl:=lowerFactor_pos N (1:ℝ) (1/4) (by norm_num) (by norm_num)
  have hh:=f.physical_pos l
  have hv:=volume_pos (f.input l)
  have hh':=ha l
  have he':=he l
  have hp':=hp (slots l)
  have hr':=hr l
  unfold firstCost
  positivity

/-- The original complete block provides the nonzero witness for the
outside scalar even when every exceptional selected row vanishes. -/
lemma original_outside {slots:Label→Finset α}{W:𝓢(ℝ,ℂ)}{Z:ℝ}
    (f:CorrectedFamilyData slots W Z)(Q:Ideal O)(N:ℕ)(hN:Fintype.card α≤N)
    (hlower:∀l,1≤(f.input l).lower)
    (hW₁:∀l x,(f.input l).W₁ x≠0→(1/4:ℝ)≤x)
    (hW₂:∀l x,(f.input l).W₂ x≠0→(1/4:ℝ)≤x)(q:f.Carrier):
    (f.datum Q q).block.outside≤f.physicalScale q.1/
      (lowerFactor N 1 (1/4)*volume (f.input q.1))*
      normalizer (f.datum Q q).C (f.datum Q q).D (f.datum Q q).inactive:=by
  let d:=modifiedRetainedDatum (slots q.1) (f.input q.1) (f.modifier q.1)
    (f.puncture q.1) (f.seed q.1) (f.seed_squarefree q.1) (f.zero₁ q.1) (f.zero₂ q.1)
    (f.physicalScale q.1) (f.sectorScale q.1) Z f.mesh (f.physical_pos q.1) q.2.val
  exact actual_modified_second_outside N 1 (1/4) (by norm_num) (by norm_num) d
    (f.modifier q.1) W hN (hlower q.1) (hW₁ q.1) (hW₂ q.1) q.2.property

lemma effective_phase_le {slots:Label→Finset α}{W:𝓢(ℝ,ℂ)}{Z:ℝ}
    (f:CorrectedFamilyData slots W Z)(Q:Ideal O)
    (ha:∀l,0≤f.amplitude l)(he:∀l,0<f.energyScale l)(q:f.Carrier):
    ‖secondEffectiveWeight (f.block Q) (f.phase Q) W q‖≤f.amplitude q.1/f.energyScale q.1:=by
  have hh:=actual_family_weight_parent slots f.input f.modifier f.puncture f.seed W
    f.physicalScale f.sectorScale (fun _=>Z) (fun _=>f.mesh) f.energyScale f.amplitude he ha
    (fun l q z=>¬Admission.SelectedSecondNatural.regularKeep slots f.input f.modifier f.puncture f.seed
      f.physicalScale f.sectorScale Z f.mesh f.referenceRay Q f.rowMask l q z) q
  unfold secondEffectiveWeight
  split
  · simpa only [norm_zero] using div_nonneg (ha q.1) (he q.1).le
  · exact hh

/-- Summation of the exact analytic payment: both allocation cards, every
second common label, inactive subset, dyad and residual divisor are paid.
All remaining terms are indexed only by the original first label. -/
theorem eventually_family_payment (N:ℕ)(Bsource L Cr Bdiv δ epsMass:ℝ)
    (hBs:0≤Bsource)(hL:0≤L)(hCr:0<Cr)(hBd:0≤Bdiv)(hδ:0<δ)(hεm:0<epsMass):
    ∃A Hmass:ℝ,0<A ∧ 0<Hmass ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀{α Label:Type*}[Fintype α][Fintype Label](slots:Label→Finset α)
      (W:𝓢(ℝ,ℂ))(f:CorrectedFamilyData slots W Z)(Q:Ideal O)
      (J:Finset α→ℕ)(T:Finset α→Finset (ℕ×ℕ))(C₀ K₀ Cphys:Finset α→ℝ)
      (ε εL:ℝ)(raw:Label→ℝ)(decay:ℕ),
    Fintype.card α≤N→0≤εL→(∀A,0≤K₀ A)→(∀A,0≤Cphys A)→
    (∀l,0≤f.amplitude l)→(∀l,0<f.energyScale l)→
    (∀l,1≤(f.input l).lower)→
    (∀l x,(f.input l).W₁ x≠0→(1/4:ℝ)≤x)→
    (∀l x,(f.input l).W₂ x≠0→(1/4:ℝ)≤x)→
    (∀l,sourceRadius (f.input l)≤Z^Bsource)→
    (∀l,0≤frequencyRadius (f.sectorScale l) Z f.mesh)→
    (∀l,frequencyRadius (f.sectorScale l) Z f.mesh≤Cr*Z^L)→
    (∀l,f.seed l≠0)→
    (∀q:f.Carrier,∀I:sectorPool (f.datum Q q).D (f.datum Q q).hD.1
      (finiteColumns (Fintype.piFinset (f.datum Q q).input.pools)),((I:Ideal O).absNorm:ℝ)≤Z^Bdiv)→
    (∑q,‖secondEffectiveWeight (f.block Q) (f.phase Q) W q‖*
      familyPayment f (f.retainedRadial Q (fun q=>raw q.1)) Q J T C₀ K₀ Cphys ε εL (499/1000) decay q)≤
      A*Hmass*Z^(epsMass+δ+Bdiv*εL)*∑l,firstCost f N Q J T C₀ K₀ Cphys ε raw l/(f.seed l).absNorm:=by
  obtain ⟨A,hA,hm⟩:=actual_complete_allocation_radical_mass N Bsource L Cr epsMass hBs hL hCr hεm
  obtain ⟨Hmass,hH,hp⟩:=eventually_normalized_divisor_price Bdiv δ hBd hδ
  refine ⟨A,Hmass,hA,hH,?_⟩
  filter_upwards [hm,hp] with Z hm hp
  refine ⟨hp.1,?_⟩
  intro α Label instα instLabel slots W f Q J T C₀ K₀ Cphys ε εL raw decay hN hεL hK hphys ha he
    hlower hW₁ hW₂ hsource hrad0 hradius hseed hdiv
  have hZ:0<Z:=zero_lt_one.trans hp.1
  have point (q:f.Carrier):
      ‖secondEffectiveWeight (f.block Q) (f.phase Q) W q‖*
        familyPayment f (f.retainedRadial Q (fun q=>raw q.1)) Q J T C₀ K₀ Cphys ε εL (499/1000) decay q≤
      (Hmass*Z^(δ+Bdiv*εL)*firstCost f N Q J T C₀ K₀ Cphys ε raw q.1)*
        allocationRadical (f.input q.1) (f.datum Q q).C (f.datum Q q).D:=by
    let d:=f.datum Q q
    let Dsum:=radicalDivisorSum d (T (slots q.1)) (f.W₁ q.1) (f.W₂ q.1) ballProfile Q
      Z ε εL (499/1000) (Cycle61FinalNatural.retainedScale d.radius d.C d.D d.inactive)
      2 (raw q.1) (C₀ (slots q.1)) (K₀ (slots q.1)) (J (slots q.1))
    have hD:0≤Dsum:=by
      unfold Dsum radicalDivisorSum
      exact Finset.sum_nonneg fun L hL=>mul_nonneg (norm_nonneg _)
        (radicalPair_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hZ.le (by norm_num) (hK _))
    have hprice:=hp.2 d (T (slots q.1)) (f.W₁ q.1) (f.W₂ q.1) Q ε εL (raw q.1)
      (C₀ (slots q.1)) (K₀ (slots q.1)) (J (slots q.1)) hεL (hK _) (hdiv q)
      (CoupledFirst.coefficient (f.input q.1) (f.modifier q.1) (f.puncture q.1) (f.seed q.1))
      (blockRows d.C d.D d.inactive d.radius) W
      (fun z hz=>(liveRows_geometry _ _ _ _ _ z hz).2.1) q.2.property
    have ho:=original_outside f Q N hN hlower hW₁ hW₂ q
    have hw:=effective_phase_le f Q ha he q
    have hn:0≤normalizer d.C d.D d.inactive:=(normalizer_pos d.C d.D d.hC d.inactive).le
    have hv:=volume_pos d.input
    have hl:=lowerFactor_pos N (1:ℝ) (1/4) (by norm_num) (by norm_num)
    have hd:1≤(1+dyadicScale (d.dyad 0)*dyadicScale (d.dyad 1)/
        (dyadicScale (d.dyad 2)*dyadicScale (d.dyad 3)))^decay:=one_le_pow₀ (by
      have hh:0≤dyadicScale (d.dyad 0)*dyadicScale (d.dyad 1)/
          (dyadicScale (d.dyad 2)*dyadicScale (d.dyad 3)):=div_nonneg (mul_nonneg (dyadicScale_pos _).le (dyadicScale_pos _).le)
            (mul_nonneg (dyadicScale_pos _).le (dyadicScale_pos _).le)
      linarith)
    have houtside:0≤d.block.outside:=by
      change 0≤outerScalar d.C d.D d.K d.dyad*normalizer d.C d.D d.inactive
      have hdk:=d.K_pos
      unfold outerScalar
      positivity
    have hCp:=hphys (slots q.1)
    change ‖secondEffectiveWeight (f.block Q) (f.phase Q) W q‖*
      (Cphys (slots q.1)*d.block.outside*Dsum/_ )≤_
    rw [←mul_div_assoc]
    calc
      _≤‖secondEffectiveWeight (f.block Q) (f.phase Q) W q‖*
        (Cphys (slots q.1)*d.block.outside*Dsum):=div_le_self (by positivity) hd
      _≤(f.amplitude q.1/f.energyScale q.1)*
          (Cphys (slots q.1)*(f.physicalScale q.1/(lowerFactor N 1 (1/4)*volume d.input)*
            normalizer d.C d.D d.inactive)*Dsum):=by
        apply mul_le_mul hw _ (by positivity) (div_nonneg (ha _) (he _).le)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ho (hphys _)) hD
      _=((f.amplitude q.1/f.energyScale q.1)*(f.physicalScale q.1/lowerFactor N 1 (1/4))*Cphys (slots q.1))*
          (normalizer d.C d.D d.inactive*Dsum/volume d.input):=by ring
      _≤((f.amplitude q.1/f.energyScale q.1)*(f.physicalScale q.1/lowerFactor N 1 (1/4))*Cphys (slots q.1))*
          (Hmass*Z^(δ+Bdiv*εL)*(CenteredMomentCommonExceptionalCost.frozenProfile d.input)^2*
          centeredProfileFactor d.input (T (slots q.1)) (f.W₁ q.1) (f.W₂ q.1) ballProfile Q Z ε (499/1000)
          (raw q.1) 2 (C₀ (slots q.1)) (K₀ (slots q.1))*volume d.input*(4*d.radius)^(1/6:ℝ)*
          (heightEnvelope d.input.t^(J (slots q.1))*profileMoment (J (slots q.1)))^2*allocationRadical d.input d.C d.D):=by
        exact mul_le_mul_of_nonneg_left hprice (mul_nonneg
          (mul_nonneg (div_nonneg (ha _) (he _).le) (div_pos (f.physical_pos _) hl).le) (hphys _))
      _=_:=by
        dsimp only [firstCost,d,CorrectedFamilyData.datum,exceptionalDatum,familyDatum,
          restrictedRetainedDatum,restrictDatum,modifiedRetainedDatum,modifiedSecondDatum]
        ring!

  apply (Finset.sum_le_sum fun q _=>point q).trans
  rw [Fintype.sum_sigma]
  calc
    _=∑l,(Hmass*Z^(δ+Bdiv*εL)*firstCost f N Q J T C₀ K₀ Cphys ε raw l)*
        ∑q:CompleteBlock (f.input l) (f.modifier l) (f.puncture l) (f.seed l) W
          (f.physicalScale l) (f.sectorScale l) Z f.mesh,
          allocationRadical (f.input l) q.val.1.val.val.1 q.val.1.val.val.2:=by
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.mul_sum]
      rfl
    _≤∑l,(Hmass*Z^(δ+Bdiv*εL)*firstCost f N Q J T C₀ K₀ Cphys ε raw l)*(A*Z^epsMass/(f.seed l).absNorm):=by
      apply Finset.sum_le_sum
      intro l _
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg hH.le (Real.rpow_nonneg hZ.le _))
        (firstCost_nonneg f N Q J T C₀ K₀ Cphys ε raw ha he hK hphys hrad0 l))
      have hslots:Fintype.card (slots l)≤Fintype.card α:=by simpa using Finset.card_le_univ (slots l)
      exact hm (ι:=slots l) (hslots.trans hN)
        (f.input l) (f.zero₁ l) (f.zero₂ l) (hsource l) (f.A₁ l) (f.A₂ l) (f.frozen l) (f.marked l)
        (f.puncture l) (f.seed l) (poolCorrection (f.pool l)) (f.seed_squarefree l) (hseed l) W
        (f.physicalScale l) (f.sectorScale l) f.mesh (f.physical_pos l) (hradius l)
    _=_:=by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      rw [show Z^(epsMass+δ+Bdiv*εL)=Z^epsMass*Z^(δ+Bdiv*εL) by
        rw [←Real.rpow_add hZ];congr 1;ring]
      ring
end
end QRH.Record1252270103Source.Low.SelectedExceptionalRadicalAggregate
#print axioms QRH.Record1252270103Source.Low.SelectedExceptionalRadicalAggregate.eventually_family_payment
