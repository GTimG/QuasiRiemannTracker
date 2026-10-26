/- Copyright (c) 2026 Hailey Collet; additive returned-source assembly (c) 2026 Zhongpai Gao.
Released under Apache 2.0. The native seed reciprocal is preserved. -/
import Candidate.Cycle63.Physical.InitialMass.LowChildAllowancePayment
import Candidate.Cycle63.Physical.InitialMass.LowChildSideExponent
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowFinalPayment
import Candidate.Research.RecursiveAffine.NativeSourceSide
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle153LowPhysical
open Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceLiveColumn CenteredMomentSecondInputCapacitySource
open CenteredMomentCommonPairedSource
open CenteredMomentSecondEnergySplit CenteredMomentSectorLocalization
open Cycle63FinalNatural CenteredMomentEnergyState
open CenteredMomentSecondLiveBlock CenteredMomentSecondCanonical CenteredMomentSourceRow
open CenteredMomentSecondRetainedAggregate CenteredMomentFirstDiscardedEnergy
open CenteredMomentSecondBlockAggregate CenteredMomentSourceMass CenteredMomentRankinRadical
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentCanonicalFirst
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentEligibleEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale
open CenteredMomentCommonLinearNormalization CenteredMomentSourceLiveColumn
open Cycle63Moment CenteredMomentLogDyadic CenteredMomentCommonPairedSource
open CenteredMomentWholeDivisorShell
open Cycle63FinalLow
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle63FinalProfiles
/-- The native supported-label allowance theorem pays the actual weighted old term.
Only the physical first-mass upper bound is assumed; the allowance sum is proved
from supported sources. The first projector reciprocal remains explicit. -/
theorem eventual_actual_old_mass_allowance
    (N : ℕ) (lo εv B ε : ℝ) (hlo : 0< lo) (hev : 0<εv) (hB : 0≤ B) (hε : 0<ε) :
    ∃K₀ : ℝ,0< K₀ ∧
    ∀ᶠZ : ℝ in atTop,2≤ Z ∧ ∀{ι : Type}[Fintype ι]
    (s : Input ι),Fintype.card ι≤ N → lo≤ s.lower →
    ∀{Label : Type}[Fintype Label]
    (reflected second : Bool) (first : Label→FirstSourceLabel),
    (∀l,Supported (first l).1.1 ∧ Supported (first l).1.2) →
    (∀l,primeSupport (first l).1.1=primeSupport (first l).1.2) →
    ∀(Rfirst : Ideal O)
      (alloc : (l : Label)→actualAllocations s.pools
        (if reflected then (first l).1.2 else (first l).1.1))
      (χ : Label→ Character) (t : Label→ℝ),
    (∀l,frozenCoefficient (alloc l).val
      (if reflected then (first l).1.2 else (first l).1.1) Rfirst s.ν s.W s.P≠0) →
    let src := fun l=>child s (if reflected then (first l).1.2 else (first l).1.1)
      Rfirst (alloc l) (χ l) (t l)
    ∀(R seed : Label→ Ideal O)(K Tsec : Label→ℝ)(ξ unit M a reserve error εcommon : ℝ),
    (∀l,Squarefree (seed l)) → (∀l,(src l).W₁ 0=0) → (∀l,(src l).W₂ 0=0) →
    0≤εcommon → (∀l,CenteredMomentOriginalCommonHarmonic.sourceRadius (src l)≤ Z^B) →
    ∀(T p exponent : ℝ),1≤ T → p≤ B →
    ∀seed₀ : Ideal O,Squarefree seed₀ → seed₀≠0 →
    Function.Injective (fun l=>(first l,seed l)) →
    (∀l,seed₀∣(first l).1.1 ∧ seed₀∣(first l).1.2) →
    (∀l,((first l).1.1.absNorm:ℝ)≤ Z^B ∧ ((first l).1.2.absNorm:ℝ)≤ Z^B) →
    (∀l,((commonRadical (first l).1.1 (first l).1.2).absNorm:ℝ)≤ Z^p) →
    (∀l,lowAllowedExponent reflected Z (Real.logb Z (volume s)) (first l)≤ exponent) →
    (∀l,T≤((seed l).absNorm:ℝ) ∧ ((seed l).absNorm:ℝ)<2*T) →
    ∀(rows : Finset ((l : Label)×ActualSecondBlockIndex (src l) (R l) (seed l)
      (K l) (Tsec l) Z ξ))
      (hU : ∀q∈rows,ActualSecondBlockIndex.IsInactive q.2)
      (box : Finset (Fin 4→ℤ)),
    (∀q∈rows,actualSecondDyad (src q.1) (R q.1) (seed q.1)
      (K q.1) (Tsec q.1) Z ξ q.2∈box) →
    let pay := fun (l : Label)(v : FirstSourceLabel)=>
      Z^(-a)*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve (first l)/volume (src l))*
        (normalizer v.1.1 v.1.2 v.2.val*((if second then v.1.2 else v.1.1).absNorm:ℝ)^(εcommon-1))*
        Z^(secondNominal unit Z a (frequencyLoss Z 32 ξ+reserve)
          (if reflected then (first l).1.2 else (first l).1.1)
          (if reflected then (first l).1.1 else (first l).1.2) v.1.1 v.1.2 v.2.val+a+error)*
        Z^(lowAllowance Z (if reflected then (first l).1.2 else (first l).1.1)
          (if reflected then (first l).1.1 else (first l).1.2) v.1.1 v.1.2 (if second then v.1.2 else v.1.1))
    ∀(mass : Label→ℝ)(Cg fixed physical loss : ℝ),
    0≤ Cg → 0≤ fixed → 0≤ physical → (∀l,mass l≤ physical*Z^loss) →
    (∑q : rows,Cg*fixed*(mass q.val.1*Z^a)*pay q.val.1
      (actualSecondSupportedLabel (src q.val.1) (R q.val.1) (seed q.val.1)
        (K q.val.1) (Tsec q.val.1) Z ξ q.val.2 (hU q.val q.property)))≤
      Cg*fixed*physical*(box.card:ℝ)*K₀*
        Z^(loss+a+p+exponent+error+(unit-M)+εv+B*εcommon+ε)/(seed₀.absNorm:ℝ) := by
  obtain ⟨K₀,hK₀,hpaid⟩ := eventual_selected_low_allowance_paid N lo εv B ε hlo hev hB hε
  refine ⟨K₀,hK₀,?_⟩
  filter_upwards [hpaid] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι _ s hn hs Label _ reflected second first hfirst heq Rfirst alloc χ t halloc
    src R seed K Tsec ξ unit M a reserve error εcommon hseed hw₁ hw₂ hecommon hsource
    T p exponent hT hp seed₀ hs₀ hs₀0 hinj hfirstseed hfirstnorm hrad hgeom hdyad
    rows hU box hbox pay mass Cg fixed physical loss hCg hfixed hphysical hmass
  have hZ : 0< Z := by linarith only [hz.1]
  have hpays := hz.2 s hn hs reflected second first hfirst heq Rfirst alloc χ t halloc
    R seed K Tsec ξ unit M a reserve error εcommon hseed hw₁ hw₂ hecommon hsource
    T p exponent hT hp seed₀ hs₀ hs₀0 hinj hfirstseed hfirstnorm hrad hgeom hdyad
    rows hU box hbox
  let label := fun q : rows=>actualSecondSupportedLabel (src q.val.1) (R q.val.1) (seed q.val.1)
    (K q.val.1) (Tsec q.val.1) Z ξ q.val.2 (hU q.val q.property)
  have hlabel (q : rows) : label q∈actualSecondLabels (src q.val.1) (R q.val.1) (seed q.val.1) :=
    actual_second_supported_label_mem _ _ _ _ _ _ _ _ _
  have hpay (q : rows) : 0≤ pay q.val.1 (label q) := by
    have hg:=actual_second_labels_gates (src q.val.1) (R q.val.1) (seed q.val.1)
      (hseed q.val.1) (hw₁ q.val.1) (hw₂ q.val.1) (label q) (hlabel q)
    dsimp only [pay]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hZ.le _)
      (div_nonneg (first_main_radius_pos _ _ _ _ _ _ _ hZ _).le
        (CenteredMomentAmplificationChildInput.volume_pos _).le))
      (mul_nonneg (normalizer_pos _ _ hg.1 _).le (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
      (Real.rpow_nonneg hZ.le _)) (Real.rpow_nonneg hZ.le _)
  have hbound : (∑q : rows,Cg*fixed*(mass q.val.1*Z^a)*pay q.val.1 (label q)) ≤
      Cg*fixed*(physical*Z^(loss+a))*((box.card:ℝ)*(K₀*
        Z^(p+exponent+error+(unit-M)+εv+B*εcommon+ε)/(seed₀.absNorm:ℝ))) := by
    calc
      _ ≤ ∑q : rows,Cg*fixed*(physical*Z^(loss+a))*pay q.val.1 (label q) := by
        refine Finset.sum_le_sum fun q _=>?_
        apply mul_le_mul_of_nonneg_right _ (hpay q)
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCg hfixed)
        simpa only [Real.rpow_add hZ,mul_assoc] using
          mul_le_mul_of_nonneg_right (hmass q.val.1) (Real.rpow_nonneg hZ.le a)
      _ = Cg*fixed*(physical*Z^(loss+a))*∑q : rows,pay q.val.1 (label q) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hpays
        (mul_nonneg (mul_nonneg hCg hfixed) (mul_nonneg hphysical (Real.rpow_nonneg hZ.le _)))
  apply hbound.trans_eq
  have hpow : Z^(loss+a+p+exponent+error+(unit-M)+εv+B*εcommon+ε)=
      Z^(loss+a)*Z^(p+exponent+error+(unit-M)+εv+B*εcommon+ε) := by
    rw [show loss+a+p+exponent+error+(unit-M)+εv+B*εcommon+ε=
      (loss+a)+(p+exponent+error+(unit-M)+εv+B*εcommon+ε) by ring,Real.rpow_add hZ]
  rw [hpow]
  ring

end
end OAI.SevenEighths.Cycle153LowPhysical
#print axioms OAI.SevenEighths.Cycle153LowPhysical.eventual_actual_old_mass_allowance
