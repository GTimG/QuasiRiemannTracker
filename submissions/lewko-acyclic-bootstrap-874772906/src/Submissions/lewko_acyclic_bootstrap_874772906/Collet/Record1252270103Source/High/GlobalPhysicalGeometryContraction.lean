/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual modified first geometry payment, adapted from pinned Cycle61. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.LocalizedFirst
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalGeometryPayment
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.GeometryContraction

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CoupledFirst
open OAI OAI.SevenEighths Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT ActualEisensteinCubic
open CenteredMomentFirstPhysicalSource CenteredMomentFirstChildBound
open CenteredMomentFirstColumns CenteredMomentFirstAssembly CenteredMomentGaussEnergy
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentSmooth
open CenteredMomentCommonSupport CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstReduced CenteredMomentCommonRadialData
open CenteredMomentFirstReferenceSource CenteredMomentFirstSourceReduction
open CenteredMomentSecondRetainedRows CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentHeckeColumnWindow FourierBridge Cycle61Moment RayFourExpansion CenteredMomentPrimitive CenteredMomentScale
local notation "O" => HeckeFamily.O

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def geometryFirstSource (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K)
    (r : ℤ×(Fin 5→ℤ)) (q : CommonGeometryFiber s modifier R seed K Z ξ r) :=
  originalFirstBlock s modifier R seed K Z ξ hK q.val

def geometryFirstPhase (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O) (W : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ)
    (r : ℤ×(Fin 5→ℤ)) (q : CommonGeometryFiber s modifier R seed K Z ξ r) :=
  normPhase (coordinateBlock s modifier R seed W K Z ξ q.val)

/-- Actual physical mass is contracted over each actual common geometry and ratio group, with
all first labels inside the matched column energy. -/
theorem actual_physical_mass_geometry_contraction (W : 𝓢(ℝ,ℂ)) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K)
      (E : ℤ×(Fin 5→ℤ) → ℝ), (∀r∈commonGeometryBins s modifier R seed K Z ξ, 0≤E r) →
      (∀r∈commonGeometryBins s modifier R seed K Z ξ, ∀t : ℝ,
        firstActiveEnergyPair (geometryFirstSource s modifier R seed K Z ξ hK r)
          (geometryFirstPhase s modifier R seed W K Z ξ r) (fun _ => logAnnulus) t ≤
          E r*(1+‖t‖)^J) →
      physicalMass s modifier R seed (CenteredMomentSecondHeightFamily.fixedBadMask*
        ConcretePrimeRowBridge.idealGenerator R) 1 W K Z ξ ≤
        C*∑r∈commonGeometryBins s modifier R seed K Z ξ, E r/(1+dyadicScale r.1)^A := by
  obtain ⟨C,hC,hbound⟩ := actual_first_active_contraction W (fun _ => logAnnulus)
    (fun _ => Real.log 4) (fun _ => Real.log_nonneg (by norm_num))
    (fun _ _ hn => CenteredMomentSecondIdealBlockBound.logAnnulus_enclosure _ hn) A J
  refine ⟨C,hC,?_⟩
  intro s modifier R seed K Z ξ hK E hE he
  rw [actual_physical_mass_geometry_groups,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  have hh := hbound (geometryFirstSource s modifier R seed K Z ξ hK r)
    (geometryFirstPhase s modifier R seed W K Z ξ r) (dyadicScale r.1) (dyadicScale_pos r.1)
    (fun q => actual_source_ratio_fiber s modifier R seed K Z ξ r.1
      ⟨q.val,commonGeometryFiber_ratio s modifier R seed K Z ξ r q⟩)
    (fun q => logAnnulus_norm _) (fun q => logAnnulus_norm _) (E r) (hE r hr) (he r hr)
  have hp : 0<(1+dyadicScale r.1)^A := pow_pos (by linarith [dyadicScale_pos r.1]) _
  rw [←mul_div_assoc]
  apply (le_div_iff₀ hp).mpr
  have hv (q : CommonGeometryFiber s modifier R seed K Z ξ r) :
      (geometryFirstSource s modifier R seed K Z ξ hK r q).value W (fun _ => logAnnulus) =
        coordinateBlock s modifier R seed W K Z ξ q.val := rfl
  simpa only [geometryFirstPhase,hv,mul_comm] using hh



/-- Literal normalized left energy: the original phase and outside scalar
are inside the square, and only the proven geometric power is divided out. -/
def geometryLeftEnergy (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ M A : ℝ) (hK : 0<K)
    (key : ℤ×(Fin 5→ℤ)) (weight : CommonGeometryFiber s modifier R seed K Z ξ key→ℂ)
    (V : Fin 4→ℝ→ℂ) (t : ℝ) : ℝ :=
  ∑q∈firstActiveSectors (geometryFirstSource s modifier R seed K Z ξ hK key) V,
    ‖CenteredMomentCauchy.leftColumn Finset.univ
      (firstJointLeft (geometryFirstSource s modifier R seed K Z ξ hK key) weight q)
      (V 2) (firstLeftLog (geometryFirstSource s modifier R seed K Z ξ hK key q.1)) t‖^2/
      Z^(2*outsideExponent M A (geometryExponents s modifier R seed K Z ξ q.1.val)+
        leftExponent A (geometryExponents s modifier R seed K Z ξ q.1.val))

def geometryRightEnergy (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ A : ℝ) (hK : 0<K)
    (key : ℤ×(Fin 5→ℤ)) (V : Fin 4→ℝ→ℂ) (t : ℝ) : ℝ :=
  ∑q∈firstActiveSectors (geometryFirstSource s modifier R seed K Z ξ hK key) V,
    ‖CenteredMomentCauchy.rightColumn Finset.univ
      (firstJointRight (geometryFirstSource s modifier R seed K Z ξ hK key) q)
      (V 3) (firstRightLog (geometryFirstSource s modifier R seed K Z ξ hK key q.1)) t‖^2/
      Z^(rightExponent A (geometryExponents s modifier R seed K Z ξ q.1.val))

omit [DecidableEq ι] in
/-- Applies the cross-label payment to the actual joint first-sector energy.
All divisor, ray and frequency indices remain in the two normalized sums. -/
theorem actual_first_energy_geometry_payment (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O)
    (K Z ξ B M A : ℝ) (hK : 0<K) (hZ : 1<Z) (hs : Squarefree seed)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hsource : CenteredMomentOriginalCommonHarmonic.sourceRadius s≤Z^B)
    (key : ℤ×(Fin 5→ℤ)) (weight : CommonGeometryFiber s modifier R seed K Z ξ key→ℂ)
    (V : Fin 4→ℝ→ℂ) (t : ℝ) :
    firstActiveEnergyPair (geometryFirstSource s modifier R seed K Z ξ hK key) weight V t ≤
      32*Z^M*Real.sqrt (geometryLeftEnergy s modifier R seed K Z ξ M A hK key weight V t)*
        Real.sqrt (geometryRightEnergy s modifier R seed K Z ξ A hK key V t) := by
  let src := geometryFirstSource s modifier R seed K Z ξ hK key
  let L : FirstSector src→ℝ := fun q=>
    ‖CenteredMomentCauchy.leftColumn Finset.univ (firstJointLeft src weight q)
      (V 2) (firstLeftLog (src q.1)) t‖^2/
      Z^(2*outsideExponent M A (geometryExponents s modifier R seed K Z ξ q.1.val)+
        leftExponent A (geometryExponents s modifier R seed K Z ξ q.1.val))
  let N : FirstSector src→ℝ := fun q=>
    ‖CenteredMomentCauchy.rightColumn Finset.univ (firstJointRight src q)
      (V 3) (firstRightLog (src q.1)) t‖^2/
      Z^(rightExponent A (geometryExponents s modifier R seed K Z ξ q.1.val))
  have hz : 0<Z := zero_lt_one.trans hZ
  let p (q : FirstSector src) := Z^(2*outsideExponent M A
    (geometryExponents s modifier R seed K Z ξ q.1.val)+
      leftExponent A (geometryExponents s modifier R seed K Z ξ q.1.val))
  let r (q : FirstSector src) := Z^(rightExponent A (geometryExponents s modifier R seed K Z ξ q.1.val))
  have hpair (q u : FirstSector src) : p q*r u≤(32*Z^M)^2 := by
    have hh := actual_geometry_cross_payment s modifier R seed K Z ξ B M A hZ hs hz₁ hz₂ hsource key q.1 u.1
    have hp := pow_le_pow_left₀ (by positivity) hh 2
    rw [mul_pow,mul_pow,Real.sq_sqrt (Real.rpow_nonneg hz.le _),
      Real.sq_sqrt (Real.rpow_nonneg hz.le _),←Real.rpow_mul_natCast hz.le,
      ←Real.rpow_add hz] at hp
    convert hp using 1
    dsimp [p,r]
    congr 2
    ring
  have hh := weighted_joint_energy_finset (firstActiveSectors src V) (firstActiveSectors src V)
    p L r N (32*Z^M) (fun _=>Real.rpow_nonneg hz.le _)
    (fun _=>Real.rpow_nonneg hz.le _) (fun _=>by dsimp [L];positivity)
    (fun _=>by dsimp [N];positivity) (by positivity) hpair
  simpa only [p,r,L,N,mul_div_cancel₀ _ (Real.rpow_pos_of_pos hz _).ne',
    firstActiveEnergyPair,geometryLeftEnergy,geometryRightEnergy,src] using hh


end
end QRH.Record1252270103Source.High.CoupledFirst
#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_physical_mass_geometry_contraction

#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_first_energy_geometry_payment
