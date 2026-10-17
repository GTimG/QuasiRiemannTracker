import Candidate.Cycle63.Physical.InitialMass.GeometryContraction
import Candidate.Target830.Source.BalancedPayment

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Target830.Source
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
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentHeckeColumnWindow FourierBridge Cycle63Moment RayFourExpansion CenteredMomentPrimitive CenteredMomentScale
local notation "O" => HeckeFamily.O

open Cycle63InitialMass

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Literal normalized left energy: the original phase and outside scalar
are inside the square, and only the proven geometric power is divided out. -/
def balancedLeftEnergy (s : Input ι) (R seed : Ideal O) (K Z ξ M A : ℝ) (hK : 0<K)
    (key : ℤ×(Fin 5→ℤ)) (weight : CommonGeometryFiber s R seed K Z ξ key→ℂ)
    (V : Fin 4→ℝ→ℂ) (t : ℝ) : ℝ :=
  ∑q∈firstActiveSectors (geometryFirstSource s R seed K Z ξ hK key) V,
    ‖CenteredMomentCauchy.leftColumn Finset.univ
      (firstJointLeft (geometryFirstSource s R seed K Z ξ hK key) weight q)
      (V 2) (firstLeftLog (geometryFirstSource s R seed K Z ξ hK key q.1)) t‖^2/
      Z^(2*outsideExponent M A (geometryExponents s R seed K Z ξ q.1.val)+
        balancedLeft A (geometryExponents s R seed K Z ξ q.1.val))

def balancedRightEnergy (s : Input ι) (R seed : Ideal O) (K Z ξ A : ℝ) (hK : 0<K)
    (key : ℤ×(Fin 5→ℤ)) (V : Fin 4→ℝ→ℂ) (t : ℝ) : ℝ :=
  ∑q∈firstActiveSectors (geometryFirstSource s R seed K Z ξ hK key) V,
    ‖CenteredMomentCauchy.rightColumn Finset.univ
      (firstJointRight (geometryFirstSource s R seed K Z ξ hK key) q)
      (V 3) (firstRightLog (geometryFirstSource s R seed K Z ξ hK key q.1)) t‖^2/
      Z^(balancedRight A (geometryExponents s R seed K Z ξ q.1.val))

omit [DecidableEq ι] in
/-- Applies the cross-label payment to the actual joint first-sector energy.
All divisor, ray and frequency indices remain in the two normalized sums. -/
theorem actual_first_energy_balanced_payment (s : Input ι) (R seed : Ideal O)
    (K Z ξ B M A : ℝ) (hK : 0<K) (hZ : 1<Z) (hs : Squarefree seed)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hsource : CenteredMomentOriginalCommonHarmonic.sourceRadius s≤Z^B)
    (key : ℤ×(Fin 5→ℤ)) (weight : CommonGeometryFiber s R seed K Z ξ key→ℂ)
    (V : Fin 4→ℝ→ℂ) (t : ℝ) :
    firstActiveEnergyPair (geometryFirstSource s R seed K Z ξ hK key) weight V t ≤
      4*Z^M*Real.sqrt (balancedLeftEnergy s R seed K Z ξ M A hK key weight V t)*
        Real.sqrt (balancedRightEnergy s R seed K Z ξ A hK key V t) := by
  let src := geometryFirstSource s R seed K Z ξ hK key
  let L : FirstSector src→ℝ := fun q=>
    ‖CenteredMomentCauchy.leftColumn Finset.univ (firstJointLeft src weight q)
      (V 2) (firstLeftLog (src q.1)) t‖^2/
      Z^(2*outsideExponent M A (geometryExponents s R seed K Z ξ q.1.val)+
        balancedLeft A (geometryExponents s R seed K Z ξ q.1.val))
  let N : FirstSector src→ℝ := fun q=>
    ‖CenteredMomentCauchy.rightColumn Finset.univ (firstJointRight src q)
      (V 3) (firstRightLog (src q.1)) t‖^2/
      Z^(balancedRight A (geometryExponents s R seed K Z ξ q.1.val))
  have hz : 0<Z := zero_lt_one.trans hZ
  let p (q : FirstSector src) := Z^(2*outsideExponent M A
    (geometryExponents s R seed K Z ξ q.1.val)+
      balancedLeft A (geometryExponents s R seed K Z ξ q.1.val))
  let r (q : FirstSector src) := Z^(balancedRight A (geometryExponents s R seed K Z ξ q.1.val))
  have hpair (q u : FirstSector src) : p q*r u≤(4*Z^M)^2 := by
    have hh := actual_balanced_cross_payment s R seed K Z ξ B M A hZ hs hz₁ hz₂ hsource key q.1 u.1
    have hp := pow_le_pow_left₀ (by positivity) hh 2
    rw [mul_pow,mul_pow,Real.sq_sqrt (Real.rpow_nonneg hz.le _),
      Real.sq_sqrt (Real.rpow_nonneg hz.le _),←Real.rpow_mul_natCast hz.le,
      ←Real.rpow_add hz] at hp
    convert hp using 1
    dsimp [p,r]
    congr 2
    ring
  have hh := weighted_joint_energy_finset (firstActiveSectors src V) (firstActiveSectors src V)
    p L r N (4*Z^M) (fun _=>Real.rpow_nonneg hz.le _)
    (fun _=>Real.rpow_nonneg hz.le _) (fun _=>by dsimp [L];positivity)
    (fun _=>by dsimp [N];positivity) (by positivity) hpair
  simpa only [p,r,L,N,mul_div_cancel₀ _ (Real.rpow_pos_of_pos hz _).ne',
    firstActiveEnergyPair,balancedLeftEnergy,balancedRightEnergy,src] using hh


end
end OAI.SevenEighths.Target830.Source
#print axioms OAI.SevenEighths.Target830.Source.actual_first_energy_balanced_payment
