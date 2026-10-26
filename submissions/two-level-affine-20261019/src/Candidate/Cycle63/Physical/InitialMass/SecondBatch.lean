import Candidate.Cycle63.Physical.InitialMass.SecondBlock

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondSectorColumns CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondCanonicalScalar CenteredMomentSmooth CenteredMomentCauchy
open CenteredMomentLogDyadic CenteredMomentHeckeColumnWindow CenteredMomentSourceRow
open Cycle63Moment RayFourExpansion
local notation "O" => HeckeFamily.O

abbrev SecondBlockSource.LeftIndex (s : SecondBlockSource) := sectorPool s.C s.hC.1 s.pool
abbrev SecondBlockSource.RightIndex (s : SecondBlockSource) := sectorPool s.D s.hD.1 s.pool
abbrev SecondSector {Label : Type*} (s : Label→SecondBlockSource) :=
  (l : Label) × (_L : ↥(s l).divisors) × RayCharacter × RayCharacter × ↥(s l).rows

def SecondBlockSource.outside (s : SecondBlockSource) : ℝ :=
  outerScalar s.C s.D s.K s.dyad*normalizer s.C s.D s.inactive
def SecondBlockSource.value (s : SecondBlockSource) (W : 𝓢(ℝ,ℂ)) : ℂ :=
  physicalBlock s.character s.height s.pool s.beta s.C s.D s.hC s.hD s.inactive
    s.radius s.rows W s.K s.dyad
def secondJointSource {Label : Type*} (s : Label→SecondBlockSource) (q : SecondSector s) :=
  (s q.1).sector q.2.1.val q.2.2.1 q.2.2.2.1
def secondJointWeight {Label : Type*} (s : Label→SecondBlockSource) (q : SecondSector s) : ℂ :=
  (secondJointSource s q).signedWeight ((s q.1).rowWeight q.2.2.2.2.val)
def secondJointLeft {Label : Type*} (s : Label→SecondBlockSource) (w : Label→ℂ)
    (q : SecondSector s) (i : (s q.1).LeftIndex) : ℂ :=
  w q.1*(s q.1).outside*(secondJointSource s q).leftCoefficient i*idealRowHom q.2.2.2.2.val i
def secondJointRight {Label : Type*} (s : Label→SecondBlockSource)
    (q : SecondSector s) (i : (s q.1).RightIndex) : ℂ :=
  (secondJointSource s q).rightCoefficient i*idealRowHom (-q.2.2.2.2.val) i
def secondLeftLog (s : SecondBlockSource) (i : s.LeftIndex) :=
  Real.log ((i.val.absNorm:ℝ)/CenteredMomentSectorLocalization.dyadicScale (s.dyad 2))
def secondRightLog (s : SecondBlockSource) (i : s.RightIndex) :=
  Real.log ((i.val.absNorm:ℝ)/CenteredMomentSectorLocalization.dyadicScale (s.dyad 3))

/-- The literal weighted physical blocks expand over one joint coordinate,
with no supremum or independent charge for their original source labels. -/
theorem actual_second_batch_expression {Label : Type*} [Fintype Label]
    (s : Label→SecondBlockSource) (w : Label→ℂ) (W : 𝓢(ℝ,ℂ)) :
    (∑l,w l*(s l).value W)=
      ∑q : SecondSector s,secondJointWeight s q*
        ∑i : (s q.1).LeftIndex,∑j : (s q.1).RightIndex,
          (secondJointLeft s w q i*star (secondJointRight s q j))*
            wholeKernel W (fun _=>logAnnulus) (s q.1).ratio (s q.1).rho
              ((s q.1).x q.2.2.2.2.val) (secondLeftLog (s q.1) i) (secondRightLog (s q.1) j) := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [SecondBlockSource.value,actual_second_physical_block_expression]
  simp only [Fintype.sum_sigma,Fintype.sum_prod_type,Finset.mul_sum]
  rw [←Finset.sum_coe_sort]
  refine Finset.sum_congr rfl fun L hL => Finset.sum_congr rfl fun χ hχ => Finset.sum_congr rfl fun ψ hψ => ?_
  rw [←Finset.sum_coe_sort]
  refine Finset.sum_congr rfl fun z hz => ?_
  simp only [secondSectorTerm,Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  simp only [secondJointWeight,secondJointLeft,secondJointRight,secondJointSource,
    SecondBlockSource.outside,Complex.ofReal_mul,secondLeftLog,secondRightLog,
    CanonicalSectorSource.leftLog,CanonicalSectorSource.rightLog,SecondBlockSource.sector]
  ring

def secondActiveSectors {Label : Type*} [Fintype Label]
    (s : Label→SecondBlockSource) : Finset (SecondSector s) :=
  Finset.univ.filter (fun q=>logAnnulus (s q.1).rho≠0 ∧
    logAnnulus ((s q.1).x q.2.2.2.2.val)≠0 ∧ Squarefree q.2.1.val ∧
    (s q.1).rowWeight q.2.2.2.2.val≠0)

theorem actual_second_batch_active_expression {Label : Type*} [Fintype Label]
    (s : Label→SecondBlockSource) (w : Label→ℂ) (W : 𝓢(ℝ,ℂ)) :
    (∑l,w l*(s l).value W)=
      ∑q∈secondActiveSectors s,secondJointWeight s q*
        ∑i : (s q.1).LeftIndex,∑j : (s q.1).RightIndex,
          (secondJointLeft s w q i*star (secondJointRight s q j))*
            wholeKernel W (fun _=>logAnnulus) (s q.1).ratio (s q.1).rho
              ((s q.1).x q.2.2.2.2.val) (secondLeftLog (s q.1) i) (secondRightLog (s q.1) j) := by
  rw [actual_second_batch_expression,secondActiveSectors,Finset.sum_filter]
  refine Finset.sum_congr rfl fun q hq => ?_
  by_cases h₀ : logAnnulus (s q.1).rho=0
  · simp [h₀,wholeKernel]
  · by_cases h₁ : logAnnulus ((s q.1).x q.2.2.2.2.val)=0
    · simp [h₁,wholeKernel]
    · by_cases hL : Squarefree q.2.1.val
      · by_cases hw : (s q.1).rowWeight q.2.2.2.2.val=0
        · simp [hw,secondJointWeight,CanonicalSectorSource.signedWeight]
        · simp [h₀,h₁,hL,hw]
      · simp [h₀,h₁,hL,secondJointWeight,secondJointSource,SecondBlockSource.sector,
          CanonicalSectorSource.signedWeight]

end
end OAI.SevenEighths.Cycle63InitialMass
