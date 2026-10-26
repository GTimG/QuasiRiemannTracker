import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.SecondExtraction
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.SecondCorrelatedFamily

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondExceptionalFamily
open CenteredMomentCanonicalFirst CenteredMomentCauchy CenteredMomentSectorLocalization
open CenteredMomentLogDyadic Cycle61Moment RayFourExpansion
local notation "O" => HeckeFamily.O
local instance secondFamilyDecidableSum {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- Original source and literal second-block parameters, including the
actual fixed-character family used for its two columns. -/
structure SecondInputDatum (α : Type*) [Fintype α] [DecidableEq α] where
  slots : Finset α
  input : Input slots
  R : Ideal O
  seed : Ideal O
  C : Ideal O
  D : Ideal O
  hC : Supported C
  hD : Supported D
  sameSupport : primeSupport C=primeSupport D
  inactive : Finset (CommonIndex C D)
  radius : ℝ
  rows : Finset O
  rows_ne : ∀z∈rows,z≠0
  K : ℝ
  K_pos : 0<K
  dyad : Fin 4→ℤ
  τ : RayCharacter→Character
  family : Family input.η C D hC hD inactive τ
  rowBudget : SecondRowConductorBudget input.η C D hC hD inactive τ

variable {α : Type*} [Fintype α] [DecidableEq α]

def SecondInputDatum.block (d : SecondInputDatum α) : SecondBlockSource :=
  originalSecondBlock d.input d.R d.seed d.C d.D d.hC d.hD d.sameSupport
    d.inactive d.radius d.rows d.rows_ne d.K d.K_pos d.dyad

def secondFamilyLeftScalar {Label : Type*} (d : Label→SecondInputDatum α) (w : Label→ℂ)
    (q : SecondSector (fun l=>(d l).block)) : ℂ :=
  w q.1*(d q.1).block.outside*(Real.sqrt (volume (d q.1).input.toData):ℂ)
def secondFamilyRightScalar {Label : Type*} (d : Label→SecondInputDatum α)
    (q : SecondSector (fun l=>(d l).block)) : ℂ :=
  Real.sqrt (volume (d q.1).input.toData)

theorem actual_second_family_left_column {Label : Type*}
    (d : Label→SecondInputDatum α) (w : Label→ℂ)
    (q : SecondSector (fun l=>(d l).block)) (t : ℝ) :
    leftColumn Finset.univ (secondJointLeft (fun l=>(d l).block) w q)
      logAnnulus (secondLeftLog (d q.1).block) t=
    secondFamilyLeftScalar d w q*windowColumn (d q.1).input (d q.1).C (d q.1).hC
      (d q.1).R (d q.1).seed q.2.1.val ((d q.1).τ q.2.2.1) (d q.1).input.t t
      (dyadicScale ((d q.1).dyad 2)) logAnnulus q.2.2.2.2.val := by
  let v := d q.1
  have he := actual_original_second_left_window v.input v.R v.seed v.C v.D v.hC v.hD
    v.sameSupport v.inactive v.radius v.rows v.rows_ne v.K v.K_pos v.dyad
    q.2.1.val q.2.2.1 q.2.2.2.1 v.τ v.family q.2.2.2.2.val t logAnnulus
  have hS : (Real.sqrt (volume v.input.toData):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (volume_pos v.input.toData)).ne'
  have he' := congrArg (fun z : ℂ=>(Real.sqrt (volume v.input.toData):ℂ)*z) he
  simp only [←mul_assoc,mul_inv_cancel₀ hS,one_mul] at he'
  unfold secondFamilyLeftScalar
  rw [mul_assoc,←he']
  simp only [leftColumn,secondJointLeft,Finset.mul_sum,secondLeftLog,
    CanonicalSectorSource.leftLog,SecondBlockSource.sector,secondJointSource]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [v,SecondInputDatum.block,originalSecondBlock]
  ring

theorem actual_second_family_right_column {Label : Type*}
    (d : Label→SecondInputDatum α) (q : SecondSector (fun l=>(d l).block)) (t : ℝ) :
    rightColumn Finset.univ (secondJointRight (fun l=>(d l).block) q)
      logAnnulus (secondRightLog (d q.1).block) t=
    secondFamilyRightScalar d q*star (windowColumn (d q.1).input (d q.1).D (d q.1).hD
      (d q.1).R (d q.1).seed q.2.1.val ((d q.1).τ q.2.2.2.1⁻¹) (d q.1).input.t (-t)
      (dyadicScale ((d q.1).dyad 3)) (fun x=>star (logAnnulus x)) (-q.2.2.2.2.val)) := by
  let v := d q.1
  have he := actual_original_second_right_window v.input v.R v.seed v.C v.D v.hC v.hD
    v.sameSupport v.inactive v.radius v.rows v.rows_ne v.K v.K_pos v.dyad
    q.2.1.val q.2.2.1 q.2.2.2.1 v.τ v.family q.2.2.2.2.val t logAnnulus
  have hS : (Real.sqrt (volume v.input.toData):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (volume_pos v.input.toData)).ne'
  have he' := congrArg (fun z : ℂ=>(Real.sqrt (volume v.input.toData):ℂ)*z) he
  simp only [←mul_assoc,mul_inv_cancel₀ hS,one_mul] at he'
  dsimp only [secondJointRight,secondJointSource,secondFamilyRightScalar,secondRightLog,
    SecondInputDatum.block,originalSecondBlock,SecondBlockSource.sector]
  dsimp only [v,CanonicalSectorSource.rightLog,originalSecondBlock,SecondBlockSource.sector] at he'
  exact he'

theorem actual_second_family_energy {Label : Type*} [Fintype Label]
    (d : Label→SecondInputDatum α) (w : Label→ℂ) (t : ℝ) :
    secondActiveEnergyPair (fun l=>(d l).block) w t=
    Real.sqrt (∑q∈secondActiveSectors (fun l=>(d l).block),
      ‖secondFamilyLeftScalar d w q*windowColumn (d q.1).input (d q.1).C (d q.1).hC
        (d q.1).R (d q.1).seed q.2.1.val ((d q.1).τ q.2.2.1) (d q.1).input.t t
        (dyadicScale ((d q.1).dyad 2)) logAnnulus q.2.2.2.2.val‖^2)*
    Real.sqrt (∑q∈secondActiveSectors (fun l=>(d l).block),
      ‖secondFamilyRightScalar d q*windowColumn (d q.1).input (d q.1).D (d q.1).hD
        (d q.1).R (d q.1).seed q.2.1.val ((d q.1).τ q.2.2.2.1⁻¹) (d q.1).input.t (-t)
        (dyadicScale ((d q.1).dyad 3)) (fun x=>star (logAnnulus x)) (-q.2.2.2.2.val)‖^2) := by
  unfold secondActiveEnergyPair
  simp_rw [actual_second_family_left_column,actual_second_family_right_column,norm_mul,norm_star]

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_family_left_column
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_family_right_column
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_family_energy
