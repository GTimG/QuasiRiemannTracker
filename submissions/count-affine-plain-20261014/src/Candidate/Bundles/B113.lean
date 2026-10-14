/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B091
import Candidate.Bundles.B110
import Candidate.Bundles.B111
import Candidate.Bundles.B112
import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamily

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondInput; sha256 5dff614f6ebf0a14598d59f518918acbeb88bf78da6d3b2cb071a3cfea542218 -/
section
                                                 
                                               
                                                                  

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentCommonWindowColumn CenteredMomentExceptionalAmplitudePair
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst
open CenteredMomentHeckeColumnWindow CenteredMomentCauchy CenteredMomentSectorLocalization
open Cycle61Moment RayFourExpansion
local notation "O" => HeckeFamily.O
local instance secondInputDecidableSum {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The second block of the literal finite source polynomial. -/
def originalSecondBlock (s : Input ι) (R seed : Ideal O)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D))
    (radius : ℝ) (rows : Finset O) (hrows : ∀z∈rows,z≠0)
    (K : ℝ) (hK : 0< K) (n : Fin 4→ℤ) : SecondBlockSource where
  character := s.η
  height := s.t
  pool := finiteColumns (Fintype.piFinset s.pools)
  beta := finiteColumnCoefficient (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
  C := C
  D := D
  hC := hC
  hD := hD
  sameSupport := hCD
  inactive := U
  radius := radius
  rows := rows
  rows_ne := hrows
  K := K
  K_pos := hK
  dyad := n

omit [DecidableEq ι] in
theorem actual_original_second_sector (s : Input ι) (R seed : Ideal O)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D))
    (radius : ℝ) (rows : Finset O) (hrows : ∀z∈rows,z≠0)
    (K : ℝ) (hK : 0< K) (n : Fin 4→ℤ) (L : Ideal O) (χ ψ : RayCharacter) :
    let B := originalSecondBlock s R seed C D hC hD hCD U radius rows hrows K hK n
    B.sector L χ ψ=originalSecondSector s R seed s.η s.t B.frequency C D hC hD hCD
      L χ ψ (dyadicScale (n 2)) (dyadicScale (n 3)) := rfl

omit [DecidableEq ι] in
theorem actual_original_second_left_window (s : Input ι) (R seed : Ideal O)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D))
    (radius : ℝ) (rows : Finset O) (hrows : ∀z∈rows,z≠0)
    (K : ℝ) (hK : 0< K) (n : Fin 4→ℤ) (L : Ideal O) (χ ψ : RayCharacter)
    (τ : RayCharacter→ Character) (hτ : Family s.η C D hC hD U τ)
    (z : O) (θ : ℝ) (V : ℝ→ℂ) :
    let B := originalSecondBlock s R seed C D hC hD hCD U radius rows hrows K hK n
    let src := B.sector L χ ψ
    (Real.sqrt (volume s.toData):ℂ)⁻¹*
      leftColumn Finset.univ (fun I=>src.leftCoefficient I*idealRowHom z I) V src.leftLog θ=
        windowColumn s C hC R seed L (τ χ) s.t θ (dyadicScale (n 2)) V z := by
  exact actual_second_left_window s R seed s.η (τ χ) s.t θ
    (dyadicScale (n 2)) (dyadicScale (n 3)) _ z C D hC hD hCD L χ ψ V
    (fun I hI hc v=>hτ.height_eq χ I hI (Or.inl hc) v)

omit [DecidableEq ι] in
theorem actual_original_second_right_window (s : Input ι) (R seed : Ideal O)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D))
    (radius : ℝ) (rows : Finset O) (hrows : ∀z∈rows,z≠0)
    (K : ℝ) (hK : 0< K) (n : Fin 4→ℤ) (L : Ideal O) (χ ψ : RayCharacter)
    (τ : RayCharacter→ Character) (hτ : Family s.η C D hC hD U τ)
    (z : O) (θ : ℝ) (V : ℝ→ℂ) :
    let B := originalSecondBlock s R seed C D hC hD hCD U radius rows hrows K hK n
    let src := B.sector L χ ψ
    (Real.sqrt (volume s.toData):ℂ)⁻¹*
      rightColumn Finset.univ (fun I=>src.rightCoefficient I*idealRowHom (-z) I) V src.rightLog θ=
        star (windowColumn s D hD R seed L (τ ψ⁻¹) s.t (-θ) (dyadicScale (n 3))
          (fun x=>star (V x)) (-z)) := by
  exact actual_second_right_window s R seed s.η (τ ψ⁻¹) s.t θ
    (dyadicScale (n 2)) (dyadicScale (n 3)) _ z C D hC hD hCD L χ ψ V
    (fun I hI hc v=>hτ.height_eq ψ⁻¹ I hI (Or.inr hc) v)

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_original_second_sector
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_original_second_left_window
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_original_second_right_window

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondInput -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondExtraction; sha256 1cf8acd84c9ba2bb48b52fea44029cb41d6dd272a32622f1c2147e81537a4083 -/
section
                                               
                                           

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonPairedSource Cycle61Moment
open CenteredMomentCommonWindowColumn CenteredMomentCommonHeightEnvelope
open CenteredMomentHeckeColumnWindow
local notation "O" => HeckeFamily.O
local instance secondExtractionDecidableSum {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- One extraction constant for every surviving subset of the original
finite slot dictionary, chosen before all moving source data. -/
theorem actual_uniform_second_column_extraction {α : Type*} [Fintype α] [DecidableEq α]
    (ε : ℝ) (hε : 0<ε) :
    ∃K : ℝ,0< K ∧ ∀ S : Finset α,∀s : Input S,∀C : Ideal O,∀hC : Supported C,
      ∀R seed L : Ideal O,seed∣C → Squarefree L → ∀z : O,
      ‖normalizedColumn s C hC R seed L z‖^2≤
        K*(L.absNorm:ℝ)^ε*commonRetainedCost s C R L z := by
  have he (S : Finset α) := actual_common_column_extraction (ι:=S) ε hε
  choose K hK hb using he
  let Ksum := 1+∑S : Finset α,K S
  have hs : 0≤∑S : Finset α,K S := Finset.sum_nonneg (fun S _=>(hK S).le)
  refine ⟨Ksum,by dsimp [Ksum]; linarith,?_⟩
  intro S s C hC R seed L hseed hL z
  have hle : K S≤ Ksum := by
    have hh := Finset.single_le_sum (fun S _=>(hK S).le) (Finset.mem_univ S)
    dsimp [Ksum]
    linarith
  exact (hb S s C hC R seed L hseed hL z).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (common_retained_cost_nonneg _ _ _ _ _))

/-- Both common and residual allocations are expanded inside the joint
Hilbert sum; there is no per-source maximum or source-label count. -/
theorem actual_heterogeneous_second_extraction {α : Type*} [Fintype α] [DecidableEq α]
    (ε : ℝ) (hε : 0<ε) :
    ∃K : ℝ,0< K ∧ ∀{κ : Type*}(rows : Finset κ)(slots : κ→ Finset α)
      (s : (k : κ)→ Input (slots k)) (C R seed L : κ→ Ideal O)
      (hC : ∀k,Supported (C k)) (z : κ→ O) (scalar : κ→ℂ),
      (∀k∈rows,seed k∣C k) → (∀k∈rows,Squarefree (L k)) →
      (∑k∈rows,‖scalar k*normalizedColumn (s k) (C k) (hC k) (R k) (seed k) (L k) (z k)‖^2)≤
        K*∑k∈rows,‖scalar k‖^2*(L k).absNorm^ε*commonRetainedCost (s k) (C k) (R k) (L k) (z k) := by
  obtain ⟨K,hK,hbound⟩ := actual_uniform_second_column_extraction (α:=α) ε hε
  refine ⟨K,hK,?_⟩
  intro κ rows slots s C R seed L hC z scalar hseed hL
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  rw [norm_mul,mul_pow]
  calc
    _≤‖scalar k‖^2*(K*((L k).absNorm:ℝ)^ε*commonRetainedCost (s k) (C k) (R k) (L k) (z k)) :=
      mul_le_mul_of_nonneg_left
        (hbound (slots k) (s k) (C k) (hC k) (R k) (seed k) (L k) (hseed k hk) (hL k hk) (z k))
        (sq_nonneg _)
    _=_ := by ring

/-- The actual joint allocation budget passes through the second Mellin
window with one uniform extraction constant. -/
theorem actual_second_allocation_window_energy {α : Type*} [Fintype α] [DecidableEq α]
    (ε : ℝ) (hε : 0<ε) :
    ∃K : ℝ,0< K ∧ ∀{κ : Type*}(rows : Finset κ)(slots : κ→ Finset α)
      (s : (k : κ)→ Input (slots k)) (C R seed L : κ→ Ideal O)
      (hC : ∀k,Supported (C k)) (η : κ→ Character)
      (t θ X : κ→ℝ) (hX : ∀k,0< X k) (z : κ→ O) (scalar : κ→ℂ)
      (V : ℝ→ℂ) (hc : HasCompactSupport V) (hs : ContDiff ℝ ∞ V)
      (J : ℕ) (E : ℝ),0≤ E →
      (∀k∈rows,seed k∣C k) → (∀k∈rows,Squarefree (L k)) →
      (∀u : ℝ,(∑k∈rows,‖scalar k‖^2*((L k).absNorm:ℝ)^ε*
        commonRetainedCost (withHeight (s k) (η k) (t k+2*Real.pi*(u-θ k)))
          (C k) (R k) (L k) (z k))≤ E*(1+‖u‖)^(2*J)) →
      (∑k∈rows,‖scalar k*windowColumn (s k) (C k) (hC k) (R k) (seed k) (L k)
        (η k) (t k) (θ k) (X k) V (z k)‖^2)≤
          (K*E)*(∫u : ℝ,(1+‖u‖)^J*‖columnDensity V hc hs u‖)^2 := by
  obtain ⟨K,hK,hbound⟩ := actual_heterogeneous_second_extraction (α:=α) ε hε
  refine ⟨K,hK,?_⟩
  intro κ rows slots s C R seed L hC η t θ X hX z scalar V hc hs J E hE hseed hL hbudget
  apply actual_heterogeneous_joint_window_energy rows slots s C R seed L hC η t θ X hX
    z scalar V hc hs J (K*E) (mul_nonneg hK.le hE)
  intro u
  have hh := hbound rows slots
    (fun k=>withHeight (s k) (η k) (t k+2*Real.pi*(u-θ k)))
    C R seed L hC z scalar hseed hL
  exact hh.trans ((mul_le_mul_of_nonneg_left (hbudget u) hK.le).trans_eq (by ring))

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_uniform_second_column_extraction
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_heterogeneous_second_extraction
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_allocation_window_energy

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondExtraction -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondFamily; sha256 5cb531f2b01faa05d9d53f42fd29b158568d510901c35012f112b0fa9cf3f19f -/
section
                                                    
                                                          

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
  K_pos : 0< K
  dyad : Fin 4→ℤ
  τ : RayCharacter→ Character
  family : Family input.η C D hC hD inactive τ
  rowBudget : SecondRowConductorBudget input.η C D hC hD inactive τ

variable {α : Type*} [Fintype α] [DecidableEq α]

def SecondInputDatum.block (d : SecondInputDatum α) : SecondBlockSource :=
  originalSecondBlock d.input d.R d.seed d.C d.D d.hC d.hD d.sameSupport
    d.inactive d.radius d.rows d.rows_ne d.K d.K_pos d.dyad

def secondFamilyLeftScalar {Label : Type*} (d : Label→ SecondInputDatum α) (w : Label→ℂ)
    (q : SecondSector (fun l=>(d l).block)) : ℂ :=
  w q.1*(d q.1).block.outside*(Real.sqrt (volume (d q.1).input.toData):ℂ)
def secondFamilyRightScalar {Label : Type*} (d : Label→ SecondInputDatum α)
    (q : SecondSector (fun l=>(d l).block)) : ℂ :=
  Real.sqrt (volume (d q.1).input.toData)

theorem actual_second_family_left_column {Label : Type*}
    (d : Label→ SecondInputDatum α) (w : Label→ℂ)
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
    (d : Label→ SecondInputDatum α) (q : SecondSector (fun l=>(d l).block)) (t : ℝ) :
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
    (d : Label→ SecondInputDatum α) (w : Label→ℂ) (t : ℝ) :
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

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondFamily -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondCommonSelection; sha256 4eb648dc8478b9f7741129962c113cacb568dbcf23e502d62365208f27d992a8 -/
section
                                                
                                                              

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonLinearNormalization CenteredMomentCommonProfile
local notation "O" => HeckeFamily.O
local instance secondSelectionDecidableSum {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- Common-allocation selection after residual shells have been summed,
including the actual outside scalar and different surviving slot sets. -/
theorem actual_heterogeneous_common_cost_selection {α κ : Type*}
    [Fintype α] [DecidableEq α] (rows : Finset κ) (slots : κ→ Finset α)
    (s : (k : κ)→ Input (slots k)) (C R : κ→ Ideal O) (Ds : κ→ Finset (Ideal O))
    (z : κ→ O) (scalar : κ→ℂ) (W E : ℝ) (hW : 0≤ W)
    (hmass : ∀k∈rows,‖scalar k‖^2*((actualAllocations (s k).pools (C k)).card:ℝ)*
      (∑B : actualAllocations (s k).pools (C k),‖commonScalar (s k) (C k) (R k) B‖^2)≤ W)
    (hjoint : ∀S : Finset rows,
      ∀pick : (k : S)→ actualAllocations (s k.val.val).pools (C k.val.val),
      (∀k,commonScalar (s k.val.val) (C k.val.val) (R k.val.val) (pick k)≠0) →
      (∑k : S,∑L∈Ds k.val.val,
        ∑a∈(commonData (s k.val.val) (C k.val.val) (R k.val.val) (pick k)).toSource.active L,
          retainedAllocationCost (commonData (s k.val.val) (C k.val.val) (R k.val.val) (pick k))
            L a (z k.val.val))≤ E) :
    (∑k∈rows,‖scalar k‖^2*∑L∈Ds k,commonRetainedCost (s k) (C k) (R k) L (z k))≤ W*E := by
  have hh := joint_supported_weighted_selection
    (fun (k : rows) (B : actualAllocations (s k.val).pools (C k.val))=>
      ‖scalar k.val‖^2*((actualAllocations (s k.val).pools (C k.val)).card:ℝ)*
        ‖commonScalar (s k.val) (C k.val) (R k.val) B‖^2)
    (fun (k : rows) (B : actualAllocations (s k.val).pools (C k.val))=>
      ∑L∈Ds k.val,∑a∈(commonData (s k.val) (C k.val) (R k.val) B).toSource.active L,
        retainedAllocationCost (commonData (s k.val) (C k.val) (R k.val) B) L a (z k.val))
    W E hW (fun _ _=>by positivity)
    (fun _ _=>Finset.sum_nonneg (fun _ _=>Finset.sum_nonneg (fun _ _=>
      retained_allocation_cost_nonneg _ _ _ _)))
    (fun k=>by rw [←Finset.mul_sum];exact hmass k.val k.property)
    (fun S pick hne=>hjoint S pick (fun k hc=>hne k (by simp [hc])))
  apply le_trans (le_of_eq ?_) hh
  rw [Finset.sum_coe_sort rows (fun k=>∑B : actualAllocations (s k).pools (C k),
    (‖scalar k‖^2*((actualAllocations (s k).pools (C k)).card:ℝ)*
      ‖commonScalar (s k) (C k) (R k) B‖^2)*
    (∑L∈Ds k,∑a∈(commonData (s k) (C k) (R k) B).toSource.active L,
      retainedAllocationCost (commonData (s k) (C k) (R k) B) L a (z k)))]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [commonRetainedCost,Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]

theorem actual_second_common_mass_selection {α : Type*} [Fintype α] [DecidableEq α]
    (b ε : ℝ) (hε : 0<ε) :
    ∃K : ℝ,0< K ∧ ∀{κ : Type*}(rows : Finset κ)(slots : κ→ Finset α)
      (s : (k : κ)→ Input (slots k)) (C R : κ→ Ideal O) (Ds : κ→ Finset (Ideal O))
      (z : κ→ O) (scalar : κ→ℂ) (G E : ℝ),0≤ G →
      (∀k∈rows,(s k).upper≤ b) → (∀k∈rows,C k≠0) →
      (∀k∈rows,‖scalar k‖^2*(∏i,(s k).M i)^2*((C k).absNorm:ℝ)^(ε-1)≤ G) →
      (∀S : Finset rows,
        ∀pick : (k : S)→ actualAllocations (s k.val.val).pools (C k.val.val),
        (∀k,commonScalar (s k.val.val) (C k.val.val) (R k.val.val) (pick k)≠0) →
        (∑k : S,∑L∈Ds k.val.val,
          ∑a∈(commonData (s k.val.val) (C k.val.val) (R k.val.val) (pick k)).toSource.active L,
            retainedAllocationCost (commonData (s k.val.val) (C k.val.val) (R k.val.val) (pick k))
              L a (z k.val.val))≤ E) →
      (∑k∈rows,‖scalar k‖^2*∑L∈Ds k,commonRetainedCost (s k) (C k) (R k) L (z k))≤
        (K*G)*E := by
  obtain ⟨K,hK,hbound⟩ := uniform_common_scalar_mass (Fintype.card α) b ε hε
  refine ⟨K,hK,?_⟩
  intro κ rows slots s C R Ds z scalar G E hG hupper hC hscalar hjoint
  apply actual_heterogeneous_common_cost_selection rows slots s C R Ds z scalar (K*G) E
    (mul_nonneg hK.le hG) _ hjoint
  intro k hk
  have hh := hbound (ι:=slots k) (by simpa using Finset.card_le_univ (slots k))
    (s k) (hupper k hk) (C k) (R k) (hC k hk)
  calc
    _=‖scalar k‖^2*(((actualAllocations (s k).pools (C k)).card:ℝ)*
      ∑B : actualAllocations (s k).pools (C k),‖commonScalar (s k) (C k) (R k) B‖^2) := by ring
    _≤‖scalar k‖^2*(K*(∏i,(s k).M i)^2*((C k).absNorm:ℝ)^(ε-1)) :=
      mul_le_mul_of_nonneg_left hh (sq_nonneg _)
    _=K*(‖scalar k‖^2*(∏i,(s k).M i)^2*((C k).absNorm:ℝ)^(ε-1)) := by ring
    _≤ K*G := mul_le_mul_of_nonneg_left (hscalar k hk) hK.le

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_heterogeneous_common_cost_selection
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_common_mass_selection

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondCommonSelection -/
