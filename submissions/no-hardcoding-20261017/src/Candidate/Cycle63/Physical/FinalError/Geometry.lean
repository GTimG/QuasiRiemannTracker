import Candidate.Cycle63.Physical.FinalError.Chain
import Candidate.Cycle63.Arithmetic.Constants

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63FinalError
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentCompleteCommon CenteredMomentSecondHeightFamily ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondPhysicalBlock CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentCommonRadialData CenteredMomentCommonRawScale
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open Cycle63FinalNatural Cycle63FinalCapacity Cycle63FinalErrorCapacity
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

def errorRadius {s : Input α} (q : Chain s) (D₁ : Ideal O) (E : Finset (CommonIndex q.C₁ D₁))
    (Z Mrow amp δ reserve ξ b : ℝ) (N : ℕ) : ℝ :=
  frequencyRadius ((b^N*volume s/((q.C₁.absNorm:ℝ)*(normValue q.p)^q.k))^2/
    errorCommonRadius Z (Real.logb Z (D₁.absNorm:ℝ))
      (nominalLog q.C₁ D₁ (Ideal.span {primeSubsetGenerator (fun j:CommonIndex q.C₁ D₁=>j.val) E})
        (Z^Mrow) (volume s) Z) (Real.logb Z (q.C₁.absNorm:ℝ)) (3*amp) δ reserve q.p q.k) Z ξ

/-- Original and extracted conductor data and the actual second block.
 There is no capacity, final-width or moment-bound field. -/
structure Geometry (s : Input α) (q : Chain s) (Z Mrow amp omega ξ b J : ℝ) (N : ℕ) where
  D₁ : Ideal O
  hC₁ : Supported q.C₁
  hD₁ : Supported D₁
  heq₁ : primeSupport q.C₁=primeSupport D₁
  E : Finset (CommonIndex q.C₁ D₁)
  hmod : q.η₁.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
    Ideal.span {primeSubsetGenerator (fun j:CommonIndex q.C₁ D₁=>j.val) E*activeConductor q.C₁ D₁}
  moving_modulus : (q.υ.modulus.absNorm:ℝ)≤J*(q.η₁.modulus.absNorm:ℝ)*Z^(errorMoving q.p Z q.k)
  δ : ℝ
  reserve : ℝ
  homega : δ+reserve=omega
  C : Ideal O
  D : Ideal O
  hC : Supported C
  hD : Supported D
  heq : primeSupport C=primeSupport D
  U : Finset (CommonIndex C D)
  τ : RayFourExpansion.RayCharacter→Character
  family : Family q.υ C D hC hD U τ
  label : q.E₂=C ∨ q.E₂=D
  first_nonzero : frozenCoefficient q.B₁.val q.C₁ q.R₁ s.ν s.W s.P≠0
  second_nonzero : frozenCoefficient q.B₂.val q.E₂ q.R₂ q.extracted.ν q.extracted.W q.extracted.P≠0
  cols : Finset (Ideal O)
  coefficient : Ideal O→ℂ
  frequencies : Finset O
  profile : SchwartzMap ℝ ℂ
  scale : ℝ
  scale_pos : 0<scale
  bin : Fin 4→ℤ
  block_nonzero : physicalBlock q.υ q.t₂ cols coefficient C D hC hD U
    (errorRadius q D₁ E Z Mrow amp δ reserve ξ b N) frequencies profile scale bin≠0

def Geometry.radius {s : Input α} {q : Chain s} {Z Mrow amp omega ξ b J : ℝ} {N : ℕ}
    (g : Geometry s q Z Mrow amp omega ξ b J N) := errorRadius q g.D₁ g.E Z Mrow amp g.δ g.reserve ξ b N

def Geometry.nominal {s : Input α} {q : Chain s} {Z Mrow amp omega ξ b J : ℝ} {N : ℕ}
    (g : Geometry s q Z Mrow amp omega ξ b J N) :=
  errorNominal Mrow Z amp omega (errorRemoval q.p Z q.k) (errorMoving q.p Z q.k)
    q.C₁ g.D₁ g.C g.D g.U

omit [DecidableEq α] in
theorem error_state_width {s : Input α} {q : Chain s} {Z Mrow amp omega ξ b J : ℝ} {N : ℕ}
    (g : Geometry s q Z Mrow amp omega ξ b J N) (Bmask : ℝ) (hZ : 1<Z) (hb : 0<b) (hJ : 0<J)
    (χ : RayFourExpansion.RayCharacter) (Q : Ideal O) (hP : q.R₂*q.E₂≠0)
    (hPN : ((q.R₂*q.E₂).absNorm:ℝ)≤Z^Bmask) :
    (retainedState Z Bmask hZ (g.τ χ) Q (q.R₂*q.E₂) hP hPN g.radius g.C g.D g.U).width ≤
      g.nominal+(Real.logb Z (s.η.modulus.absNorm:ℝ)+
        Real.logb Z CenteredMomentFirstPhysicalSource.fixedPresentationCost+2*(N:ℝ)*Real.logb Z b+
        ξ/2+Real.logb Z J+Real.logb Z (4*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ))) := by
  have hh := actual_error_retainedState_width s.η q.η₁ q.υ q.C₁ g.D₁ g.hC₁ g.hD₁ g.heq₁ g.E
    (Z^Mrow) (volume s) Z amp g.δ g.reserve ξ b J N q.p q.k q.hp
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) (volume_pos s) hZ hb hJ g.hmod g.moving_modulus
    g.C g.D g.hC g.hD g.U g.τ g.family q.t₂ g.cols g.coefficient g.frequencies
    g.profile g.scale g.scale_pos g.bin Bmask χ Q _ hP hPN g.block_nonzero
  rw [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hh
  change (retainedState Z Bmask hZ (g.τ χ) Q (q.R₂*q.E₂) hP hPN g.radius g.C g.D g.U).width≤_ at hh
  unfold Geometry.nominal errorNominal
  linarith [g.homega]

theorem error_source_capacity {s : Input α} {q : Chain s} {Z Mrow amp omega ξ b J : ℝ}
    (g : Geometry s q Z Mrow amp omega ξ b J (Fintype.card α)) (hb : 1≤b)
    (hs : s.upper≤b) (hZ : 1<Z) (hM : 0<Mrow) (hP : ∀j,1≤s.P j)
    (hz : Cycle63.Optimization.slotFloor*Mrow≤∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j))≤Cycle63.Optimization.slotTop*Mrow)
    (haff : CenteredMomentEnergyBands.length Z s.X₁+CenteredMomentEnergyBands.length Z s.X₂+
      Cycle63.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤Cycle63.Arithmetic.B*Mrow)
    (η : Character) (v : ℝ) (second : Bool) (L : Ideal O)
    (a : CenteredMomentDivisorAllocation.Allocation L (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2))) (z : O)
    (hne : Cycle63.Physical.sourcePositiveRow (q.final η v).toSource second L a z≠0) :
    let cell := Cycle63.Arithmetic.cellUpper (Cycle63.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
    CenteredMomentEnergyBands.length Z (Cycle63Moment.LowBranch.finalPlain (q.final η v) second L a 0)+
      CenteredMomentEnergyBands.length Z (Cycle63Moment.LowBranch.finalPlain (q.final η v) second L a 1)+
        (9/2)*CenteredMomentAllocatedChildCapacity.remainingLogs L a Z (q.final η v).P-g.nominal ≤
      Mrow*Cycle63.Arithmetic.g cell+3*amp+(errorRemoval q.p Z q.k-errorMoving q.p Z q.k)+omega+
        supportPadding (Fintype.card α) b s.b₁ s.b₂ Z := by
  exact actual_error_source_capacity (Fintype.card α) b hb s le_rfl hs q.C₁ q.R₁ q.B₁
    g.first_nonzero q.η₁ q.t₁ (Ideal.span {q.p}) (Ideal.span_singleton_eq_bot.not.mpr q.hp)
    q.k q.coprime q.Bp η v g.C g.D q.E₂ q.R₂ g.label q.B₂ g.second_nonzero
    g.D₁ g.hD₁.1 g.hC g.hD g.heq g.U L a Z Mrow amp omega (errorMoving q.p Z q.k)
    hZ hM hP (actual_prime_widths q.p q.hp Z hZ q.k q.hk).2.2 hz haff second z hne

#print axioms error_state_width
#print axioms error_source_capacity
end
end OAI.SevenEighths.Cycle63FinalError
