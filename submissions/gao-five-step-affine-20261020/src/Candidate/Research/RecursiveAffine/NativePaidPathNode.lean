/- Literal native per-node source payment in the global physical unit. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeSourceSide
import Candidate.Research.RecursiveAffine.CorrectedJointBudget

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153JointCount
noncomputable section
open scoped Classical HeckeNotation
open HeckeFamily CanonicalQuadraticSieve IdealMobiusDivisorSum Cycle63Moment Cycle63InitialMass
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalScalar
open CenteredMomentSectorLocalization Cycle153RegionalLow LocalMoment

/-- Arithmetic metadata of a selected actual physical source node.
`massLoss` is the native first-mass dyad loss, which is shifted into X0.
Its cancellation against the SAME first-label side is explicit. The
constructor is populated from NativeSourceSide's actual bin gate, rather
than by declaring the mass dyad loss itself tiny. -/
structure NativePaidPathNode (Z : ℝ) where
  unit : ℝ
  unit_pos : 0 < unit
  local_base : 1 < Z^unit
  reflected : Bool
  second : Bool
  first : FirstSourceLabel
  firstC : Supported first.1.1
  firstD : Supported first.1.2
  firstSupport : primeSupport first.1.1=primeSupport first.1.2
  C : Ideal O
  D : Ideal O
  hC : Supported C
  hD : Supported D
  secondSupport : primeSupport C=primeSupport D
  inactive : Finset (CommonIndex C D)
  rowWidth : ℝ
  length : ℝ
  amp : ℝ
  xi : ℝ
  reserve : ℝ
  eps : ℝ
  massLoss : ℝ
  sideError : ℝ
  side : massLoss+lowLabelSide reflected (Z^unit) length first ≤ sideError

namespace NativePaidPathNode
variable {Z : ℝ} (p : NativePaidPathNode Z)
def scale : ℝ := p.unit*p.rowWidth
def volumeLength : ℝ := p.unit*p.length
def amplification : ℝ := p.unit*p.amp
def coordinate (k : Fin 4) : ℝ := p.unit*
  actualHighCoordinates p.reflected (!p.reflected) p.second p.first p.C p.D p.inactive
    (Z^p.unit) p.rowWidth p.length p.amp p.xi p.reserve p.eps k
def shiftedOutside : ℝ := p.coordinate 0+p.unit*p.massLoss
def commonLog : ℝ := p.unit*
  (Real.logb (Z^p.unit) ((if p.reflected then p.first.1.2 else p.first.1.1).absNorm:ℝ)+
    Real.logb (Z^p.unit) ((if p.second then p.D else p.C).absNorm:ℝ))
def saving (delta : ℝ) : ℝ := (delta-Cycle153.commonLoss delta)*p.commonLog
def small (delta : ℝ) : ℝ := p.unit*
  (p.sideError+(1-unmarkedDensity delta)*(frequencyLoss (Z^p.unit) 32 p.xi+p.reserve)+
    unmarkedDensity delta*p.eps)

/-- The retained raw volume loses the two literal own common norms. -/
theorem coordinate_three : p.coordinate 3=p.volumeLength-p.commonLog := by
  change p.unit*(p.length-
    Real.logb (Z^p.unit) ((if p.reflected then p.first.1.2 else p.first.1.1).absNorm:ℝ)-
    Real.logb (Z^p.unit) ((if p.second then p.D else p.C).absNorm:ℝ))=
    p.unit*p.length-p.unit*_
  ring

/-- Native reserve_E applied to the SAME actual first/second common data,
then converted by the literal physical unit. Historical X1 is retained
with coefficient one, and the reserve is at the actual row scale. -/
theorem payment (delta : ℝ) (hdelta : Cycle63.Arithmetic.q0 ≤ delta ∧ delta ≤ 3/4) :
    p.shiftedOutside+p.coordinate 1+unmarkedDensity delta*p.coordinate 2+delta*p.coordinate 3 ≤
      p.small delta-(p.scale*(1-unmarkedDensity delta)-delta*p.volumeLength-
        p.amplification*(5-6*unmarkedDensity delta))-p.saving delta := by
  have hp:=actual_shifted_raw_row_payment p.reflected p.second p.first p.firstC p.firstD p.firstSupport
    p.C p.D p.hC p.hD p.secondSupport p.inactive (Z^p.unit) delta p.rowWidth p.length
    p.amp p.xi p.reserve p.eps p.massLoss p.sideError p.local_base hdelta p.side
  dsimp only at hp
  have h:=mul_le_mul_of_nonneg_left hp p.unit_pos.le
  dsimp only [shiftedOutside,coordinate,small,scale,volumeLength,amplification,saving,commonLog]
  unfold Cycle63InitialMass.highExponentValue at h
  simp only [ValuationCone.commonRate,Cycle153.commonLoss,Cycle63.Optimization.density,unmarkedDensity] at h ⊢
  nlinarith only [h]

/-- A coarse envelope for the actual shifted outside coordinate. It uses
native reserve_E at one fixed bin and true source boxes. The first-mass
loss itself is never assumed bounded or small. -/
theorem shiftedOutside_coarse
    (hq : Cycle63.Arithmetic.q0 ≤ 3/4)
    (hm : 0 ≤ p.scale) (hA : p.volumeLength ≤ 4) (ha : p.amplification ≤ 4)
    (hsmall : p.small (3/4) ≤ 1) (hX1 : 0 ≤ p.coordinate 1)
    (hX2 : -(149:ℝ) ≤ p.coordinate 2) (hX3 : -(149:ℝ) ≤ p.coordinate 3)
    (hcommon : 0 ≤ p.commonLog) : p.shiftedOutside ≤ 200 := by
  have hp:=p.payment (3/4) ⟨hq,le_rfl⟩
  have hs : 0 ≤ p.saving (3/4) := by
    dsimp only [saving]
    exact mul_nonneg (by norm_num [Cycle153.commonLoss,Cycle63.Optimization.density,unmarkedDensity]) hcommon
  norm_num [unmarkedDensity] at hp
  nlinarith only [hp,hm,hA,ha,hsmall,hX1,hX2,hX3,hs]

end NativePaidPathNode
end
end OAI.SevenEighths.Cycle153JointCount
#print axioms OAI.SevenEighths.Cycle153JointCount.NativePaidPathNode.payment
