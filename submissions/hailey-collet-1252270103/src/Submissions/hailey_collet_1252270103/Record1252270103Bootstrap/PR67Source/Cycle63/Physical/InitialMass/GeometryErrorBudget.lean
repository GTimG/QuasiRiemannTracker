import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.FinalError.Chain
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.FinalError.Payment
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryErrorTail
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Cycle63Moment Cycle63FinalError
open CenteredMomentFirstChildProfileControl CenteredMomentCommonHeightEnvelope CenteredMomentEligibleEnergy
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentRankinRadical
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationErrorEnergy CenteredMomentAmplificationChildSourceCaps
open CenteredMomentAmplificationAllocationCost CenteredMomentAmplificationActiveFactor
open CenteredMomentAmplifiedRetainedRadius CenteredMomentPrimeElements
open CenteredMomentFirstScale Cycle63FinalErrorCapacity RayFourExpansion
open CenteredMomentFirstAnnularInput
local instance errorBudgetDecidableEq {ι : Type*} : DecidableEq ι := Classical.decEq _

/-- Actual supported second labels, including all inactive subsets, over
one squarefree residual projector shell. These are finite geometry gates. -/
structure ErrorResidualLabelShell (Z T B : ℝ) where
  projectors : Finset (Ideal O)
  labels : Ideal O→Finset FirstSourceLabel
  squarefree : ∀D∈projectors,Squarefree D
  dyad : ∀D∈projectors,T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T
  supported : ∀D∈projectors,∀v∈labels D,Supported v.1.1 ∧ Supported v.1.2
  equalSupport : ∀D∈projectors,∀v∈labels D,primeSupport v.1.1=primeSupport v.1.2
  divides : ∀D∈projectors,∀v∈labels D,D∣v.1.1 ∧ D∣v.1.2
  norm : ∀D∈projectors,∀v∈labels D,(v.1.1.absNorm:ℝ)≤Z^B ∧ (v.1.2.absNorm:ℝ)≤Z^B

/-- Exact image of the active extraction menu in the unpruned source. -/
def errorLiftedActiveAllocations {ι : Type*}[Fintype ι]
    (s : Input ι)(Q : Ideal O)(k : ℕ) : Finset (actualAllocations s.pools (Q^k)) :=
  Finset.univ.image (errorActiveAllocation s (Q^k))

/-- Reindex the literal active menu without adding unpruned allocations. -/
theorem error_lifted_active_allocations_sum {ι : Type*}[Fintype ι]
    (s : Input ι)(Q : Ideal O)(k : ℕ)
    (f : actualAllocations s.pools (Q^k)→ℝ) :
    (∑B : errorLiftedActiveAllocations s Q k,f B.val)=
      ∑B : actualAllocations (activeInput s).pools (Q^k),f (errorActiveAllocation s (Q^k) B) := by
  rw [Finset.sum_coe_sort (errorLiftedActiveAllocations s Q k) f]
  unfold errorLiftedActiveAllocations
  rw [Finset.sum_image]
  intro B _ D _ h
  exact errorActiveAllocation_injective s (Q^k) h

variable [Cycle63.AffineLedger] in
/-- The scalar remaining after the genuine paid column estimate. Its
prime shifts and extracted source volume have not been canceled by definition.
Its radius and nominal width are taken at the radial scale `M`, its branch
reserve in the ledger unit `unit`. -/
def extractedErrorLabelScalar (reflected second : Bool) (l v : FirstSourceLabel)
    (Z unit M a δ reserve error εcommon V Vextract : ℝ) (p : O) (k : ℕ) : ℝ :=
  (firstErrorTailRadius reflected l Z M V a δ reserve p k/Vextract)*
    (normalizer v.1.1 v.1.2 v.2.val*((if second then v.1.2 else v.1.1).absNorm:ℝ)^(εcommon-1))*
    Z^(errorNominal M Z a (δ+reserve) (errorRemoval p Z k) (errorMoving p Z k)
      (if reflected then l.1.2 else l.1.1) (if reflected then l.1.1 else l.1.2)
      v.1.1 v.1.2 v.2.val+(error-unit*branchReserve k)+errorRemoval p Z k-errorMoving p Z k)

/-- Both child restrictions preserve the original fixed profile envelope.
The four mass powers remain visible until this pointwise payment. -/
theorem actual_error_fixed_source_factor {α : Type*}[Fintype α][DecidableEq α]
    (N : ℕ)(Cs bp : ℝ)(hCs : 1≤Cs)(hbp : 1≤bp)
    (s : Input α)(hcard : Fintype.card α≤N)(hM : ∀j,s.M j≤Cs)
    (hb₁ : s.b₁=bp)(hb₂ : s.b₂=bp)(q : Chain s)(η : Character)(v : ℝ) :
    let src := withHeight q.extracted η v
    src.toData.profileFactor*(∏j,src.M j)^2≤2*bp^2*Cs^(4*N) := by
  intro src
  have hfirst := child_mass s q.C₁ q.R₁ q.B₁ q.η₁ q.t₁
  have hextract := child_mass q.first ((Ideal.span {q.p})^q.k) (q.R₁*q.C₁) q.Bp q.υ q.t₂
  have hm : mass src≤ mass s := hextract.trans hfirst
  have hprod : mass s≤Cs^N := by
    apply (Finset.prod_le_prod₀ (fun j _=>zero_le_one.trans (s.M_ge_one j)) (fun j _=>hM j)).trans
    simpa only [Finset.prod_const,Finset.card_univ] using pow_le_pow_right₀ hCs hcard
  have hbound := pow_le_pow_left₀ (mass_nonneg src) (hm.trans hprod) 4
  have hfactor : src.toData.profileFactor*(∏j,src.M j)^2=2*bp^2*(mass src)^4 := by
    change (2*(max 1 s.b₁*max 1 s.b₂))*(∏j,src.M j)^2*(∏j,src.M j)^2=_
    rw [hb₁,hb₂,max_eq_right hbp]
    dsimp only [mass]
    ring
  rw [hfactor]
  apply (mul_le_mul_of_nonneg_left hbound (by positivity)).trans_eq
  rw [←pow_mul]
  congr 2
  omega

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
