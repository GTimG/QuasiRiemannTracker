/- The fixed-source main payment of the first step of the two-level ledger: row 5 from the second step's return.
Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineMainUniform
import Candidate.Cycle63.Physical.InitialMass.LowChildSecondStep
import Candidate.Cycle63.Physical.InitialMass.LowChildSideExponent
import Candidate.Cycle63.Physical.InitialMass.DepthTwoHighProducer

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open Cycle63MarkedPlain
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondCanonicalScalar
open CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondInputCapacitySource Cycle63Moment
open Cycle63Moment.LowBranch
open LocalMoment
open CenteredMomentEnergyBandMonotonicity CenteredMomentSecondEnergySplit
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstAmplificationChoice
open CenteredMomentEnergyFirstAnnularAdmission CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CompletedGauss
open Cycle63FinalNatural CenteredMomentDivisorExtraction CenteredMomentCommonRawScale
open Cycle63InitialSource CenteredMomentNaturalFixedRaySource
open CenteredMomentNaturalRowSource
open CenteredMomentEnergyState CenteredMomentEnergyBands
open Cycle63Moment.LowBranch

variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The ledger of the first step is the first step of the two-level ledger: its junction, plane, region and window
are those of the two-level ledger. -/
instance firstLevelLedger_isTwoLevelFirstStep : IsTwoLevelFirstStep Cycle63.Arithmetic.firstLevelLedger where
  q_eq := rfl
  lam_eq := rfl
  B_eq := rfl
  price_eq := rfl
  intercept_eq := rfl
  slotFloor_eq := rfl
  slotTop_eq := rfl
  cellMesh_eq := rfl

/-- The fixed-source main payment of the first step of the two-level ledger. Row 5 comes from the second step's
return (`lowSelectedPaidAt_first_level`) at the slot bound `mesh`, which is at most the common mesh of the width cap
`101/100` and `2/5` of the mesh of the second step; the children are presented at the height exponent
`levelOneHeight` of the dictionary rate of the schedule. The HIGH given of the second step is
`twoLevelHighProducer`. -/
theorem actual_affine_main_uniform_paid_two_level
    (A : ℕ)(hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤HeckeZeroSupremum.beta)(hβhi : HeckeZeroSupremum.beta≤7/8)
    (η₀ : Character)(u₀ : O)(F₀ : CenteredMomentNaturalRowSource.NaturalRow η₀ u₀)
    (R₀ : Ideal O)(hu₀ : u₀≠0)
    (εaffine mesh bΦ : ℝ)(hε : 0<εaffine)
    (hmesh : mesh<Cycle63.Arithmetic.amplifierFloor/2)(hmesh0 : 0≤ mesh)
    (hmeshμ : mesh≤geometryLossUnit 1 εaffine/8)
    (hmeshcap : mesh≤Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 εaffine/8))
    (hmeshlow : mesh≤Cycle25.Energy.commonMesh (101/100) 28 1 (geometryLossUnit 1 εaffine/8))
    (hslot : 5/2*mesh ≤ secondStepMesh εaffine)
    (hmarkedmesh : mesh≤ markedRawMesh*markedCoreMin)
    (hbΦ : 2≤bΦ) :
    ∃τ : ℝ,0<τ ∧ τ≤geometryLossUnit 1 εaffine/16 ∧
    ∀(Q : Ideal O)(_hQM : Q≤M),internalQ Q η₀≠0 → internalQ Q η₀≠⊤ →
    ∀_hQ72 : internalQ Q η₀≤Ideal.span {(72:O)},
    ∀T : Finset α,∃S : Finset (ℕ×ℕ),∃D : ℕ,∃Cm : ℝ,0≤Cm ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧
        GeometryAffineMainPaidSpec M H hH Sbad W hW.continuous hWs
          (excluded F₀.character R₀) η₀ mesh (geometryLossUnit 1 εaffine) T S D Cm Z := by
  have hμ := geometry_loss_unit_pos 1 εaffine (by norm_num) hε
  obtain ⟨Z₀,-,hZ₀⟩ := CenteredMomentFirstPhysicalLedger.frequency_loss_eventually 32 (geometryLossUnit 1 εaffine/64)
    (by norm_num) (by positivity)
  have hAdm : ∀ᶠZ : ℝ in atTop,(1:ℝ)=1 ∧
      frequencyLoss Z 32 (geometryLossUnit 1 εaffine/64)+geometryLossUnit 1 εaffine/8≤geometryLossUnit 1 εaffine/4 := by
    filter_upwards [eventually_ge_atTop Z₀] with Z hZ
    refine ⟨rfl,?_⟩
    have := (hZ₀ Z hZ).2
    linarith
  exact actual_affine_main_uniform_paid_of_fibers (α:=α) M H hH
    (Presented:=levelOnePresented
      (levelOneHeight M H hH (geometryAffineHighDictionaryRate (geometryLossUnit 1 εaffine) (Fintype.card α))))
    actual_geometry_low_bin_gate_side A hc hs Sbad hbad W hW hWs hβlo hβhi η₀ u₀ F₀ R₀ hu₀ εaffine mesh bΦ hε hmesh
    hmesh0 hmeshμ (101/100) le_rfl (by norm_num)
    (fun g hgμ hgδ => by
      have h := lowSelectedPaidAt_first_level M H hH hβlo hβhi εaffine hε g hgμ mesh (by rw [hgμ]; exact hmeshlow)
        hslot (fun W hW hWs => twoLevelHighProducer M H hH W hW hWs hβlo hβhi _ _ _)
      rw [hgμ, hgδ] at h
      exact h)
    hmeshcap hmarkedmesh hbΦ hAdm _
    (fun T => geometryLowChildrenPresented_depthTwo _ η₀ u₀ F₀ R₀ 8)
    (fun T=>geometry_affine_high_selected_fiber_receipt (α:=T) η₀ u₀ F₀ R₀ hu₀
      (geometryLossUnit 1 εaffine) hμ)

end
end OAI.SevenEighths.Cycle63InitialMass
