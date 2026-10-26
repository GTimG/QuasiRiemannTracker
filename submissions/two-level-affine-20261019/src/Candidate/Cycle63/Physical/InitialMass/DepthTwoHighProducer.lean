/- The producer of the HIGH given of the second step of the two-level ledger: the HIGH given at every subset of the
slots, with one schedule for all subsets. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.DepthTwoHighProducerSlots
import Candidate.Cycle63.Physical.InitialMass.SecondStepFirstLevel
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineHighUniform
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineExceptionalGates

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open Cycle63MarkedPlain
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open CenteredMomentSectorLocalization
open ActualEisensteinCubic
open MeasureTheory
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentNaturalFixedRaySource
open CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT Cycle63Moment
open CenteredMomentAmplificationChildInput
open CenteredMomentSlotRatios CenteredMomentSourceLiveColumn
open CenteredMomentChildRows RayFourExpansion
open CenteredMomentOriginalCommonHarmonic
open ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSecondHeightFamily Cycle63Moment.LowBranch HeckeDetectorZeros
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondExceptionalFamily
open CenteredMomentExceptionalAmplitudePair CenteredMomentFiniteProfileExceptional
open CenteredMomentAllocatedRayDictionary CenteredMomentSecondInputCapacitySource
open Cycle63InitialSource CenteredMomentCommonRawScale QuadraticInitialBound CenteredMomentEnergyBands

/-- The producer of the HIGH given of the second step: for every modulus, slot type and smooth slot profile supported
in `[1, 2]`, the HIGH given of the second step holds at its affine loss `secondStepAffineLoss`, the plain profiles of
the class `(1/4, 9/4)`, the radial support `2`, the mask `20`, every mesh, height exponent and label cap, and the loss
`secondStepLossNeeded` of the number of slots. -/
def TwoLevelHighProducer : Prop :=
  ∀ (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    {β : Type} [Fintype β] [DecidableEq β] (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8) (mesh τlow B : ℝ),
    DepthTwoHighGivenStatement (α:=β) M H hH W hW hWs hβlo hβhi secondStepAffineLoss (1/4) (9/4) 2 20 mesh τlow B
      (secondStepLossNeeded (Fintype.card β))

set_option maxHeartbeats 800000 in
/-- The producer of the HIGH given of the second step. For every ledger whose junction is at least the second junction,
one schedule `g` of the loss unit `μ` serves every subset `T` of the slots (`affine_high_uniform_schedule_of_high` with
the top transport theorem `actual_affine_high_top` at `T` and the height cap `τlow/2`); at each subset the HIGH given
holds from `depth_two_high_core`, and the profile set, the degree and the constant of the given are the union, the
largest degree and the sum over the subsets. -/
theorem twoLevelHighProducer : TwoLevelHighProducer := by
  intro M _ H hH β _ _ W hW hWs hβlo hβhi mesh τlow B hε hap _ _ hbΦ hBmask0 hBmask hmesh0 hmesh hτlow η₀ Q hQM
    _ _ hQ72 μ hμdef Led hq
  have hμ : 0<μ := by rw [hμdef]; exact @geometry_loss_unit_pos Cycle63.Arithmetic.firstLevelLedger 1 _ one_pos hε
  have hμ1 : μ≤1 := by
    rw [hμdef]; unfold geometryLossUnit
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (by norm_num)))
  have hμcap : μ≤Cycle63.Optimization.geometryLossCap := by
    have h1 : μ ≤ secondStepAffineLoss/128 := by rw [hμdef]; unfold geometryLossUnit; exact min_le_left _ _
    have hk := Cycle63.Optimization.slotPrice_mem
    have hk0 : 0<Cycle63.Optimization.slotPrice := by linarith [hk.1]
    have h2 : (12:ℝ)/37≤1-(1/2)/Cycle63.Optimization.slotPrice := by
      have : (1/2)/Cycle63.Optimization.slotPrice≤25/37 := by
        rw [div_le_iff₀ hk0]; linarith [hk.1]
      linarith
    unfold Cycle63.Optimization.geometryLossCap Cycle63.Optimization.lowReserveWeight
      Cycle63.Optimization.allowanceUnit
    unfold secondStepAffineLoss at h1
    nlinarith
  have hmesh' : mesh≤Cycle25.Energy.commonMesh 2 28 1 (μ/8) := hμdef ▸ hmesh
  have hqh : Cycle63.Arithmetic.q0≤Cycle63.AffineLedger.q :=
    (Cycle63.Arithmetic.q0_bounds.2.trans (by linarith [Cycle63.Optimization.secondJunction_mem.1])).trans hq
  obtain ⟨Cs,hCs,hsources⟩:=eventual_actual_affine_exceptional_source_gates (α:=β) M H hH W hW.continuous hWs
  obtain ⟨τ,hτ,-,hτcap,g,hgμ,hgδ,hgτ,hT⟩:=affine_high_uniform_schedule_of_high (α:=β) W hWs hW μ 2 (τlow/2) hμ hμcap
    le_rfl (by positivity)
    (fun T P=>AffineHighTopConclusion (ι:=T) M H hH η₀ 1 (naturalRow η₀ 1 one_ne_zero) 1 one_ne_zero W hβlo P.e P.τ
      P.he μ Cs (geometryAffineHighDictionaryRate μ (Fintype.card β)) Cycle63.AffineLedger.q (Fintype.card β))
    (fun T=>actual_affine_high_top (ι:=T) M H hH η₀ 1 (naturalRow η₀ 1 one_ne_zero) 1 one_ne_zero W hWs hW hβlo
      (by unfold Cycle63.Optimization.plainCapacityCost; linarith) μ Cs (Fintype.card β) hμ hμcap hCs
      Cycle63.AffineLedger.q hqh (Fintype.card_le_of_injective (fun i : T=>i.val) Subtype.val_injective)
      (geometry_affine_high_selected_fiber_receipt (α:=T) η₀ 1 (naturalRow η₀ 1 one_ne_zero) 1 one_ne_zero μ hμ)
      _ rfl)
  refine ⟨g,hgμ,hgδ,by rw [hgτ]; linarith,?_⟩
  intro Ψ _ _
  choose P hPτ _ hPe _ _ _ hPc using hT
  have hPc' := fun T : Finset β => AffineHighTopConclusion_congr M H hH (ι:=T) η₀ 1 (naturalRow η₀ 1 one_ne_zero) 1
    one_ne_zero W hβlo (P T).e g.e (P T).τ g.τ (P T).he g.e_pos (hPe T).symm ((hPτ T).trans hgτ.symm) μ Cs _ _ _
    (hPc T)
  choose Sp hSp0 K Kt _ hKt htop using hPc'
  have hcore := fun T : Finset β => depth_two_high_core M H hH (ι:=T) W hW hWs hβlo hβhi g 2 20 mesh τlow B
    (secondStepLossNeeded (Fintype.card β)) μ (geometryAffineHighDictionaryRate μ (Fintype.card β)) Cs
    (Fintype.card β) η₀ Q hQM hQ72 hμ hμ1 hCs hgμ hgδ rfl le_rfl (by norm_num) le_rfl hmesh0 hmesh' (by rw [hgτ]; linarith) hq
    (Fintype.card_le_of_injective (fun i : T=>i.val) Subtype.val_injective)
    (by rw [hμdef]; exact le_rfl)
    (Sp T) (hSp0 T) (K T) (Kt T) (hKt T) (htop T Q hQM hQ72)
    (hsources.mono fun Z hz=>⟨hz.1,by
      intro θ w σ freq hσ _ bΦ state p t X₁ X₂ hX₁ hX₂ hw hwin _
      exact { hz.2 T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hwin with card := le_rfl }⟩)
  choose dh₀ hdh using hcore
  refine ⟨Finset.univ.biUnion Sp,Finset.univ.sup dh₀,depthTwoHighClassBound g.e μ,?_⟩
  intro ε hε
  have hK := fun T : Finset β => hdh T Ψ (Finset.univ.biUnion Sp)
    (Finset.subset_biUnion_of_mem Sp (Finset.mem_univ T)) (Finset.univ.sup dh₀)
    (Finset.le_sup (Finset.mem_univ T)) ε hε
  choose Kh₀ hKh₀ hKh using hK
  refine ⟨∑ T, Kh₀ T,Finset.sum_nonneg (fun T _=>hKh₀ T),?_⟩
  filter_upwards [Filter.eventually_all.2 fun T=>hKh T (∑ T, Kh₀ T)
    (Finset.single_le_sum (fun T _=>hKh₀ T) (Finset.mem_univ T))] with Z hZ
  exact depthTwoHighGivenAt_of_slots M H hH W hW hWs hβlo hβhi g (1/4) (9/4) 2 20 mesh ε τlow B
    (secondStepLossNeeded (Fintype.card β)) hap Ψ _ _ _ _ η₀ Q hQM hQ72 Z hZ

end
end OAI.SevenEighths.Cycle63InitialMass
