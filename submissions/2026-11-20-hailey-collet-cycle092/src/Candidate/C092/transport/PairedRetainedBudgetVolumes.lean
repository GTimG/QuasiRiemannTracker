/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Actual allocation volumes and the genuine quadratic common-factor saving. -/
import Candidate.C092.transport.PairedRetainedBudgetWeights
import Submissions.sil_density_split_20261026.CubeFree.FP.MixedFirstNonexceptionalAllocation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.PairedRetainedBudget
noncomputable section
local instance (priority := 2000) pairedVolumeSubtypeDecEq {κ : Type*} {p : κ→Prop} :
    DecidableEq (Subtype p) := Classical.decEq _
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentSourceLiveAllocation CenteredMomentCommonRawScale
open QRH.Record1252270103KernelMass
open QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations MixedFirstLiveSource
open MixedInnerExceptionalBlock MixedCommonCoefficient MixedCommonRestriction MixedFirstNonexceptionalAllocation
open QRH.Cycle092.TwistedRawBall
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type} [Fintype ι] {a b : ℝ}

/-- The live source still carries its inherited ordinary prefixes. This
    equality uses its true divided volume, without charging them twice. -/
theorem allocated_volume_ratio (s : Source ι a b) (hb : 0≤b) (cover : OriginalEnclosure s)
    (G : Id) (B : actualAllocations (tuplePools s) G) :
    sourceVolume (allocatedLiveSource s hb cover G B)/pairNorm (allocatedLiveSource s hb cover G B).d =
      (sourceVolume s/pairNorm s.d)/rawReduction B.val s.P := by
  exact live_volume_ratio B.val
    (allocation_data (tuplePools s) G B.val (Finset.mem_filter.mp B.property).1).1
    s.d (s.X₁*s.X₂) s.P (fun i=>zero_lt_one.trans_le (s.hP i))

/-- Both independently colored ordinary factors are contractions; the full
    native frozen-coefficient saving therefore survives with true NG². -/
theorem colored_allocation_volume_sq_le (s : Source ι a b) (hb : 0≤b)
    (cover : OriginalEnclosure s) (η₁ η₂ : Character) (G : Id) (hG : G≠0)
    (B : actualAllocations (tuplePools s) G) :
    allocationWeight s (idealCoeff η₁) (idealCoeff η₂) G B *
      (sourceVolume (allocatedLiveSource s hb cover G B)/pairNorm (allocatedLiveSource s hb cover G B).d)^2 ≤
      (∏i,s.M i)^2*((2:ℝ)^Fintype.card ι)^2 *
        (sourceVolume s/pairNorm s.d)^2/(G.absNorm:ℝ)^2 := by
  let F := frozenWeight (punctureProduct s.S s.H) B.val*
    frozenCoefficient B.val G s.R s.ν s.Wslot s.P
  have hc := TwistedRawSource.ordinaryColor_norm_le_one η₁ η₂ B.val
  have he : allocationScalar s (idealCoeff η₁) (idealCoeff η₂) G B =
      F*TwistedRawSource.ordinaryColor (idealCoeff η₁) (idealCoeff η₂) B.val := by
    unfold allocationScalar F
    ring
  have hnorm : allocationWeight s (idealCoeff η₁) (idealCoeff η₂) G B ≤ ‖F‖^2 := by
    unfold allocationWeight
    rw [he,norm_mul]
    exact pow_le_pow_left₀ (by positivity) (mul_le_of_le_one_right (norm_nonneg _) hc) 2
  have hB := (allocation_data (tuplePools s) G B.val (Finset.mem_filter.mp B.property).1).1
  have hf := frozen_quadratic_cost (punctureProduct s.S s.H) B.val hB G s.R hG
    (Finset.mem_filter.mp B.property).2 s.ν s.Wslot s.P s.M
    (fun i=>zero_lt_one.trans_le (s.hP i)) s.hν s.hWnorm s.hM s.hW
  have hw : allocationWeight s (idealCoeff η₁) (idealCoeff η₂) G B/(rawReduction B.val s.P)^2 ≤
      (∏i,s.M i)^2*((2:ℝ)^Fintype.card ι)^2/(G.absNorm:ℝ)^2 :=
    (div_le_div_of_nonneg_right hnorm (sq_nonneg _)).trans hf
  calc
    _=(allocationWeight s (idealCoeff η₁) (idealCoeff η₂) G B/(rawReduction B.val s.P)^2)*
        (sourceVolume s/pairNorm s.d)^2 := by
      rw [allocated_volume_ratio]
      ring
    _ ≤ ((∏i,s.M i)^2*((2:ℝ)^Fintype.card ι)^2/(G.absNorm:ℝ)^2)*
        (sourceVolume s/pairNorm s.d)^2 := mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    _ = _ := by ring

#print axioms allocated_volume_ratio
#print axioms colored_allocation_volume_sq_le
end
end QRH.Cycle092.PairedRetainedBudget
