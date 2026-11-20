/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The first common code shortens the actual four-scale minimum by at most NG.
The native selected slot product and actual divisor also bound the volume. -/
import Candidate.C092.transport.FixedFrameTerminal
import Submissions.sil_density_split_20261026.CubeFree.Second.ProviderLabelBudget
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow
open MixedInnerExceptionalBlock MixedFirstLiveSource
open QRH.SilDensitySplit.CubeFree.Second.Provider QRH.SilDensitySplit.CubeFree.Second.Concrete
namespace QRH.Cycle092.FixedFramePacking
local notation "Id" => Ideal HeckeFamily.O
variable {ι:Type*} [Fintype ι] {a b:ℝ}
local instance (priority := 2000) c092LocalInst_Candidate_C092_transport_FixedFirstGeometry_13f811e4c06a5819_001 {κ : Type*} {p : κ → Prop} : DecidableEq (Subtype p) := Classical.decEq _

theorem first_minimum (s:Source ι a b) (hb:0≤b) (cover:OriginalEnclosure s) (G:Id)
    (B:actualAllocations (tuplePools s) G) (J:Finset (liveIndices B.val)) (hd:s.d=(1,1)) :
    s.L ≤ (renorm (restOf s hb cover G B J)).L*(G.absNorm:ℝ) := by
  let b₁:=B.val (Sum.inr 0)
  let b₂:=B.val (Sum.inr 1)
  have hn:∀ i,B.val i ≠ 0 := (allocation_data (tuplePools s) G B.val (Finset.mem_filter.mp B.property).1).1
  have hp : (1:ℝ) ≤ ∏ i, (Ideal.absNorm (B.val (Sum.inl i)):ℝ) := by
    calc
      (1:ℝ) = ∏ _i:ι, (1:ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _=>zero_le_one) (fun i _ => nrm_one_le (hn (Sum.inl i)))
  have hb' : 0<nrm b₁*nrm b₂:=mul_pos (nrm_pos (hn _)) (nrm_pos (hn _))
  have hg:nrm b₁*nrm b₂ ≤ (G.absNorm:ℝ) := by
    rw [alloc_common_norm s G B]
    exact le_mul_of_one_le_right hb'.le hp
  change s.L ≤ s.L/(nrm (s.d.1*b₁)*nrm (s.d.2*b₂))*(G.absNorm:ℝ)
  rw [hd];simp only [one_mul]
  calc
    _ = s.L/(nrm b₁*nrm b₂)*(nrm b₁*nrm b₂) := (div_mul_cancel₀ _ hb'.ne').symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hg (div_nonneg s.hL.le hb'.le)

theorem first_volume (s:Source ι a b) (hb:0≤b) (cover:OriginalEnclosure s) (G:Id)
    (B:actualAllocations (tuplePools s) G) (J:Finset (liveIndices B.val)) :
    sourceVolume (renorm (restOf s hb cover G B J))*
      (∏ j:J,s.P j.val.val)*(G.absNorm:ℝ) ≤ (2:ℝ)^(Fintype.card ι)*sourceVolume s := by
  have hk:=rest_volume_mul (allocatedLiveSource s hb cover G B) (fun _=>rfl) J
  change sourceVolume (renorm (restOf s hb cover G B J))*(∏ j:J,s.P j.val.val)=_ at hk
  rw [hk]
  exact live_volume_le s hb cover G B

theorem first_minimum_log (s:Source ι a b) (hb:0≤b) (cover:OriginalEnclosure s) (G:Id)
    (hG:G≠0) (B:actualAllocations (tuplePools s) G) (J:Finset (liveIndices B.val))
    (hd:s.d=(1,1)) (U:ℝ) (hU:1<U) (hshort:U^(115/1000:ℝ) ≤ s.L) :
    max 0 (115/1000-Real.logb U (G.absNorm:ℝ)) ≤ Real.logb U (max 1 (renorm (restOf s hb cover G B J)).L) := by
  let r:=renorm (restOf s hb cover G B J)
  have hNG : 0 < (G.absNorm:ℝ) := nrm_pos hG
  have hp:=hshort.trans (first_minimum s hb cover G B J hd)
  have hl:=Real.logb_le_logb_of_le hU (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _) hp
  change Real.logb U (U^(115/1000:ℝ)) ≤ Real.logb U (r.L*(G.absNorm:ℝ)) at hl
  rw [Real.logb_rpow (zero_lt_one.trans hU) hU.ne',Real.logb_mul r.hL.ne' hNG.ne'] at hl
  change max 0 (115/1000-Real.logb U (G.absNorm:ℝ)) ≤ Real.logb U (max 1 r.L)
  apply max_le
  · exact Real.logb_nonneg hU (le_max_left _ _)
  · have h:=Real.logb_le_logb_of_le hU r.hL (le_max_right 1 r.L)
    linarith

#print axioms first_minimum
#print axioms first_volume
#print axioms first_minimum_log
end QRH.Cycle092.FixedFramePacking
