/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Whole slots are chosen on each actual first allocation before any row or
later cofactor subset. An exhausted prefix leaves a zero-slot source. -/
import Candidate.C092.transport.FixedFirstFilled
import Candidate.C092.transport.WholeSlotSelection
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical
open OAI OAI.SevenEighths HeckeFamily CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedFirstLiveSource
open QRH.SilDensitySplit.CubeFree.Second.Concrete
namespace QRH.Cycle092.FixedFramePacking
local notation "Id" => Ideal HeckeFamily.O
local instance (priority := 2000) c092LocalInst_Candidate_C092_transport_FixedFirstSelection_7688bafc0eaf0a37_001 {κ : Type*} {p : κ → Prop} : DecidableEq (Subtype p) := Classical.decEq _

theorem actual_whole_selection {ι:Type} [Fintype ι] {a b:ℝ} (s:Source ι a b) (G:Id)
    (w:ι→ℝ) (mesh cap:ℝ) (hw:∀i,0≤w i) (hm:∀i,w i ≤ mesh) (hm₀:0 ≤ mesh)
    (hcap:(∑i,w i)+mesh ≤ cap) (hcu:(QRH.SourceCertificate.u:ℝ)≤cap) :
    ∃ Js : ∀ B:actualAllocations (tuplePools s) G,Finset (liveIndices B.val),
    ∀ (B:actualAllocations (tuplePools s) G),let J:=Js B
        let u':=∑j∈J,w j.val
        u' ≤ (QRH.SourceCertificate.u:ℝ) ∧ u' ≤ 3/5000 ∧
        (∑j:Rest J,w j.val.val) ≤ cap-(QRH.SourceCertificate.u:ℝ) ∧
        ((J=Finset.univ ∧ Fintype.card (Rest J)=0) ∨
          (QRH.SourceCertificate.u:ℝ)-mesh ≤ u') := by
  classical
  have hu : 0 ≤ (QRH.SourceCertificate.u:ℝ) := by norm_num [QRH.SourceCertificate.u]
  choose Js hJ using fun B:actualAllocations (tuplePools s) G=>
    WholeSlot.select_before_rows (fun i:liveIndices B.val=>w i.val) mesh (QRH.SourceCertificate.u:ℝ)
      (fun i=>hw i.val) (fun i=>hm i.val) hm₀ hu
  refine ⟨Js,?_⟩
  intro B
  let J:=Js B
  let w':liveIndices B.val→ℝ:=fun i=>w i.val
  have hsum: (∑i,w' i)≤∑i,w i := by
    change (∑i:liveIndices B.val,w i.val) ≤ _
    rw [Finset.sum_coe_sort]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>hw i)
  have hrem : (∑j:Rest J, w' j.val) = ∑j∈Finset.univ\J,w' j := by
    exact (Finset.sum_subtype (Finset.univ\J) (p:=fun i=>i∉J) (fun i=>by simp) w').symm
  have hh:=hJ B
  dsimp only
  refine ⟨hh.1, hh.1.trans (by norm_num [QRH.SourceCertificate.u]),?_,?_⟩
  · change (∑j:Rest J,w' j.val)≤_
    rw [hrem]
    exact hh.2.1.trans (max_le (by linarith) (by change (∑i,w' i)-_+_≤_;linarith))
  · by_cases hall:(∑i,w' i)≤(QRH.SourceCertificate.u:ℝ)
    · have he:J=Finset.univ:=hh.2.2 hall
      left
      refine ⟨he,?_⟩
      apply Fintype.card_eq_zero_iff.mpr
      exact ⟨fun z=>z.property (show z.val∈J by rw [he];exact Finset.mem_univ _)⟩
    · right
      have hp:0 ≤ (∑i,w' i)-(QRH.SourceCertificate.u:ℝ)+mesh := by linarith [lt_of_not_ge hall]
      have hR:=hh.2.1
      change (∑i∈Finset.univ\J,w' i) ≤ max 0 ((∑i,w' i)-(QRH.SourceCertificate.u:ℝ)+mesh) at hR
      rw [max_eq_right hp, Finset.sum_sdiff_eq_sub (Finset.subset_univ _)] at hR
      change _ ≤ ∑i∈J,w' i
      linarith

#print axioms actual_whole_selection
end QRH.Cycle092.FixedFramePacking
