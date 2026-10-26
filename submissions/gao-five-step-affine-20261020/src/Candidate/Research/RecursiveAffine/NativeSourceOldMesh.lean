/- The existing prechosen mesh already admits the actual OLD/reflection source.
Copyright (c)2026 Zhongpai Gao. Native mesh by OpenAI and Hailey Collet. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.SourceContextMesh

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace OAI.SevenEighths.Cycle153SourceSchedule
noncomputable section
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentFirstSecondLossParameters

/-- Halving the error while halving the input width leaves the native
induction count unchanged. The smaller mask then pays the doubled source
cap. This compares the literal meshes, before any cardinality or node. -/
theorem common_old_mesh_admits_wide_source {e : ℝ}(he : 0<e)(he1 : e≤1) :
    Cycle25.Energy.commonMesh 1 20 1 (e/2)≤Cycle25.Energy.commonMesh 2 28 1 e :=by
  have ha : amplification e=e/16000:=min_eq_right (by linarith only [he1])
  have hah : amplification (e/2)=(e/2)/16000:=min_eq_right (by linarith only [he1])
  have hratio : 2*(1:ℝ)/amplification (e/2)=2*(2:ℝ)/amplification e:=by
    rw [ha,hah]
    field_simp [he.ne']
    <;> ring
  have hc : count 1 (e/2)=count 2 e:=by
    unfold count depth
    rw [hratio]
  have hrange : ∀n,range 2 28 1 n≤2*range 1 20 1 n:=by
    intro n
    induction n with
    | zero=>norm_num [range]
    | succ n ih=>simp only [range,step];linarith only [ih]
  have hcap : finalSourceCap 2 28 1 e≤2*finalSourceCap 1 20 1 (e/2):=by
    unfold finalSourceCap
    rw [←hc]
    have hh:=hrange (count 1 (e/2))
    unfold sourceCap
    linarith only [hh]
  have hs : scale 2 (finalSourceCap 2 28 1 e) e≤
      2*scale 1 (finalSourceCap 1 20 1 (e/2)) (e/2):=by
    unfold scale
    rw [←hc]
    have hn : (0:ℝ)≤count 1 (e/2):=Nat.cast_nonneg _
    linarith only [hcap,hn]
  have hc0:=sourceCap_nonneg 1 20 1 (by norm_num) (by norm_num) (count 1 (e/2))
  have hc1:=sourceCap_nonneg 2 28 1 (by norm_num) (by norm_num) (count 2 e)
  have hs0 : 0<scale 1 (finalSourceCap 1 20 1 (e/2)) (e/2):=by
    unfold scale
    change 0<(count 1 (e/2):ℝ)+1+10*sourceCap 1 20 1 (count 1 (e/2))+30
    positivity
  have hs1 : 0<scale 2 (finalSourceCap 2 28 1 e) e:=by
    unfold scale
    change 0<(count 2 e:ℝ)+2+10*sourceCap 2 28 1 (count 2 e)+30
    positivity
  have heRatio : (e/2)/(1000000*scale 1 (finalSourceCap 1 20 1 (e/2)) (e/2))≤
      e/(1000000*scale 2 (finalSourceCap 2 28 1 e) e):=by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hs he.le]
  unfold Cycle25.Energy.commonMesh fineMesh mesh reserve
  apply div_le_div_of_nonneg_right ?_ (by norm_num)
  apply min_le_min ?_ heRatio
  rw [ha,hah]
  linarith only [he]

/-- No additional mesh minimum or N-dependent choice is needed for the
actual width-two, mask28 OLD/reflection source at the same oldLoss. -/
theorem localSlotMesh_admits_old_source {eps : ℝ}(heps : 0<eps) :
    localSlotMesh eps≤Cycle25.Energy.commonMesh 2 28 1 (oldLoss eps) :=by
  have he:=oldLoss_pos heps
  have he1 : oldLoss eps≤1:=by
    have hh:=(oldLoss_bounds eps).2
    have hm : nativeMu/1024≤1:=by norm_num [nativeMu,Cycle153.RegionalSchedule.primitiveError]
    exact hh.trans hm
  exact (localSlotMesh_gates heps).2.2.2.1.trans (common_old_mesh_admits_wide_source he he1)

end
end OAI.SevenEighths.Cycle153SourceSchedule
#print axioms OAI.SevenEighths.Cycle153SourceSchedule.common_old_mesh_admits_wide_source
#print axioms OAI.SevenEighths.Cycle153SourceSchedule.localSlotMesh_admits_old_source
