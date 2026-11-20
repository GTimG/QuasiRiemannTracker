/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
One common mesh and genuine whole-slot selections before the actual rows,
with the true second-radius collar paid inside the native P.2 reserve. -/
import Candidate.C092.transport.NativeStrip
import Candidate.C092.transport.FixedFirstSelection
import Candidate.C092.transport.FirstGroupBudget
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualStageFrameBudget
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalAllocations MixedFirstLiveSource
open QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.Cycle092.FixedFramePacking QRH.Cycle092.PackedPrice
open QRH.Cycle090 QRH.SourceCertificate
local notation "Id"=>Ideal HeckeFamily.O
local instance (priority := 2000) selectedSubtypeDecEq {κ : Type*} {p : κ → Prop} : DecidableEq (Subtype p) := Classical.decEq _

/-- The genuine live source quota has ample space for the fixed u prefix. -/
theorem stage_width_has_prefix {n y:ℝ}(hy:y ≤ sourceY)(hn:n ≤ sourceRatio*y) :
    (u:ℝ) ≤ sourceWidth n y := by
  have hg:=sourceGain_antitone hy (le_refl sourceY)
  rw [source_native_value] at hg
  unfold sourceWidth
  norm_num [sourceRatio,sourceY,u] at hy hn ⊢
  linarith

/-- These global parameters are chosen before any finite slot type or ray
arithmetic. Their strict positive slack remains available to all later fees. -/
theorem early_parameters {n y l loss:ℝ}(hl:l<sourceWidth n y)(hLoss:0<loss) :
    ∃δ mesh:ℝ,0<δ ∧ 0 < mesh ∧ δ ≤ loss/250 ∧ δ ≤ (rho:ℝ)/10000 ∧
      mesh ≤ δ ∧ l+mesh ≤ sourceWidth n y ∧ mesh ≤ 1/100 ∧ mesh ≤ 1/6 ∧
      mesh+(δ+(3/2)*δ) ≤ terminalReserve ∧ 3*δ<loss := by
  let δ:=min (loss/250) ((rho:ℝ)/10000)
  let mesh:=min δ ((sourceWidth n y-l)/4)
  have hd:0<δ:=lt_min (by positivity) (by norm_num [rho])
  have hm:0 < mesh:=lt_min hd (by linarith)
  have hd1:δ ≤ loss/250:=min_le_left _ _
  have hd2:δ ≤ (rho:ℝ)/10000:=min_le_right _ _
  have hm1:mesh ≤ δ:=min_le_left _ _
  have hm2:mesh ≤ (sourceWidth n y-l)/4:=min_le_right _ _
  refine ⟨δ,mesh,hd,hm,hd1,hd2,hm1,by linarith,?_,?_,?_,by linarith⟩
  · norm_num [rho] at hd2;linarith
  · norm_num [rho] at hd2;linarith
  · unfold terminalReserve;linarith

/-- One selection on each actual allocation, prior to rows and native
frame labels; the exhausted branch is an actual zero-slot residual. -/
theorem stage_whole_selection {ι:Type} [Fintype ι] {a b n y l mesh:ℝ}
    (s:Source ι a b)(G:Id)(w:ι→ℝ)
    (hy:y ≤ sourceY)(hn:n ≤ sourceRatio*y)(hw:∀i,0 ≤ w i)(hm:∀i,w i ≤ mesh)
    (hm0:0 ≤ mesh)(hwidth:(∑i,w i) ≤ l)(hgap:l+mesh ≤ sourceWidth n y) :
    ∃Js:∀B:actualAllocations (tuplePools s) G,Finset (liveIndices B.val),
    ∀B:actualAllocations (tuplePools s) G,
      (∑j∈Js B,w j.val) ≤ (u:ℝ) ∧ (∑j∈Js B,w j.val) ≤ 3/5000 ∧
      (∑j:Rest (Js B),w j.val.val) ≤ sourceWidth n y-(u:ℝ) ∧
      ((Js B=Finset.univ ∧ Fintype.card (Rest (Js B))=0) ∨
        (u:ℝ)-mesh ≤ ∑j∈Js B,w j.val) := by
  obtain ⟨Js,hJs⟩ := actual_whole_selection s G w mesh (sourceWidth n y) hw hm hm0 (by linarith)
    (stage_width_has_prefix hy hn)
  exact ⟨Js,hJs⟩

/-- The real group window and the actual selected prefix imply both the
filled P.2 price and the exhausted zero-slot surplus at one fixed horizon. -/
theorem paid_actual_window (N:ℕ)(δ mesh:ℝ)(hδ:0<δ)(hm0:0 ≤ mesh)(hm:mesh ≤ δ)
    (hd:δ ≤ (rho:ℝ)/10000) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀j≤N,∀u' M aRoot:ℝ,
      0 ≤ u' → u' ≤ (u:ℝ) → aRoot ≤ 9179599/10000000 →
      1-6*u'+mesh-(Real.logb Z (64*((2:ℝ)^j)^4)+(3/2)*δ) ≤ M →
      M ≤ 2*aRoot+2*Real.logb Z ((2:ℝ)^N)+mesh →
      0 ≤ M ∧ M ≤ 19/10 ∧
      (∀w p s,(u:ℝ)-mesh ≤ u' → (regular terminalReserve terminalReserve_le).f w p s M ≤ u') ∧
      (5/6:ℝ)*max 0 (1-6*u'-M) ≤ δ+(3/2)*δ := by
  filter_upwards [early_dyad_cost N δ hδ] with Z hz
  refine ⟨hz.1,?_⟩
  intro j hj u' M aRoot hu0 hu ha hlo hhi
  have hlj:Real.logb Z (64*((2:ℝ)^j)^4) ≤ δ:=(hz.2 j hj).1
  have hln:Real.logb Z ((2:ℝ)^N) ≤ δ:=(hz.2 N le_rfl).2
  have hδ1:δ ≤ 1/100:=by norm_num [rho] at hd;linarith
  have hpaid:mesh+(δ+(3/2)*δ) ≤ terminalReserve:=by unfold terminalReserve;linarith
  exact paid_group_prices hm0 (by linarith) hu hu0 (by linarith) ha hδ1
    (hm.trans hδ1) (by positivity) hpaid

#print axioms stage_width_has_prefix
#print axioms early_parameters
#print axioms stage_whole_selection
#print axioms paid_actual_window
end
end QRH.Cycle092.ActualStageFrameBudget
