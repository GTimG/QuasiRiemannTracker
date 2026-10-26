/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.AdmittedWindow
import Submissions.hailey_collet_1252270103.Cycle25.Assembly.Count.Endpoint
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.RH20261023Return
noncomputable section
class CountScheme where
 naturalκ : ℝ
 natural_lo : 7/10≤naturalκ
 natural_hi : naturalκ≤3/4
 windows : List (AdmittedWindow naturalκ)
namespace GenericCount
open OAI.SevenEighths
variable [S:CountScheme]
def admittedBranches : List Branch := S.windows.map AdmittedWindow.toBranch
def envelope (κ δ p:ℝ) : ℝ := QRH.RH20261023Return.envelope admittedBranches κ δ p
inductive Choice [S:CountScheme]
 | old
 | affine (window:AdmittedWindow S.naturalκ)
def Choice.Available : Choice→ℝ→ℝ→Prop
 | .old,_,_ => True
 | .affine w,δ,p => w∈S.windows ∧ w.Available δ p
def Choice.value : Choice→ℝ→ℝ→ℝ→ℝ
 | .old,κ,δ,p => countingR κ δ p
 | .affine w,_,δ,p => w.value δ p
def Choice.cutoff : Choice→ℝ→ℝ→ℝ→ℝ
 | .old,κ,δ,p => Cycle25DetectorRowCount.cutoff δ p κ
 | .affine w,_,δ,p => w.cutoff δ p

theorem envelope_attained (κ δ p:ℝ) :
 ∃c:Choice,c.Available δ p ∧ c.value κ δ p=envelope κ δ p := by
 rcases QRH.Record12518109Return.finiteEnvelope_attained
  QRH.Record12518109Return.countingR admittedBranches κ δ p with h | ⟨b,hb,ha,heq⟩
 · exact ⟨.old,trivial,h.symm⟩
 · rcases List.mem_map.mp hb with ⟨w,hw,rfl⟩
   exact ⟨.affine w,⟨hw,ha⟩,heq.symm⟩
def selectedChoice (κ δ p:ℝ) : Choice := Classical.choose (envelope_attained κ δ p)
theorem selectedChoice_available (κ δ p:ℝ) : (selectedChoice κ δ p).Available δ p :=
 (Classical.choose_spec (envelope_attained κ δ p)).1
theorem selectedChoice_value (κ δ p:ℝ) : (selectedChoice κ δ p).value κ δ p=envelope κ δ p :=
 (Classical.choose_spec (envelope_attained κ δ p)).2
def selectedCutoff (κ δ p:ℝ) : ℝ := (selectedChoice κ δ p).cutoff κ δ p

theorem Choice.cutoff_bounds (c:Choice) {κ δ p:ℝ} (ha:c.Available δ p)
 (hk:7/10≤κ) (hkhi:κ≤3/4) (hδ:δ∈Set.Icc 0 (3/4)) (hp:p∈Set.Icc 0 (1/2)) :
 1≤c.cutoff κ δ p ∧ c.cutoff κ δ p≤3/2 := by
 cases c with
 | old => exact Cycle25DetectorRowCount.cutoff_bounds hδ.1 hδ.2 hp.1 hp.2 hk hkhi
 | affine w => exact w.cutoff_bounds ha.2.1 ha.2.2

theorem selectedCutoff_bounds {κ δ p:ℝ}
 (hk:7/10≤κ) (hkhi:κ≤3/4) (hδ:δ∈Set.Icc 0 (3/4)) (hp:p∈Set.Icc 0 (1/2)) :
 1≤selectedCutoff κ δ p ∧ selectedCutoff κ δ p≤3/2 :=
 Choice.cutoff_bounds _ (selectedChoice_available κ δ p) hk hkhi hδ hp
end GenericCount
end
end QRH.RH20261023Return
#print axioms QRH.RH20261023Return.GenericCount.envelope_attained
#print axioms QRH.RH20261023Return.GenericCount.selectedCutoff_bounds
