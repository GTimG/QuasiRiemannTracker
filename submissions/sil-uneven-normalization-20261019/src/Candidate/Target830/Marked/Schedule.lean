import Candidate.Target830.Marked.GeometryLiteralRawMax
import Candidate.Target830.Parameters

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Marked830Plain
noncomputable section
open scoped ContDiff
open Cycle63Moment Cycle63MarkedPlain

def rawRate830 : ℝ := 1/100000000000000

def rawBin830 : ℝ := 1/10000000000

def rawWitness830 : ℝ := 1/1000000000000000000

def rawPad830 : ℝ := rawRate830

def rawCore830 : ℝ := 3/4

def rawTail830 : ℝ := 1/1000000000

def rawTiny830 (N : ℕ) : ℝ := 1/(1000000000*((N:ℝ)+1))

def rawMesh830 : ℝ := min (markedPlainMesh (3/4) rawRate830) rawRate830

/-- Every field is fixed before moving source labels and heights. The mesh
field is independent of cardinality; only the tiny-slot loss depends on N. -/
structure MarkedSchedule830 (P : HighSourceParameters) (N : ℕ)
    (W : ℝ→ℂ) (lo hi : ℝ) : Prop where
  slot : P.Wslot=W
  slotCap : P.B₀=2
  sigmaLo : lo ≤ P.σmin
  sigmaHi : P.σmax ≤ hi
  degree : P.d=31
  mask : 0 ≤ P.Bmask
  heightZero : P.τ<rawCore830/2
  heightWitness : 4*P.τ<rawCore830*rawWitness830
  buffer : 12*P.e*((22:ℝ)+2)+8*rawWitness830+2*rawWitness830 ≤ rawRate830/2
  slotLoss : 2*P.εslot*P.d ≤ rawBin830*rawTiny830 N

theorem raw_mesh830_gates : 0<rawMesh830 ∧
    rawMesh830 ≤ markedPlainMesh (3/4) rawRate830 ∧ rawMesh830 ≤ rawRate830 := by
  have h:=markedPlainMesh_pos (show (3/4:ℝ) ≤ 3/4 by rfl)
    (show 0<rawRate830 by norm_num [rawRate830])
  exact ⟨lt_min h (by norm_num [rawRate830]),min_le_left _ _,min_le_right _ _⟩

theorem raw_tiny830_gates (N : ℕ) :
    0<rawTiny830 N ∧ (N:ℝ)*rawTiny830 N ≤ 1/1000000000 := by
  have hp : 0<rawTiny830 N := by unfold rawTiny830;positivity
  have he : rawTiny830 N*(1000000000*((N:ℝ)+1))=1 :=
    div_mul_cancel₀ _ (by positivity)
  exact ⟨hp,by nlinarith⟩

theorem raw_core830_bound (plane : Target830.SourcePlane) :
    rawCore830 ≤ (4/5)*(1-6*plane.rootCutoff) := by
  cases plane <;> norm_num [rawCore830,Target830.SourcePlane.rootCutoff]


theorem raw_tiny830_antitone {N M : ℕ} (hN : N ≤ M) : rawTiny830 M ≤ rawTiny830 N := by
  unfold rawTiny830
  apply one_div_le_one_div_of_le (by positivity)
  have hn : (N:ℝ) ≤ M := by exact_mod_cast hN
  nlinarith

theorem MarkedSchedule830.of_card_le {P : HighSourceParameters} {N Nbudget : ℕ}
    {W : ℝ→ℂ} {lo hi : ℝ} (h : MarkedSchedule830 P Nbudget W lo hi)
    (hN : N ≤ Nbudget) : MarkedSchedule830 P N W lo hi := by
  refine {h with slotLoss:=h.slotLoss.trans ?_}
  exact mul_le_mul_of_nonneg_left (raw_tiny830_antitone hN) (by norm_num [rawBin830])

def geometryMesh830 (oldMesh : ℝ) : ℝ := min oldMesh (rawMesh830*rawCore830/64)

theorem geometry_mesh830_gates (oldMesh : ℝ) (hold : 0<oldMesh) :
    0<geometryMesh830 oldMesh ∧ geometryMesh830 oldMesh ≤ oldMesh ∧
      31*geometryMesh830 oldMesh ≤ rawMesh830*rawCore830 := by
  have hm:=raw_mesh830_gates.1
  have hc : 0<rawCore830 := by norm_num [rawCore830]
  have hcap : geometryMesh830 oldMesh ≤ rawMesh830*rawCore830/64 := min_le_right _ _
  exact ⟨lt_min hold (by positivity),min_le_left _ _,by nlinarith⟩

theorem MarkedSchedule830.width_cap {P : HighSourceParameters} {N : ℕ}
    {W : ℝ→ℂ} {lo hi mesh oldMesh w : ℝ}
    (h : MarkedSchedule830 P N W lo hi) (hm : mesh ≤ geometryMesh830 oldMesh)
    (hw : w ≤ P.d*mesh) : w ≤ rawMesh830*rawCore830 := by
  rw [h.degree] at hw
  have hc : geometryMesh830 oldMesh ≤ rawMesh830*rawCore830/64 := min_le_right _ _
  have hp : 0 ≤ rawMesh830*rawCore830 := mul_nonneg raw_mesh830_gates.1.le (by norm_num [rawCore830])
  nlinarith

end
end OAI.SevenEighths.Marked830Plain
#print axioms OAI.SevenEighths.Marked830Plain.raw_mesh830_gates
#print axioms OAI.SevenEighths.Marked830Plain.raw_core830_bound
