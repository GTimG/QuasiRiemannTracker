/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0.
   The tighter schedule preserves the reserve needed by the final sources. -/
import Candidate.Target830.Marked.GeometryLiteralRawMax


set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.SaturatedPlain
noncomputable section
open scoped ContDiff
open Cycle63Moment Cycle63MarkedPlain

def fineRawRate : ℝ := 1/1000000000000000000

def fineRawBin : ℝ := 1/100000000000000

def fineRawWitness : ℝ := 1/1000000000000000000000000

def fineRawPad : ℝ := fineRawRate

def fineRawCore : ℝ := 3/4

def fineRawTail : ℝ := 1/1000000000

def fineRawTiny (N : ℕ) : ℝ := 1/(10000000000000*((N:ℝ)+1))

def fineRawMesh : ℝ := min (markedPlainMesh (3/4) fineRawRate) fineRawRate

def fineHighRawFee : ℝ := 1/10000000000

/-- Every field is fixed before moving source labels and heights. The mesh
field is independent of cardinality; only the tiny-slot loss depends on N. -/
structure FineMarkedSchedule (P : HighSourceParameters) (N : ℕ)
    (W : ℝ→ℂ) (lo hi : ℝ) : Prop where
  slot : P.Wslot=W
  slotCap : P.B₀=2
  sigmaLo : lo ≤ P.σmin
  sigmaHi : P.σmax ≤ hi
  degree : P.d=31
  mask : 0 ≤ P.Bmask
  heightZero : P.τ<fineRawCore/2
  heightWitness : 4*P.τ<fineRawCore*fineRawWitness
  buffer : 12*P.e*((22:ℝ)+2)+8*fineRawWitness+2*fineRawWitness ≤ fineRawRate/2
  slotLoss : 2*P.εslot*P.d ≤ fineRawBin*fineRawTiny N

theorem fine_raw_mesh_gates : 0<fineRawMesh ∧
    fineRawMesh ≤ markedPlainMesh (3/4) fineRawRate ∧ fineRawMesh ≤ fineRawRate := by
  have h:=markedPlainMesh_pos (show (3/4:ℝ) ≤ 3/4 by rfl)
    (show 0<fineRawRate by norm_num [fineRawRate])
  exact ⟨lt_min h (by norm_num [fineRawRate]),min_le_left _ _,min_le_right _ _⟩

theorem fine_raw_tiny_gates (N : ℕ) :
    0<fineRawTiny N ∧ (N:ℝ)*fineRawTiny N ≤ 1/10000000000000 := by
  have hp : 0<fineRawTiny N := by unfold fineRawTiny;positivity
  have he : fineRawTiny N*(10000000000000*((N:ℝ)+1))=1 :=
    div_mul_cancel₀ _ (by positivity)
  exact ⟨hp,by nlinarith⟩

theorem fine_raw_tiny_antitone {N M : ℕ} (hN : N ≤ M) : fineRawTiny M ≤ fineRawTiny N := by
  unfold fineRawTiny
  apply one_div_le_one_div_of_le (by positivity)
  have hn : (N:ℝ) ≤ M := by exact_mod_cast hN
  nlinarith

theorem FineMarkedSchedule.of_card_le {P : HighSourceParameters} {N Nbudget : ℕ}
    {W : ℝ→ℂ} {lo hi : ℝ} (h : FineMarkedSchedule P Nbudget W lo hi)
    (hN : N ≤ Nbudget) : FineMarkedSchedule P N W lo hi := by
  refine {h with slotLoss:=h.slotLoss.trans ?_}
  exact mul_le_mul_of_nonneg_left (fine_raw_tiny_antitone hN) (by norm_num [fineRawBin])

def fineGeometryMesh (oldMesh : ℝ) : ℝ := min oldMesh (fineRawMesh*fineRawCore/64)



end
end OAI.SevenEighths.SaturatedPlain
