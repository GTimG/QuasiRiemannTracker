import Candidate.Cycle63.Marked.ActualMarkedPlain
import Candidate.Cycle63.Moment.HighSourceEnergy

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical ContDiff
open Cycle63Moment

/-- Scalar marked-count parameters are fixed before the slot dictionary. -/
def markedRate : ℝ := 1/10000000000

def markedBinWidth : ℝ := 1/100000

def markedRootCutoff : ℝ := 1/250

def markedCoreMin : ℝ := 488/625

def markedPad : ℝ := 1/10000000

def markedWitnessRate : ℝ := markedRate/128

def markedTinyWidth (N : ℕ) : ℝ := 1/(2000*((N:ℝ)+1))

def markedRawMesh : ℝ := min (markedPlainMesh (94/125) markedRate) markedRate

/-- Intersecting the original mesh with this scalar cap is independent of
all later choices of cardinality, profiles, characters and height degrees. -/
def markedGeometryMesh (oldMesh : ℝ) : ℝ :=
  min oldMesh (markedRawMesh*markedCoreMin/64)

/-- The old common height can be decreased after all density degrees have
been fixed, preserving every previously paid height inequality. -/
def markedHeight (oldHeight : ℝ) : ℝ :=
  min oldHeight (min (markedCoreMin/4) (markedCoreMin*markedWitnessRate/8))

theorem marked_scalar_gates :
    0< markedRate ∧ markedRate≤1/1000 ∧
    0< markedBinWidth ∧ markedBinWidth≤(17/25:ℝ)/2 ∧
    0≤ markedRootCutoff ∧ markedRootCutoff<1/6 ∧
    0< markedCoreMin ∧ markedCoreMin=(4/5:ℝ)*(1-6*markedRootCutoff) ∧
    0< markedPad ∧ (130:ℝ)+markedPad≤131 ∧
    0< markedWitnessRate ∧ markedWitnessRate≤1 ∧
    0<(1/10:ℝ) ∧ (1/10:ℝ)≤5/7 := by
  norm_num [markedRate,markedBinWidth,markedRootCutoff,markedCoreMin,markedPad,markedWitnessRate]

theorem marked_raw_mesh_gates :
    0< markedRawMesh ∧ markedRawMesh≤ markedPlainMesh (94/125) markedRate ∧
      markedRawMesh≤ markedRate := by
  have h := markedPlainMesh_pos (show (3/4:ℝ)≤94/125 by norm_num)
    (show 0< markedRate by norm_num [markedRate])
  exact ⟨lt_min h (by norm_num [markedRate]),min_le_left _ _,min_le_right _ _⟩

theorem marked_geometry_mesh_gates (oldMesh : ℝ) (hold : 0<oldMesh) :
    0< markedGeometryMesh oldMesh ∧ markedGeometryMesh oldMesh≤oldMesh ∧
      31*markedGeometryMesh oldMesh≤ markedRawMesh*markedCoreMin := by
  have hm := marked_raw_mesh_gates.1
  have hc : 0< markedCoreMin := by norm_num [markedCoreMin]
  have hcap : markedGeometryMesh oldMesh≤ markedRawMesh*markedCoreMin/64 := min_le_right _ _
  have hp : 0< markedGeometryMesh oldMesh := by unfold markedGeometryMesh;positivity
  exact ⟨hp,min_le_left _ _,by nlinarith⟩

theorem marked_tiny_width_gates (N : ℕ) :
    0< markedTinyWidth N ∧ (N:ℝ)*markedTinyWidth N≤1/2000 := by
  have hpos : 0< markedTinyWidth N := by unfold markedTinyWidth;positivity
  have he : markedTinyWidth N*(2000*((N:ℝ)+1))=1 :=
    div_mul_cancel₀ _ (by positivity)
  exact ⟨hpos,by nlinarith⟩

theorem marked_height_gates (oldHeight : ℝ) (h : 0<oldHeight) :
    0< markedHeight oldHeight ∧ markedHeight oldHeight≤oldHeight ∧
      markedHeight oldHeight< markedCoreMin/2 ∧
      4*markedHeight oldHeight< markedCoreMin*markedWitnessRate := by
  have hc : 0< markedCoreMin := by norm_num [markedCoreMin]
  have hw : 0< markedWitnessRate := by norm_num [markedWitnessRate,markedRate]
  have hpos : 0< markedHeight oldHeight := by unfold markedHeight;positivity
  have hcap : markedHeight oldHeight≤ markedCoreMin/4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hfreq : markedHeight oldHeight≤ markedCoreMin*markedWitnessRate/8 :=
    (min_le_right _ _).trans (min_le_right _ _)
  exact ⟨hpos,min_le_left _ _,by linarith,by nlinarith⟩

theorem marked_height_preserves_budget (oldHeight μ : ℝ) (J : ℕ)
    (h : 2*oldHeight*((J:ℝ)+1)≤μ/8) :
    2*markedHeight oldHeight*((J:ℝ)+1)≤μ/8 := by
  have ht : markedHeight oldHeight≤oldHeight := min_le_left _ _
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (by norm_num))
    (by positivity)).trans h


/-- The unchanged selector buffer pays the marked detector's buffer budget. -/
theorem marked_buffer_budget (μ e : ℝ) (hμ : μ≤1/100000000)
    (he : e≤μ/294912) :
    12*e*((22:ℝ)+2)+8*markedWitnessRate+2*markedWitnessRate≤ markedRate/2 := by
  norm_num [markedWitnessRate,markedRate]
  linarith

/-- The original slot error already fits the tiny-width amplitude gate. -/
theorem marked_slot_loss_gate (μ δ : ℝ) (N : ℕ)
    (hμ : μ≤1/100000000)
    (hδ : δ≤μ/(64*(31+1)*((N:ℝ)+1))) :
    2*δ*31≤ markedBinWidth*markedTinyWidth N := by
  have hp : 0<2000*((N:ℝ)+1) := by positivity
  have hd := (le_div_iff₀ (by positivity : 0<64*(31+1)*((N:ℝ)+1))).mp hδ
  rw [markedBinWidth,markedTinyWidth,mul_one_div]
  apply (le_div_iff₀ hp).mpr
  nlinarith


/-- The large-root tail is stronger than the full capped marked gain. -/
theorem marked_tail_dominates (D ρ ordloss S : ℝ) (hD : 0≤D)
    (hρ : (19/54:ℝ)≤ρ) (hord : 0≤ordloss) :
    min ((224/1755)*min S ((13/400)*((1-6*markedRootCutoff)*D)))
      (D*markedRootCutoff*(6*(ρ+ordloss)-1-(9/100))) =
        (224/1755)*min S ((13/400)*((1-6*markedRootCutoff)*D)) := by
  apply min_eq_left
  have hcap := mul_le_mul_of_nonneg_left (min_le_right S ((13/400)*((1-6*markedRootCutoff)*D)))
    (by norm_num : (0:ℝ)≤224/1755)
  have ht := mul_le_mul_of_nonneg_left (show (919/900:ℝ)≤6*(ρ+ordloss)-1-(9/100) by linarith)
    (show 0≤D*markedRootCutoff by unfold markedRootCutoff;positivity)
  dsimp [markedRootCutoff] at hcap ht ⊢
  nlinarith

/-- All count losses fit well below the geometric reserve, uniformly in
the original live supply and every actual raw exponent up to 130. -/
theorem marked_raw_error_budget (D S ρ mesh μ normfee heightfee : ℝ)
    (hD : D≤130) (hS : S≤1/25) (hρ : ρ≤1) (hmesh : mesh≤ markedRate)
    (hμ : μ≤1/100000000) (hnorm : normfee≤μ/32) (hheight : heightfee≤μ/8) :
    D*markedRate+2*markedBinWidth*S+
      131*(156*markedRate+mesh+markedRate+markedRate)+markedPad*ρ+normfee+heightfee≤
        (1/200000:ℝ) := by
  norm_num [markedRate,markedBinWidth,markedPad] at hmesh ⊢
  linarith

/-- The scheduled raw count has exactly the signed live-width gain used
by the allocation ledger, with every analytic addition already paid. -/
theorem marked_raw_exponent_paid (D S ρ δ mesh μ normfee heightfee : ℝ)
    (hD0 : 0≤D) (hD : D≤130) (hS : S≤1/25)
    (hρ0 : (19/54:ℝ)≤ρ) (hρ : ρ≤1) (hmesh : mesh≤ markedRate)
    (hμ : μ≤1/100000000) (hnorm : normfee≤μ/32) (hheight : heightfee≤μ/8) :
    D*(ρ+markedRate)+(δ+2*markedBinWidth)*S+
      131*(156*markedRate+mesh+markedRate+markedRate)+markedPad*ρ-
      min ((224/1755)*min S ((13/400)*((1-6*markedRootCutoff)*D)))
        (D*markedRootCutoff*(6*(ρ+markedRate)-1-(9/100)))+normfee+heightfee≤
      D*ρ+δ*S-(224/1755)*min S ((13/400)*((1-6*markedRootCutoff)*D))+(1/200000:ℝ) := by
  rw [marked_tail_dominates D ρ markedRate S hD0 hρ0 (by norm_num [markedRate])]
  have h := marked_raw_error_budget D S ρ mesh μ normfee heightfee hD hS hρ hmesh hμ hnorm hheight
  nlinarith

theorem marked_mesh_transfer (oldMesh mesh : ℝ) (hmesh : mesh≤ markedGeometryMesh oldMesh)
    {w : ℝ} (hw : w≤31*mesh) : w≤ markedRawMesh*markedCoreMin := by
  have hc : markedGeometryMesh oldMesh≤ markedRawMesh*markedCoreMin/64 := min_le_right _ _
  have hp : 0≤ markedRawMesh*markedCoreMin := mul_nonneg marked_raw_mesh_gates.1.le
    (by norm_num [markedCoreMin])
  nlinarith

end
end OAI.SevenEighths.Cycle63MarkedPlain

