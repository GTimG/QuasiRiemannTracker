import Candidate.Cycle63.Marked.ActualMarkedPlain
import Candidate.Cycle63.Moment.HighSourceEnergy
import Candidate.Cycle63.Arithmetic.Constants

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical ContDiff
open Cycle63Moment

/-- Scalar marked-count parameters are fixed before the slot dictionary. -/
def markedRate : ℝ := Cycle63.Optimization.markedRate

def markedBinWidth : ℝ := Cycle63.Optimization.markedBinWidth

def markedRootCutoff : ℝ := Cycle63.Optimization.markedRootCutoff

def markedCoreMin : ℝ := 4/5*Cycle63.Optimization.coreFactor

def markedPad : ℝ := Cycle63.Optimization.markedPad

def markedWitnessRate : ℝ := markedRate/128

def markedTinyWidth (N : ℕ) : ℝ := Cycle63.Optimization.tinySlotLoss/((N:ℝ)+1)

def markedRawMesh : ℝ := min (markedPlainMesh (Cycle63.Optimization.plainCapacityCost) markedRate) markedRate

/-- Intersecting the original mesh with this scalar cap is independent of
all later choices of cardinality, profiles, characters and height degrees. -/
def markedGeometryMesh (oldMesh : ℝ) : ℝ :=
  min oldMesh (markedRawMesh*markedCoreMin/64)

/-- The old common height can be decreased after all density degrees have
been fixed, preserving every previously paid height inequality. -/
def markedHeight (oldHeight : ℝ) : ℝ :=
  min oldHeight (min (markedCoreMin/4) (markedCoreMin*markedWitnessRate/8))

theorem markedCoreMin_pos : 0< markedCoreMin := by
  have hk := Cycle63.Optimization.coreFactor_bounds
  unfold markedCoreMin
  linarith

theorem marked_raw_mesh_gates :
    0< markedRawMesh ∧ markedRawMesh≤ markedPlainMesh (Cycle63.Optimization.plainCapacityCost) markedRate ∧
      markedRawMesh≤ markedRate := by
  have h := markedPlainMesh_pos (show (3/4:ℝ)≤Cycle63.Optimization.plainCapacityCost by
    norm_num [Cycle63.Optimization.plainCapacityCost])
    (show 0< markedRate by norm_num [markedRate, Cycle63.Optimization.markedRate, Cycle63.Optimization.geometryLossCap, Cycle63.Optimization.lowReserveWeight])
  exact ⟨lt_min h (by norm_num [markedRate, Cycle63.Optimization.markedRate, Cycle63.Optimization.geometryLossCap, Cycle63.Optimization.lowReserveWeight]),min_le_left _ _,min_le_right _ _⟩

theorem marked_geometry_mesh_gates (oldMesh : ℝ) (hold : 0<oldMesh) :
    0< markedGeometryMesh oldMesh ∧ markedGeometryMesh oldMesh≤oldMesh ∧
      31*markedGeometryMesh oldMesh≤ markedRawMesh*markedCoreMin := by
  have hm := marked_raw_mesh_gates.1
  have hc : 0< markedCoreMin := markedCoreMin_pos
  have hcap : markedGeometryMesh oldMesh≤ markedRawMesh*markedCoreMin/64 := min_le_right _ _
  have hp : 0< markedGeometryMesh oldMesh := by unfold markedGeometryMesh;positivity
  exact ⟨hp,min_le_left _ _,by nlinarith⟩

theorem marked_tiny_width_gates (N : ℕ) :
    0< markedTinyWidth N ∧ (N:ℝ)*markedTinyWidth N≤Cycle63.Optimization.tinySlotLoss := by
  have hL := Cycle63.Optimization.tinySlotLoss_pos
  have hN : 0<(N:ℝ)+1 := by positivity
  have hpos : 0< markedTinyWidth N := by unfold markedTinyWidth;positivity
  have he : markedTinyWidth N*((N:ℝ)+1)=Cycle63.Optimization.tinySlotLoss :=
    div_mul_cancel₀ _ hN.ne'
  exact ⟨hpos,by nlinarith⟩

theorem marked_height_gates (oldHeight : ℝ) (h : 0<oldHeight) :
    0< markedHeight oldHeight ∧ markedHeight oldHeight≤oldHeight ∧
      markedHeight oldHeight< markedCoreMin/2 ∧
      4*markedHeight oldHeight< markedCoreMin*markedWitnessRate := by
  have hc : 0< markedCoreMin := markedCoreMin_pos
  have hw : 0< markedWitnessRate := by norm_num [markedWitnessRate, markedRate, Cycle63.Optimization.markedRate, Cycle63.Optimization.geometryLossCap, Cycle63.Optimization.lowReserveWeight]
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
theorem marked_buffer_budget (μ e : ℝ) (hμ : μ≤Cycle63.Optimization.geometryLossCap)
    (he : e≤μ/294912) :
    12*e*((22:ℝ)+2)+8*markedWitnessRate+2*markedWitnessRate≤ markedRate/2 := by
  norm_num [markedWitnessRate, markedRate, Cycle63.Optimization.markedRate, Cycle63.Optimization.geometryLossCap, Cycle63.Optimization.lowReserveWeight] at hμ ⊢
  linarith

/-- The original slot error already fits the tiny-width amplitude gate. -/
theorem marked_slot_loss_gate (μ δ : ℝ) (N : ℕ)
    (hμ : μ≤Cycle63.Optimization.geometryLossCap)
    (hδ : δ≤μ/(64*(31+1)*((N:ℝ)+1))) :
    2*δ*31≤ markedBinWidth*markedTinyWidth N := by
  have hN : 0<(N:ℝ)+1 := by positivity
  have hd := (le_div_iff₀ (by positivity : 0<64*(31+1)*((N:ℝ)+1))).mp hδ
  have hid : markedBinWidth*markedTinyWidth N =
      62*Cycle63.Optimization.geometryLossCap/(2048*((N:ℝ)+1)) := by
    have hu : Cycle63.Optimization.allowanceUnit ≠ 0 := Cycle63.Optimization.allowanceUnit_pos.ne'
    unfold markedBinWidth markedTinyWidth Cycle63.Optimization.tinySlotLoss
      Cycle63.Optimization.markedBinWidth
    field_simp
  rw [hid, le_div_iff₀ (by positivity)]
  nlinarith


/-- The large-root tail is at least the full capped marked gain in every bin of the marked range:
the two are equal at the bin top (`root_cutoff_balance`), and the excess of the tail falls with the
bin. -/
theorem marked_tail_dominates (D ρ ordloss S δ : ℝ) (hD : 0≤D)
    (hδ : Cycle63.Arithmetic.q0≤δ ∧ δ≤Cycle63.Optimization.markedBinTop) (hρ : Cycle63.Optimization.density δ≤ρ)
    (hord : 0≤ordloss) :
    min (Cycle63.Optimization.liveRate δ*min S (Cycle63.Optimization.inverseWidthCap*((1-6*markedRootCutoff)*D)))
      (D*markedRootCutoff*(6*(ρ+ordloss)-1-Cycle63.Optimization.tailSlack)) =
        Cycle63.Optimization.liveRate δ*min S (Cycle63.Optimization.inverseWidthCap*((1-6*markedRootCutoff)*D)) := by
  apply min_eq_left
  have hq := Cycle63.Arithmetic.q0_bounds
  have htop := Cycle63.Optimization.markedBinTop_bounds
  have hw := Cycle63.Optimization.inverseWidthCap_bounds
  have hk := Cycle63.Optimization.markedRootCutoff_bounds
  have hbal := Cycle63.Optimization.root_cutoff_balance
  unfold Cycle63.Optimization.coreFactor at hbal
  unfold markedRootCutoff
  have hδ' : Cycle63.Arithmetic.q0≤δ ∧ δ≤Cycle63.Optimization.markedBinTop := hδ
  have hr0 : 0≤Cycle63.Optimization.liveRate δ := by
    apply le_of_lt
    unfold Cycle63.Optimization.liveRate Cycle63.Optimization.liveRatio Cycle63.Optimization.chosenPerUnit Cycle63.Optimization.plainCapacityCost Cycle63.Optimization.halfGain
    rat_pos [hq, hδ', htop]
  -- The excess of the tail over the live gain at `δ`, less the one at the bin top.
  have hfall : 0 ≤ 100*Cycle63.Optimization.markedRootCutoff-Cycle63.Optimization.inverseWidthCap*(1-6*Cycle63.Optimization.markedRootCutoff)*
      Cycle63.Optimization.liveRatio*(30*(δ+Cycle63.Optimization.markedBinTop)-25-12*δ*Cycle63.Optimization.markedBinTop) := by
    unfold Cycle63.Optimization.liveRatio Cycle63.Optimization.chosenPerUnit Cycle63.Optimization.plainCapacityCost
    apply le_of_lt
    rat_pos [hq, hδ', htop, hw, hk]
  have h5δ : (0:ℝ) < 5-2*δ := by linarith
  have h5d : (0:ℝ) < 5-2*Cycle63.Optimization.markedBinTop := by linarith
  have hid : (Cycle63.Optimization.markedRootCutoff*(6*Cycle63.Optimization.density δ-1-Cycle63.Optimization.tailSlack)-
        Cycle63.Optimization.liveRate δ*(Cycle63.Optimization.inverseWidthCap*(1-6*Cycle63.Optimization.markedRootCutoff)))-
      (Cycle63.Optimization.markedRootCutoff*(6*Cycle63.Optimization.density Cycle63.Optimization.markedBinTop-1-Cycle63.Optimization.tailSlack)-
        Cycle63.Optimization.liveRate Cycle63.Optimization.markedBinTop*(Cycle63.Optimization.inverseWidthCap*(1-6*Cycle63.Optimization.markedRootCutoff))) =
      (Cycle63.Optimization.markedBinTop-δ)*(100*Cycle63.Optimization.markedRootCutoff-Cycle63.Optimization.inverseWidthCap*(1-6*Cycle63.Optimization.markedRootCutoff)*
        Cycle63.Optimization.liveRatio*(30*(δ+Cycle63.Optimization.markedBinTop)-25-12*δ*Cycle63.Optimization.markedBinTop))/
        ((5-2*δ)*(5-2*Cycle63.Optimization.markedBinTop)) := by
    unfold Cycle63.Optimization.density Cycle63.Optimization.liveRate Cycle63.Optimization.halfGain
    field_simp [h5δ.ne', h5d.ne', show (5:ℝ)-δ*2≠0 by linarith,
      show (5:ℝ)-Cycle63.Optimization.markedBinTop*2≠0 by linarith]
    ring
  have hpos : 0 ≤ (Cycle63.Optimization.markedBinTop-δ)*(100*Cycle63.Optimization.markedRootCutoff-Cycle63.Optimization.inverseWidthCap*
      (1-6*Cycle63.Optimization.markedRootCutoff)*Cycle63.Optimization.liveRatio*(30*(δ+Cycle63.Optimization.markedBinTop)-25-12*δ*Cycle63.Optimization.markedBinTop))/
      ((5-2*δ)*(5-2*Cycle63.Optimization.markedBinTop)) :=
    div_nonneg (mul_nonneg (by linarith [hδ.2]) hfall) (by positivity)
  have hcert : Cycle63.Optimization.liveRate δ*(Cycle63.Optimization.inverseWidthCap*(1-6*Cycle63.Optimization.markedRootCutoff)) ≤
      Cycle63.Optimization.markedRootCutoff*(6*Cycle63.Optimization.density δ-1-Cycle63.Optimization.tailSlack) := by
    linarith
  have hcap := mul_le_mul_of_nonneg_left
    (min_le_right S (Cycle63.Optimization.inverseWidthCap*((1-6*Cycle63.Optimization.markedRootCutoff)*D))) hr0
  have htail : D*Cycle63.Optimization.markedRootCutoff*(6*Cycle63.Optimization.density δ-1-Cycle63.Optimization.tailSlack) ≤
      D*Cycle63.Optimization.markedRootCutoff*(6*(ρ+ordloss)-1-Cycle63.Optimization.tailSlack) := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hD (by linarith [hk.1]))
    linarith
  have hscale := mul_le_mul_of_nonneg_left hcert hD
  calc _ ≤ Cycle63.Optimization.liveRate δ*(Cycle63.Optimization.inverseWidthCap*((1-6*Cycle63.Optimization.markedRootCutoff)*D)) := hcap
    _ = D*(Cycle63.Optimization.liveRate δ*(Cycle63.Optimization.inverseWidthCap*(1-6*Cycle63.Optimization.markedRootCutoff))) := by ring
    _ ≤ D*(Cycle63.Optimization.markedRootCutoff*(6*Cycle63.Optimization.density δ-1-Cycle63.Optimization.tailSlack)) := hscale
    _ = D*Cycle63.Optimization.markedRootCutoff*(6*Cycle63.Optimization.density δ-1-Cycle63.Optimization.tailSlack) := by ring
    _ ≤ _ := htail

/-- All count losses fit well below the geometric reserve, uniformly in
the original live supply and every actual raw exponent up to 130. -/
theorem marked_raw_error_budget (D S ρ mesh μ normfee heightfee : ℝ)
    (hD : D≤130) (hS : S≤Cycle63.Optimization.slotTop) (hρ : ρ≤1) (hmesh : mesh≤ markedRate)
    (hμ : μ≤Cycle63.Optimization.geometryLossCap) (hnorm : normfee≤μ/32) (hheight : heightfee≤μ/8) :
    D*markedRate+2*markedBinWidth*S+
      131*(156*markedRate+mesh+markedRate+markedRate)+markedPad*ρ+normfee+heightfee≤
        Cycle63.Optimization.markedLoss := by
  norm_num [markedRate,markedBinWidth,Cycle63.Optimization.markedBinWidth,markedPad,
    Cycle63.Optimization.markedRate, Cycle63.Optimization.markedPad, Cycle63.Optimization.markedLoss,
    Cycle63.Optimization.geometryLossCap, Cycle63.Optimization.lowReserveWeight,
    Cycle63.Optimization.slotTop, Cycle63.Optimization.allowanceUnit] at hS hmesh hμ ⊢
  linarith

/-- The scheduled raw count has exactly the signed live-width gain used
by the allocation ledger, with every analytic addition already paid. -/
theorem marked_raw_exponent_paid (D S ρ δ mesh μ normfee heightfee : ℝ)
    (hD0 : 0≤D) (hD : D≤130) (hS : S≤Cycle63.Optimization.slotTop)
    (hδ : Cycle63.Arithmetic.q0≤δ ∧ δ≤Cycle63.Optimization.markedBinTop) (hρδ : Cycle63.Optimization.density δ≤ρ)
    (hρ : ρ≤1) (hmesh : mesh≤ markedRate)
    (hμ : μ≤Cycle63.Optimization.geometryLossCap) (hnorm : normfee≤μ/32) (hheight : heightfee≤μ/8) :
    D*(ρ+markedRate)+(δ+2*markedBinWidth)*S+
      131*(156*markedRate+mesh+markedRate+markedRate)+markedPad*ρ-
      min (Cycle63.Optimization.liveRate δ*min S ((Cycle63.Optimization.inverseWidthCap)*((1-6*markedRootCutoff)*D)))
        (D*markedRootCutoff*(6*(ρ+markedRate)-1-(Cycle63.Optimization.tailSlack)))+normfee+heightfee≤
      D*ρ+δ*S-Cycle63.Optimization.liveRate δ*min S ((Cycle63.Optimization.inverseWidthCap)*((1-6*markedRootCutoff)*D))+
        Cycle63.Optimization.markedLoss := by
  rw [marked_tail_dominates D ρ markedRate S δ hD0 hδ hρδ (by norm_num [markedRate, Cycle63.Optimization.markedRate, Cycle63.Optimization.geometryLossCap, Cycle63.Optimization.lowReserveWeight])]
  have h := marked_raw_error_budget D S ρ mesh μ normfee heightfee hD hS hρ hmesh hμ hnorm hheight
  nlinarith

theorem marked_mesh_transfer (oldMesh mesh : ℝ) (hmesh : mesh≤ markedGeometryMesh oldMesh)
    {w : ℝ} (hw : w≤31*mesh) : w≤ markedRawMesh*markedCoreMin := by
  have hc : markedGeometryMesh oldMesh≤ markedRawMesh*markedCoreMin/64 := min_le_right _ _
  have hp : 0≤ markedRawMesh*markedCoreMin := mul_nonneg marked_raw_mesh_gates.1.le
    markedCoreMin_pos.le
  nlinarith

end
end OAI.SevenEighths.Cycle63MarkedPlain

