import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorRawBranches

/- Uses the original fiber and original moment record. The auxiliary offset
   (capacity-3/4)/2 may be negative; actual capacity is the analytic parameter.
   These are count implications conditional on the original moment estimates. -/
set_option autoImplicit false
namespace BelowSevenEighthsTight.FiberExtension
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorSupportedWitness
open HeckeDetectorRawFiber HeckeDetectorInverseFiberCount HeckeDetectorPlainFiberCount
variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

abbrev CapacityMoments (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (capacity c κ C height εm : ℝ) : Prop :=
  Moments F ((capacity-3/4)/2) c κ C height εm

theorem capacity_moments_original_parameter
    (F : Fiber M H Label Slot U a ε tstar T allowance i) (Δ c κ C height εm : ℝ) :
    CapacityMoments F (3/4+2*Δ) c κ C height εm ↔ Moments F Δ c κ C height εm := by
  have he : ((3/4:ℝ)+2*Δ-3/4)/2=Δ := by ring
  simp only [CapacityMoments,he]

theorem inverse_marked_count (F : Fiber M H Label Slot U a ε tstar T allowance i)
    {capacity c κ C height εm : ℝ} (moments : CapacityMoments F capacity c κ C height εm)
    (hU : 1<U) (ha : 1/2≤a) (hC : 0≤C) (hh : 0≤height)
    (hf : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (z : ℝ) (hz : 0≤z) (hz' : z≤7/37) (hcap1 : F.r+2*z<1) (hcap2 : 2*F.r+8*z<3) :
    (F.rows.card : ℝ)≤(12*(1+height)*C)*
      U^(1-(2*a-1)*F.r-2*F.q*z+2*ε+(2*a-1)*F.mesh+εm) := by
  exact F.inverse_marked_count moments hU ha hC hh hf z hz hz' hcap1 hcap2

theorem plain_marked_count (F : Fiber M H Label Slot U a ε tstar T allowance i)
    {capacity c κ C height εm : ℝ} (moments : CapacityMoments F capacity c κ C height εm)
    (hU : 1<U) (ha : 1/2≤a) (hcapacity : 0≤capacity) (hC : 0≤C) (hh : 0≤height)
    (hf : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (z : ℝ) (hz : 0≤z) (hz' : z≤7/37) (hcap : 2*F.m+6*capacity*z≤1) :
    (F.rows.card : ℝ)≤(192*(1+height)*C)*
      U^(1-2*(2*a-1)*F.m-2*F.q*z+4*ε+(2*a-1)*F.mesh+εm) := by
  have hm := moments.plain_marked
  have he : (3/4:ℝ)+2*((capacity-3/4)/2)=capacity := by ring
  rw [he] at hm
  exact plain_fiber_count M H F.rows F.nonempty F.family U a ε tstar T allowance i hU ha
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    F.slots (fun u => u.val) F.profile F.upper F.widths F.bin F.external F.mesh F.binWidth
    z capacity εm C height
    F.mesh_nonneg F.binWidth_pos F.widths_pos F.widths_mesh (by linarith [F.supply])
    hz (hz'.trans F.supply) F.fixed_bin hcapacity hC hh hf hcap hm

theorem plain_unmarked_count (F : Fiber M H Label Slot U a ε tstar T allowance i)
    {capacity c κ C height εm : ℝ} (moments : CapacityMoments F capacity c κ C height εm)
    (hU : 1<U) (ha : 0≤a) (hC : 0≤C) (hh : 0≤height)
    (hf : 2*Real.pi*allowance+(3*i : ℕ)*T≤height) :
    (F.rows.card : ℝ)≤(192*(1+height)*C)*
      U^(max 1 (2*F.m)-2*(2*a-1)*F.m+4*ε+εm) := by
  exact F.plain_unmarked_count moments hU ha hC hh hf

#print axioms inverse_marked_count
#print axioms plain_marked_count
#print axioms plain_unmarked_count
end
end BelowSevenEighthsTight.FiberExtension
