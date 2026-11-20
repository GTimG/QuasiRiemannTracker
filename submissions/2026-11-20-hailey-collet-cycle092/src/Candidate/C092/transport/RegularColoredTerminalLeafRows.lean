/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
Literal independently colored StrongPair leaves on actual sixth-free fibers,
retaining the actual original/reference componentwise rectangle.
-/
import Candidate.C092.transport.RegularColoredTerminalLeafHigh
import Candidate.C092.transport.RegularColoredTerminalLeafLowSelected
import Submissions.sil_density_split_20261026.CubeFree.Packet.GroupedAt

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ConcreteTraceCRT
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion CenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional CenteredMomentFirstAmplificationChoice
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondCanonical
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSectorLocalization
open LocalMoment ProbePhysical Record12518109GainRoot
open QRH.Cycle092 QRH.Cycle092.WholeSlot QRH.Cycle092.SixthCore
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Packet.Reduce
open ProfileSeparation (commonPair scale pairWeight scale_pos)
open OAI.SevenEighths.CenteredMomentEnergyBands (length)
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance c092LocalInst_Candidate_C092_transport_RegularColoredTerminalLeafRows_b9b4e3b4d2d96313_001 (M : Id) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {L : ℝ}


/-- The high and low sources inspect precisely the same complete original
mark response, on T rather than on an unrelated carrier or lower bound. -/
theorem terminal_original_response_eq {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
    (hHr : RayOrthogonality.globalUnits rayM ≤ Hr) (T : Finset Slot)
    (old base : Character) (θ : Slot→RayQuotient.Characters rayM Hr) (W : ℝ→ℂ)
    (U pay t : ℝ) (w σ v : Slot→ℝ) (u : FreeRow) :
    LowActual.response U pay (fun i:T=> w i.val)
      (fun i=>‖StrongPair.originalMark rayM Hr hHr old base θ W U w σ v t i.val u‖^2)=
      LowActual.originalResponse old pmask 1 t U pay (fun i:T=> w i.val)
        (originalPools rayM Hr 2 U (fun i:T=> w i.val))
        (originalCoefficients rayM Hr hHr base (fun i:T=>θ i.val) W U
          (fun i:T=> w i.val) (fun i:T=>σ i.val) (fun i:T=> v i.val))
        (fun i:T=> U^(w i.val)) u.val := rfl

/-- An exact low/high/medium partition of the actual finite original source.
No estimate or row count occurs in this identity. -/
theorem terminal_energy_response_partition {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (T : Finset Slot) (s : Finset FreeRow) (η₁ η₂ : Character) (W₁ W₂ : ℝ→ℂ)
    (t₁ t₂ X₁ X₂ : ℝ) (mark : Slot→FreeRow→ℂ) (response : FreeRow→ℝ)
    {threshold upper : ℝ} (h : threshold≤ upper) :
    StrongPair.finiteEnergyOn T s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark=
      StrongPair.finiteEnergyOn T (s.filter (fun u=> response u≤ threshold)) η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark+
      StrongPair.finiteEnergyOn T (s.filter (fun u=> upper< response u)) η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark+
      StrongPair.finiteEnergyOn T (s.filter (fun u=> threshold< response u ∧ response u≤ upper))
        η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark := by
  simp only [StrongPair.finiteEnergyOn,Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hl : response u≤ threshold
  · have hh : ¬upper< response u := not_lt.mpr (hl.trans h)
    simp only [hl,hh,not_lt.mpr hl,false_and,ite_true,ite_false,add_zero]
  · by_cases hh : upper< response u
    · have hm : ¬(threshold< response u ∧ response u≤ upper) := fun hm=> not_le.mpr hh hm.2
      simp only [hl,hh,hm,ite_false,ite_true,zero_add,add_zero]
    · have hm : threshold< response u ∧ response u≤ upper := ⟨lt_of_not_ge hl,le_of_not_gt hh⟩
      simp [hl,hh,hm,not_le.mp hl,not_lt.mp hh]

/-- Partition by actual row-ticket keys before invoking a source on each
class. The whole original ordinary and mark factors are unchanged. -/
theorem terminal_energy_ticket_partition {Slot Key : Type} [Fintype Slot] [DecidableEq Slot]
    [Fintype Key] [DecidableEq Key] (T : Finset Slot) (s : Finset FreeRow)
    (η₁ η₂ : Character) (W₁ W₂ : ℝ→ℂ) (t₁ t₂ X₁ X₂ : ℝ)
    (mark : Slot→FreeRow→ℂ) (key : FreeRow→Key) :
    StrongPair.finiteEnergyOn T s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark=
      ∑k:Key,StrongPair.finiteEnergyOn T (s.filter (fun u=> key u=k)) η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark := by
  simp only [StrongPair.finiteEnergyOn,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  simp

#print axioms terminal_original_response_eq
#print axioms terminal_energy_response_partition
#print axioms terminal_energy_ticket_partition
end
end QRH.Cycle092.RegularColoredForward
