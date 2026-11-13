/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Closest rational checkpoint supported by the 256-character bound field. Uses Sil's paired marked-anchor
method, the checked zero-decrement source, the actual averaged floor and the
complete return. The inherited all-moduli descent is unchanged. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.ClosestSchedule
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveSource
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.ContactSource
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.SourceClosure
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.PositiveGap.BestEndpoint

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Qrh.TwoSlot.AnchorContinuum.ClosestRational
noncomputable section
open Qrh.TwoSlot.AnchorZeroLoss
open QRH.Record1252270103Return
open QRH.Record12518109Source QRH.Record12518109Existence
open OAI OAI.SevenEighths HeckeFamily
open QRH.PositiveGap.Return (selected_sources_common_mesh)
open QRH.PositiveGap.Return.Tuning (uniform_restrict source_restricts_count source_restricts_physical)
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
local instance : Geometry.Parameters := parameters
local instance : BoundsCore := coarseBounds
local instance : Affine.Return.ImprovedCountScheme Contact.exactLine := Contact.exactScheme
local instance : Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic.PhysicalSchedule := physicalSchedule

/-- One early mesh supplies both native windows, including the low window. -/
theorem count_mesh
    (hC : UniformUnitFaceSource QRH.PositiveGap.Return.countGlobal) (hP : UniformUnitFaceSource QRH.PositiveGap.Return.physicalGlobal)
    (ε : ℝ) (hε : 0 < ε) : ∃ mesh : ℝ, 0 < mesh ∧
      ∀ w ∈ Contact.exactScheme.windows, UnitFaceSource w.face mesh ε := by
  obtain ⟨mesh,hm,hc,hp⟩ := selected_sources_common_mesh hC hP hε
  refine ⟨mesh,hm,?_⟩
  intro w hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  change UnitFaceSource (QRH.PositiveGap.Return.countingSource v.branch) mesh ε
  apply unit_source_restrict (QRH.PositiveGap.Return.supplier_restricts_counting v.branch v.nonold)
  cases v.branch <;> first | exact (v.nonold rfl).elim | exact hc | exact hp

/-- Positive-cost source at the actual physical face. -/
theorem physical_source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
    UniformUnitFaceSource physicalFace := by
  exact PositiveSource.physical_source cost_pos cost_small hβ

/-- Full Hecke supremum bound: every moment/source/schedule input is supplied. -/
theorem beta_le_target : HeckeZeroSupremum.beta ≤ target := by
  apply beta_le_theta_of_initial_source (line := Contact.exactLine)
  intro hgap
  have hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta := by
    have ht : (51/100:ℝ) < target := by norm_num [target,numerator,denominator]
    change target < HeckeZeroSupremum.beta at hgap
    linarith
  have hG := Qrh.PositiveGap.return_source hβ
  have hC : UniformUnitFaceSource QRH.PositiveGap.Return.countGlobal := uniform_restrict source_restricts_count hG
  have hP : UniformUnitFaceSource QRH.PositiveGap.Return.physicalGlobal := uniform_restrict source_restricts_physical hG
  have hcap : 2*HeckeZeroSupremum.beta-1 ≤ Contact.exactScheme.naturalκ :=
    QRH.PositiveGap.Return.Tuning.natural_cap_return
  obtain ⟨A,_,hA⟩ := exists_chosen_initial_source_small_mesh
    (line := Contact.exactLine) hcap (count_mesh hC hP) (physical_source hβ)
    (Contact.exact_fiber_moments hβ) hgap 1 (by norm_num)
  exact ⟨A,hA⟩

/-- Every positive modulus and every Dirichlet character, excluding only the
principal pole. No numerical or analytic premise remains in this theorem. -/
theorem bound {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : target < s.re) (hpole : ¬(χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  Cycle25.dirichlet_of_hecke (by norm_num [target,numerator,denominator])
    (fun η s hs hpole => HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt η
      (beta_le_target.trans_lt hs) hpole) χ s hs hpole

end
end Qrh.TwoSlot.AnchorContinuum.ClosestRational
#print axioms Qrh.TwoSlot.AnchorContinuum.ClosestRational.beta_le_target
#print axioms Qrh.TwoSlot.AnchorContinuum.ClosestRational.bound
