/- Repeated marks: fork of Collet's generic return module PhysicalDirect.SourcePools (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Actual physical numerator source/normalizer closure, adapted Gao/Hailey Collet/OpenAI; Apache-2.0. -/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.ReturnD.Schedule
import Submissions.arvi_repeated_marks_on_sil_face_20261025.ReturnD.PhysicalDirect.Helpers
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeNormalizer
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
open scoped Classical BigOperators ContDiff
open Filter
namespace QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect.Source
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
variable [Geometry.Parameters] [Geometry.BoundsR] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
open OAI.SevenEighths HeckeFamily ProbePhysical ProbeHighRowFamily Cycle25ProbeFinalAssembly
open PrincipalSignalComparison ProbePrincipalResidueActual ProbeRaySlots PrincipalMellinResidues
open Cycle25.Numerator Cycle25.Weighted.Numerator

theorem source_pools_nonempty (D : BaselineData) (F : BaselineSourceData D) :
    ∀ᶠZ : ℝ in atTop,∀j : Fin D.N,(sourcePrimePool F Z j).Nonempty := by
  have hpos : ∀j : Fin D.N,tsupport F.w⊆Set.Ioi 0 := by
    intro j
    exact F.positive_support
  have hh := power_ray_mass_and_normalizer F.modulus ⊤ le_top F.S (fun _ : Fin D.N=>F.w)
    1 2 (by norm_num) (by norm_num) (fun _=>F.support) (fun _=>F.smooth)
    (fun _=>F.compact) hpos (fun _ x=>(F.bounded x).1) (fun _=>F.nonzero)
    D.length D.slots_pos (D.t/8) (by have:=D.t_pos; positivity)
  filter_upwards [hh] with Z hm
  intro j
  by_contra he
  have he0 := Finset.not_nonempty_iff_eq_empty.mp he
  have hzero : slotMass (sourcePrimePool F Z)
      (residueWeights (fun _=>F.w) (fun i=>Z^(D.length i))) j=0 := by
    simp only [slotMass,he0,Finset.sum_empty]
  have hp := hm.1 j
  change 0 < slotMass (sourcePrimePool F Z) (residueWeights (fun _=>F.w) (fun i=>Z^(D.length i))) j at hp
  rw [hzero] at hp
  exact lt_irrefl _ hp
end QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect.Source
