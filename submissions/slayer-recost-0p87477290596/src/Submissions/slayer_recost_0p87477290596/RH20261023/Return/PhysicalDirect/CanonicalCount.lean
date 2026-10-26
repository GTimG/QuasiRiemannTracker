/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Original retained full-class and error-mask count transport, adapted Gao/Hailey Collet/OpenAI; Apache-2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.Schedule
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.PhysicalDirect.PhysicalSourceCount
import Submissions.hailey_collet_1252270103.Cycle61.Assembly.Count.SourceCount
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorDictionary
open QRH.RH20261023Return

namespace QRH.RH20261023Return.GenericPhysical.PhysicalDirect
variable [Geometry.Parameters] [Geometry.Bounds] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
open OAI OAI.SevenEighths QRH.Record12518109Count
open QRH.RH20261023Return.GenericPhysical (SourceData)
noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
open HeckeFamily HeckeInverseAmplification HeckeDetectorPhysicalSelection ProbeHighRowFamily

def canonicalFamily (D : BaselineData) (F : SourceData) (Z : ℝ) (z : ℂ) : FreeRow→Fin D.N→ℂ :=
  fun u j=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val
    (fun y=>(F.w y:ℂ)) 2 (Z^(D.length j)) z

theorem physical_eq_canonical (D : BaselineData) (F : SourceData) (Z d : ℝ)
    (hZ : 0<Z) (hd : d≠0) (z : ℂ) :
    physical F.modulus ⊤ (fun u : FreeRow=>u.val) (fun _ y=>(F.w y:ℂ))
      (fun _=>2) (fun j=>D.length j/d) (fun _=>z) (Z^d) = canonicalFamily D F Z z := by
  funext u j
  exact source_physical_amplitude F.modulus ⊤ D.length (fun _ y=>(F.w y:ℂ)) Z d 2 z hZ hd u j
end
end QRH.RH20261023Return.GenericPhysical.PhysicalDirect

#print axioms QRH.RH20261023Return.GenericPhysical.PhysicalDirect.physical_eq_canonical
