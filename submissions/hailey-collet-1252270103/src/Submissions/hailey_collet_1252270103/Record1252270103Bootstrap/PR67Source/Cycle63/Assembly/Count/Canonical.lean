import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Assembly.Count.SourceCount
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorDictionary
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
namespace OAI.SevenEighths.Cycle63DetectorCount
noncomputable section
open HeckeFamily HeckeInverseAmplification HeckeDetectorPhysicalSelection ProbeHighRowFamily

def canonicalFamily (D : Data) (F : SourceData) (Z : ℝ) (z : ℂ) : FreeRow→Fin D.N→ℂ :=
  fun u j=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val
    (fun y=>(F.w y:ℂ)) 2 (Z^(D.length j)) z

theorem physical_eq_canonical (D : Data) (F : SourceData) (Z d : ℝ)
    (hZ : 0<Z) (hd : d≠0) (z : ℂ) :
    physical F.modulus ⊤ (fun u : FreeRow=>u.val) (fun _ y=>(F.w y:ℂ))
      (fun _=>2) (fun j=>D.length j/d) (fun _=>z) (Z^d) = canonicalFamily D F Z z := by
  funext u j
  exact source_physical_amplitude F.modulus ⊤ D.length (fun _ y=>(F.w y:ℂ)) Z d 2 z hZ hd u j
end
end OAI.SevenEighths.Cycle63DetectorCount

end Record1252270103Bootstrap.PR67
