/- Prepared retuned physical tails. Compilation and replay are recorded separately. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.TailScales
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RetunedCentralExponent

namespace OAI
noncomputable section
open scoped BigOperators
namespace SevenEighths.ProbeHighRowFamily
open _root_.BelowSevenEighthsTight _root_.BelowSevenEighthsTight.PrincipalExtension

def smallRawOffset : ℝ := -1+lxRat/2-lyRat/2+hRat*(17/50)+1/1000
def smallTailOffset : ℝ := smallRawOffset+1/50
def largeTailBase : ℝ := 1+lxRat/2+lyRat

lemma rational_tail_sigma_lower (β e : ℝ) (hβ : sigmaRat≤β) (he : 0≤e) :
    (7/8:ℝ)≤β+1/1000+8*e := by
  norm_num [sigmaRat] at hβ
  linarith

lemma rational_small_tail_margin :
    smallTailOffset≤sourceShift lxRat ellRat-1/16 := by
  norm_num [smallTailOffset,smallRawOffset,sourceShift,lxRat,lyRat,hRat,ellRat,bRat]

lemma small_source_scale_retuned {K : ℕ} (Z : ℝ) (hZ : 0<Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=ellRat) (β e : ℝ) :
    (∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^lxRat)^(1/2-(17/50:ℝ))*Z^(β+1/1000+8*e+(17/50:ℝ)-1)*
        (Z^lyRat)^((1/2:ℝ)-1))=Z^(β+smallRawOffset+8*e) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  dsimp [smallRawOffset,lxRat,hRat]
  ring

lemma large_source_scale_retuned {K : ℕ} (Z : ℝ) (hZ : 0<Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=ellRat) (r : ℝ) :
    (∏i,(Z^(length i))^r)*
      ((Z^lxRat)^(1/2-r)*Z^(2+r-1)*(Z^lyRat)^((2:ℝ)-1))=
      Z^(largeTailBase+hRat*r) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  dsimp [largeTailBase,lxRat,hRat]
  ring

end SevenEighths.ProbeHighRowFamily
end
end OAI

#print axioms OAI.SevenEighths.ProbeHighRowFamily.rational_tail_sigma_lower
#print axioms OAI.SevenEighths.ProbeHighRowFamily.rational_small_tail_margin
#print axioms OAI.SevenEighths.ProbeHighRowFamily.small_source_scale_retuned
#print axioms OAI.SevenEighths.ProbeHighRowFamily.large_source_scale_retuned
