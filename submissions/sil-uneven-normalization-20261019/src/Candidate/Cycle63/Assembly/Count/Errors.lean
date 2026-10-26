import Candidate.Cycle63.Assembly.Count.SourceCount
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorDictionary

/- Original module: Candidate.Cycle63.Assembly.Count.Canonical. -/
section

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
end

/- Original module: Candidate.Cycle63.Assembly.Count.Errors. -/
section

namespace OAI.SevenEighths.Cycle63DetectorCount
noncomputable section

theorem source_error_absorption (Z d t ε R σ A : ℝ)
    (hZ : 1≤Z) (hd : (1/200:ℝ)≤d) (ht : 0≤t) (hA : 0≤A)
    (hbudget : 159*ε+609*t≤σ) :
    A*Z^(3*t)*(Z^d)^(R+(159*ε+9*t))≤A*(Z^d)^(R+σ) := by
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hdp : 0<d := by linarith
  have hscale : 1≤Z^d := Real.one_le_rpow hZ hdp.le
  have hratio : 3*t/d≤600*t := by
    apply (div_le_iff₀ hdp).mpr
    nlinarith
  have hid : Z^(3*t)=(Z^d)^(3*t/d) := by
    rw [←Real.rpow_mul hZp.le]
    congr 1
    field_simp
  rw [hid,mul_assoc,←Real.rpow_add (Real.rpow_pos_of_pos hZp d)]
  apply mul_le_mul_of_nonneg_left _ hA
  exact Real.rpow_le_rpow_of_exponent_le hscale (by linarith)
end
end OAI.SevenEighths.Cycle63DetectorCount
end
