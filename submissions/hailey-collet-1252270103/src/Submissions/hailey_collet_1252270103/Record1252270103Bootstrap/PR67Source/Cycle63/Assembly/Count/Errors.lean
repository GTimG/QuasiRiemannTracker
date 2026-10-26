import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Assembly.Count.Canonical
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
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

end Record1252270103Bootstrap.PR67
