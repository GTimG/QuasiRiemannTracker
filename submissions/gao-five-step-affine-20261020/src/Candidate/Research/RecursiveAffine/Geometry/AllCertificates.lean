import Candidate.Research.RecursiveAffine.Geometry.Certificate00
import Candidate.Research.RecursiveAffine.Geometry.Certificate01
import Candidate.Research.RecursiveAffine.Geometry.Certificate02
import Candidate.Research.RecursiveAffine.Geometry.Certificate03
import Candidate.Research.RecursiveAffine.Geometry.Certificate04
import Candidate.Research.RecursiveAffine.Geometry.Certificate05
import Candidate.Research.RecursiveAffine.Geometry.Certificate06
import Candidate.Research.RecursiveAffine.Geometry.Certificate07
import Candidate.Research.RecursiveAffine.Geometry.Certificate08
import Candidate.Research.RecursiveAffine.Geometry.Certificate09
import Candidate.Research.RecursiveAffine.Geometry.Certificate10
import Candidate.Research.RecursiveAffine.Geometry.Certificate11
import Candidate.Research.RecursiveAffine.Geometry.Certificate12
import Candidate.Research.RecursiveAffine.Geometry.Certificate13
import Candidate.Research.RecursiveAffine.Geometry.Certificate14
import Candidate.Research.RecursiveAffine.Geometry.Certificate15
import Candidate.Research.RecursiveAffine.Geometry.Certificate16
import Candidate.Research.RecursiveAffine.Geometry.Certificate17
import Candidate.Research.RecursiveAffine.Geometry.Certificate18
import Candidate.Research.RecursiveAffine.Geometry.Certificate19
import Candidate.Research.RecursiveAffine.Geometry.Certificate20
import Candidate.Research.RecursiveAffine.Geometry.Certificate21
import Candidate.Research.RecursiveAffine.Geometry.Certificate22
import Candidate.Research.RecursiveAffine.Geometry.Certificate23
import Candidate.Research.RecursiveAffine.Geometry.Certificate24
import Candidate.Research.RecursiveAffine.Geometry.Certificate25
import Candidate.Research.RecursiveAffine.Geometry.Certificate26
import Candidate.Research.RecursiveAffine.Geometry.Certificate27
import Candidate.Research.RecursiveAffine.Geometry.Certificate28
import Candidate.Research.RecursiveAffine.Geometry.Certificate29
import Candidate.Research.RecursiveAffine.Geometry.Certificate30
import Candidate.Research.RecursiveAffine.Geometry.Certificate31
import Candidate.Research.RecursiveAffine.Geometry.Certificate32
import Candidate.Research.RecursiveAffine.Geometry.Certificate33
import Candidate.Research.RecursiveAffine.Geometry.Certificate34
import Candidate.Research.RecursiveAffine.Geometry.Certificate35
import Candidate.Research.RecursiveAffine.Geometry.Certificate36
import Candidate.Research.RecursiveAffine.Geometry.Certificate37
import Candidate.Research.RecursiveAffine.Geometry.Certificate38
import Candidate.Research.RecursiveAffine.Geometry.Certificate39
import Candidate.Research.RecursiveAffine.Geometry.Certificate40
import Candidate.Research.RecursiveAffine.Geometry.Certificate41
import Candidate.Research.RecursiveAffine.Geometry.Certificate42
import Candidate.Research.RecursiveAffine.Geometry.Certificate43
import Candidate.Research.RecursiveAffine.Geometry.Certificate44
import Candidate.Research.RecursiveAffine.Geometry.Certificate45
import Candidate.Research.RecursiveAffine.Geometry.Certificate46
import Candidate.Research.RecursiveAffine.Geometry.Certificate47
import Candidate.Research.RecursiveAffine.Geometry.Certificate48
import Candidate.Research.RecursiveAffine.Geometry.Certificate49
import Candidate.Research.RecursiveAffine.Geometry.Certificate50
import Candidate.Research.RecursiveAffine.Geometry.Certificate51
import Candidate.Research.RecursiveAffine.Geometry.Certificate52
import Candidate.Research.RecursiveAffine.Geometry.Certificate53
import Candidate.Research.RecursiveAffine.Geometry.Certificate54
import Candidate.Research.RecursiveAffine.Geometry.Certificate55
import Candidate.Research.RecursiveAffine.Geometry.Certificate56
import Candidate.Research.RecursiveAffine.Geometry.Certificate57
import Candidate.Research.RecursiveAffine.Geometry.Certificate58
import Candidate.Research.RecursiveAffine.Geometry.Certificate59
import Candidate.Research.RecursiveAffine.Geometry.Certificate60
import Candidate.Research.RecursiveAffine.Geometry.Certificate61

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153Geometry
noncomputable section

/-- A concrete gate retains both its exact dual certificate and the literal
indices of the native affine constraints used by that certificate. -/
structure Gate where
  count : ℕ
  certificate : Certificate 14 count
  selected : Fin count → Fin 48
  rows_selected : ∀ j, certificate.rows j = Model.constraint (selected j)

def gates : Fin 62 → Gate := ![⟨5, Certificate00.certificate, Certificate00.selected, Certificate00.rows_selected⟩,
  ⟨4, Certificate01.certificate, Certificate01.selected, Certificate01.rows_selected⟩,
  ⟨5, Certificate02.certificate, Certificate02.selected, Certificate02.rows_selected⟩,
  ⟨5, Certificate03.certificate, Certificate03.selected, Certificate03.rows_selected⟩,
  ⟨5, Certificate04.certificate, Certificate04.selected, Certificate04.rows_selected⟩,
  ⟨4, Certificate05.certificate, Certificate05.selected, Certificate05.rows_selected⟩,
  ⟨5, Certificate06.certificate, Certificate06.selected, Certificate06.rows_selected⟩,
  ⟨5, Certificate07.certificate, Certificate07.selected, Certificate07.rows_selected⟩,
  ⟨5, Certificate08.certificate, Certificate08.selected, Certificate08.rows_selected⟩,
  ⟨5, Certificate09.certificate, Certificate09.selected, Certificate09.rows_selected⟩,
  ⟨4, Certificate10.certificate, Certificate10.selected, Certificate10.rows_selected⟩,
  ⟨1, Certificate11.certificate, Certificate11.selected, Certificate11.rows_selected⟩,
  ⟨5, Certificate12.certificate, Certificate12.selected, Certificate12.rows_selected⟩,
  ⟨5, Certificate13.certificate, Certificate13.selected, Certificate13.rows_selected⟩,
  ⟨4, Certificate14.certificate, Certificate14.selected, Certificate14.rows_selected⟩,
  ⟨5, Certificate15.certificate, Certificate15.selected, Certificate15.rows_selected⟩,
  ⟨8, Certificate16.certificate, Certificate16.selected, Certificate16.rows_selected⟩,
  ⟨8, Certificate17.certificate, Certificate17.selected, Certificate17.rows_selected⟩,
  ⟨8, Certificate18.certificate, Certificate18.selected, Certificate18.rows_selected⟩,
  ⟨8, Certificate19.certificate, Certificate19.selected, Certificate19.rows_selected⟩,
  ⟨8, Certificate20.certificate, Certificate20.selected, Certificate20.rows_selected⟩,
  ⟨8, Certificate21.certificate, Certificate21.selected, Certificate21.rows_selected⟩,
  ⟨8, Certificate22.certificate, Certificate22.selected, Certificate22.rows_selected⟩,
  ⟨8, Certificate23.certificate, Certificate23.selected, Certificate23.rows_selected⟩,
  ⟨8, Certificate24.certificate, Certificate24.selected, Certificate24.rows_selected⟩,
  ⟨8, Certificate25.certificate, Certificate25.selected, Certificate25.rows_selected⟩,
  ⟨8, Certificate26.certificate, Certificate26.selected, Certificate26.rows_selected⟩,
  ⟨8, Certificate27.certificate, Certificate27.selected, Certificate27.rows_selected⟩,
  ⟨8, Certificate28.certificate, Certificate28.selected, Certificate28.rows_selected⟩,
  ⟨8, Certificate29.certificate, Certificate29.selected, Certificate29.rows_selected⟩,
  ⟨8, Certificate30.certificate, Certificate30.selected, Certificate30.rows_selected⟩,
  ⟨8, Certificate31.certificate, Certificate31.selected, Certificate31.rows_selected⟩,
  ⟨11, Certificate32.certificate, Certificate32.selected, Certificate32.rows_selected⟩,
  ⟨11, Certificate33.certificate, Certificate33.selected, Certificate33.rows_selected⟩,
  ⟨11, Certificate34.certificate, Certificate34.selected, Certificate34.rows_selected⟩,
  ⟨11, Certificate35.certificate, Certificate35.selected, Certificate35.rows_selected⟩,
  ⟨11, Certificate36.certificate, Certificate36.selected, Certificate36.rows_selected⟩,
  ⟨11, Certificate37.certificate, Certificate37.selected, Certificate37.rows_selected⟩,
  ⟨11, Certificate38.certificate, Certificate38.selected, Certificate38.rows_selected⟩,
  ⟨11, Certificate39.certificate, Certificate39.selected, Certificate39.rows_selected⟩,
  ⟨11, Certificate40.certificate, Certificate40.selected, Certificate40.rows_selected⟩,
  ⟨11, Certificate41.certificate, Certificate41.selected, Certificate41.rows_selected⟩,
  ⟨11, Certificate42.certificate, Certificate42.selected, Certificate42.rows_selected⟩,
  ⟨11, Certificate43.certificate, Certificate43.selected, Certificate43.rows_selected⟩,
  ⟨11, Certificate44.certificate, Certificate44.selected, Certificate44.rows_selected⟩,
  ⟨11, Certificate45.certificate, Certificate45.selected, Certificate45.rows_selected⟩,
  ⟨11, Certificate46.certificate, Certificate46.selected, Certificate46.rows_selected⟩,
  ⟨11, Certificate47.certificate, Certificate47.selected, Certificate47.rows_selected⟩,
  ⟨14, Certificate48.certificate, Certificate48.selected, Certificate48.rows_selected⟩,
  ⟨14, Certificate49.certificate, Certificate49.selected, Certificate49.rows_selected⟩,
  ⟨14, Certificate50.certificate, Certificate50.selected, Certificate50.rows_selected⟩,
  ⟨14, Certificate51.certificate, Certificate51.selected, Certificate51.rows_selected⟩,
  ⟨14, Certificate52.certificate, Certificate52.selected, Certificate52.rows_selected⟩,
  ⟨14, Certificate53.certificate, Certificate53.selected, Certificate53.rows_selected⟩,
  ⟨14, Certificate54.certificate, Certificate54.selected, Certificate54.rows_selected⟩,
  ⟨14, Certificate55.certificate, Certificate55.selected, Certificate55.rows_selected⟩,
  ⟨14, Certificate56.certificate, Certificate56.selected, Certificate56.rows_selected⟩,
  ⟨14, Certificate57.certificate, Certificate57.selected, Certificate57.rows_selected⟩,
  ⟨14, Certificate58.certificate, Certificate58.selected, Certificate58.rows_selected⟩,
  ⟨14, Certificate59.certificate, Certificate59.selected, Certificate59.rows_selected⟩,
  ⟨14, Certificate60.certificate, Certificate60.selected, Certificate60.rows_selected⟩,
  ⟨14, Certificate61.certificate, Certificate61.selected, Certificate61.rows_selected⟩]

/-- All sixty-two specific rational identities have a real consumer.
The selected-gate hypotheses are independent: future constraints are never
required for a gate on an earlier prefix or an OLD-closing skip branch. -/
theorem robust_for_gate (i : Fin 62) (x : Fin 14 → ℝ) (E : ℝ)
    (hE : E ≤ 1 / 1000000000000000)
    (hc : ∀ j, -E ≤ eval (Model.constraint ((gates i).selected j)) x) :
    (1568511 / 1000000000000000 : ℝ) < eval (gates i).certificate.objective x := by
  apply (gates i).certificate.uniform_robust_lower x E hE
  intro j
  rw [(gates i).rows_selected]
  exact hc j

theorem positive_for_gate (i : Fin 62) (x : Fin 14 → ℝ) (E : ℝ)
    (hE : E ≤ 1 / 1000000000000000)
    (hc : ∀ j, -E ≤ eval (Model.constraint ((gates i).selected j)) x) :
    0 < eval (gates i).certificate.objective x :=
  lt_trans (by norm_num) (robust_for_gate i x E hE hc)

end
end OAI.SevenEighths.Cycle153Geometry

#print axioms OAI.SevenEighths.Cycle153Geometry.robust_for_gate
