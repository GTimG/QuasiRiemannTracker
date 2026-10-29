/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveBernstein
namespace Qrh.JointDetector.RepeatedMarks.SourceCurveInteger
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 60000
def intervalNumerator (a : Fin 12→ℤ) (den : ℕ) (lo hi : ℤ) (i : Fin 12) : ℤ :=
  ![a 0*1*lo^0*(hi-lo)^0*(den:ℤ)^11 + a 1*1*lo^1*(hi-lo)^0*(den:ℤ)^10 + a 2*1*lo^2*(hi-lo)^0*(den:ℤ)^9 + a 3*1*lo^3*(hi-lo)^0*(den:ℤ)^8 + a 4*1*lo^4*(hi-lo)^0*(den:ℤ)^7 + a 5*1*lo^5*(hi-lo)^0*(den:ℤ)^6 + a 6*1*lo^6*(hi-lo)^0*(den:ℤ)^5 + a 7*1*lo^7*(hi-lo)^0*(den:ℤ)^4 + a 8*1*lo^8*(hi-lo)^0*(den:ℤ)^3 + a 9*1*lo^9*(hi-lo)^0*(den:ℤ)^2 + a 10*1*lo^10*(hi-lo)^0*(den:ℤ)^1 + a 11*1*lo^11*(hi-lo)^0*(den:ℤ)^0,
    a 1*1*lo^0*(hi-lo)^1*(den:ℤ)^10 + a 2*2*lo^1*(hi-lo)^1*(den:ℤ)^9 + a 3*3*lo^2*(hi-lo)^1*(den:ℤ)^8 + a 4*4*lo^3*(hi-lo)^1*(den:ℤ)^7 + a 5*5*lo^4*(hi-lo)^1*(den:ℤ)^6 + a 6*6*lo^5*(hi-lo)^1*(den:ℤ)^5 + a 7*7*lo^6*(hi-lo)^1*(den:ℤ)^4 + a 8*8*lo^7*(hi-lo)^1*(den:ℤ)^3 + a 9*9*lo^8*(hi-lo)^1*(den:ℤ)^2 + a 10*10*lo^9*(hi-lo)^1*(den:ℤ)^1 + a 11*11*lo^10*(hi-lo)^1*(den:ℤ)^0,
    a 2*1*lo^0*(hi-lo)^2*(den:ℤ)^9 + a 3*3*lo^1*(hi-lo)^2*(den:ℤ)^8 + a 4*6*lo^2*(hi-lo)^2*(den:ℤ)^7 + a 5*10*lo^3*(hi-lo)^2*(den:ℤ)^6 + a 6*15*lo^4*(hi-lo)^2*(den:ℤ)^5 + a 7*21*lo^5*(hi-lo)^2*(den:ℤ)^4 + a 8*28*lo^6*(hi-lo)^2*(den:ℤ)^3 + a 9*36*lo^7*(hi-lo)^2*(den:ℤ)^2 + a 10*45*lo^8*(hi-lo)^2*(den:ℤ)^1 + a 11*55*lo^9*(hi-lo)^2*(den:ℤ)^0,
    a 3*1*lo^0*(hi-lo)^3*(den:ℤ)^8 + a 4*4*lo^1*(hi-lo)^3*(den:ℤ)^7 + a 5*10*lo^2*(hi-lo)^3*(den:ℤ)^6 + a 6*20*lo^3*(hi-lo)^3*(den:ℤ)^5 + a 7*35*lo^4*(hi-lo)^3*(den:ℤ)^4 + a 8*56*lo^5*(hi-lo)^3*(den:ℤ)^3 + a 9*84*lo^6*(hi-lo)^3*(den:ℤ)^2 + a 10*120*lo^7*(hi-lo)^3*(den:ℤ)^1 + a 11*165*lo^8*(hi-lo)^3*(den:ℤ)^0,
    a 4*1*lo^0*(hi-lo)^4*(den:ℤ)^7 + a 5*5*lo^1*(hi-lo)^4*(den:ℤ)^6 + a 6*15*lo^2*(hi-lo)^4*(den:ℤ)^5 + a 7*35*lo^3*(hi-lo)^4*(den:ℤ)^4 + a 8*70*lo^4*(hi-lo)^4*(den:ℤ)^3 + a 9*126*lo^5*(hi-lo)^4*(den:ℤ)^2 + a 10*210*lo^6*(hi-lo)^4*(den:ℤ)^1 + a 11*330*lo^7*(hi-lo)^4*(den:ℤ)^0,
    a 5*1*lo^0*(hi-lo)^5*(den:ℤ)^6 + a 6*6*lo^1*(hi-lo)^5*(den:ℤ)^5 + a 7*21*lo^2*(hi-lo)^5*(den:ℤ)^4 + a 8*56*lo^3*(hi-lo)^5*(den:ℤ)^3 + a 9*126*lo^4*(hi-lo)^5*(den:ℤ)^2 + a 10*252*lo^5*(hi-lo)^5*(den:ℤ)^1 + a 11*462*lo^6*(hi-lo)^5*(den:ℤ)^0,
    a 6*1*lo^0*(hi-lo)^6*(den:ℤ)^5 + a 7*7*lo^1*(hi-lo)^6*(den:ℤ)^4 + a 8*28*lo^2*(hi-lo)^6*(den:ℤ)^3 + a 9*84*lo^3*(hi-lo)^6*(den:ℤ)^2 + a 10*210*lo^4*(hi-lo)^6*(den:ℤ)^1 + a 11*462*lo^5*(hi-lo)^6*(den:ℤ)^0,
    a 7*1*lo^0*(hi-lo)^7*(den:ℤ)^4 + a 8*8*lo^1*(hi-lo)^7*(den:ℤ)^3 + a 9*36*lo^2*(hi-lo)^7*(den:ℤ)^2 + a 10*120*lo^3*(hi-lo)^7*(den:ℤ)^1 + a 11*330*lo^4*(hi-lo)^7*(den:ℤ)^0,
    a 8*1*lo^0*(hi-lo)^8*(den:ℤ)^3 + a 9*9*lo^1*(hi-lo)^8*(den:ℤ)^2 + a 10*45*lo^2*(hi-lo)^8*(den:ℤ)^1 + a 11*165*lo^3*(hi-lo)^8*(den:ℤ)^0,
    a 9*1*lo^0*(hi-lo)^9*(den:ℤ)^2 + a 10*10*lo^1*(hi-lo)^9*(den:ℤ)^1 + a 11*55*lo^2*(hi-lo)^9*(den:ℤ)^0,
    a 10*1*lo^0*(hi-lo)^10*(den:ℤ)^1 + a 11*11*lo^1*(hi-lo)^10*(den:ℤ)^0,
    a 11*1*lo^0*(hi-lo)^11*(den:ℤ)^0] i
def bernsteinNumerator (a : Fin 12→ℤ) (den : ℕ) (lo hi : ℤ) (i : Fin 12) : ℤ :=
  ![intervalNumerator a den lo hi 0*2310,
    intervalNumerator a den lo hi 0*2310 + intervalNumerator a den lo hi 1*210,
    intervalNumerator a den lo hi 0*2310 + intervalNumerator a den lo hi 1*420 + intervalNumerator a den lo hi 2*42,
    intervalNumerator a den lo hi 0*2310 + intervalNumerator a den lo hi 1*630 + intervalNumerator a den lo hi 2*126 + intervalNumerator a den lo hi 3*14,
    intervalNumerator a den lo hi 0*2310 + intervalNumerator a den lo hi 1*840 + intervalNumerator a den lo hi 2*252 + intervalNumerator a den lo hi 3*56 + intervalNumerator a den lo hi 4*7,
    intervalNumerator a den lo hi 0*2310 + intervalNumerator a den lo hi 1*1050 + intervalNumerator a den lo hi 2*420 + intervalNumerator a den lo hi 3*140 + intervalNumerator a den lo hi 4*35 + intervalNumerator a den lo hi 5*5,
    intervalNumerator a den lo hi 0*2310 + intervalNumerator a den lo hi 1*1260 + intervalNumerator a den lo hi 2*630 + intervalNumerator a den lo hi 3*280 + intervalNumerator a den lo hi 4*105 + intervalNumerator a den lo hi 5*30 + intervalNumerator a den lo hi 6*5,
    intervalNumerator a den lo hi 0*2310 + intervalNumerator a den lo hi 1*1470 + intervalNumerator a den lo hi 2*882 + intervalNumerator a den lo hi 3*490 + intervalNumerator a den lo hi 4*245 + intervalNumerator a den lo hi 5*105 + intervalNumerator a den lo hi 6*35 + intervalNumerator a den lo hi 7*7,
    intervalNumerator a den lo hi 0*2310 + intervalNumerator a den lo hi 1*1680 + intervalNumerator a den lo hi 2*1176 + intervalNumerator a den lo hi 3*784 + intervalNumerator a den lo hi 4*490 + intervalNumerator a den lo hi 5*280 + intervalNumerator a den lo hi 6*140 + intervalNumerator a den lo hi 7*56 + intervalNumerator a den lo hi 8*14,
    intervalNumerator a den lo hi 0*2310 + intervalNumerator a den lo hi 1*1890 + intervalNumerator a den lo hi 2*1512 + intervalNumerator a den lo hi 3*1176 + intervalNumerator a den lo hi 4*882 + intervalNumerator a den lo hi 5*630 + intervalNumerator a den lo hi 6*420 + intervalNumerator a den lo hi 7*252 + intervalNumerator a den lo hi 8*126 + intervalNumerator a den lo hi 9*42,
    intervalNumerator a den lo hi 0*2310 + intervalNumerator a den lo hi 1*2100 + intervalNumerator a den lo hi 2*1890 + intervalNumerator a den lo hi 3*1680 + intervalNumerator a den lo hi 4*1470 + intervalNumerator a den lo hi 5*1260 + intervalNumerator a den lo hi 6*1050 + intervalNumerator a den lo hi 7*840 + intervalNumerator a den lo hi 8*630 + intervalNumerator a den lo hi 9*420 + intervalNumerator a den lo hi 10*210,
    intervalNumerator a den lo hi 0*2310 + intervalNumerator a den lo hi 1*2310 + intervalNumerator a den lo hi 2*2310 + intervalNumerator a den lo hi 3*2310 + intervalNumerator a den lo hi 4*2310 + intervalNumerator a den lo hi 5*2310 + intervalNumerator a den lo hi 6*2310 + intervalNumerator a den lo hi 7*2310 + intervalNumerator a den lo hi 8*2310 + intervalNumerator a den lo hi 9*2310 + intervalNumerator a den lo hi 10*2310 + intervalNumerator a den lo hi 11*2310] i

noncomputable section
open SourceCurveCertificate BernsteinBox

theorem bernsteinNumerator_eval (a : Fin 12→ℤ) (den baseDen : ℕ) (lo hi : ℤ)
    (hd : 0<den) (hb : 0<baseDen) (i : Fin 12) :
    coeff (fun j => (a j:ℝ)/(baseDen:ℝ)) ((lo:ℝ)/(den:ℝ)) ((hi:ℝ)/(den:ℝ)) i =
      (bernsteinNumerator a den lo hi i:ℝ)/((baseDen:ℝ)*2310*(den:ℝ)^11) := by
  have hd0 : (den:ℝ) ≠ 0 := by positivity
  have hb0 : (baseDen:ℝ) ≠ 0 := by positivity
  fin_cases i <;>
    norm_num [coeff,coefficients,intervalPower,bernsteinNumerator,intervalNumerator,
      Fin.sum_univ_succ,Nat.choose] <;>
    field_simp [hd0,hb0] <;> ring

theorem positive_of_numerator {a : Fin 12→ℤ} {den baseDen : ℕ} {lo hi : ℤ}
    (hd : 0<den) (hb : 0<baseDen) (hw : lo<hi)
    (hnum : ∀ i,0<bernsteinNumerator a den lo hi i) {u : ℝ}
    (hu : u∈Set.Icc ((lo:ℝ)/(den:ℝ)) ((hi:ℝ)/(den:ℝ))) :
    0<eval (fun j=>(a j:ℝ)/(baseDen:ℝ)) u := by
  apply positive ((div_lt_div_iff_of_pos_right (by positivity : 0<(den:ℝ))).2 (by exact_mod_cast hw)) hu
  intro i
  rw [bernsteinNumerator_eval a den baseDen lo hi hd hb]
  exact div_pos (by exact_mod_cast hnum i) (by positivity)

end
end Qrh.JointDetector.RepeatedMarks.SourceCurveInteger
#print axioms Qrh.JointDetector.RepeatedMarks.SourceCurveInteger.positive_of_numerator
