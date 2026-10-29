/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherBernstein
namespace Qrh.JointDetector.RepeatedMarks.SourceCurveHigherInteger
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 60000
def intervalNumerator (a : Fin 16→ℤ) (den : ℕ) (lo hi : ℤ) (i : Fin 16) : ℤ :=
  ![a 0*1*lo^0*(hi-lo)^0*(den:ℤ)^15 + a 1*1*lo^1*(hi-lo)^0*(den:ℤ)^14 + a 2*1*lo^2*(hi-lo)^0*(den:ℤ)^13 + a 3*1*lo^3*(hi-lo)^0*(den:ℤ)^12 + a 4*1*lo^4*(hi-lo)^0*(den:ℤ)^11 + a 5*1*lo^5*(hi-lo)^0*(den:ℤ)^10 + a 6*1*lo^6*(hi-lo)^0*(den:ℤ)^9 + a 7*1*lo^7*(hi-lo)^0*(den:ℤ)^8 + a 8*1*lo^8*(hi-lo)^0*(den:ℤ)^7 + a 9*1*lo^9*(hi-lo)^0*(den:ℤ)^6 + a 10*1*lo^10*(hi-lo)^0*(den:ℤ)^5 + a 11*1*lo^11*(hi-lo)^0*(den:ℤ)^4 + a 12*1*lo^12*(hi-lo)^0*(den:ℤ)^3 + a 13*1*lo^13*(hi-lo)^0*(den:ℤ)^2 + a 14*1*lo^14*(hi-lo)^0*(den:ℤ)^1 + a 15*1*lo^15*(hi-lo)^0*(den:ℤ)^0,
    a 1*1*lo^0*(hi-lo)^1*(den:ℤ)^14 + a 2*2*lo^1*(hi-lo)^1*(den:ℤ)^13 + a 3*3*lo^2*(hi-lo)^1*(den:ℤ)^12 + a 4*4*lo^3*(hi-lo)^1*(den:ℤ)^11 + a 5*5*lo^4*(hi-lo)^1*(den:ℤ)^10 + a 6*6*lo^5*(hi-lo)^1*(den:ℤ)^9 + a 7*7*lo^6*(hi-lo)^1*(den:ℤ)^8 + a 8*8*lo^7*(hi-lo)^1*(den:ℤ)^7 + a 9*9*lo^8*(hi-lo)^1*(den:ℤ)^6 + a 10*10*lo^9*(hi-lo)^1*(den:ℤ)^5 + a 11*11*lo^10*(hi-lo)^1*(den:ℤ)^4 + a 12*12*lo^11*(hi-lo)^1*(den:ℤ)^3 + a 13*13*lo^12*(hi-lo)^1*(den:ℤ)^2 + a 14*14*lo^13*(hi-lo)^1*(den:ℤ)^1 + a 15*15*lo^14*(hi-lo)^1*(den:ℤ)^0,
    a 2*1*lo^0*(hi-lo)^2*(den:ℤ)^13 + a 3*3*lo^1*(hi-lo)^2*(den:ℤ)^12 + a 4*6*lo^2*(hi-lo)^2*(den:ℤ)^11 + a 5*10*lo^3*(hi-lo)^2*(den:ℤ)^10 + a 6*15*lo^4*(hi-lo)^2*(den:ℤ)^9 + a 7*21*lo^5*(hi-lo)^2*(den:ℤ)^8 + a 8*28*lo^6*(hi-lo)^2*(den:ℤ)^7 + a 9*36*lo^7*(hi-lo)^2*(den:ℤ)^6 + a 10*45*lo^8*(hi-lo)^2*(den:ℤ)^5 + a 11*55*lo^9*(hi-lo)^2*(den:ℤ)^4 + a 12*66*lo^10*(hi-lo)^2*(den:ℤ)^3 + a 13*78*lo^11*(hi-lo)^2*(den:ℤ)^2 + a 14*91*lo^12*(hi-lo)^2*(den:ℤ)^1 + a 15*105*lo^13*(hi-lo)^2*(den:ℤ)^0,
    a 3*1*lo^0*(hi-lo)^3*(den:ℤ)^12 + a 4*4*lo^1*(hi-lo)^3*(den:ℤ)^11 + a 5*10*lo^2*(hi-lo)^3*(den:ℤ)^10 + a 6*20*lo^3*(hi-lo)^3*(den:ℤ)^9 + a 7*35*lo^4*(hi-lo)^3*(den:ℤ)^8 + a 8*56*lo^5*(hi-lo)^3*(den:ℤ)^7 + a 9*84*lo^6*(hi-lo)^3*(den:ℤ)^6 + a 10*120*lo^7*(hi-lo)^3*(den:ℤ)^5 + a 11*165*lo^8*(hi-lo)^3*(den:ℤ)^4 + a 12*220*lo^9*(hi-lo)^3*(den:ℤ)^3 + a 13*286*lo^10*(hi-lo)^3*(den:ℤ)^2 + a 14*364*lo^11*(hi-lo)^3*(den:ℤ)^1 + a 15*455*lo^12*(hi-lo)^3*(den:ℤ)^0,
    a 4*1*lo^0*(hi-lo)^4*(den:ℤ)^11 + a 5*5*lo^1*(hi-lo)^4*(den:ℤ)^10 + a 6*15*lo^2*(hi-lo)^4*(den:ℤ)^9 + a 7*35*lo^3*(hi-lo)^4*(den:ℤ)^8 + a 8*70*lo^4*(hi-lo)^4*(den:ℤ)^7 + a 9*126*lo^5*(hi-lo)^4*(den:ℤ)^6 + a 10*210*lo^6*(hi-lo)^4*(den:ℤ)^5 + a 11*330*lo^7*(hi-lo)^4*(den:ℤ)^4 + a 12*495*lo^8*(hi-lo)^4*(den:ℤ)^3 + a 13*715*lo^9*(hi-lo)^4*(den:ℤ)^2 + a 14*1001*lo^10*(hi-lo)^4*(den:ℤ)^1 + a 15*1365*lo^11*(hi-lo)^4*(den:ℤ)^0,
    a 5*1*lo^0*(hi-lo)^5*(den:ℤ)^10 + a 6*6*lo^1*(hi-lo)^5*(den:ℤ)^9 + a 7*21*lo^2*(hi-lo)^5*(den:ℤ)^8 + a 8*56*lo^3*(hi-lo)^5*(den:ℤ)^7 + a 9*126*lo^4*(hi-lo)^5*(den:ℤ)^6 + a 10*252*lo^5*(hi-lo)^5*(den:ℤ)^5 + a 11*462*lo^6*(hi-lo)^5*(den:ℤ)^4 + a 12*792*lo^7*(hi-lo)^5*(den:ℤ)^3 + a 13*1287*lo^8*(hi-lo)^5*(den:ℤ)^2 + a 14*2002*lo^9*(hi-lo)^5*(den:ℤ)^1 + a 15*3003*lo^10*(hi-lo)^5*(den:ℤ)^0,
    a 6*1*lo^0*(hi-lo)^6*(den:ℤ)^9 + a 7*7*lo^1*(hi-lo)^6*(den:ℤ)^8 + a 8*28*lo^2*(hi-lo)^6*(den:ℤ)^7 + a 9*84*lo^3*(hi-lo)^6*(den:ℤ)^6 + a 10*210*lo^4*(hi-lo)^6*(den:ℤ)^5 + a 11*462*lo^5*(hi-lo)^6*(den:ℤ)^4 + a 12*924*lo^6*(hi-lo)^6*(den:ℤ)^3 + a 13*1716*lo^7*(hi-lo)^6*(den:ℤ)^2 + a 14*3003*lo^8*(hi-lo)^6*(den:ℤ)^1 + a 15*5005*lo^9*(hi-lo)^6*(den:ℤ)^0,
    a 7*1*lo^0*(hi-lo)^7*(den:ℤ)^8 + a 8*8*lo^1*(hi-lo)^7*(den:ℤ)^7 + a 9*36*lo^2*(hi-lo)^7*(den:ℤ)^6 + a 10*120*lo^3*(hi-lo)^7*(den:ℤ)^5 + a 11*330*lo^4*(hi-lo)^7*(den:ℤ)^4 + a 12*792*lo^5*(hi-lo)^7*(den:ℤ)^3 + a 13*1716*lo^6*(hi-lo)^7*(den:ℤ)^2 + a 14*3432*lo^7*(hi-lo)^7*(den:ℤ)^1 + a 15*6435*lo^8*(hi-lo)^7*(den:ℤ)^0,
    a 8*1*lo^0*(hi-lo)^8*(den:ℤ)^7 + a 9*9*lo^1*(hi-lo)^8*(den:ℤ)^6 + a 10*45*lo^2*(hi-lo)^8*(den:ℤ)^5 + a 11*165*lo^3*(hi-lo)^8*(den:ℤ)^4 + a 12*495*lo^4*(hi-lo)^8*(den:ℤ)^3 + a 13*1287*lo^5*(hi-lo)^8*(den:ℤ)^2 + a 14*3003*lo^6*(hi-lo)^8*(den:ℤ)^1 + a 15*6435*lo^7*(hi-lo)^8*(den:ℤ)^0,
    a 9*1*lo^0*(hi-lo)^9*(den:ℤ)^6 + a 10*10*lo^1*(hi-lo)^9*(den:ℤ)^5 + a 11*55*lo^2*(hi-lo)^9*(den:ℤ)^4 + a 12*220*lo^3*(hi-lo)^9*(den:ℤ)^3 + a 13*715*lo^4*(hi-lo)^9*(den:ℤ)^2 + a 14*2002*lo^5*(hi-lo)^9*(den:ℤ)^1 + a 15*5005*lo^6*(hi-lo)^9*(den:ℤ)^0,
    a 10*1*lo^0*(hi-lo)^10*(den:ℤ)^5 + a 11*11*lo^1*(hi-lo)^10*(den:ℤ)^4 + a 12*66*lo^2*(hi-lo)^10*(den:ℤ)^3 + a 13*286*lo^3*(hi-lo)^10*(den:ℤ)^2 + a 14*1001*lo^4*(hi-lo)^10*(den:ℤ)^1 + a 15*3003*lo^5*(hi-lo)^10*(den:ℤ)^0,
    a 11*1*lo^0*(hi-lo)^11*(den:ℤ)^4 + a 12*12*lo^1*(hi-lo)^11*(den:ℤ)^3 + a 13*78*lo^2*(hi-lo)^11*(den:ℤ)^2 + a 14*364*lo^3*(hi-lo)^11*(den:ℤ)^1 + a 15*1365*lo^4*(hi-lo)^11*(den:ℤ)^0,
    a 12*1*lo^0*(hi-lo)^12*(den:ℤ)^3 + a 13*13*lo^1*(hi-lo)^12*(den:ℤ)^2 + a 14*91*lo^2*(hi-lo)^12*(den:ℤ)^1 + a 15*455*lo^3*(hi-lo)^12*(den:ℤ)^0,
    a 13*1*lo^0*(hi-lo)^13*(den:ℤ)^2 + a 14*14*lo^1*(hi-lo)^13*(den:ℤ)^1 + a 15*105*lo^2*(hi-lo)^13*(den:ℤ)^0,
    a 14*1*lo^0*(hi-lo)^14*(den:ℤ)^1 + a 15*15*lo^1*(hi-lo)^14*(den:ℤ)^0,
    a 15*1*lo^0*(hi-lo)^15*(den:ℤ)^0] i
def bernsteinNumerator (a : Fin 16→ℤ) (den : ℕ) (lo hi : ℤ) (i : Fin 16) : ℤ :=
  ![intervalNumerator a den lo hi 0*45045,
    intervalNumerator a den lo hi 0*45045 + intervalNumerator a den lo hi 1*3003,
    intervalNumerator a den lo hi 0*45045 + intervalNumerator a den lo hi 1*6006 + intervalNumerator a den lo hi 2*429,
    intervalNumerator a den lo hi 0*45045 + intervalNumerator a den lo hi 1*9009 + intervalNumerator a den lo hi 2*1287 + intervalNumerator a den lo hi 3*99,
    intervalNumerator a den lo hi 0*45045 + intervalNumerator a den lo hi 1*12012 + intervalNumerator a den lo hi 2*2574 + intervalNumerator a den lo hi 3*396 + intervalNumerator a den lo hi 4*33,
    intervalNumerator a den lo hi 0*45045 + intervalNumerator a den lo hi 1*15015 + intervalNumerator a den lo hi 2*4290 + intervalNumerator a den lo hi 3*990 + intervalNumerator a den lo hi 4*165 + intervalNumerator a den lo hi 5*15,
    intervalNumerator a den lo hi 0*45045 + intervalNumerator a den lo hi 1*18018 + intervalNumerator a den lo hi 2*6435 + intervalNumerator a den lo hi 3*1980 + intervalNumerator a den lo hi 4*495 + intervalNumerator a den lo hi 5*90 + intervalNumerator a den lo hi 6*9,
    intervalNumerator a den lo hi 0*45045 + intervalNumerator a den lo hi 1*21021 + intervalNumerator a den lo hi 2*9009 + intervalNumerator a den lo hi 3*3465 + intervalNumerator a den lo hi 4*1155 + intervalNumerator a den lo hi 5*315 + intervalNumerator a den lo hi 6*63 + intervalNumerator a den lo hi 7*7,
    intervalNumerator a den lo hi 0*45045 + intervalNumerator a den lo hi 1*24024 + intervalNumerator a den lo hi 2*12012 + intervalNumerator a den lo hi 3*5544 + intervalNumerator a den lo hi 4*2310 + intervalNumerator a den lo hi 5*840 + intervalNumerator a den lo hi 6*252 + intervalNumerator a den lo hi 7*56 + intervalNumerator a den lo hi 8*7,
    intervalNumerator a den lo hi 0*45045 + intervalNumerator a den lo hi 1*27027 + intervalNumerator a den lo hi 2*15444 + intervalNumerator a den lo hi 3*8316 + intervalNumerator a den lo hi 4*4158 + intervalNumerator a den lo hi 5*1890 + intervalNumerator a den lo hi 6*756 + intervalNumerator a den lo hi 7*252 + intervalNumerator a den lo hi 8*63 + intervalNumerator a den lo hi 9*9,
    intervalNumerator a den lo hi 0*45045 + intervalNumerator a den lo hi 1*30030 + intervalNumerator a den lo hi 2*19305 + intervalNumerator a den lo hi 3*11880 + intervalNumerator a den lo hi 4*6930 + intervalNumerator a den lo hi 5*3780 + intervalNumerator a den lo hi 6*1890 + intervalNumerator a den lo hi 7*840 + intervalNumerator a den lo hi 8*315 + intervalNumerator a den lo hi 9*90 + intervalNumerator a den lo hi 10*15,
    intervalNumerator a den lo hi 0*45045 + intervalNumerator a den lo hi 1*33033 + intervalNumerator a den lo hi 2*23595 + intervalNumerator a den lo hi 3*16335 + intervalNumerator a den lo hi 4*10890 + intervalNumerator a den lo hi 5*6930 + intervalNumerator a den lo hi 6*4158 + intervalNumerator a den lo hi 7*2310 + intervalNumerator a den lo hi 8*1155 + intervalNumerator a den lo hi 9*495 + intervalNumerator a den lo hi 10*165 + intervalNumerator a den lo hi 11*33,
    intervalNumerator a den lo hi 0*45045 + intervalNumerator a den lo hi 1*36036 + intervalNumerator a den lo hi 2*28314 + intervalNumerator a den lo hi 3*21780 + intervalNumerator a den lo hi 4*16335 + intervalNumerator a den lo hi 5*11880 + intervalNumerator a den lo hi 6*8316 + intervalNumerator a den lo hi 7*5544 + intervalNumerator a den lo hi 8*3465 + intervalNumerator a den lo hi 9*1980 + intervalNumerator a den lo hi 10*990 + intervalNumerator a den lo hi 11*396 + intervalNumerator a den lo hi 12*99,
    intervalNumerator a den lo hi 0*45045 + intervalNumerator a den lo hi 1*39039 + intervalNumerator a den lo hi 2*33462 + intervalNumerator a den lo hi 3*28314 + intervalNumerator a den lo hi 4*23595 + intervalNumerator a den lo hi 5*19305 + intervalNumerator a den lo hi 6*15444 + intervalNumerator a den lo hi 7*12012 + intervalNumerator a den lo hi 8*9009 + intervalNumerator a den lo hi 9*6435 + intervalNumerator a den lo hi 10*4290 + intervalNumerator a den lo hi 11*2574 + intervalNumerator a den lo hi 12*1287 + intervalNumerator a den lo hi 13*429,
    intervalNumerator a den lo hi 0*45045 + intervalNumerator a den lo hi 1*42042 + intervalNumerator a den lo hi 2*39039 + intervalNumerator a den lo hi 3*36036 + intervalNumerator a den lo hi 4*33033 + intervalNumerator a den lo hi 5*30030 + intervalNumerator a den lo hi 6*27027 + intervalNumerator a den lo hi 7*24024 + intervalNumerator a den lo hi 8*21021 + intervalNumerator a den lo hi 9*18018 + intervalNumerator a den lo hi 10*15015 + intervalNumerator a den lo hi 11*12012 + intervalNumerator a den lo hi 12*9009 + intervalNumerator a den lo hi 13*6006 + intervalNumerator a den lo hi 14*3003,
    intervalNumerator a den lo hi 0*45045 + intervalNumerator a den lo hi 1*45045 + intervalNumerator a den lo hi 2*45045 + intervalNumerator a den lo hi 3*45045 + intervalNumerator a den lo hi 4*45045 + intervalNumerator a den lo hi 5*45045 + intervalNumerator a den lo hi 6*45045 + intervalNumerator a den lo hi 7*45045 + intervalNumerator a den lo hi 8*45045 + intervalNumerator a den lo hi 9*45045 + intervalNumerator a den lo hi 10*45045 + intervalNumerator a den lo hi 11*45045 + intervalNumerator a den lo hi 12*45045 + intervalNumerator a den lo hi 13*45045 + intervalNumerator a den lo hi 14*45045 + intervalNumerator a den lo hi 15*45045] i

noncomputable section
open SourceCurveHigherCertificate BernsteinBox

theorem bernsteinNumerator_eval (a : Fin 16→ℤ) (den baseDen : ℕ) (lo hi : ℤ)
    (hd : 0<den) (hb : 0<baseDen) (i : Fin 16) :
    coeff (fun j => (a j:ℝ)/(baseDen:ℝ)) ((lo:ℝ)/(den:ℝ)) ((hi:ℝ)/(den:ℝ)) i =
      (bernsteinNumerator a den lo hi i:ℝ)/((baseDen:ℝ)*45045*(den:ℝ)^15) := by
  have hd0 : (den:ℝ) ≠ 0 := by positivity
  have hb0 : (baseDen:ℝ) ≠ 0 := by positivity
  fin_cases i <;>
    norm_num [coeff,coefficients,intervalPower,bernsteinNumerator,intervalNumerator,
      Fin.sum_univ_succ,Nat.choose] <;>
    field_simp [hd0,hb0] <;> ring

theorem positive_of_numerator {a : Fin 16→ℤ} {den baseDen : ℕ} {lo hi : ℤ}
    (hd : 0<den) (hb : 0<baseDen) (hw : lo<hi)
    (hnum : ∀ i,0<bernsteinNumerator a den lo hi i) {u : ℝ}
    (hu : u∈Set.Icc ((lo:ℝ)/(den:ℝ)) ((hi:ℝ)/(den:ℝ))) :
    0<eval (fun j=>(a j:ℝ)/(baseDen:ℝ)) u := by
  apply positive ((div_lt_div_iff_of_pos_right (by positivity : 0<(den:ℝ))).2 (by exact_mod_cast hw)) hu
  intro i
  rw [bernsteinNumerator_eval a den baseDen lo hi hd hb]
  exact div_pos (by exact_mod_cast hnum i) (by positivity)

end
end Qrh.JointDetector.RepeatedMarks.SourceCurveHigherInteger
#print axioms Qrh.JointDetector.RepeatedMarks.SourceCurveHigherInteger.positive_of_numerator
