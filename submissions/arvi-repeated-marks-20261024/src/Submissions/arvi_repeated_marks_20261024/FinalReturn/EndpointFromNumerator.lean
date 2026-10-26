/- Repeated marks: fork of Collet's final-stage module EndpointFromNumerator (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
import Submissions.arvi_repeated_marks_20261024.ReturnD.Transport.FinalCommonProbe
import Submissions.arvi_repeated_marks_20261024.FinalReturn.TransportInstances
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.RepeatedMarks.Return
open QRH.Record1252270103Return
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
namespace Final
local instance : Geometry.Parameters := Geometry.finalParameters
local instance : Geometry.BoundsR := Geometry.finalBounds
abbrev LiteralNumeratorInput : Prop := GenericPhysical.FinalAssembly.ChosenFiniteNumeratorInput

theorem beta_of_literal_numerator (h : LiteralNumeratorInput) :
 HeckeZeroSupremum.beta≤QRH.RepeatedMarks.Return.theta :=
 GenericPhysical.FinalAssembly.beta_le_theta_of_finite_numerator h

theorem hecke_of_literal_numerator (h : LiteralNumeratorInput) (χ : Character) (s : ℂ)
 (hs : QRH.RepeatedMarks.Return.theta<s.re) (hpole : s≠1 ∨ χ.residue≠1) :
 LFunction χ s≠0 := HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ
 ((beta_of_literal_numerator h).trans_lt hs) hpole

theorem dirichlet_of_literal_numerator (h : LiteralNumeratorInput) {q:ℕ} [NeZero q]
 (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : QRH.RepeatedMarks.Return.theta<s.re)
 (hpole : ¬(χ=1 ∧ s=1)) : χ.LFunction s≠0 :=
 Cycle25.dirichlet_of_hecke (by norm_num [QRH.RepeatedMarks.Return.theta,QRH.RepeatedMarks.Return.c])
 (hecke_of_literal_numerator h) χ s hs hpole

theorem zeta_of_literal_numerator (h : LiteralNumeratorInput) (s:ℂ)
 (hs : QRH.RepeatedMarks.Return.theta<s.re) : riemannZeta s≠0 :=
 Cycle25.zeta_of_hecke (by norm_num [QRH.RepeatedMarks.Return.theta,QRH.RepeatedMarks.Return.c])
 (hecke_of_literal_numerator h) s hs
end Final
end
end QRH.RepeatedMarks.Return
#print axioms QRH.RepeatedMarks.Return.Final.beta_of_literal_numerator
#print axioms QRH.RepeatedMarks.Return.Final.hecke_of_literal_numerator
#print axioms QRH.RepeatedMarks.Return.Final.dirichlet_of_literal_numerator
#print axioms QRH.RepeatedMarks.Return.Final.zeta_of_literal_numerator
