/- Adapted by Joseph Bebel (2026-10-30, 2026-10-31) for the fixed five-window return. -/
/- Repeated marks: fork of Collet's final-stage module EndpointFromNumerator (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
/- Modified by Sil (2026-10-26): instances at theta = 174799/200000 -/
/- Modified by ArviFoxy (2026-10-28): module prefix and namespaces renamed to Submissions.arvi_density.Return and QRH.ArviDensity.Return (no other change). -/
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.Transport.FinalCommonProbe
import Candidate.Local.Qrh.PR99Improvement.Return.TransportInstances
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.PR99Improvement.Return
open QRH.Record1252270103Return Qrh.JointDetector.BoundaryPhysical.Return
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
namespace Final
local instance : Geometry.Parameters := Geometry.finalParameters
local instance : Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN := Geometry.finalBounds
abbrev LiteralNumeratorInput : Prop := GenericPhysical.FinalAssembly.ChosenFiniteNumeratorInput

theorem beta_of_literal_numerator (h : LiteralNumeratorInput) :
 HeckeZeroSupremum.beta≤QRH.PR99Improvement.Return.theta :=
 GenericPhysical.FinalAssembly.beta_le_theta_of_finite_numerator h

theorem hecke_of_literal_numerator (h : LiteralNumeratorInput) (χ : Character) (s : ℂ)
 (hs : QRH.PR99Improvement.Return.theta<s.re) (hpole : s≠1 ∨ χ.residue≠1) :
 LFunction χ s≠0 := HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ
 ((beta_of_literal_numerator h).trans_lt hs) hpole

theorem dirichlet_of_literal_numerator (h : LiteralNumeratorInput) {q:ℕ} [NeZero q]
 (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : QRH.PR99Improvement.Return.theta<s.re)
 (hpole : ¬(χ=1 ∧ s=1)) : χ.LFunction s≠0 :=
 Cycle25.dirichlet_of_hecke (by norm_num [QRH.PR99Improvement.Return.theta,QRH.PR99Improvement.Return.c])
 (hecke_of_literal_numerator h) χ s hs hpole

theorem zeta_of_literal_numerator (h : LiteralNumeratorInput) (s:ℂ)
 (hs : QRH.PR99Improvement.Return.theta<s.re) : riemannZeta s≠0 :=
 Cycle25.zeta_of_hecke (by norm_num [QRH.PR99Improvement.Return.theta,QRH.PR99Improvement.Return.c])
 (hecke_of_literal_numerator h) s hs
end Final
end
end QRH.PR99Improvement.Return
