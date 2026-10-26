/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The literal numerator is an explicit integration obligation, not a source surrogate. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Return.Transport.FinalCommonProbe
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Return.TransportInstances
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Return
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
namespace Final
local instance : Geometry.Parameters := Geometry.finalParameters
local instance : Geometry.Bounds := Geometry.finalBounds
abbrev LiteralNumeratorInput : Prop := GenericPhysical.FinalAssembly.ChosenFiniteNumeratorInput

theorem beta_of_literal_numerator (h : LiteralNumeratorInput) :
 HeckeZeroSupremum.beta≤Record1252270103Finite.theta :=
 GenericPhysical.FinalAssembly.beta_le_theta_of_finite_numerator h

theorem hecke_of_literal_numerator (h : LiteralNumeratorInput) (χ : Character) (s : ℂ)
 (hs : Record1252270103Finite.theta<s.re) (hpole : s≠1 ∨ χ.residue≠1) :
 LFunction χ s≠0 := HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ
 ((beta_of_literal_numerator h).trans_lt hs) hpole

theorem dirichlet_of_literal_numerator (h : LiteralNumeratorInput) {q:ℕ} [NeZero q]
 (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : Record1252270103Finite.theta<s.re)
 (hpole : ¬(χ=1 ∧ s=1)) : χ.LFunction s≠0 :=
 Cycle25.dirichlet_of_hecke (by norm_num [Record1252270103Finite.theta,Record1252270103Finite.c])
 (hecke_of_literal_numerator h) χ s hs hpole

theorem zeta_of_literal_numerator (h : LiteralNumeratorInput) (s:ℂ)
 (hs : Record1252270103Finite.theta<s.re) : riemannZeta s≠0 :=
 Cycle25.zeta_of_hecke (by norm_num [Record1252270103Finite.theta,Record1252270103Finite.c])
 (hecke_of_literal_numerator h) s hs
end Final
namespace Intermediate
local instance : Geometry.Parameters := Geometry.intermediateParameters
local instance : Geometry.Bounds := Geometry.intermediateBounds
abbrev LiteralNumeratorInput : Prop := GenericPhysical.FinalAssembly.ChosenFiniteNumeratorInput

theorem beta_of_literal_numerator (h : LiteralNumeratorInput) :
 HeckeZeroSupremum.beta≤(8747759/10000000:ℝ) :=
 GenericPhysical.FinalAssembly.beta_le_theta_of_finite_numerator h
end Intermediate
end
end QRH.Record1252270103Return
#print axioms QRH.Record1252270103Return.Final.beta_of_literal_numerator
#print axioms QRH.Record1252270103Return.Final.hecke_of_literal_numerator
#print axioms QRH.Record1252270103Return.Final.dirichlet_of_literal_numerator
#print axioms QRH.Record1252270103Return.Final.zeta_of_literal_numerator
#print axioms QRH.Record1252270103Return.Intermediate.beta_of_literal_numerator
