/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Conditional canonical endpoint, retaining the exact mixed analytic obligation. -/
import Candidate.C092.transport.FinalCycle092Assembly
noncomputable section
set_option autoImplicit false
open OAI OAI.SevenEighths HeckeFamily
open QRH.Record1252270103Return
namespace QRH.Cycle092.Final

/-- The canonical boundary, principal-pole exception, all Hecke characters and
ordinary Dirichlet target follow from only the retained mixed packet input. -/
theorem exact_targets_of_mixed [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]
    (contact : ℝ) (hx : QRH.RationalInterval.Contains QRH.ContactCertificate.alphaInterval contact)
    (hboundary : Geometry.theta=Cycle090.theta)
    (hh : Cycle090.hLower≤Geometry.h) (hh' : Geometry.h≤Cycle090.hUpper)
    (hell : Geometry.ell=Physical.ell) (hmixed : MixedUpperEstimate contact) :
    HeckeZeroSupremum.beta≤Cycle090.theta ∧
    (∀ (η : Character) (s : ℂ),Cycle090.theta<s.re →
      (s≠1 ∨ η.residue≠1) → LFunction η s≠0) ∧ Cycle090.OrdinaryTarget :=
  ProbeAssembly.exact_targets_of_actual_finite hboundary
    (actual_finite_of_mixed contact hx hboundary hh hh' hell hmixed)

/-- This holds throughout the manuscript's actual directed h interval; no
coarse endpoint is substituted for its shifted-contact conductor. The mixed
input is interpreted in the authentic native Q parameter record. -/
theorem canonical_targets_of_mixed (h : ℝ)
    (hl : Cycle090.hLower≤h) (hu : h≤Cycle090.hUpper)
    (contact : ℝ) (hx : QRH.RationalInterval.Contains QRH.ContactCertificate.alphaInterval contact)
    (hmixed : letI : Geometry.Parameters := ActualGeometry.parameters h hl hu
      letI : ActualGeometry.WidenedCoreBounds := ActualGeometry.widenedBounds h hl hu
      MixedUpperEstimate contact) :
    HeckeZeroSupremum.beta≤Cycle090.theta ∧
    (∀ (η : Character) (s : ℂ),Cycle090.theta<s.re →
      (s≠1 ∨ η.residue≠1) → LFunction η s≠0) ∧ Cycle090.OrdinaryTarget := by
  letI : Geometry.Parameters := ActualGeometry.parameters h hl hu
  letI : ActualGeometry.WidenedCoreBounds := ActualGeometry.widenedBounds h hl hu
  apply exact_targets_of_mixed contact hx rfl
    (by simpa only [ActualGeometry.parameters_h] using hl)
    (by simpa only [ActualGeometry.parameters_h] using hu) _ hmixed
  change Cycle090.ell=Physical.ell
  norm_num [Cycle090.ell,Physical.ell,Cycle090.theta]

end QRH.Cycle092.Final
#print axioms QRH.Cycle092.Final.exact_targets_of_mixed
#print axioms QRH.Cycle092.Final.canonical_targets_of_mixed
