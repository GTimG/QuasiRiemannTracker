/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.Transport.Transport.LowNormalizer
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.Physical
set_option autoImplicit false
namespace OAI
noncomputable section
variable [QRH.LewkoStage2Return.Geometry.Parameters] [QRH.LewkoStage2Return.Geometry.Bounds]
open scoped Classical ContDiff
open Filter Asymptotics
namespace SevenEighths.LewkoStage2TransportLow
open HeckeFamily ProbePhysical ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues
open ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

def normalizedProbe {K : ℕ} (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    [NeZero (∏P∈S,P)] (ell : Fin K→ℝ) (a b : ℝ) (W : Fin K→ℝ→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (η : Character) (Z : ℝ) : ℂ :=
  let Yp := fun j=>Z^(ell j)
  let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
  compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
    (fun j=>canonicalSlotSupport (T j)) (fun j y=>(W j y:ℂ)) Yp
    (Z^(LewkoStage2Return.Transport.Arithmetic.x:ℝ)) (Z^(LewkoStage2Return.Transport.Arithmetic.y:ℝ)) Z /
    (sourceResidueConstant W0 W1 (∏P∈S,P)*
      (Probe.principalScalar Finset.univ Z (LewkoStage2Return.Transport.Arithmetic.ell) (slotMass T (residueWeights W Yp)) : ℂ))

lemma isBigO_rpow_of_eventual_norm_bound (f : ℝ→ℂ) (r : ℝ)
    (h : ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,‖f Z‖≤C*Z^r) :
    f=O[atTop](fun Z : ℝ=>Z^r) := by
  obtain ⟨C,hC,hb⟩ := h
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [hb,eventually_ge_atTop (0:ℝ)] with Z hb hZ
  simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hZ r)] using hb

end SevenEighths.LewkoStage2TransportLow
end
end OAI
#print axioms OAI.SevenEighths.LewkoStage2TransportLow.normalizedProbe
#print axioms OAI.SevenEighths.LewkoStage2TransportLow.isBigO_rpow_of_eventual_norm_bound
