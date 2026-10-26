import Submissions.hailey_collet_1252270103.Record1252270103Return.Transport.Transport.LowNormalizer
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.Physical
set_option autoImplicit false
namespace OAI
noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [QRH.Record1252270103Return.Geometry.Bounds]
open scoped Classical ContDiff
open Filter Asymptotics
namespace SevenEighths.Record1252270103TransportLow
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
    (Z^(Record1252270103Return.Transport.Arithmetic.x:ℝ)) (Z^(Record1252270103Return.Transport.Arithmetic.y:ℝ)) Z /
    (sourceResidueConstant W0 W1 (∏P∈S,P)*
      (Probe.principalScalar Finset.univ Z (Record1252270103Return.Transport.Arithmetic.ell) (slotMass T (residueWeights W Yp)) : ℂ))

lemma isBigO_rpow_of_eventual_norm_bound (f : ℝ→ℂ) (r : ℝ)
    (h : ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,‖f Z‖≤C*Z^r) :
    f=O[atTop](fun Z : ℝ=>Z^r) := by
  obtain ⟨C,hC,hb⟩ := h
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [hb,eventually_ge_atTop (0:ℝ)] with Z hb hZ
  simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hZ r)] using hb

end SevenEighths.Record1252270103TransportLow
end
end OAI
#print axioms OAI.SevenEighths.Record1252270103TransportLow.normalizedProbe
#print axioms OAI.SevenEighths.Record1252270103TransportLow.isBigO_rpow_of_eventual_norm_bound
