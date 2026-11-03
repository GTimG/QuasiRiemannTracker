/- UNVERIFIED low-growth estimate for a concrete original physical probe.
   The companion high estimate and full analytic bridge remain outstanding. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblySource
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.LowEnergyExtension.LowNormalized
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowNormalized
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.CommonProbe
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.ModulusRefinement

namespace OAI

noncomputable section
open scoped Classical ContDiff
open Filter Asymptotics
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues
open ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

def normalizedProbe_retuned (ξ υ total : ℝ) {K : ℕ} (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    [NeZero (∏P∈S,P)] (ell : Fin K→ℝ) (a b : ℝ) (W : Fin K→ℝ→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (η : Character) (Z : ℝ) : ℂ :=
  let Yp := fun j=>Z^(ell j)
  let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
  compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
    (fun j=>canonicalSlotSupport (T j)) (fun j y=>(W j y:ℂ)) Yp
    (Z^ξ) (Z^υ) Z /
    (sourceResidueConstant W0 W1 (∏P∈S,P)*
      (Probe.principalScalar Finset.univ Z (total) (slotMass T (residueWeights W Yp)) : ℂ))

theorem normalizedProbe_low_retuned (ξ υ total : ℝ) (htotal : 0≤total) (htotal1 : total≤1/5)
    (hscale : ξ+υ=1-total) (hgap : 0<υ-ξ)
    (hmargin : 0<2*ξ-υ-total) (hυ : υ≤1) {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (a b B loss : ℝ) (ha : 0<a) (hab : a≤b) (hloss : 0<loss)
    (ell : Fin K→ℝ) (hell : ∀j,0<ell j) (hinj : Function.Injective ell) (hsum : ∑j,ell j=total)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo a b)
    (hWB : ∀j y,0≤W j y ∧ W j y≤B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∀η : Character,normalizedProbe_retuned ξ υ total M H S hmax ell a b W W0 W1 η=O[atTop](fun Z : ℝ=>Z^(((5*ξ+υ)/12)+loss)) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  intro η
  obtain ⟨C,hC,hb⟩ := original_normalized_compensatedPhysicalProbe_low_retuned ξ υ total htotal htotal1 hscale hgap hmargin hυ M H hH S hS hmax
    a b B loss ha hab hloss ell hell hinj hsum W hW hcompact hsupp hWB hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 η
  apply isBigO_rpow_of_eventual_norm_bound
  exact ⟨C,hC,hb.mono (fun Z h=>h.2)⟩

end SevenEighths.ProbeFinalAssembly
end

end OAI

#print axioms OAI.SevenEighths.ProbeFinalAssembly.normalizedProbe_low_retuned
