import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.FinalAssemblySourceGeneric
import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.QuasiPerturbationParameters

namespace OAI

noncomputable section
open scoped Classical ContDiff
open Filter Asymptotics
namespace SevenEighths.ProbePhysical
open ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues
open ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

namespace QuasiLow

open OAI.SevenEighths.QuasiPerturbationParameters

theorem original_normalized_compensatedPhysicalProbe_low_quasi {K : ℕ}
    (Mray : Ideal O) [NeZero Mray] [Finite (O ⧸ Mray)]
    (H : Subgroup (O ⧸ Mray)ˣ) (hH : RayOrthogonality.globalUnits Mray≤H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal)
    (a b B loss : ℝ) (ha : 0<a) (hab : a≤b) (hloss : 0<loss)
    (ell : Fin K→ℝ) (hell : ∀j,0<ell j) (hinj : Function.Injective ell)
    (hsum : ∑j,ell j=E)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j))
    (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo a b)
    (hWB : ∀j y,0≤W j y ∧ W j y≤B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re)
    (hn0 : W0≠0) (hn1 : W1≠0) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∀η : HeckeFamily.Character,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
      let Yp := fun j=>Z^(ell j)
      let T := fun j=>pool (RayQuotient.identityClass Mray H) S a b (Yp j)
      let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z E
          (slotMass T (residueWeights W Yp)) : ℂ)
      normer≠0 ∧
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
        (fun j=>canonicalSlotSupport (T j)) WC Yp (Z^lx) (Z^ly) Z/normer‖≤
        C*Z^(sigma-11/16+loss) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  intro η
  obtain ⟨C,hC,hb⟩ := original_normalized_compensatedPhysicalProbe_low_generic
    Mray H hH S hS hmax a b B loss ha hab hloss
    E lx ly E_nonneg E_le_one_fifth source_exponents_sum E_lt_lx lx_lt_ly
    E_lt_two_lx_sub_ly ell hell hinj hsum W hW hcompact hsupp hWB hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 η
  refine ⟨C,hC,?_⟩
  filter_upwards [hb] with Z hZ
  simpa only [gram_exponent_eq_sigma] using hZ

end QuasiLow

end SevenEighths.ProbePhysical

namespace SevenEighths.ProbeFinalAssembly

open HeckeFamily ProbePhysical ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues
open ProbePrincipalResidueActual OAI.SevenEighths.QuasiPerturbationParameters
local notation "O" => HeckeFamily.O

theorem normalizedProbe_low_quasi {K : ℕ}
    (Mray : Ideal O) [NeZero Mray] [Finite (O ⧸ Mray)]
    (H : Subgroup (O ⧸ Mray)ˣ) (hH : RayOrthogonality.globalUnits Mray≤H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal)
    (a b B loss : ℝ) (ha : 0<a) (hab : a≤b) (hloss : 0<loss)
    (ell : Fin K→ℝ) (hell : ∀j,0<ell j) (hinj : Function.Injective ell)
    (hsum : ∑j,ell j=E)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j))
    (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo a b)
    (hWB : ∀j y,0≤W j y ∧ W j y≤B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re)
    (hn0 : W0≠0) (hn1 : W1≠0) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∀η : Character,
      normalizedProbeGeneric E lx ly Mray H S hmax ell a b W W0 W1 η
        =O[atTop](fun Z : ℝ=>Z^(sigma-11/16+loss)) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  intro η
  have h := normalizedProbe_low_generic Mray H hH S hS hmax
    a b B loss ha hab hloss E lx ly E_nonneg E_le_one_fifth
    source_exponents_sum E_lt_lx lx_lt_ly E_lt_two_lx_sub_ly
    ell hell hinj hsum W hW hcompact hsupp hWB hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 η
  simpa only [gram_exponent_eq_sigma] using h

end SevenEighths.ProbeFinalAssembly

end

end OAI
