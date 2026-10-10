import Cycle25.Energy.Physical.CertifiedZero
import Cycle25.Energy.Physical.RetainedGeometry
import Cycle25.Numerator.ReflectionRetained
import OAI.NumberTheory.DirichletL.Energy.ReferenceLowWindow

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter
namespace SevenEighths.Cycle25WeightedNumeratorPhysical
open Cycle25WeightedNumeratorReflection
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands
open CenteredMomentRetainedWeightedSource CenteredMomentUniformReflectionApproximation
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentEnergyReferenceLowWindow CenteredMomentNaturalPrimitive
local notation "O" => HeckeFamily.O
set_option maxHeartbeats 1000000

/-- Certified fourth moment of the actual natural primitive restoration. The
original scale X, presentation τ, primitive ψ and profile may vary independently
with the row. All dependence on that choice is controlled by the combined
conductor/scale bound and the stated profile seminorm. The selected family can
also be empty, in which case the zero-slot endpoint covers lengths up to U². -/
theorem certified_actual_retained_fourth {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (κ : ℝ) (hκlo : 7/10 ≤ κ) (hκhi : κ ≤ 3/4)
    (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ κ)
    (epsilon Cscale xi : ℝ) (hepsilon : 0 < epsilon) (hCscale : 0 < Cscale) (hxi : 0 < xi) :
    ∃degree:ℕ, ∃H:Finset (ℕ×ℕ), ∃C:ℝ, 0 < C ∧ ∀ᶠU:ℝ in atTop,
      1 < U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows, U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀(τ ψ:rows→Character) (G:rows→𝓢(ℝ,ℂ)) (X:rows→ℝ) (m B Rcap:ℝ),
      (∀i, ∀n:O, elementCoeff (rowCharacter F.S F.exclusions.prime i.val) n = elementCoeff (τ i) n) →
      (∀i, 0 < X i) → 0 ≤ m → m+xi ≤ 2 → 0 < B →
      (∀i, H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i) ≤ B) →
      1 ≤ Rcap → (∀i, (Ideal.absNorm (∏P∈sourcePrimes (τ i) (ψ i),P):ℝ) ≤ Rcap) →
      (∀i, ((ψ i).modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈sourcePrimes (τ i) (ψ i),P):ℝ)
        ≤ Cscale*U^m*X i) →
      ∀T:Finset (Fin D.N), ∀width:T→ℝ, ∀z:T→ℂ, ∀height:ℝ,
      (∀i, 0 ≤ width i) →
      (∀i, width i ≤ Cycle25.Energy.commonMesh 2 0 1 (D.t/4)) →
      (∀i, (z i).re = 17/50) → 0 ≤ height → (∀i, |(z i).im| ≤ height) →
      (2*(m+xi)+6*κ*(∑i,width i) ≤ 1 ∨ T=∅) →
      (∑i:rows, ‖retainedSchwartz (τ i) (ψ i) (G i) (X i) (U^(xi/4))‖^4 *
        ‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (U^(width s)) (z s)‖^2)
        ≤ C*Rcap^epsilon*B^4*(1+2*((m+xi)*Real.log U))^2*
          (1+height)^degree*U^(1+D.t) := by
  obtain ⟨degree,Jp,Cp,hCp,hpositive⟩ := certified_reflected_fourier_moment F κ hκlo hκhi hbeta hκbeta
  obtain ⟨Jz,Cz,hCz,hzero⟩ := certified_reflected_zero_fourier_moment F
  obtain ⟨H,Cr,hCr,hretained⟩ := actual_retained_uniform_fourth epsilon hepsilon 2 (Jp+Jz) (by norm_num)
  refine ⟨degree,H,Cr*(Cp+Cz),by positivity,?_⟩
  filter_upwards [hpositive,hzero,eventually_retained_log_interval Cscale xi hCscale hxi]
    with U hp hz hg
  have hκpos : 0 < κ := by linarith
  have hU := hp.1
  have hUpos := zero_lt_one.trans hU
  refine ⟨hU,?_⟩
  intro rows hrows τ ψ G X m B Rcap he hX hm hmmax hB hG hRcap hR
    hcombined T width z height hw hwmax hreal hheight hzim hcapacity
  let n := m+xi
  have hn : 0 ≤ n := by dsimp [n]; linarith
  let P (i:rows) := ∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
    (U^(width s)) (z s)
  let E := (Cp+Cz)*(1+height)^degree*U^(1+D.t)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hinterval : 0 ≤ n*Real.log U := mul_nonneg hn (Real.log_pos hU).le
  have hgeom (i:rows) (a:CenteredMomentReflectionWeightedEnergy.Index (sourcePrimes (τ i) (ψ i)))
      (hY:0 < dualScale (τ i) (ψ i) (X i) a.1.1 a.1.2)
      (ha:a.2∈CenteredMomentReflectedTruncation.retainedAnnuli (U^(xi/4))
        (dualScale (τ i) (ψ i) (X i) a.1.1 a.1.2) hY) :
      Real.log (dyadicScale a.2*dualScale (τ i) (ψ i) (X i) a.1.1 a.1.2)
        ∈ Set.Icc 0 (n*Real.log U) := hg.2 (τ i) (ψ i) (X i) m (hX i) (hcombined i) a hY ha
  have hpoly (i:rows) (W:ℝ→ℂ) (x freq:ℝ) :
      polynomial (τ i).inverse false W x 0 freq =
        polynomial (rowCharacter F.S F.exclusions.prime i.val).inverse false W x 0 freq :=
    (Cycle25.Weighted.RowConductor.polynomial_eq_of_elementCoeff_eq _ _
      (Cycle25.Weighted.RowConductor.inverse_elementCoeff_eq _ _ (he i)) false W x 0 freq).symm
  have hmoment (v w:ℝ) (j k:Fin 2) (x:ℝ) (hx:x∈Set.Icc 0 (n*Real.log U))
      (y:ℝ) (hy:y∈Set.Icc 0 (n*Real.log U)) :
      (∑i:rows, ‖polynomial (τ i).inverse false (scaleTest (fun z:ℝ=>(annulus z:ℂ)) j)
        (Real.exp x) 0 (2*Real.pi*v) *
        polynomial (τ i).inverse false (scaleTest (fun z:ℝ=>(annulus z:ℂ)) k)
        (Real.exp y) 0 (2*Real.pi*w) * P i‖^2)
        ≤ E*((1+‖v‖)^(Jp+Jz))^2*((1+‖w‖)^(Jp+Jz))^2 := by
    have hxlen := reflection_window_length U n x hU hn hx
    have hylen := reflection_window_length U n y hU hn hy
    simp_rw [hpoly]
    rcases hcapacity with hcap | hempty
    · have hsum : 0 ≤ ∑s,width s := Finset.sum_nonneg (fun s _=>hw s)
      have hn1 : n ≤ 1 := by dsimp [n]; nlinarith
      have hexp : U^n ≤ U := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hU.le hn1
      have hcap' : length U (Real.exp x)+length U (Real.exp y)+6*κ*(∑s,width s) ≤ 1 := by
        dsimp [n] at hxlen hylen
        linarith [hxlen.1,hylen.1]
      have hb := hp.2 rows hrows T width z height hw hwmax hreal hheight hzim
        (Real.exp x) (Real.exp y) (Real.exp_pos _) (Real.exp_pos _)
        (hxlen.2.trans hexp) (hylen.2.trans hexp) hcap' j k v w
      have hsumBound : (∑i:rows, ‖polynomial (rowCharacter F.S F.exclusions.prime i.val).inverse false
          (scaleTest (fun z:ℝ=>(annulus z:ℂ)) j) (Real.exp x) 0 (2*Real.pi*v) *
          polynomial (rowCharacter F.S F.exclusions.prime i.val).inverse false
          (scaleTest (fun z:ℝ=>(annulus z:ℂ)) k) (Real.exp y) 0 (2*Real.pi*w) * P i‖^2) ≤
          (Cp*(1+height)^degree*U^(1+D.t))*((1+‖v‖)^Jp)^2*((1+‖w‖)^Jp)^2 := by
        rw [←Finset.sum_coe_sort rows] at hb
        simpa only [P] using hb
      apply hsumBound.trans
      dsimp [E]
      gcongr <;> first | linarith [norm_nonneg v,norm_nonneg w,abs_nonneg v,abs_nonneg w] | omega
    · have hslot (i:rows) : P i = 1 := by subst T; simp [P]
      simp only [hslot,mul_one]
      have hexp : U^n ≤ U^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le hU.le hmmax
      have hb := hz.2 rows hrows (Real.exp x) (Real.exp y) (Real.exp_pos _) (Real.exp_pos _)
        (hxlen.2.trans hexp) (hylen.2.trans hexp) j k v w
      have hsumBound : (∑i:rows, ‖polynomial (rowCharacter F.S F.exclusions.prime i.val).inverse false
          (scaleTest (fun z:ℝ=>(annulus z:ℂ)) j) (Real.exp x) 0 (2*Real.pi*v) *
          polynomial (rowCharacter F.S F.exclusions.prime i.val).inverse false
          (scaleTest (fun z:ℝ=>(annulus z:ℂ)) k) (Real.exp y) 0 (2*Real.pi*w)‖^2) ≤
          (Cz*U^(1+D.t))*((1+‖v‖)^Jz)^2*((1+‖w‖)^Jz)^2 := by
        rw [←Finset.sum_coe_sort rows] at hb
        exact hb
      apply hsumBound.trans
      have hfac : Cz ≤ (Cp+Cz)*(1+height)^degree := by
        apply (show Cz ≤ Cp+Cz by linarith).trans
        exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by linarith))
      dsimp [E]
      gcongr <;> first | exact hfac | linarith [norm_nonneg v,norm_nonneg w,abs_nonneg v,abs_nonneg w] | omega
  have hresult := hretained G τ ψ P X (fun _=>U^(xi/4)) 0 (n*Real.log U) B E Rcap
    hX hinterval hgeom hB hE hG hRcap hR hmoment
  convert hresult using 1 <;> dsimp [E,n] <;> ring

end SevenEighths.Cycle25WeightedNumeratorPhysical
end
end OAI

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 keeps the original physical family and explicit variable-kappa capacity. -/
