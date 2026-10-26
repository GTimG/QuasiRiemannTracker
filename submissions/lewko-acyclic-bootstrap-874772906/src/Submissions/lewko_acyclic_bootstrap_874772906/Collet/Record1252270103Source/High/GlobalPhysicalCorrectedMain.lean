/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The corrected MAIN bound with the literal coefficient consumed by the second
transform, including all marked and ordinary projectors. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalCorrection
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceRow CenteredMomentGaussEnergy CenteredMomentPrimeElements
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentOriginalCommonHarmonic CenteredMomentPrimePool
open Record1252270103Source Record1252270103Source.Collision QRH.Record1252270103Low
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
theorem actual_marked_main_ideal_coefficient
    (s : Input ι) (A₁ A₂ D K R seed : Ideal O) (F Γ : Ideal O→ℂ)
    (P : Finset (Ideal O)) (hP : P.Nonempty)
    (hp : ∀Q∈P,Prime Q) (hbad : ∀Q∈P,Q∉fixedBadPrimes)
    (hmarked : ∀Q∈P,∀i,∀J∈s.pools (Sum.inl i),¬Q∣J)
    (n : ℤ) (Z ell L M B : ℝ) (hZ : 1<Z) (hell : 0<ell)
    (hscale : 0≤M+6*L)
    (hlower : ∀Q∈P,Z^ell≤(Q.absNorm:ℝ))
    (hupper : ∀Q∈P,(Q.absNorm:ℝ)≤Z^L)
    (hsize : 2*(B/ell)≤(P.card:ℝ))
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (hsource : sourceRadius s≤Z^B)
    (hdyad : dyadicScale n≤Z^M) :
    let T:=finiteColumns (Fintype.piFinset s.pools)
    let c:=fun I:supportedColumns T=>
      CoupledFirst.coefficient s (markedSourceModifier A₁ A₂ D K F) R seed I*Γ I
    (∑'h:O,dyadicWeight n (normValue h)*
      ‖gaussPolynomial Finset.univ (sourceGenerator T) (sourceGenerator_supported T) c h‖^2)≤
      (P.card:ℝ)⁻¹*((M+6*L)/ell)*
        (gaussEnergy Finset.univ (sourceGenerator T) (sourceGenerator_supported T)
          (fun I:supportedColumns T=>
            CoupledFirst.coefficient s
              (markedSourceModifier A₁ A₂ 1 K
                (fun J=>(((P.card:ℝ)/((P.card:ℝ)-(idealDividingPool P J).card)):ℂ)*F (D*J)))
              R seed I*Γ I)
          ballProfile (Z^(M+6*L))).re := by
  have hh := actual_marked_corrected_main s A₁ A₂ D K R seed F Γ P hP hp hbad hmarked
    n Z ell L M B hZ hell hscale hlower hupper hsize hz₁ hz₂ hsource hdyad
  dsimp only at hh ⊢
  have he := funext (actual_marked_corrected_coefficient s A₁ A₂ D K R seed F Γ P hp hbad)
  rw [he] at hh
  exact hh

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_marked_main_ideal_coefficient
