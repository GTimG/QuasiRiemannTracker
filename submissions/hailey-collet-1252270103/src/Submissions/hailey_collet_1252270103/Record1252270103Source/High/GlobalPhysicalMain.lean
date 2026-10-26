/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Corrected MAIN applied to the actual marked-squarefree Input coefficient.
Both tuple projectors remain inside the finite column sum. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.CoupledFirstData
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.SourceAmplifier
import Submissions.hailey_collet_1252270103.Record1252270103Source.Collision.Projector

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceRow CenteredMomentSourceProfileMass CenteredMomentGaussEnergy
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentOriginalCommonHarmonic CenteredMomentPrimePool
open CenteredMomentPrimeElements
open Record1252270103Source Record1252270103Source.Collision
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

theorem marked_input_column_valuation (s : Input ι) (A₁ A₂ D K R seed I : Ideal O)
    (F : Ideal O→ℂ)
    (h : CoupledFirst.coefficient s (markedSourceModifier A₁ A₂ D K F) R seed I≠0) :
    Record1252270103CommonGeometry.ValuationAtMostTwo I := by
  unfold CoupledFirst.coefficient at h
  exact marked_source_column_valuation_bound _ A₁ A₂ D K F
    (fun v=>profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed v) I h

/-- The actual norm support supplies the MAIN column cap. No norm comparison
with the unprojected coefficient is used. -/
theorem actual_marked_corrected_main
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
          (correctedCoefficient (elementPool P) (sourceGenerator T) c)
          ballProfile (Z^(M+6*L))).re := by
  let β := fun v=>
    QRH.Record1252270103TwoIdeal.squarefreeIndicator (K*markedProduct v)*
      profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed v
  have he : (fun v=>sourceModifier A₁ A₂ D F v*β v)=
      CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ D K F) R seed := by
    funext v
    simp only [β,CoupledFirst.tupleCoefficient,markedSourceModifier]
    ring
  have hec : finiteColumnCoefficient (Fintype.piFinset s.pools)
      (fun v=>sourceModifier A₁ A₂ D F v*β v)=
      CoupledFirst.coefficient s (markedSourceModifier A₁ A₂ D K F) R seed := by
    rw [he]
    unfold CoupledFirst.coefficient
    congr 1
    ext v
    simp
  have hcolumn (I : Ideal O) (_hI : I∈finiteColumns (Fintype.piFinset s.pools))
      (hne : finiteColumnCoefficient (Fintype.piFinset s.pools)
        (fun v=>sourceModifier A₁ A₂ D F v*β v) I≠0) : (I.absNorm:ℝ)≤Z^B := by
    rw [hec] at hne
    exact (CoupledFirst.original_column_norm s (markedSourceModifier A₁ A₂ D K F)
      R seed I hz₁ hz₂ hne).2.trans hsource
  have hh := corrected_source_dyadic_main s.pools A₁ A₂ D F β Γ P hP hp hbad hmarked
    n Z ell L M B hZ hell hscale hlower hupper hsize hcolumn hdyad
  simp only [hec] at hh
  exact hh

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.marked_input_column_valuation
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_marked_corrected_main
