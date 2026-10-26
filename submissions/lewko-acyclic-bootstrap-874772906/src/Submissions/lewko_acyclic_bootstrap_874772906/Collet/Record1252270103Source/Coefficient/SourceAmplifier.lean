/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Instantiation of the corrected MAIN norm with literal source generators.
Pool squarefreeness and correction denominators are proved from the actual
nonzero tuple witness, slot separation and polynomial norm support. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.AmplifierSupport

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap
open CanonicalQuadraticSieve ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentGaussEnergy CenteredMomentPrimeElements CenteredMomentPrimePool
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentAmplificationSlotGap
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

theorem corrected_source_dyadic_main
    (S : (ι⊕Fin 2)→Finset (Ideal O)) (A₁ A₂ D : Ideal O) (F : Ideal O→ℂ)
    (β : Tuple ι→ℂ) (Γ : Ideal O→ℂ)
    (P : Finset (Ideal O)) (hP : P.Nonempty)
    (hp : ∀Q∈P,Prime Q) (hbad : ∀Q∈P,Q∉fixedBadPrimes)
    (hmarked : ∀Q∈P,∀i,∀J∈S (Sum.inl i),¬Q∣J)
    (n : ℤ) (Z ell L M B : ℝ) (hZ : 1<Z) (hell : 0<ell)
    (hscale : 0≤M+6*L)
    (hlower : ∀Q∈P,Z^ell≤(Ideal.absNorm Q:ℝ))
    (hupper : ∀Q∈P,(Ideal.absNorm Q:ℝ)≤Z^L)
    (hsize : 2*(B/ell)≤(P.card:ℝ))
    (hcolumn : ∀I∈finiteColumns (Fintype.piFinset S),
      finiteColumnCoefficient (Fintype.piFinset S) (fun v=>sourceModifier A₁ A₂ D F v*β v) I≠0 →
      (Ideal.absNorm I:ℝ)≤Z^B)
    (hdyad : dyadicScale n≤Z^M) :
    let T:=finiteColumns (Fintype.piFinset S)
    let c:=fun I:supportedColumns T=>
      finiteColumnCoefficient (Fintype.piFinset S) (fun v=>sourceModifier A₁ A₂ D F v*β v) I*Γ I
    (∑'h:O,dyadicWeight n (normValue h)*
      ‖gaussPolynomial Finset.univ (sourceGenerator T) (sourceGenerator_supported T) c h‖^2)≤
      (P.card:ℝ)⁻¹*((M+6*L)/ell)*
        (gaussEnergy Finset.univ (sourceGenerator T) (sourceGenerator_supported T)
          (correctedCoefficient (elementPool P) (sourceGenerator T) c)
          ballProfile (Z^(M+6*L))).re := by
  dsimp only
  let T:=finiteColumns (Fintype.piFinset S)
  let c:=fun I:supportedColumns T=>
    finiteColumnCoefficient (Fintype.piFinset S) (fun v=>sourceModifier A₁ A₂ D F v*β v) I*Γ I
  have hdata:=elementPool_data P hp hbad
  have hcard:=elementPool_card P hp hbad
  have hcap (I:supportedColumns T) (hci:c I≠0) : (Ideal.absNorm I.val:ℝ)≤Z^B :=
    hcolumn I (Finset.mem_filter.mp I.property).1 (mul_ne_zero_iff.mp hci).1
  have he := corrected_dyadic_energy_ball Finset.univ (sourceGenerator T) (sourceGenerator_supported T) c
    n (elementPool P) (Finset.Nonempty.image hP _)
    (fun p hpm=>(hdata p hpm).1)
    (fun p hpm=>(hdata p hpm).2.2.2.1)
    (fun p hpm=>(hdata p hpm).2.2.2.2.1)
    (fun p hpm=>(hdata p hpm).2.2.2.2.2)
    (fun p hpm=>(hdata p hpm).2.2.1) ?_ ?_ Z ell M L hZ hell hscale
    (fun p hpm=>hlower _ (hdata p hpm).2.1)
    (fun p hpm=>hupper _ (hdata p hpm).2.1) hdyad
  · simpa only [hcard] using he
  · intro I hI hci p hpm
    apply source_generator_no_prime_square T I p
    exact source_column_no_prime_square S A₁ A₂ D F β I (Ideal.span {p})
      (hp _ (hdata p hpm).2.1) (hmarked _ (hdata p hpm).2.1) (mul_ne_zero_iff.mp hci).1
  · intro I hI hci
    apply dividingPool_card_lt_of_geometry (elementPool P) (Finset.Nonempty.image hP _)
      (sourceGenerator T I) ?_ (fun p hpm=>(hdata p hpm).1)
      (fun p hpm=>(hdata p hpm).2.2.1) Z ell B hZ hell
      (fun p hpm=>hlower _ (hdata p hpm).2.1) ?_ ?_
    · exact Ideal.span_singleton_eq_bot.not.mp (sourceGenerator_supported T I).1
    · simpa only [sourceGenerator,primary_span_supported I (Finset.mem_filter.mp I.property).2] using hcap I hci
    · simpa only [hcard] using hsize

/-- The finite pool is separated from every marked factor by the actual norm
gap. Its choice is independent of tuple coefficients and Mellin heights. -/
theorem pool_avoids_marked_factors
    (S : (ι⊕Fin 2)→Finset (Ideal O)) (P : Finset (Ideal O))
    (hp : ∀Q∈P,Prime Q) (hs : ∀i,∀J∈S (Sum.inl i),Prime J)
    (Z ell eta b : ℝ) (hgap : b*Z^eta<Z^ell)
    (hlower : ∀Q∈P,Z^ell≤(Ideal.absNorm Q:ℝ))
    (hupper : ∀i,∀J∈S (Sum.inl i),(Ideal.absNorm J:ℝ)≤b*Z^eta) :
    ∀Q∈P,∀i,∀J∈S (Sum.inl i),¬Q∣J := by
  intro Q hQ i J hJ
  exact amplifier_not_dvd_slot Q J (hp Q hQ) (hs i J hJ) Z ell eta b hgap
    (hlower Q hQ) (hupper i J hJ)

end
end OAI.SevenEighths.Record1252270103Source

#print axioms OAI.SevenEighths.Record1252270103Source.corrected_source_dyadic_main
#print axioms OAI.SevenEighths.Record1252270103Source.pool_avoids_marked_factors
