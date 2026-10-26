/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
The exact whole-pool corrected amplifier pays one inverse pool cardinality.
Only nonzero annular rows are pushed forward. The corrected coefficient stays
inside the enlarged positive Gauss norm throughout. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.PoolPayment
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstAmplificationChoice

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap
open CanonicalQuadraticSieve ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentGaussEnergy CenteredMomentAmplificationEnergy
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
local notation "O" => ActualEisensteinCubic.O

theorem corrected_gauss_energy_pushforward {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (c : α→ℂ)
    (rows P : Finset O) (hP : P.Nonempty)
    (hrows : ∀h∈rows,h≠0) (hp : ∀p∈P,Prime p)
    (hs : ∀p∈P,Supported (Ideal.span {p}))
    (hg : ∀p∈P,goodLambda∉Ideal.span {p})
    (hc : ∀p∈P,ringChar (O⧸Ideal.span {p})≠2)
    (hprimary : ∀p∈P,goodLambda^2∣p-1)
    (hsq : ∀i∈S,c i≠0 →∀p∈P,¬p^2∣a i)
    (hsmall : ∀i∈S,c i≠0 →(dividingPool P (a i)).card<P.card)
    (Z ell M L : ℝ) (hZ : 1<Z) (hell : 0<ell)
    (hpl : ∀p∈P,Z^ell≤(Ideal.absNorm (Ideal.span {p}):ℝ))
    (hpu : ∀p∈P,(Ideal.absNorm (Ideal.span {p}):ℝ)≤Z^L)
    (hhu : ∀h∈rows,(Ideal.absNorm (Ideal.span {h}):ℝ)≤Z^M) :
    (∑h∈rows,‖gaussPolynomial S a ha c h‖^2)≤
      (P.card:ℝ)⁻¹*((M+6*L)/ell)*
        ∑y∈(rows×ˢP).image outputRow,‖gaussPolynomial S a ha (correctedCoefficient P a c) y‖^2 := by
  have hpoint : (∑h∈rows,‖gaussPolynomial S a ha c h‖^2)≤
      (P.card:ℝ)⁻¹*∑h∈rows,∑p∈P,
        ‖gaussPolynomial S a ha (correctedCoefficient P a c) (p^6*h)‖^2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun h _=>corrected_pool_bound S a ha c P hP hp hs hg hc hsq hsmall h)
  have hpush := amplified_energy_pushforward rows P (fun _ _=>True) hrows hp hprimary
    Z ell M L hZ hell hpl hpu hhu (gaussPolynomial S a ha (correctedCoefficient P a c))
  simp only [eligiblePairs,Finset.filter_true] at hpush
  change (∑x∈rows×ˢP,‖gaussPolynomial S a ha (correctedCoefficient P a c) (outputRow x)‖^2)≤
    ((M+6*L)/ell)*∑y∈(rows×ˢP).image outputRow,
      ‖gaussPolynomial S a ha (correctedCoefficient P a c) y‖^2 at hpush
  have he : (∑h∈rows,∑p∈P,‖gaussPolynomial S a ha (correctedCoefficient P a c) (p^6*h)‖^2)=
      ∑x∈rows×ˢP,‖gaussPolynomial S a ha (correctedCoefficient P a c) (outputRow x)‖^2 := by
    simp only [Finset.sum_product,outputRow]
  rw [he] at hpoint
  exact hpoint.trans ((mul_le_mul_of_nonneg_left hpush (by positivity)).trans_eq (mul_assoc _ _ _).symm)

theorem corrected_gauss_energy_ball {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (c : α→ℂ)
    (rows P : Finset O) (hP : P.Nonempty)
    (hrows : ∀h∈rows,h≠0) (hp : ∀p∈P,Prime p)
    (hs : ∀p∈P,Supported (Ideal.span {p}))
    (hg : ∀p∈P,goodLambda∉Ideal.span {p})
    (hc : ∀p∈P,ringChar (O⧸Ideal.span {p})≠2)
    (hprimary : ∀p∈P,goodLambda^2∣p-1)
    (hsq : ∀i∈S,c i≠0 →∀p∈P,¬p^2∣a i)
    (hsmall : ∀i∈S,c i≠0 →(dividingPool P (a i)).card<P.card)
    (Z ell M L : ℝ) (hZ : 1<Z) (hell : 0<ell) (hscale : 0≤M+6*L)
    (hpl : ∀p∈P,Z^ell≤(Ideal.absNorm (Ideal.span {p}):ℝ))
    (hpu : ∀p∈P,(Ideal.absNorm (Ideal.span {p}):ℝ)≤Z^L)
    (hhu : ∀h∈rows,(Ideal.absNorm (Ideal.span {h}):ℝ)≤Z^M) :
    (∑h∈rows,‖gaussPolynomial S a ha c h‖^2)≤
      (P.card:ℝ)⁻¹*((M+6*L)/ell)*
        (gaussEnergy S a ha (correctedCoefficient P a c) ballProfile (Z^(M+6*L))).re := by
  have hpos := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (M+6*L)
  have hball := finite_energy_le_gaussEnergy S a ha (correctedCoefficient P a c)
    ballProfile (Z^(M+6*L)) hpos ((rows×ˢP).image outputRow)
    (fun z=>ballProfile_nonneg _) (by
      intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨hx,hp'⟩ := Finset.mem_product.mp hx
      apply ballProfile_majorizes _ hpos
      exact outputRow_norm x Z M L (zero_lt_one.trans hZ) (hhu x.1 hx) (hpu x.2 hp'))
  exact (corrected_gauss_energy_pushforward S a ha c rows P hP hrows hp hs hg hc
    hprimary hsq hsmall Z ell M L hZ hell hpl hpu hhu).trans
      (mul_le_mul_of_nonneg_left hball (mul_nonneg (by positivity) (div_nonneg hscale hell.le)))

/-- The annular support excludes zero before the sparse pushforward is used. -/
theorem corrected_dyadic_energy_ball {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (c : α→ℂ)
    (n : ℤ) (P : Finset O) (hP : P.Nonempty) (hp : ∀p∈P,Prime p)
    (hs : ∀p∈P,Supported (Ideal.span {p}))
    (hg : ∀p∈P,goodLambda∉Ideal.span {p})
    (hc : ∀p∈P,ringChar (O⧸Ideal.span {p})≠2)
    (hprimary : ∀p∈P,goodLambda^2∣p-1)
    (hsq : ∀i∈S,c i≠0 →∀p∈P,¬p^2∣a i)
    (hsmall : ∀i∈S,c i≠0 →(dividingPool P (a i)).card<P.card)
    (Z ell M L : ℝ) (hZ : 1<Z) (hell : 0<ell) (hscale : 0≤M+6*L)
    (hpl : ∀p∈P,Z^ell≤(Ideal.absNorm (Ideal.span {p}):ℝ))
    (hpu : ∀p∈P,(Ideal.absNorm (Ideal.span {p}):ℝ)≤Z^L)
    (hdyad : dyadicScale n≤Z^M) :
    (∑'h:O,dyadicWeight n (normValue h)*‖gaussPolynomial S a ha c h‖^2)≤
      (P.card:ℝ)⁻¹*((M+6*L)/ell)*
        (gaussEnergy S a ha (correctedCoefficient P a c) ballProfile (Z^(M+6*L))).re := by
  apply (dyadic_energy_le_sum n _).trans
  exact corrected_gauss_energy_ball S a ha c (dyadRows n) P hP
    (dyadRows_ne_zero n) hp hs hg hc hprimary hsq hsmall Z ell M L hZ hell hscale
    hpl hpu (fun h hh=>(dyadRows_norm_lt n h hh).le.trans hdyad)

end
end OAI.SevenEighths.Record1252270103Source

#print axioms OAI.SevenEighths.Record1252270103Source.corrected_gauss_energy_ball
#print axioms OAI.SevenEighths.Record1252270103Source.corrected_dyadic_energy_ball
