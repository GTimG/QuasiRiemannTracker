/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal fixed rows, including the original frequency generator and reflection. -/
import Candidate.C092.transport.FixedFourierH15All

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily RayFourExpansion CanonicalQuadraticSieve
open CenteredMomentCanonicalFirst
open CenteredMomentChildAssembly CenteredMomentSecondCanonicalScalar CenteredMomentProductCRT
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair
open CenteredMomentRowNorm CenteredMomentSecondSectorColumns CenteredMomentChildRows
open CenteredMomentSecondScaled CanonicalRowCompletion CenteredExceptionalProfile
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondEnergySplit CenteredMomentSecondExceptionalKernel
open QRH.Cycle092.SignedCenter
namespace QRH.Cycle092.FixedFourierH15
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-- No auxiliary character or coefficient factorization is assumed: the datum
is obtained directly from the genuine inducing-row classifier. -/
def fixedDatum (η : Character) (Q : Id) (m A z : O)
    (hQ : Q≠0) (hm : m≠0) (hA : A≠0) (hz : z≠0)
    (hl : ConcretePrimeRowBridge.goodLambda∣m) (h2 : (2:O)∣m)
    (hf : FixedInducingRow η Q m A z) : FixedCubeDatum :=
  ⟨η,Q,m,A,z,hQ,hm,hA,hz,hl,h2,hf⟩

lemma fixedInducingRow_absorb (η : Character) (Q : Id) (m A z : O) :
    FixedInducingRow η Q m A z ↔ FixedInducingRow η Q m 1 (A*z) := by
  simp only [FixedInducingRow,one_mul]

/-- Absorb the physical generator into the native packed row. -/
def absorbDatum (D : FixedCubeDatum) : FixedCubeDatum :=
  fixedDatum D.η D.Q D.m 1 (D.A*D.z) D.hQ D.hm one_ne_zero
    (mul_ne_zero D.hA D.hz) D.hml D.hm2 ((fixedInducingRow_absorb _ _ _ _ _).mp D.fixed)

lemma absorbDatum_coefficient (D : FixedCubeDatum) :
    (absorbDatum D).actualCoefficient=D.actualCoefficient := by
  funext I
  simp only [FixedCubeDatum.actualCoefficient,absorbDatum,fixedDatum,one_mul]

/-- Both divisibility and the original moving coefficient survive the change
of row variable. This identity also permits arbitrary Fourier window factors. -/
lemma rowPolynomial_absorb {α : Type*} (S : Finset α) (a : α→O) (c q : α→ℂ)
    (L : Id) (χ : RayCharacter) (A z : O) :
    rowPolynomial S a (fun i=>divisorCoefficient L a (movingCoefficient A a c) χ i*q i) z =
      rowPolynomial S a (fun i=>divisorCoefficient L a (movingCoefficient 1 a c) χ i*q i) (A*z) := by
  unfold rowPolynomial
  apply Finset.sum_congr rfl
  intro i hi
  simp only [divisorCoefficient_moving,idealRowHom_argument_mul]
  have hh := idealRowHom_argument_mul (1:O) A (Ideal.span {a i})
  simp only [one_mul] at hh
  linear_combination (divisorCoefficient L a c χ i*q i*idealRowHom z (Ideal.span {a i}))*hh

lemma nativeRowPolynomial_absorb {ι : Type*} [Fintype ι] {a b : ℝ}
    (s : Source ι a b) (ha : 0<a) (D : FixedCubeDatum)
    (ω₁ ω₂ η : Character) (χ : RayCharacter) (G : Id) (hG : Supported G) (L : Id) (t : ℝ) :
    nativeRowPolynomial s ha D ω₁ ω₂ η χ G hG L t =
      nativeRowPolynomial s ha (absorbDatum D) ω₁ ω₂ η χ G hG L t := by
  simpa only [nativeRowPolynomial,absorbDatum,fixedDatum,mul_one] using
    rowPolynomial_absorb Finset.univ _ _ (fun _=>1) L χ D.A D.z

lemma nativeWindowPolynomial_absorb {ι : Type*} [Fintype ι] {a b : ℝ}
    (s : Source ι a b) (ha : 0<a) (D : FixedCubeDatum)
    (ω₁ ω₂ η : Character) (χ : RayCharacter) (G : Id) (hG : Supported G) (L : Id)
    (t θ X : ℝ) (V : ℝ→ℂ) :
    nativeWindowPolynomial s ha D ω₁ ω₂ η χ G hG L t θ X V =
      nativeWindowPolynomial s ha (absorbDatum D) ω₁ ω₂ η χ G hG L t θ X V := by
  exact rowPolynomial_absorb Finset.univ _ _ _ L χ D.A D.z

lemma partRows_true_spec (η : Character) (χ₀ : RayCharacter) (Q : Id) (m : O)
    (C D : Id) (U : Finset (CommonIndex C D)) (R : ℝ) (z : O)
    (hz : z∈partRows true η χ₀ Q m C D U R) :
    z≠0 ∧ FixedInducingRow (childCharacter η χ₀) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z := by
  have hh := Finset.mem_filter.mp hz
  exact ⟨sourceRows_nonzero C D U R z hh.1,by simpa only [ite_true] using hh.2⟩

/-- Every original fixed physical row supplies the left and reflected right
inducing data for every genuine ray-character pair. -/
def partLeftDatum (η : Character) (χ₀ χ ξ : RayCharacter) (Q : Id)
    (hQ : Q≠0) (hQ72 : Q≤Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hl : ConcretePrimeRowBridge.goodLambda∣m) (h2 : (2:O)∣m)
    (C D : Id) (hC : Supported C) (U : Finset (CommonIndex C D)) (R : ℝ)
    (z : O) (hz : z∈partRows true η χ₀ Q m C D U R) : FixedCubeDatum :=
  fixedDatum (childCharacter η χ) Q m
    (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z hQ hm
    (mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC) (nonunitFrequencyGenerator_ne_zero C D hC U))
    (partRows_true_spec η χ₀ Q m C D U R z hz).1 hl h2
    ((exceptional_rows_pair η χ₀ χ ξ Q hQ72 m _ hl h2 _
      (fun z hz=>(partRows_true_spec η χ₀ Q m C D U R z hz).2)).1 z hz)

def partRightDatum (η : Character) (χ₀ χ ξ : RayCharacter) (Q : Id)
    (hQ : Q≠0) (hQ72 : Q≤Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hl : ConcretePrimeRowBridge.goodLambda∣m) (h2 : (2:O)∣m)
    (C D : Id) (hC : Supported C) (U : Finset (CommonIndex C D)) (R : ℝ)
    (z : O) (hz : z∈partRows true η χ₀ Q m C D U R) : FixedCubeDatum :=
  fixedDatum (childCharacter η (ξ⁻¹)) Q m
    (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) (-z) hQ hm
    (mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC) (nonunitFrequencyGenerator_ne_zero C D hC U))
    (neg_ne_zero.mpr (partRows_true_spec η χ₀ Q m C D U R z hz).1) hl h2
    ((exceptional_rows_pair η χ₀ χ ξ Q hQ72 m _ hl h2 _
      (fun z hz=>(partRows_true_spec η χ₀ Q m C D U R z hz).2)).2 z hz)

/-- A nonzero literal native ball weight supplies the honest dyadic radius. -/
lemma fixed_ball_support (z : O) (n : ℤ)
    (hp : (CenteredMomentFirstAmplificationChoice.ballProfile
      (‖ConcreteTraceCRT.eisEmbedding z‖^2/CenteredMomentSectorLocalization.dyadicScale n)).re ≠ 0) :
    ((Ideal.span {z}).absNorm:ℝ) ≤ 2*CenteredMomentSectorLocalization.dyadicScale n := by
  have hc : CenteredMomentFirstAmplificationChoice.ballProfile
      (‖ConcreteTraceCRT.eisEmbedding z‖^2/CenteredMomentSectorLocalization.dyadicScale n) ≠ 0 :=
    fun h=>hp (congrArg Complex.re h)
  have hh := CenteredMomentAmplifiedRetainedRadius.ballProfile_support_upper
    (‖ConcreteTraceCRT.eisEmbedding z‖^2/CenteredMomentSectorLocalization.dyadicScale n)
    (div_nonneg (sq_nonneg _) (CenteredMomentSectorLocalization.dyadicScale_pos n).le) hc
  have hn := ((div_lt_iff₀ (CenteredMomentSectorLocalization.dyadicScale_pos n)).mp hh).le
  simpa only [←CenteredMomentSectorLocalization.normValue_eq_embedding,
    CenteredMomentSectorLocalization.normValue] using hn

#print axioms rowPolynomial_absorb
#print axioms nativeWindowPolynomial_absorb
#print axioms partLeftDatum
#print axioms partRightDatum
end QRH.Cycle092.FixedFourierH15
