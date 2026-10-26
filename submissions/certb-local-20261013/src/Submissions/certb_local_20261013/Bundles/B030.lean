/-
Reserve-balanced affine local-capacity adaptation for Kari Roegnvaldsson, with AI assistance.
Based on nielstron local44-20261013 and Kari Roegnvaldsson affine-local-20261013 at c707738.
Retains the amplifier and final savings while reallocating intermediate reserves.
Status: candidate under verification; no admission is claimed here.
All inherited attribution and Apache-2.0 notices are retained below.
Section hashes identify original, pre-adaptation module snapshots.
-/
/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B009
import Submissions.certb_local_20261013.Bundles.B020
import Submissions.certb_local_20261013.Bundles.B021
import Submissions.certb_local_20261013.Bundles.B027
import Submissions.certb_local_20261013.Bundles.B028
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceLowDirect
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceLowReflectionError
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CentralNormalized
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.RestoreCorrection

/- BEGIN ORIGINAL MODULE Cycle25.Energy.ReferenceRobustDeletedEnergy ; sha256 87e026fcb726c43bfb46692baf224c4c0e5f943c4b2d89b4ada4a921c51d8fc4 -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/ReferenceRobustDeletedEnergy.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/






namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.Cycle25CenteredMomentEnergyReferenceRobustDeletedEnergy
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open Cycle25CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open Cycle25CenteredMomentEnergyDeletedRobustGeometry CenteredMomentEnergyReferenceLowReflectionError
open CenteredMomentEnergyReferenceLowDirect CenteredMomentEnergyReferenceChild
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem deleted_energy_from_low_robust
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ epsilon xi defect saving Mcap Bmask L:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hepsilon:0< epsilon)(hxi:0< xi)
    (hdefect:0≤ defect)(hBmask:0≤ Bmask)(hL:Mcap+Bmask+xi≤ L)
    (B:ℕ)(hB:2≤ B)(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0< Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D:ℝ,0< C ∧ 0< D ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(Lslot ε κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap ε κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) → 7/10≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → s.width≤ Mcap → xi+13*defect/8≤ s.width/16 →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      ∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      ∀X₁ X₂:ℝ,0< X₁ → 0< X₂ →
      5*s.width/6-defect≤ Real.logb Z (X₁*X₂)+(∑i,w i) →
      Real.logb Z (X₁*X₂)+(∑i,w i)+(6*κ-1)*(∑i,w i)≤ s.width →
      ∀D₁∈(CompletedGauss.primeSupport s.puncture).powerset,
      ∀D₂∈(CompletedGauss.primeSupport s.puncture).powerset,
      ∀F:Finset α,
      let β:=fun i I=> heightCoefficient (fun I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t I;
      radialEnergy (fun z=> polynomial (naturalCharacter s.character z) false W₁
          (comparisonFirst Z s.width/((∏I∈D₁,I).absNorm:ℝ)) 0 t *
        polynomial (naturalCharacter s.character z) false W₂
          (comparisonSecond Z s.width X₁ X₂/((∏I∈D₂,I).absNorm:ℝ)) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i))) (β i) (Z^(w i)))
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
        K*diagonalControl s.radial.profile*
          ((independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
          (1+|t|+height)^degree*Z^(s.width+ε) +
        (C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
          (1+2*(L*Real.log Z))*
          (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
            (1+|t|+height)^(degree+2*n)*Z^(s.width+ε)) +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*(Z^(s.width/4))*∏i,Z^(w i)):=by
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩:=reference_from_low_with_error (α:=α) M H hH
    Finset.univ Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ epsilon xi saving (Mcap+Bmask) ha hlo hhi hbΦ hepsilon hxi B hB degree S
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Lslot ε κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hs hxiM W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hlarge hcap D₁ hD₁ D₂ hD₂ F
  dsimp only
  let short:=s.width/4-Real.logb Z ((∏I∈D₁,I).absNorm:ℝ)
  let along:=Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏I∈D₂,I).absNorm:ℝ)
  have hsum:0≤∑i∈F,w i:=Finset.sum_nonneg (fun i _=> hw i)
  have hsumle:(∑i∈F,w i)≤∑i,w i:=Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ F) (fun i _ _=> hw i)
  have hg:=actual_deleted_gates s hZ.1 hBmask Mcap L X₁ X₂ (∑i,w i) (∑i∈F,w i) κ xi defect hs hL
    hX₁ hX₂ (Finset.sum_nonneg (fun i _=> hw i)) hsum hsumle hκ hxi.le hdefect hxiM hlarge hcap D₁ D₂ hD₁ hD₂
  dsimp only at hg
  rw [←hg.1,←hg.2.1]
  have hZpos:0< Z:=zero_lt_one.trans hZ.1
  have hdiag:0≤ diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hLpos:0≤ L:=by linarith [s.width_nonneg]
  have hlog:0≤ Real.log Z:=(Real.log_pos hZ.1).le
  have hprod: (∏i∈F,Z^(w i))≤∏i,Z^(w i):=Finset.prod_le_prod_of_subset_of_one_le₀
    (Finset.subset_univ F) (fun i _=> (Real.rpow_pos_of_pos hZpos _).le)
    (fun i _ _=> Real.one_le_rpow hZ.1.le (hw i))
  rcases hg.2.2.2.2.2.2.2 with hd|hr
  · have hdirect:=direct_child_from_low M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S K hlow hBmask ha F θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
      s hQ hs W₁ W₂ hs₁ hs₂ (Z^short) (Z^along)
      (Real.rpow_pos_of_pos hZpos _) (Real.rpow_pos_of_pos hZpos _)
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hg.2.2.2.1)
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hg.2.2.2.2.1) hd.2 hd.1
    exact hdirect.trans (le_add_of_nonneg_right (by positivity))
  · have hh:=hZ.2 Bmask L Lslot Mcap ε κ η₀ Q K hK hlow hBmask F (Finset.subset_univ F)
      θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hs W₂ W₁ hs₂ hs₁ along short
      hg.2.2.2.2.2.1 hg.2.2.2.2.2.2.1 hg.2.2.2.1 hr.2 hr.1
    dsimp only at hh
    have hswap: (fun z=> polynomial (naturalCharacter s.character z) false W₁ (Z^short) 0 t *
        polynomial (naturalCharacter s.character z) false W₂ (Z^along) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i)))
          (heightCoefficient (fun I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i))) =
      (fun z=> polynomial (naturalCharacter s.character z) false W₂ (Z^along) 0 t *
        polynomial (naturalCharacter s.character z) false W₁ (Z^short) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i)))
          (heightCoefficient (fun I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i))):=by funext z;ring
    rw [hswap]
    apply hh.trans
    apply le_trans _ (le_add_of_nonneg_left (by positivity))
    apply add_le_add
    · gcongr
      exact hg.2.2.2.2.2.2.1
    · gcongr
      · exact hZ.1.le
      · exact hg.2.2.1

end SevenEighths.Cycle25CenteredMomentEnergyReferenceRobustDeletedEnergy

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Energy.ReferenceRobustDeletedEnergy -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorActualError ; sha256 9132d48be10872d201a3c5a7d8b8f8d2550605cd850a6015da19f3e99a0124b1 -/
section





/-! Quotient-free physical error factors, with coefficients independent of w. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators NNReal Classical
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ProbeRow
local notation "O" => HeckeFamily.O

def CubicCoefficients.vector (c : CubicCoefficients) : Fin 4 → ℂ := ![c.a,c.b,c.c,c.d]

theorem cubic_vector_eval (c : CubicCoefficients) (T : ℂ) :
    (∑ j : Fin 4, c.vector j * T ^ j.val) = c.eval T := by
  simp [CubicCoefficients.vector,CubicCoefficients.eval,cubic,Fin.sum_univ_four]

theorem cubic_vector_mass (c : CubicCoefficients) (Q : ℝ≥0) (w : ℂ)
    (hQ : 0 < (Q : ℝ)) :
    (∑ j : Fin 4, ‖c.vector j * ((Q : ℂ) ^ (-w)) ^ j.val‖) =
      c.mass ((Q : ℝ) ^ (-w.re)) := by
  simp [CubicCoefficients.vector,CubicCoefficients.mass,cubicMass,
    Fin.sum_univ_four,norm_mul,norm_pow,
    Complex.norm_cpow_eq_rpow_re_of_pos hQ,Complex.neg_re]

def actualRamifiedErrorCoefficients (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (x z : ℂ) : CubicCoefficients :=
  let p := primaryGenerator P.val
  let hp := supported_primeGenerator_prime P hs
  letI : (Ideal.span {p} : Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let hsp : Supported (Ideal.span {p}) := (span_primaryGenerator_of_supported P.val hs).symm ▸ hs
  let hg := (supported_prime_data p hp hsp).1
  ramifiedErrorCoefficients p hp hg (targetMonoid η p) (actualACube η p)
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp)))
    x z (multiplicity p u.val)

def actualErrorCoefficients (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (x z : ℂ) : CubicCoefficients :=
  if P.val ∣ Ideal.span {u.val} then actualRamifiedErrorCoefficients η u P hs x z
  else unramifiedErrorCoefficients P.val.absNorm (actualAPhase η (primaryGenerator P.val))
    (idealCoeff η P.val) (idealRowHom u.val P.val) x z

def rawErrorSlot (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) : ℂ :=
  continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val) * (P.val.absNorm : ℂ)^x) ((P.val.absNorm : ℂ)^(-w)) +
    supportedCorrection η u P x w z * star (idealRowHom u.val P.val)

theorem actual_error_expansion (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (hη : IsCoprime P.val η.modulus)
    (x w z : ℂ) (hQ : (4 : ℝ) ≤ P.val.absNorm)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re) :
    rawErrorSlot η u P hs x w z =
      (actualErrorCoefficients η u P hs x z).eval ((P.val.absNorm : ℂ)^(-w)) := by
  by_cases hd : P.val ∣ Ideal.span {u.val}
  · simp only [rawErrorSlot,row_phase_ramified u P hd,star_zero,mul_zero,add_zero,
      actualErrorCoefficients,if_pos hd]
    rw [continuedCompensatedLocal_ramified η u P hs hd]
    dsimp only [actualRamifiedErrorCoefficients]
    erw [ramified_error_expansion]
    simp only [span_primaryGenerator_of_supported P.val hs]
  · have hA := actualAPhase_norm_le_one η (primaryGenerator P.val)
    have heta := PrincipalSignalComparison.idealCoeff_norm_one_of_coprime η P.val P.property.ne_zero hη
    have hv := row_phase_norm_one_of_not_dvd u P hs hd
    have hV : ‖coordV P.val.absNorm z‖ < 1 :=
      (first_region_V_half _ hQ z hz).trans_lt (by norm_num)
    have hR : ‖coordR P.val.absNorm (actualAPhase η (primaryGenerator P.val)) x z‖ < 1 :=
      (coordR_norm_le _ (by linarith) _ x z hA).trans_lt
        ((rpow_le_half _ _ hQ (by linarith)).trans_lt (by norm_num))
    obtain ⟨hRn,hVn,hDn⟩ := unramified_denominators _ _ _ _ x z hQ hA heta.le hv.le hx hz
    simp only [rawErrorSlot,actualErrorCoefficients,if_neg hd,
      supportedCorrection,dif_pos hs,if_neg hd]
    rw [continuedCompensatedLocal_unramified η u P hs hd x w z hV hR]
    exact unramified_error_expansion _ _ _ _ x w z (by linarith) hRn hVn hDn heta hv

theorem actual_ramified_error_mass (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (x z : ℂ) (alpha eps rho : ℝ)
    (hQ : (4 : ℝ) ≤ P.val.absNorm)
    (halpha : (51 / 100 : ℝ) ≤ alpha) (halpha1 : alpha ≤ 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1 / 1000)
    (hx : x.re = alpha + 16 * eps) (hz : z.re = 17 / 50)
    (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hline : 1 - alpha - 6 * eps ≤ 1 / 2 - rho) :
    (actualRamifiedErrorCoefficients η u P hs x z).mass
      ((P.val.absNorm : ℝ)^(-(1 / 2 - rho))) ≤
      1161 * (P.val.absNorm : ℝ)^(1 / 2 : ℝ) *
        (if 2 ≤ multiplicity (primaryGenerator P.val) u.val then (P.val.absNorm : ℝ)^rho else 1) := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p} = P.val := span_primaryGenerator_of_supported P.val hs
  letI : (Ideal.span {p} : Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hh := ramified_error_coefficient_mass p hp hg.1 hg.2
    (targetMonoid η p) (actualACube η p)
    (actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ (unitPart u p hp))) x z
    alpha eps rho (hspan.symm ▸ hQ) (targetMonoid_norm_le_one η p) (actualACube_norm_le η p)
    (actualSextic_unit_six p (unitPart u p hp) hg.1 hg.2 (unitPart_coprime u p hp))
    halpha halpha1 heps heps1 hx hz hrho hrho1 hline
    (multiplicity p u.val) (multiplicity_lt_six u p hp)
  change (ramifiedErrorCoefficients p hp hg.1 (targetMonoid η p) (actualACube η p)
    (actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ (unitPart u p hp))) x z
    (multiplicity p u.val)).mass _ ≤ _
  simpa only [hspan] using hh

def repeatedDeficit (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) : ℝ≥0 :=
  if P.val ∣ Ideal.span {u.val} ∧ 2 ≤ multiplicity (primaryGenerator P.val) u.val
  then primeScale P else 1

theorem repeatedDeficit_one_le (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) : 1 ≤ repeatedDeficit u P := by
  unfold repeatedDeficit
  split_ifs
  · exact primeScale_one_le P
  · rfl

def errorSize (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) : ℝ :=
  if P.val ∣ Ideal.span {u.val} then (P.val.absNorm : ℝ)^(1 / 2 : ℝ)
  else (P.val.absNorm : ℝ)^(-(51 / 100 : ℝ))

theorem actual_error_coefficient_mass (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (hη : IsCoprime P.val η.modulus)
    (x z : ℂ) (alpha eps rho : ℝ) (hQ : (4 : ℝ) ≤ P.val.absNorm)
    (halpha : (51 / 100 : ℝ) ≤ alpha) (halpha1 : alpha ≤ 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1 / 1000)
    (hx : x.re = alpha + 16 * eps) (hz : z.re = 17 / 50)
    (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hline : 1 - alpha - 6 * eps ≤ 1 / 2 - rho) :
    (actualErrorCoefficients η u P hs x z).mass ((P.val.absNorm : ℝ)^(-(1 / 2 - rho))) ≤
      2880 * errorSize u P * (repeatedDeficit u P : ℝ)^rho := by
  by_cases hd : P.val ∣ Ideal.span {u.val}
  · have hh := actual_ramified_error_mass η u P hs x z alpha eps rho hQ
      halpha halpha1 heps heps1 hx hz hrho hrho1 hline
    simp only [actualErrorCoefficients,if_pos hd,errorSize,repeatedDeficit,hd,true_and,
      primeScale] at *
    split_ifs with hj
    · simp only [ite_eq_left hj] at hh
      simp only [NNReal.coe_natCast]
      exact hh.trans (by gcongr <;> norm_num)
    · simp only [ite_eq_right hj,mul_one] at hh
      simp only [NNReal.coe_one,Real.one_rpow,mul_one]
      exact hh.trans (by gcongr <;> norm_num)
  · have heta := PrincipalSignalComparison.idealCoeff_norm_one_of_coprime η P.val P.property.ne_zero hη
    have hv := row_phase_norm_one_of_not_dvd u P hs hd
    simp only [actualErrorCoefficients,if_neg hd,errorSize,repeatedDeficit,hd,false_and,
      if_false,NNReal.coe_one,Real.one_rpow,mul_one]
    exact unramified_error_coefficient_mass _ alpha eps (1 / 2 - rho) _ _ _ x z
      hQ halpha halpha1 heps heps1 (actualAPhase_norm_le_one η _) heta hv hx hz hline

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorActualError -/

/- BEGIN ORIGINAL MODULE Endpoint.Perturbation ; sha256 b611d932dba4f2f7ce2ac3e5c68cccc3c32af626f29aeffd9597ef5a796a1903 -/
section


/-! Finite differences at the actual moment parameter preserve the strict
scalar reserve. These statements concern the row-exponent ledger. -/

noncomputable section
namespace Submission20261012.Endpoint

set_option maxHeartbeats 1000000

private lemma source_row_kappa_effect (κ d δ p : ℝ)
    (hk : kappa ≤ κ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    (3 * d / 4) * (Cycle25.Arithmetic.rowExponent κ δ p -
      Cycle25.Arithmetic.rowExponent kappa δ p) ≤ (5 / 288) * (κ - kappa) := by
  have hgap : 0 ≤ κ - kappa := sub_nonneg.mpr hk
  have hrow := Cycle25.Arithmetic.row_gap
    (show (7 : ℝ) / 10 ≤ kappa by norm_num [kappa]) hk
    ⟨hδ0, by linarith⟩ ⟨hp0, hp1⟩
  calc
    _ ≤ (3 * d / 4) * ((5 / 12) * ((κ - kappa) / 18)) :=
      mul_le_mul_of_nonneg_left hrow (by positivity)
    _ ≤ (5 / 288) * (κ - kappa) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hd1) hgap]

/-- On the new local branch the numerator cost stays fixed. -/
theorem source_local_kappa_gap (κ d δ p : ℝ)
    (hk : kappa ≤ κ) (hdlo : dmin ≤ d) (hdhi : d ≤ h + zeta)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    sourceLocalRowExponent κ d δ p -
      sourceLocalRowExponent kappa d δ p ≤ (κ - kappa) / 50 := by
  have hd0 : 0 ≤ d := (by norm_num [dmin] : (0 : ℝ) ≤ dmin).trans hdlo
  have hd1 : d ≤ 1 := hdhi.trans (by norm_num [h, zeta])
  have hgap : 0 ≤ κ - kappa := sub_nonneg.mpr hk
  have hrow := source_row_kappa_effect κ d δ p hk hd0 hd1 hδ0 hδ1 hp0 hp1
  have hid : sourceLocalRowExponent κ d δ p -
      sourceLocalRowExponent kappa d δ p =
      (3 * d / 4) * (Cycle25.Arithmetic.rowExponent κ δ p -
        Cycle25.Arithmetic.rowExponent kappa δ p) := by
    unfold sourceLocalRowExponent
    ring
  rw [hid]
  linarith

/-- The old branch also charges the variation of its numerator cost `6κ`. -/
theorem source_old_kappa_gap (κ d δ p : ℝ)
    (hk : kappa ≤ κ) (hdlo : dmin ≤ d) (hdhi : d ≤ h + zeta)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    sourceGlobalRowExponent κ d (6 * κ) δ p -
      sourceGlobalRowExponent kappa d (6 * kappa) δ p ≤ (κ - kappa) / 8 := by
  have hd0 : 0 ≤ d := (by norm_num [dmin] : (0 : ℝ) ≤ dmin).trans hdlo
  have hd1 : d ≤ 1 := hdhi.trans (by norm_num [h, zeta])
  have hk0 : (7 : ℝ) / 10 ≤ kappa := by norm_num [kappa]
  have hk' := hk0.trans hk
  have hkpos : 0 < κ := by linarith
  have hkappapos : 0 < kappa := by norm_num [kappa]
  have hgap : 0 ≤ κ - kappa := sub_nonneg.mpr hk
  have hrow := source_row_kappa_effect κ d δ p hk hd0 hd1 hδ0 hδ1 hp0 hp1
  have hprod : (7 / 10 : ℝ)^2 ≤ κ * kappa := by
    rw [pow_two]
    exact mul_le_mul hk' hk0 (by norm_num) hkpos.le
  have hinvid : 1 / kappa - 1 / κ = (κ - kappa) / (κ * kappa) := by
    field_simp
  have hinv : 1 / kappa - 1 / κ ≤ (κ - kappa) / (7 / 10 : ℝ)^2 := by
    rw [hinvid]
    exact div_le_div_of_nonneg_left hgap (by norm_num) hprod
  have hq0 : 0 ≤ δ * p := mul_nonneg hδ0 hp0
  have hq1 : δ * p ≤ (3 : ℝ) / 8 := by
    nlinarith [mul_le_mul hδ1 hp1 hp0 (by norm_num : (0 : ℝ) ≤ 3 / 4)]
  have hmin0 : 0 ≤ min d (2 * y - d) := by
    apply le_min hd0
    have hy : h + zeta ≤ 2 * y := by norm_num [h, zeta, y, ell]
    linarith
  have hmin1 : min d (2 * y - d) ≤ (1 : ℝ) / 2 := by
    have hminy : min d (2 * y - d) ≤ y := by
      by_cases hdy : d ≤ y
      · exact (min_le_left _ _).trans hdy
      · exact (min_le_right _ _).trans (by linarith)
    exact hminy.trans (by norm_num [y, h, ell])
  have hcoef0 : 0 ≤ δ * p * min d (2 * y - d) / 12 := by positivity
  have hcoef1 : δ * p * min d (2 * y - d) / 12 ≤ (1 : ℝ) / 64 := by
    have hm := mul_le_mul hq1 hmin1 hmin0 (by norm_num : (0 : ℝ) ≤ 3 / 8)
    linarith
  have hinv0 : 0 ≤ (κ - kappa) / (7 / 10 : ℝ)^2 := by positivity
  have hreciprocal : (δ * p * min d (2 * y - d) / 12) * (1 / kappa - 1 / κ) ≤
      (1 / 64) * ((κ - kappa) / (7 / 10 : ℝ)^2) := by
    calc
      _ ≤ (δ * p * min d (2 * y - d) / 12) * ((κ - kappa) / (7 / 10 : ℝ)^2) :=
        mul_le_mul_of_nonneg_left hinv hcoef0
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef1 hinv0
  have hid : sourceGlobalRowExponent κ d (6 * κ) δ p -
      sourceGlobalRowExponent kappa d (6 * kappa) δ p =
      (3 * d / 4) * (Cycle25.Arithmetic.rowExponent κ δ p -
        Cycle25.Arithmetic.rowExponent kappa δ p) +
      (δ * p * min d (2 * y - d) / 12) * (1 / kappa - 1 / κ) := by
    unfold sourceGlobalRowExponent
    field_simp
    ring
  rw [hid]
  ring_nf at hrow hreciprocal ⊢
  linarith only [hrow, hreciprocal, hgap]

/-- Both branches admit the same uniform perturbation bound. -/
theorem source_piecewise_kappa_gap (κ d δ p : ℝ)
    (hk : kappa ≤ κ) (hdlo : dmin ≤ d) (hdhi : d ≤ h + zeta)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    sourcePiecewiseRowExponent κ d δ p - sourcePiecewiseRowExponent kappa d δ p ≤
      (κ - kappa) / 8 := by
  unfold sourcePiecewiseRowExponent
  split_ifs with hjunction
  · have hlocal := source_local_kappa_gap κ d δ p hk hdlo hdhi hδ0 hδ1 hp0 hp1
    have hgap : 0 ≤ κ - kappa := sub_nonneg.mpr hk
    linarith
  · exact source_old_kappa_gap κ d δ p hk hdlo hdhi hδ0 hδ1 hp0 hp1

/-- Substitution of the actual parameter `κ = 2β - 1` improves the scalar
reserve after subtracting `β`. No upper bound on `β` is needed here. -/
theorem source_beta_feedback (β d δ p : ℝ)
    (hβ : theta ≤ β) (hdlo : dmin ≤ d) (hdhi : d ≤ h + zeta)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    sourcePiecewiseRowExponent (2 * β - 1) d δ p - β ≤
      -1 / 100000000 - (3 / 4) * (β - theta) := by
  have hkappa : kappa = 2 * theta - 1 := by norm_num [kappa, theta]
  have hk : kappa ≤ 2 * β - 1 := by rw [hkappa]; linarith
  have hgap := source_piecewise_kappa_gap (2 * β - 1) d δ p hk hdlo hdhi hδ0 hδ1 hp0 hp1
  have hbase := source_global_range d δ p hdlo hdhi hδ0 hδ1 hp0 hp1
  rw [hkappa] at hgap hbase
  linarith

#print axioms source_local_kappa_gap
#print axioms source_old_kappa_gap
#print axioms source_piecewise_kappa_gap
#print axioms source_beta_feedback

end Submission20261012.Endpoint
end
/- END ORIGINAL MODULE Endpoint.Perturbation -/

/- BEGIN ORIGINAL MODULE Global.Parameters ; sha256 51a9871c82c473177737fbd6a2ae6816ff4bed2ff1d5c261337e4b8a4e188aa0 -/
section


/-! Physical geometry for the exact rational submission endpoint. -/
noncomputable section
namespace Submission20261012.Global

def theta : ℝ := Endpoint.theta
def ell : ℝ := Endpoint.ell
def lx : ℝ := Endpoint.x
def ly : ℝ := Endpoint.y
def h : ℝ := Endpoint.h
def b : ℝ := ly-lx
def rowExtension : ℝ := Endpoint.zeta
def signal (s : ℝ) : ℝ := s-(4+b)/6

theorem ell_interval : (167200:ℝ)/1000000 < ell ∧ ell < 167201/1000000 := by
  norm_num [ell, Endpoint.ell]
theorem h_interval : (793:ℝ)/1000 < h ∧ h < 795/1000 := by norm_num [h, Endpoint.h]
theorem theta_eq : theta = 11/12-ell/4 := by norm_num [theta,ell,Endpoint.theta,Endpoint.ell]
theorem theta_pos : 0 < theta := by rw [theta_eq]; linarith [ell_interval.2]
theorem theta_gt_half : (1:ℝ)/2 < theta := by rw [theta_eq]; linarith [ell_interval.2]
theorem theta_lt_seven_eighths : theta < (7:ℝ)/8 := by rw [theta_eq]; linarith [ell_interval.1]
theorem theta_lt_one : theta < 1 := theta_lt_seven_eighths.trans (by norm_num)
theorem length_sum : lx+ly = 1-ell := by unfold lx ly ell Endpoint.x Endpoint.y; ring
theorem length_difference : ly-lx=b := rfl
theorem row_endpoint : h=1-lx+ell := by unfold h lx ell Endpoint.x; ring
theorem y_endpoint : ly=h-2*ell := rfl
theorem signal_low : signal theta=lx/2+b/12 := by
  rw [signal,theta_eq]
  have := length_sum
  unfold b
  linarith
theorem signal_slope (s t : ℝ) : signal s-signal t=s-t := by unfold signal; ring
theorem ell_pos : 0 < ell := by linarith [ell_interval.1]
theorem ell_lt_one_fifth : ell < (1:ℝ)/5 := by linarith [ell_interval.2]
theorem x_rescaled_pos : 0 < lx-ell := by norm_num [lx,ell,Endpoint.x,Endpoint.h,Endpoint.ell]
theorem b_pos : 0 < b := by norm_num [b,ly,lx,Endpoint.x,Endpoint.y,Endpoint.h,Endpoint.ell]
theorem ly_lt_half : ly < (1:ℝ)/2 := by norm_num [ly,Endpoint.y,Endpoint.h,Endpoint.ell]
theorem ly_coarse : (458:ℝ)/1000 < ly ∧ ly < 461/1000 := by
  rw [y_endpoint]
  constructor <;> linarith [h_interval.1,h_interval.2,ell_interval.1,ell_interval.2]
theorem y_rescaled_pos : 0 < ly-ell := by linarith [ly_coarse.1,ell_interval.2]
theorem row_rescaled_pos : 0 < 1-3*ell := by linarith [ell_interval.2]
theorem gram_domination : 0 < ly-ell-(11:ℝ)/6*b := by
  have := length_sum
  unfold b
  linarith [ly_coarse.2,ell_interval.2]
theorem h_pos : 0 < h := by linarith [h_interval.1]
theorem h_gt_half : (1:ℝ)/2 < h := by linarith [h_interval.1]
theorem h_lt_one : h < 1 := by linarith [h_interval.2]
theorem rowExtension_pos : 0 < rowExtension := by norm_num [rowExtension, Endpoint.zeta]
theorem extended_row_count_supply : (7:ℝ)/37 < ell/(h+rowExtension) := by
  apply (lt_div_iff₀ (add_pos h_pos rowExtension_pos)).2
  norm_num [rowExtension, Endpoint.zeta]
  linarith [ell_interval.1,h_interval.2]
theorem row_count_supply : (7:ℝ)/37 < ell/h := by
  apply (lt_div_iff₀ h_pos).2
  linarith [ell_interval.1,h_interval.2]
theorem row_extension_supply : h < 5*ell := by linarith [h_interval.2,ell_interval.1]
theorem numerator_short : h < 2*ly := by norm_num [h,ly,Endpoint.y,Endpoint.h,Endpoint.ell]
theorem extended_numerator_short : h+rowExtension < 2*ly := by
  rw [y_endpoint]
  norm_num [rowExtension, Endpoint.zeta]
  linarith [h_interval.1,ell_interval.2]
theorem extended_h_lt_one : h+rowExtension < 1 := by
  norm_num [rowExtension, Endpoint.zeta]
  linarith [h_interval.2]
theorem extended_row_supply : h+rowExtension < 5*ell := by
  norm_num [rowExtension, Endpoint.zeta]
  linarith [h_interval.2,ell_interval.1]
theorem numerator_supply_all {kap d : ℝ} (hk : 7/10 ≤ kap) (hd : (1:ℝ)/2 ≤ d) :
    (2*ly-d)/(6*kap) < ell := by
  apply (div_lt_iff₀ (by linarith : 0 < 6*kap)).2
  have hprod := mul_le_mul_of_nonneg_left hk ell_pos.le
  nlinarith [ly_coarse.2,ell_interval.1]
theorem low_rescaled_tuple {v : ℝ} (hv : 0 ≤ v) :
    -v+max 0 (5*ell-1+v)/8 ≤ 0 := by
  have hm : max 0 (5*ell-1+v) ≤ 8*v := max_le (by linarith) (by linarith [ell_lt_one_fifth])
  linarith
theorem low_rescaled_identity (v : ℝ) :
    (1-ell-2*v)+(ell-v)-1 = -3*v := by ring
theorem small_row_margin : h*(17/50-1/6)-ly/2+(63:ℝ)/5000 < 0 := by
  norm_num [h,ly,Endpoint.h,Endpoint.y,Endpoint.ell]
theorem principal_w_margin : 0 < ly/20 := by linarith [ly_coarse.1]
theorem principal_z_margin : 0 < h/600 := by linarith [h_pos]

/-- The two strict hypotheses used by compensated LOW. -/
theorem compensated_low_geometry :
    ly-2*lx+ell < 0 ∧ 1+3*ell-2*(lx+ly) < 0 := by
  norm_num [ly,lx,ell,Endpoint.x,Endpoint.y,Endpoint.h,Endpoint.ell]

/-- The local numerator supply fits the fixed global slot total. -/
theorem local_numerator_supply : ly < (22/5:ℝ)*ell := by
  norm_num [ly,ell,Endpoint.y,Endpoint.h,Endpoint.ell]

/-- The detector supply holds even at the top of the extended row interval. -/
theorem extended_row_count_supply_one_fifth : (1:ℝ)/5 < ell/(h+rowExtension) := by
  norm_num [ell,h,rowExtension,Endpoint.ell,Endpoint.h,Endpoint.zeta]

/-- The normalized LOW exponent agrees with the new endpoint. -/
theorem low_exponent_identity :
    (5*lx+ly)/12 = theta-(5/6-lx/3-ell/6) := by
  have hs := length_sum
  rw [theta_eq]
  linarith

end Submission20261012.Global

#print axioms Submission20261012.Global.ell_interval
#print axioms Submission20261012.Global.compensated_low_geometry
#print axioms Submission20261012.Global.low_exponent_identity
end
/- END ORIGINAL MODULE Global.Parameters -/

/- BEGIN ORIGINAL MODULE OAI.NumberTheory.DirichletL.Detector.FinalAssembly ; sha256 e16f7a984e46edcda6c21efe9c21d4798d421ff332cc81ec394998102af53490 -/
section


namespace OAI

noncomputable section
open scoped Classical
open Filter
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters PrincipalSignalComparison

theorem common_probe_of_raw_moments (hmom : RawMomentInput) : HeckeCommonProbe.UniformCommonProbe := by
  intro hβ
  have hgap : 0< HeckeZeroSupremum.beta-7/8 := by linarith
  obtain ⟨D⟩ := exists_high_data (HeckeZeroSupremum.beta-7/8) hgap
  obtain ⟨F⟩ := exists_source_data D
  obtain ⟨counts⟩ := source_count_parameters F
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτ2,hτeps,hsource⟩ := raw_input_chosen_height hmom hβ D F counts
  obtain ⟨C,hC,hhigh⟩ := fixed_high_bound hβ D F counts τ hτ hτd hτcost hτt hτ2 hτeps
  let loss := (HeckeZeroSupremum.beta-7/8)/2
  have hloss : 0< loss := by dsimp [loss];linarith
  have hlossgap : loss< HeckeZeroSupremum.beta-7/8 := by dsimp [loss];linarith
  refine ⟨loss,D.sigma,hloss,hlossgap,D.sigma_pos,?_⟩
  intro η hprimitive
  obtain ⟨hmask,hH,hHbound⟩ := actual_source_analytic F.S F.exclusions η
  refine ⟨η.excludePrimes F.S F.exclusions.prime,sourceCorrection η F.S,F.probe η,
    hmask,hH,hHbound,F.probe_low loss hloss η,?_⟩
  obtain ⟨Ct,hCt,hhigh⟩ := hhigh η
  obtain ⟨Cm,hCm,hsource⟩ := hsource η
  apply isBigO_rpow_of_eventual_norm_bound
  refine ⟨Ct+C*Cm*(η.modulus.absNorm:ℝ)^(2*D.eps),by positivity,?_⟩
  filter_upwards [hhigh,hsource] with Z hh hs
  exact hh Cm hCm.le hs

theorem dirichlet_of_raw_moments (hmom : RawMomentInput) (q : ℕ) (hq : q≠0)
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : (7/8:ℝ)< s.re)
    (hexc : ¬(χ=1 ∧ s=1)) :
    letI : NeZero q := ⟨hq⟩
    DirichletCharacter.LFunction χ s≠0 :=
  HeckeCommonProbe.dirichlet_of_common_probe (common_probe_of_raw_moments hmom) q hq χ s hs hexc

theorem zeta_of_raw_moments (hmom : RawMomentInput) (s : ℂ) (hs : (7/8:ℝ)< s.re) :
    riemannZeta s≠0 :=
  HeckeCommonProbe.zeta_of_common_probe (common_probe_of_raw_moments hmom) s hs

theorem hecke_of_raw_moments (hmom : RawMomentInput) (χ : Character) (s : ℂ)
    (hs : (7/8:ℝ)< s.re) (hpole : s≠1 ∨ χ.residue≠1) : LFunction χ s≠0 :=
  HeckeCommonProbe.hecke_ne_zero_of_common_probe (common_probe_of_raw_moments hmom) χ s hs hpole

end SevenEighths.ProbeFinalAssembly

end

end OAI
end
/- END ORIGINAL MODULE OAI.NumberTheory.DirichletL.Detector.FinalAssembly -/

/- BEGIN ORIGINAL MODULE Analytic.ActualFreeDensity ; sha256 1132387499bc3c00ff56885716b5b5ebef03b17723beabc29fa5a9300d628dbd -/
section




set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open HeckeDetectorCoefficientTransfer HeckeDetectorRawFiber HeckeDetectorWitnessRows
open ProbeHighRowFamily LocalMoment HeckeDetectorZeros ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

/-- Actual free-row density, with a threshold independent of the external
height and bin. The analytic moment and detector inputs are discharged. -/
theorem actual_free_density_eventually {Label : Type*} [Fintype Label]
    (η : Label → Character) (Q : Ideal O) [NeZero Q]
    (hQtop : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hQη : ∀ label, Q ≤ (η label).modulus)
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (hβupper : HeckeZeroSupremum.beta ≤ 7/8)
    (loss : ℝ) (hlosspos : 0 < loss) :
    ∃ (A : ℕ) (K : ℝ), 0 < K ∧ ∀ᶠ U : ℝ in atTop, 1 < U ∧
      ∀ (rows : Finset FreeRow) (χ : FreeRow → Label → Character)
        (reverse : Label → Bool) (hχ : ∀ u j, (χ u j).residue ≠ 1),
      (∀ u ∈ rows, rowNorm u ≤ U) →
      (∀ u ∈ rows, ∀ j I,
        idealCoeff (χ u j) I =
          if reverse j then starRingEnd ℂ (idealCoeff ((momentData (η j)).character
            ⟨u.val, u.property.1⟩) I)
          else idealCoeff ((momentData (η j)).character ⟨u.val, u.property.1⟩) I) →
      (∀ u ∈ rows, ∀ j, ((χ u j).modulus.absNorm : ℝ) ≤ U) →
      ∀ (a T : ℝ), 167/200 ≤ a → a ≤ 7/8 →
      (∀ u ∈ rows, a ≤ zeroMaximum (χ u) (hχ u) T) →
      (rows.card : ℝ) ≤ K*(1+|T|)^A*U^(unmarkedDensity (2*a-1)+loss) := by
  obtain ⟨J, C, K₀, hC, hK₀, hb⟩ := actual_binned_row_count_uniform_geometry
    η Q hQtop hQ72 hQη hβ M H hH S φ hφ hφc hφp hφ0 hφne
    a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB (loss/8) (by positivity)
  obtain ⟨τ, ε, e, κaux, ηaux, I, hτ, hτzero, hτheight, hε, hεsmall,
    he, hesmall, hκ, hκone, hη, hbudget, hI, hwidth, hloss⟩ :=
      density_geometry_parameters loss hlosspos J
  obtain ⟨D, hD, hdyadic⟩ := fixed_label_dyadic_cost (Label := Label) (loss/8) (by positivity)
  obtain ⟨A, hA⟩ := exists_nat_ge (1/τ)
  have hAτ : 1 ≤ τ*(A : ℝ) := by
    have := (div_le_iff₀ hτ).mp hA
    nlinarith
  let E : ℝ := 192*C*max 1 K₀*(1+2*Real.pi+3*(I : ℝ))^(J+1)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  let K : ℝ := max 128 (((I : ℝ)+1)^2*D*E)
  have hK : 0 < K := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hactual := hb τ ε e κaux ηaux I hτ hτzero hτheight hε hεsmall
    he hesmall hκ hκone hη hbudget hβupper hI hwidth
  have hTlarge : ∀ᶠ U : ℝ in atTop, 2 < U^τ :=
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop _)
  refine ⟨A, K, hK, ?_⟩
  filter_upwards [hactual, hdyadic, hTlarge] with U hactual hdyadic hTlarge
  refine ⟨hactual.1, ?_⟩
  intro rows χ reverse hχ hrow hcoeff hconductor a T ha haupper hinitial
  have hU : 0 < U := zero_lt_one.trans hactual.1
  have hρ : 0 ≤ unmarkedDensity (2*a-1)+loss := by
    have := unmarkedDensity_ge_two_sevenths (δ := 2*a-1) (by linarith)
    linarith
  have hweight : 1 ≤ (1+|T|)^A := one_le_pow₀ (by linarith [abs_nonneg T])
  by_cases hsmall : T ≤ U^τ
  · let height := 2*Real.pi*U^(τ/2)+((3*I : ℕ) : ℝ)*U^τ
    have hh : 0 ≤ height := by dsimp [height]; positivity
    have hcount := hactual.2 rows χ reverse hχ hrow hcoeff hconductor a height
      ha haupper (fun u hu => (hinitial u hu).trans (zeroMaximum_mono (χ u) (hχ u) hsmall))
      hTlarge hh le_rfl
    have hf : fiberConstant (C*(1+height)^J) height K₀ ≤ E*U^(τ*((J : ℝ)+1)) :=
      density_fiber_height U τ C K₀ I J hactual.1.le hτ.le hC.le
    have hconstants : (Fintype.card Label : ℝ)*(dyadicLength U : ℝ)^2 *
        fiberConstant (C*(1+height)^J) height K₀ ≤
        (D*U^(loss/8))*(E*U^(τ*((J : ℝ)+1))) :=
      mul_le_mul hdyadic hf (by dsimp [fiberConstant]; positivity) (by positivity)
    calc
      (rows.card : ℝ) ≤ ((I : ℝ)+1)^2 *
        (((Fintype.card Label : ℝ)*(dyadicLength U : ℝ)^2 *
          fiberConstant (C*(1+height)^J) height K₀) *
          U^(unmarkedDensity (2*a-1)+156*ε+loss/8+3*e)) := hcount
      _ ≤ ((I : ℝ)+1)^2 *
        (((D*U^(loss/8))*(E*U^(τ*((J : ℝ)+1)))) *
          U^(unmarkedDensity (2*a-1)+156*ε+loss/8+3*e)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hconstants (Real.rpow_nonneg hU.le _)) (sq_nonneg _)
      _ = (((I : ℝ)+1)^2*D*E) *
          U^((loss/8+τ*((J : ℝ)+1))+(unmarkedDensity (2*a-1)+156*ε+loss/8+3*e)) := by
        simp only [Real.rpow_add hU]
        ring
      _ ≤ K * U^(unmarkedDensity (2*a-1)+loss) := by
        exact mul_le_mul (le_max_right _ _)
          (Real.rpow_le_rpow_of_exponent_le hactual.1.le (by linarith))
          (Real.rpow_nonneg hU.le _) hK.le
      _ ≤ K*(1+|T|)^A*U^(unmarkedDensity (2*a-1)+loss) :=
        mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hK.le hweight) (by positivity)
  · have hc := freeRow_count rows U hactual.1.le hrow
    have hheight : U ≤ (1+|T|)^A := by
      exact row_scale_le_large_height_power U τ T A hactual.1.le hAτ (lt_of_not_ge hsmall)
    calc
      (rows.card : ℝ) ≤ 128*U := hc
      _ ≤ K*(1+|T|)^A := mul_le_mul (le_max_left _ _) hheight hU.le hK.le
      _ ≤ K*(1+|T|)^A*U^(unmarkedDensity (2*a-1)+loss) :=
        le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hactual.1.le hρ)

#print axioms actual_free_density_eventually
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.ActualFreeDensity -/
