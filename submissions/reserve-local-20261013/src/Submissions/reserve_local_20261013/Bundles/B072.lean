/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.reserve_local_20261013.Bundles.B013
import Submissions.reserve_local_20261013.Bundles.B015
import Submissions.reserve_local_20261013.Bundles.B017
import Submissions.reserve_local_20261013.Bundles.B033
import Submissions.reserve_local_20261013.Bundles.B036
import Submissions.reserve_local_20261013.Bundles.B058
import Submissions.reserve_local_20261013.Bundles.B069
import Submissions.reserve_local_20261013.Bundles.B070
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceChild
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainRelativeClass
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.OneReflectionEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CentralSupportedSplit
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Reflection.LowDyads

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Mesh ; sha256 d9856d9d22fde4759ec77150252e26257e2877b715334a53691dd86be0d261d2 -/
section


noncomputable section
namespace Cycle25

/-- One mesh for both the physical numerator and the marked detector family. -/
def sourceMesh (t : ℝ) : ℝ := Energy.commonMesh 2 0 1 (t/4)

theorem sourceMesh_pos {t : ℝ} (ht : 0 < t) : 0 < sourceMesh t := by
  exact Energy.commonMesh_pos 2 0 1 (t/4) (by norm_num) (by norm_num) (by positivity)

end Cycle25
end
/- END ORIGINAL MODULE Cycle25.Assembly.Mesh -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.Physical.PhysicalMomentInput ; sha256 05c498a791d60edfd5f600e2fa16c51d0012345aaca2d48de6cbe2bc53620170 -/
section






namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter
namespace SevenEighths.Cycle25WeightedNumeratorPhysical
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CenteredMomentDetectorDictionary CenteredMomentNaturalFixedRaySource
open CenteredMomentHeckeSlots CenteredMomentInductionEnergy CenteredMomentEnergyBands
open CenteredMomentDetectorEnergyInitialState CenteredMomentEnergyState
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentRowNorm HeckePrimeAnnular
open CenteredMomentWholeSlotDeletion CenteredMomentRetainedEnergy QuadraticInitialBound
open CenteredMomentPrimeSlot
set_option maxHeartbeats 800000
local notation "O" => HeckeFamily.O

theorem weighted_physical_annular_all {D : Cycle25.Weighted.MomentData} (S:Cycle25ProbeFinalAssembly.WeightedSourceData D)(η₀:Character)
    (P:ℝ)(hP:0< P)(ζ:ℂ)(I:Ideal O):
    physicalSlotCoefficient η₀ S.W P ζ I=
      idealCoeff η₀.inverse I*annularWeight (fun x=> conj (S.W x)) P (1-ζ.re) (-ζ.im) I := by
  by_cases hI:I=0
  · subst I
    have hw:S.W 0=0:=by
      by_contra hh
      have hs:=S.complex_support hh
      norm_num at hs
    simp [physicalSlotCoefficient,annularWeight,hw]
  · exact physicalSlotCoefficient_annular η₀ S.W P ζ I hI hP

/-- The certified positive endpoint applied directly to arbitrary physical numerator
profiles. The dependence on the two profiles remains their source seminorm control;
no bound on their Fourier frequencies is assumed here. -/
theorem finite_physical_pair_positiveAt {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (rows : Finset FreeRow)
    (η : Character) (Φ : 𝓢(ℝ,ℂ)) (U bΦ δ mesh ε κ : ℝ)
    (hU : 1 ≤ U) (hδ : 0 ≤ δ) (hδtop : δ ≤ 1)
    (hs : Function.support (Φ:ℝ→ℂ) ⊆ Set.Iic bΦ) (hp : ∀x, 0 ≤ (Φ x).re)
    (hη : (η.modulus.absNorm:ℝ) ≤ U^δ)
    (hrows : ∀u∈rows, rowNorm u ≤ U)
    (hkeep : ∀u∈rows, initialKeep η (internalQ (weighted_sourceFixedIdeal F) η) u.val)
    (hone : ∀x∈Set.Icc (0:ℝ) 1, Φ x = 1)
    (degree : ℕ) (control : Finset (ℕ×ℕ)) (C : ℝ)
    (hpositive : PositiveAt (α:=Fin D.N) F.modulus ⊤ le_top (fun x=> conj (F.W x))
      2 (1/4) (9/4) bΦ 0 1 mesh (33/50) (33/50) 2 ε κ
      U η (weighted_sourceFixedIdeal F) degree control C)
    (T : Finset (Fin D.N)) (width : T → ℝ) (z : T → ℂ) (height : ℝ)
    (hw : ∀i, 0 ≤ width i) (hwmax : ∀i, width i ≤ mesh)
    (hz : ∀i, (z i).re = 17/50) (hh : 0 ≤ height) (hzim : ∀i, |(z i).im| ≤ height)
    (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hX₁max : X₁ ≤ U) (hX₂max : X₂ ≤ U)
    (hcap : length U X₁+length U X₂+6*κ*(∑i,width i) ≤ 1+δ) :
    (∑u∈rows, ‖polynomial ((momentData η).character (momentElement u)) false
        (p.profile 0) X₁ 0 0 *
      polynomial ((momentData η).character (momentElement u)) false (p.profile 1) X₂ 0 0 *
      ∏i, normalizedSlot η rowMaskElement 1 u.val (primePool F.modulus ⊤ 2 (U^(width i)))
        (physicalSlotCoefficient η F.W (U^(width i)) (z i)) 0 (U^(width i))‖^2)
      ≤ C*diagonalControl Φ*(p.control control)^2*(1+height)^degree*U^(1+δ+ε) := by
  let state := initialState η (internalQ (weighted_sourceFixedIdeal F) η)
    Φ bΦ U δ hU hδ hs hp hη
  have hwidth : state.width ≤ 2 := by
    change 1+δ ≤ 2
    linarith
  have hX₁' : X₁ ≤ U^(1:ℝ) := by simpa using hX₁max
  have hX₂' : X₂ ≤ U^(1:ℝ) := by simpa using hX₂max
  have hpos := hpositive T (fun _=>1) width (fun _=>33/50) (fun i=>-(z i).im)
    0 height hw hwmax (fun _=> le_rfl) (fun _=> le_rfl) hh
    (fun i=> by simpa only [abs_neg] using hzim i) state rfl hwidth p X₁ X₂
    hX₁ hX₂ hX₁' hX₂' hcap
  have he := finite_actual_pair_le_energy rows η (internalQ (weighted_sourceFixedIdeal F) η)
    Φ U bΦ δ hU hδ hs hp hη hrows hkeep hone (p.profile 0) (p.profile 1)
    (9/4) (9/4) X₁ X₂
    (fun _ hx=>(p.support 0 hx).2) (fun _ hx=>(p.support 1 hx).2) hX₁ hX₂
    (fun i=> primePool F.modulus ⊤ 2 (U^(width i)))
    (fun i=> physicalSlotCoefficient η F.W (U^(width i)) (z i))
    (fun i=> U^(width i)) (fun _=> Real.rpow_pos_of_pos (zero_lt_one.trans_le hU) _)
  have hcoef : (fun (i:T) I=> physicalSlotCoefficient η F.W (U^(width i)) (z i) I) =
      (fun (i:T) I=> idealCoeff η.inverse I*HeckePrimeAnnular.annularWeight
        (fun x=> conj (F.W x)) (U^(width i)) (33/50) (-(z i).im) I) := by
    funext i I
    rw [weighted_physical_annular_all F η _ (Real.rpow_pos_of_pos (zero_lt_one.trans_le hU) _) (z i) I,hz i]
    norm_num
  rw [hcoef] at he
  have heq := CenteredMomentDetectorPlainRelativeClass.energy_eq F.modulus ⊤ le_top
    η η (fun (_:T)=>1) (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1
    (p.profile 0) (p.profile 1) (fun _=>2) (fun i=> U^(width i))
    (fun i I=> HeckePrimeAnnular.annularWeight (fun x=> conj (F.W x))
      (U^(width i)) (33/50) (-(z i).im) I)
    0 X₁ X₂ (initialKeep η (internalQ (weighted_sourceFixedIdeal F) η)) Φ U
  exact he.trans (heq.le.trans (by simpa [state,initialState,NaturalState.width,NaturalState.mask] using hpos))


/-- Each source prime slot is the conjugate of the actual negative-orientation
canonical amplitude, without deleting any natural ramified zeros. -/
theorem source_physical_slot_conj {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (u : FreeRow) (P : ℝ) (z : ℂ)
    (hP : 0 < P) :
    normalizedSlot (fixedSourcePrincipal F.S F.exclusions.prime) rowMaskElement 1 u.val
      (primePool F.modulus ⊤ 2 P)
      (physicalSlotCoefficient (fixedSourcePrincipal F.S F.exclusions.prime) F.W P z) 0 P =
      conj (HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 P z) := by
  apply physical_slot_conj F.modulus ⊤ _ rowMaskElement u.val
    (momentData (fixedSourcePrincipal F.S F.exclusions.prime)).lambda_dvd
    (CenteredMomentDetectorDictionary.source_product_le_rowMask F.S F.exclusions.bad)
    F.W 2 P z hP
  intro I hI _
  exact HeckePrimeRow.identityClass_coprime F.modulus ⊤ (Finset.mem_filter.mp hI).2.2

/-- Conjugating the complete reflected numerator/selected-slot product places
both factors in the positive moment orientation. -/
theorem reflected_pair_norm_eq {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) {ι : Type*} [Fintype ι]
    (u : FreeRow) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (P : ι → ℝ) (hP : ∀i, 0 < P i) (z : ι → ℂ) :
    ‖polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (fun x=> conj (W₁ x)) X₁ 0 0 *
      polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (fun x=> conj (W₂ x)) X₂ 0 0 *
      ∏i,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (P i) (z i)‖ =
    ‖polynomial ((momentData (fixedSourcePrincipal F.S F.exclusions.prime)).character
        (momentElement u)) false W₁ X₁ 0 0 *
      polynomial ((momentData (fixedSourcePrincipal F.S F.exclusions.prime)).character
        (momentElement u)) false W₂ X₂ 0 0 *
      ∏i,normalizedSlot (fixedSourcePrincipal F.S F.exclusions.prime) rowMaskElement 1 u.val
        (primePool F.modulus ⊤ 2 (P i))
        (physicalSlotCoefficient (fixedSourcePrincipal F.S F.exclusions.prime) F.W (P i) (z i))
        0 (P i)‖ := by
  simp_rw [source_physical_slot_conj F u _ _ (hP _)]
  rw [CenteredMomentOneReflectionEnergy.polynomial_inverse_plain _ _ X₁ hX₁,
    CenteredMomentOneReflectionEnergy.polynomial_inverse_plain _ _ X₂ hX₂]
  simp only [Complex.conj_conj]
  rw [numerator_polynomial_eq_moment F.S F.exclusions.prime F.exclusions.bad,
    numerator_polynomial_eq_moment F.S F.exclusions.prime F.exclusions.bad]
  rw [←Complex.norm_conj (_*_*∏i,_)]
  simp only [map_mul,map_prod,Complex.conj_conj]

end SevenEighths.Cycle25WeightedNumeratorPhysical
end
end OAI

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 uses the common-mesh variable-kappa positive endpoint and unconditional zero endpoint. -/
end
/- END ORIGINAL MODULE Cycle25.Energy.Physical.PhysicalMomentInput -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.Physical.Terminal ; sha256 4fba83f4e94359da0df68feeba47bbe1eb0dabef0967ff3fc6f419547731c2db -/
section




noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Filter
namespace OAI.SevenEighths.Cycle25WeightedNumeratorPhysical
open HeckeFamily CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O

theorem weighted_terminal_positive_energy {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (κ : ℝ)
    (hκlo : 7/10 ≤ κ) (hκhi : κ ≤ 3/4)
    (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ κ) (bΦ : ℝ) (hbΦ : 0 < bΦ) :
    ∃degree:ℕ, ∃control:Finset (ℕ×ℕ), ∀η₀:Character,
      ∃C:ℝ, 0 < C ∧ ∀ᶠU:ℝ in atTop, 1 < U ∧
      PositiveAt (α:=Fin D.N) F.modulus ⊤ le_top (fun x=> conj (F.W x))
        2 (1/4) (9/4) bΦ 0 1 (Cycle25.Energy.commonMesh 2 0 1 (D.t/4))
        (33/50) (33/50) 2 (D.t/4) κ U η₀ (weighted_sourceFixedIdeal F) degree control C := by
  have hsupport : Function.support (fun x=> conj (F.W x)) ⊆ Set.Icc (1:ℝ) 2 := by
    intro x hx
    exact F.complex_support (by simpa using hx)
  obtain ⟨degree,control,hbound⟩ := Cycle25.Energy.terminal_positive_at (α:=Fin D.N)
    F.modulus ⊤ le_top (fun x=> conj (F.W x)) 1 2 (1/4) (9/4) bΦ 0 1
    (33/50) (33/50) 2 κ (D.t/4) (by norm_num) hsupport
    (Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hbΦ (by norm_num) (by norm_num) hκlo hκhi
    (div_pos D.t_pos (by norm_num)) hbeta hκbeta
  refine ⟨degree,control,?_⟩
  intro η₀
  exact hbound η₀ (weighted_sourceFixedIdeal F) (weighted_sourceFixedIdeal_le_modulus F)
    (weighted_source_fixed_gates F η₀).1
    (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top F) η₀)
    (weighted_source_fixed_gates F η₀).2.2.2

theorem weighted_terminal_zero_energy {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (bΦ : ℝ) (hbΦ : 0 < bΦ) :
    ∃degree:ℕ, ∃control:Finset (ℕ×ℕ), ∀η₀:Character,
      ∃C:ℝ, 0 < C ∧ ∀ᶠU:ℝ in atTop, 1 < U ∧
      ZeroAt (internalQ (weighted_sourceFixedIdeal F) η₀) (1/4) (9/4) bΦ 0 2 2
        (D.t/4) U degree control C := by
  obtain ⟨degree,control,hbound⟩ := ZetaZeroFree.Analytic.Moments.Unconditional.nonfixed_zero_at
    F.modulus (1/4) (9/4) bΦ 0 2 2 (D.t/4) (by norm_num) (by norm_num)
    (by norm_num) hbΦ (by norm_num) (by norm_num) (div_pos D.t_pos (by norm_num))
  refine ⟨degree,control,?_⟩
  intro η₀
  exact hbound η₀ (weighted_sourceFixedIdeal F) (weighted_sourceFixedIdeal_le_modulus F)
    (weighted_source_fixed_gates F η₀).1
    (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top F) η₀)
    (weighted_source_fixed_gates F η₀).2.2.2

end OAI.SevenEighths.Cycle25WeightedNumeratorPhysical

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
The positive contour assumptions are explicit; the empty-slot endpoint is unconditional. -/
end
/- END ORIGINAL MODULE Cycle25.Energy.Physical.Terminal -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.PhysicalCollect ; sha256 453ccc5be84c91ce3cbdfa735cf4f86078d6c983ad35c254c9522187c3e422ca -/
section



/-! Literal physical error-mask contributions and their canonical prime fronts. -/
noncomputable section
open scoped BigOperators Classical
namespace Cycle25.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O

def sourceMaskContribution {D : MomentData} (F : WeightedSourceData D)
    (η : Character) (rows : Finset FreeRow) (J : Finset (Fin D.N))
    (Z : ℝ) (x z : ℂ) (Y : ℝ) : ℂ :=
  ∑u∈rows,(frequencyWeight z ⟨u.val,u.property.1⟩*numeratorFreeRowScalar F.S F.exclusions F.maximal η u x z)*
    (errorLabelNumerator F.S F.exclusions η u J (sourcePrimePool F Z)
      (fun j=> source_prime_pool_outside F Z j) (fun _=> F.W) (fun j=> Z^(D.ell j)) x z F.W Y*
      (∏j:{i:Fin D.N//i∉J},∑P:sourcePrimePool F Z j.val,
        physicalSlotWeight P.val F.W (Z^(D.ell j.val)) z*(-star (idealRowHom u.val P.val.val))))

theorem source_reconstructed_sum_masks {D : MomentData} (F : WeightedSourceData D)
    (η : Character) (rows : Finset FreeRow) (Z : ℝ) (x z : ℂ) (Y : ℝ) :
    reconstructedDyadValue F.S F.exclusions F.maximal η rows (sourcePrimePool F Z)
      (fun j=> source_prime_pool_outside F Z j) (fun _=> F.W) (fun j=> Z^(D.ell j)) x z F.W Y =
      ∑J∈Finset.univ.powerset,sourceMaskContribution F η rows J Z x z Y := by
  unfold reconstructedDyadValue sourceMaskContribution
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

theorem complement_prime_product {D : MomentData} (F : WeightedSourceData D)
    (u : FreeRow) (J : Finset (Fin D.N)) (Z : ℝ) (z : ℂ) :
    (∏j:{i:Fin D.N//i∉J},HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j.val)) z) =
      ∏j∈Finset.univ\J,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z :=
  (Finset.prod_subtype (Finset.univ\J) (by simp)
    (fun j=> HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z)).symm

theorem source_mask_physical_front {D : MomentData} (F : WeightedSourceData D)
    (η : Character) (rows : Finset FreeRow) (J : Finset (Fin D.N))
    (Z : ℝ) (hZ : 0 < Z) (x z : ℂ) (hz : z.re=17/50) (Y : ℝ)
    (hS : ∀j,∀P∈F.S,(P.absNorm:ℝ)≤ Z^(D.ell j))
    (A B : ℝ) (hA : 0≤ A)
    (ha : ∀u∈rows,‖frequencyWeight z ⟨u.val,u.property.1⟩*
      numeratorFreeRowScalar F.S F.exclusions F.maximal η u x z‖≤ A)
    (hB : (∑u∈rows,‖errorLabelNumerator F.S F.exclusions η u J (sourcePrimePool F Z)
      (fun j=> source_prime_pool_outside F Z j) (fun _=> F.W) (fun j=> Z^(D.ell j)) x z F.W Y*
      (∏j∈Finset.univ\J,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z)‖)≤ B) :
    ‖sourceMaskContribution F η rows J Z x z Y‖ ≤
      A*Z^(-(4/25:ℝ)*(∑j:{i:Fin D.N//i∉J},D.ell j.val))*B := by
  let En (u : FreeRow) := errorLabelNumerator F.S F.exclusions η u J (sourcePrimePool F Z)
    (fun j=> source_prime_pool_outside F Z j) (fun _=> F.W) (fun j=> Z^(D.ell j)) x z F.W Y
  let Main (u : FreeRow) := ∏j∈Finset.univ\J,
    HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z
  let MainRaw (u : FreeRow) := ∏j:{i:Fin D.N//i∉J},∑P:sourcePrimePool F Z j.val,
    physicalSlotWeight P.val F.W (Z^(D.ell j.val)) z*(-star (idealRowHom u.val P.val.val))
  let front : ℝ := Z^(-(4/25:ℝ)*(∑j:{i:Fin D.N//i∉J},D.ell j.val))
  have hfront : 0 ≤ front := Real.rpow_nonneg hZ.le _
  have he (u : FreeRow) : ‖En u*MainRaw u‖=front*‖En u*Main u‖ := by
    rw [norm_mul,source_main_product_norm F Z hZ hS u J z,hz,complement_prime_product]
    rw [show (∑j:{i:Fin D.N//i∉J},D.ell j.val)*((17/50:ℝ)-1/2) =
      -(4/25:ℝ)*(∑j:{i:Fin D.N//i∉J},D.ell j.val) by ring]
    dsimp only [front]
    rw [norm_mul]
    ring
  change ‖∑u∈rows,(frequencyWeight z ⟨u.val,u.property.1⟩*
    numeratorFreeRowScalar F.S F.exclusions F.maximal η u x z)*(En u*MainRaw u)‖ ≤ A*front*B
  calc
    _ ≤ ∑u∈rows,‖(frequencyWeight z ⟨u.val,u.property.1⟩*
        numeratorFreeRowScalar F.S F.exclusions F.maximal η u x z)*(En u*MainRaw u)‖ := norm_sum_le _ _
    _ ≤ ∑u∈rows,(A*front)*‖En u*Main u‖ := by
      apply Finset.sum_le_sum
      intro u hu
      rw [norm_mul,he]
      exact (mul_le_mul_of_nonneg_right (ha u hu) (mul_nonneg hfront (norm_nonneg _))).trans_eq (by ring)
    _ = (A*front)*(∑u∈rows,‖En u*Main u‖) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hB (mul_nonneg hA hfront)

end Cycle25.Numerator

/- Adapted from weighted-numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.PhysicalCollect -/

/- BEGIN ORIGINAL MODULE Global.Low.Reflection.LowDyads ; sha256 96cbb4a99bf442b43ae1ebfa1da70f7c63be1ad524c1673a4c105e577962f094 -/
section



/-! Adapted from OpenAI/math family003, pinned original module Reflection.LowDyads.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace Submission20261012.Global
open OAI OAI.SevenEighths

namespace LowReflection
open InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}

theorem low_dyadic_geometry_uniform
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (lo hi : ℝ) (hlo : 0< lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (hac : ∀ i,IsCoprime (a i) (c₀ i))
    (Q : Ideal Eis) (hQ : Q≠0) (Ck η : ℝ) (hCk : 0< Ck) (hη : 0<η) (hη1 : η≤1) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0< C ∧ 1< Z₀ ∧
    ∀ g : γ,∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J F Q₀ : Ideal Eis)
      (_hJ : J≠0) (_hF : F≠0),
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z d ell0 shift O₀ : ℝ),
      Z₀≤ Z → 0≤ d → d≤ Submission20261012.Global.ell → 0≤ ell0 → ell0≤ Submission20261012.Global.ell-d+η → |shift|≤η →
      O₀=normWidth Z (rowPowerfulPart J) →
    ∀ (parents rows : Finset (Ideal Eis)),
      (∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤ Ck*Z^((1-Submission20261012.Global.ell)-2*d)) →
      rows⊆originalResidualRows parents J Q →
      (∀ P∈fixedBadPrimes,P∣Q) →
      let Hrow := (Ck*Z^((1-Submission20261012.Global.ell)-2*d))/((Ideal.absNorm (rowPowerfulPart J):ℝ)*(Ideal.absNorm (rowMaskPart J Q):ℝ))
      let Hslot := Z^ell0
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let jF := fun b : A => completedLocalExponent J F b.val.val
    ∀ (tuples : Finset (σ→Ideal Eis))
      (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
      (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)
      (_hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis)))
      (hrows : ∀ K∈rows,Admissible K),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ p : tuples,Pairwise (Function.onFun IsCoprime (G.sum (memberTupleFamily tuples hmax hgood p)).ideal)) →
      (∀ p : tuples,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (memberTupleFamily tuples hmax hgood p)).ideal b)) →
      (∀ p : tuples,∀ b,ringChar (Eis⧸(G.sum (memberTupleFamily tuples hmax hgood p)).ideal b)≠2) →
      (∀ p∈tuples,CubicSieve.Admissible (slotTupleProduct p) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤ Hslot) →
    ∃ D : ∀ i : Fin (columnDyadicLength Hrow+1),∀ j : Fin (columnDyadicLength Hslot+1),
      CellCompletion (N:=Nlevel) (a:=a g) (c:=c₀ g) (mode:=mode g) G rows hrows tuples hmax hgood Hrow Hslot i j,
    ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
      (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
      (∑ K : rows,‖∑ p : tuples,
        dyadicPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot D (s g) (hc₀ g) jF W θ (Z^(1+ell0+shift)) r aw K p‖^2)≤
        (columnDyadicLength Hrow+1:ℝ)*(columnDyadicLength Hslot+1:ℝ)^2*
          (C*(1+‖θ‖)^degree*Z^(((1-Submission20261012.Global.ell)-d)+504*η-O₀/2)) := by
  have hsubmissionEll := Submission20261012.Global.ell_interval
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := low_fixed_member_geometry_uniform a c₀ mode lo hi hlo W hWs hW
    s hc₀ hNlevel hbase hac Q hQ Ck η hCk hη hη1
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro g σ _ _ J F Q₀ hJ hF A Z d ell0 shift O₀ hZ hd hd1 hell hellcap hshift hOeq
    parents rows hparents hsub hbad
  dsimp only
  intro tuples hmax hgood hinj hrows hGN hGchar hrowcop hpair hPN hPchar hPnorm
  let Hrow := (Ck*Z^((1-Submission20261012.Global.ell)-2*d))/((Ideal.absNorm (rowPowerfulPart J):ℝ)*(Ideal.absNorm (rowMaskPart J Q):ℝ))
  let Hslot := Z^ell0
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let jF := fun b : A => completedLocalExponent J F b.val.val
  have hz : 1< Z := lt_of_lt_of_le hZ₀ hZ
  have hzp : 0< Z := lt_trans zero_lt_one hz
  have hrowNorm : ∀ K∈rows,1≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤ Hrow :=
    fun K hK => original_residual_norm_bounds parents J Q hbad (Ck*Z^((1-Submission20261012.Global.ell)-2*d)) hparents K (hsub hK)
  have htupleNorm : ∀ p∈tuples,1≤(Ideal.absNorm (slotTupleProduct p):ℝ) ∧
      (Ideal.absNorm (slotTupleProduct p):ℝ)≤ Hslot := fun p hp =>
    ⟨QuadraticMainBoundary.norm_one_le (primaryGenerator_ne_zero_ideal _ (hPnorm p hp).1.2),(hPnorm p hp).2⟩
  apply physical_dyad_selection_energy G rows hrows tuples hmax hgood Hrow Hslot
    (s g) (hc₀ g) jF W (Z^(1+ell0+shift)) (fun θ => C*(1+‖θ‖)^degree*Z^(((1-Submission20261012.Global.ell)-d)+504*η-O₀/2))
    (fun θ => by positivity)
  intro i j hi hj
  let Rc := divisorDyadicBin rows Hrow i
  let Tc := activeTupleDyad tuples Hslot j
  let hm := fun p hp k => hmax p (activeTupleDyad_subset tuples Hslot j hp) k
  let hg := fun p hp k => hgood p (activeTupleDyad_subset tuples Hslot j hp) k
  have hTc : Tc.Nonempty := hj
  have hRi : ∀ K∈Rc,Admissible K := fun K hK => hrows K (divisorDyadicBin_subset rows Hrow i hK)
  have hti : Set.InjOn slotTupleProduct (↑Tc : Set (σ→Ideal Eis)) :=
    hinj.mono (activeTupleDyad_subset tuples Hslot j)
  have hKr := divisorDyadicBin_bounds rows Hrow hrowNorm i
  have hPr := activeTupleDyad_bounds tuples Hslot htupleNorm j
  obtain ⟨K,hK⟩ := hi
  obtain ⟨I,hI,heI⟩ := Finset.mem_image.mp (hsub (divisorDyadicBin_subset rows Hrow i hK))
  obtain ⟨hIp,hpow,hmask⟩ := Finset.mem_filter.mp hI
  have hI0 := (hparents I hIp).1
  have hIn := (hparents I hIp).2
  have hKlower : (2*divisorDyadicScale i.val)/2≤(Ideal.absNorm (rowResidualPart I Q):ℝ) := by
    rw [heI]
    convert (hKr K hK).1 using 1 ; ring
  have hKupper : 2*divisorDyadicScale i.val≤2*Ck*Z^((1-Submission20261012.Global.ell)-2*d) := by
    have hres : (Ideal.absNorm (rowResidualPart I Q):ℝ)≤(Ideal.absNorm I:ℝ) := by
      rw [rowResidualPart_norm I Q hI0]
      apply div_le_self (Nat.cast_nonneg _)
      exact one_le_mul_of_one_le_of_one_le
        (QuadraticMainBoundary.norm_one_le (rowPowerfulPart_ne_zero I))
        (QuadraticMainBoundary.norm_one_le (squarefreeMaskPart_ne_zero (rowSimplePart I) Q))
    have hs := hKlower.trans (hres.trans hIn)
    linarith
  have hPupper : (2*divisorDyadicScale j.val)/2≤ Z^ell0 := by
    convert activeTupleDyad_scale_le tuples Hslot htupleNorm j hj using 1 ; dsimp [Hslot] ; ring
  let S := tuplePrimeFamily Tc hTc hm hg
  have hScop : ∀ P∈Tc.image slotTupleProduct,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal) := by
    intro P hP
    exact hpair ⟨tupleRepresentative Tc hTc P,activeTupleDyad_subset tuples Hslot j (tupleRepresentative_mem Tc hTc P)⟩
  have hSN : ∀ P∈Tc.image slotTupleProduct,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b) := by
    intro P hP
    exact hPN ⟨tupleRepresentative Tc hTc P,activeTupleDyad_subset tuples Hslot j (tupleRepresentative_mem Tc hTc P)⟩
  have hSchar : ∀ P∈Tc.image slotTupleProduct,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2 := by
    intro P hP
    exact hPchar ⟨tupleRepresentative Tc hTc P,activeTupleDyad_subset tuples Hslot j (tupleRepresentative_mem Tc hTc P)⟩
  obtain ⟨D,hD⟩ := he g J I F Q₀ hJ hI0 hF hpow.symm hmask.symm A
    Z d ell0 shift O₀ (2*divisorDyadicScale i.val) (2*divisorDyadicScale j.val)
    hZ hd hd1 hell hellcap hshift (by rw [hpow];exact hOeq) hIn hKlower
    (by linarith [divisorDyadicScale_ge_one i.val]) hKupper
    (by linarith [divisorDyadicScale_ge_one j.val]) hPupper
    Rc Tc hTc hm hg hti hRi hGN hGchar
    (fun K hK => hrowcop K (divisorDyadicBin_subset rows Hrow i hK))
    (tuplePrimeFamily_product Tc hTc hm hg) hScop hSN hSchar
  let Dc : CellCompletion (N:=Nlevel) (a:=a g) (c:=c₀ g) (mode:=mode g)
      G rows hrows tuples hmax hgood Hrow Hslot i j := fun K p hp =>
    memberTupleControlled Tc hm hg G K.val (hRi K.val K.property) hTc hti (D K) p hp
  refine ⟨Dc,?_⟩
  intro θ r aw hr haw
  have hb := hD θ r aw (by linarith [divisorDyadicScale_ge_one i.val])
    (by linarith [divisorDyadicScale_ge_one j.val])
    (fun K hK => by convert hKr K hK using 1 ; ring_nf)
    (by
      intro P hP
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hP
      refine ⟨(hPnorm p (activeTupleDyad_subset tuples Hslot j hp)).1,?_⟩
      convert hPr p hp using 1 ; ring_nf)
    (fun K hK => hr K (divisorDyadicBin_subset rows Hrow i hK))
    (fun p hp => haw p (activeTupleDyad_subset tuples Hslot j hp))
  exact hb
end
end LowReflection

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Reflection.LowDyads -/

/- BEGIN ORIGINAL MODULE Global.Transport.NonfloorTransport ; sha256 cb20fa0b1058b6a110c75b8f6603d70ada09fe023ca6639676675e954d201ce7 -/
section
/- Adapted from weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/




open OAI OAI.SevenEighths

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace Submission20261012.Global.HighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
open ProbeRaySlots PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

omit [NeZero M] in
private theorem nonfloorTransportPoolOutside (S : Finset (Ideal O)) (K : ℕ) (a b : ℝ) (Y : Fin K→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S a b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S a b (Y j) P).mp hP |>.2.2.2

theorem actual_nonfloor_probe_transport (K : ℕ) (e δ a b B ζ saving τ ellMin nu : ℝ)
    (he : 0 < e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0 < a) (hab : a ≤ b) (hB : 0 ≤ B) (hmin : 0 < ellMin) (hnu : 0 < nu)
    (hβlo : Submission20261012.Global.theta ≤ HeckeZeroSupremum.beta)
    (hβ : HeckeZeroSupremum.beta ≤ (7/8:ℝ))
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (ell : Fin K→ℝ) (hell : ∀j,ellMin ≤ ell j) (hellinj : Function.Injective ell) (hellsum : ∑j,ell j=Submission20261012.Global.ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Ioo a b) (hWB : ∀j y,0 ≤ W j y ∧ W j y ≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (sigma : ℝ) (hsigma : 0 < sigma)
    (hgeometric : sigma+8*e+nu≤1/20) (hprincipal : sigma+nu≤1/4000)
    (hwindow : sigma+e ≤ Submission20261012.Global.theta*ellMin) (hlarge : sigma+nu ≤ saving+Submission20261012.Global.signal Submission20261012.Global.theta)
    (eps R dmin dmax rmin ε κ cost mesh margin loss : ℝ)
    (heps : 0 < eps) (hR : 0 ≤ R) (hdmin : 0 < dmin) (hdmax : 0 ≤ dmax) (hdRange : dmin ≤ dmax)
    (hrmin : 0 < rmin) (hε : 0<ε) (hκ : 0<κ) (hcost : 0 ≤ cost) (hmesh : 0 < mesh) (hmargin : 0 < margin)
    (hphasebudget : 8*e*R+κ≤ε) (hphasegap : ε < rmin*mesh)
    (hheight : 2*τ < dmin*cost) (hloss : τ*(2+4*eps) < loss)
    (hcap : Submission20261012.Global.h+ζ ≤ dmax-margin)
    (helllo : ∀j,dmax*rmin ≤ ell j) (hellhi : ∀j,ell j ≤ dmin*R)
    (hζcap : ζ ≤ Submission20261012.Global.rowExtension)
    (hfloorbudget : 26*e+(K+8)*eps+loss+mesh*Submission20261012.Global.ell+nu+sigma≤1/100) :
    let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃n : ℕ,0 < n ∧ ∀η : Character,∃C : ℝ,0 < C ∧ ∀ᶠ Z : ℝ in atTop,
      let Yp := fun j=> Z^(ell j)
      let T := fun j=> pool (RayQuotient.identityClass M H) S a b (Yp j)
      let hT := nonfloorTransportPoolOutside M H S K a b Yp
      let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (Submission20261012.Global.ell) (slotMass T (residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ) ≤ a ∧ a≤7/8 ∧
        a ≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) < a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(idx u+1:ℕ)*Z^τ) < a+2*e ∧
        (51/100 < a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue=1 ∧ s=1) ∧
          a ≤ s.re ∧ s.re < a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((Submission20261012.Global.h:ℝ)+ζ)),
        (calibrationForSet S hmax).residueMonoid u.val≠0 →
        (∀θ,(rayCubeFamily M H hH u θ).residue≠1) ∧
        (∀θ,(rayCubeFamily M H hH u θ).modulus.absNorm≤
          conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm) ∧
        ∀hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1,
        HeckeDetectorZeros.zeroMaximum (rayCubeFamily M H hH u) hnp
          (3*(idx u+1:ℕ)*Z^τ)<(51/100:ℝ)+e*grid u+2*e) ∧
      let alpha : FreeRow→ℝ := fun u=>51/100+e*grid u
      let height : FreeRow→ℝ := fun u=>(3*idx u+1:ℕ)*Z^τ
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun j=> canonicalSlotSupport (T j)) WC Yp (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-(4+Submission20261012.Global.b)/6) Z-
        finiteCentralCubeRows S hS hmax η
          (supportedNonfloorRows S hmax (rowBand (Z^(1/100:ℝ)) (Z^((Submission20261012.Global.h:ℝ)+ζ))) grid) T hT WC Yp
          W0 W1 (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z e alpha height/normer‖≤
        C*Z^(HeckeZeroSupremum.beta-(4+Submission20261012.Global.b)/6-sigma) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨n,hn,htransport⟩ := actual_normalized_probe_transport_saving M H hH K e δ a b B ζ saving τ ellMin nu
    he he' hδ hδ' hζ hζ' hτ ha hab hB hmin hnu hβlo hβ S hS hmax hfirst ell hell hellinj hellsum
    W hW hcompact hsupp hWB hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    sigma hsigma hgeometric hprincipal hwindow hlarge
  obtain ⟨Cf,hCf,hfloor⟩ := actual_floor_rows_saving M H hH K n e eps a b B R dmin dmax rmin τ ε κ cost mesh
    (1/100) margin loss he he' heps ha hab hB hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
    (by norm_num) hphasebudget hphasegap hmargin hheight hloss S hS hfirst hmax ell hellinj helllo hellhi
    W hsupp hW hWB hcompact hne hellsum W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    nu hnu sigma hsigma hfloorbudget
  refine ⟨n,hn,?_⟩
  intro η
  obtain ⟨Ct,hCt,htransport⟩ := htransport η
  let C := Ct+Cf*(η.modulus.absNorm:ℝ)^(2*eps)
  have hC : 0 < C := by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [htransport,hfloor η,eventually_ge_atTop (1:ℝ)] with Z ht hf hZ
  dsimp only at ht ⊢
  obtain ⟨hnorm,idx,grid,hlabels,hbins,hray,herror⟩ := ht
  refine ⟨hnorm,idx,grid,hlabels,hbins,hray,?_⟩
  let Yp : Fin K→ℝ := fun j=> Z^(ell j)
  let T : Fin K→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S a b (Yp j)
  let hT := nonfloorTransportPoolOutside M H S K a b Yp
  let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
  let rows := rowBand (Z^(1/100:ℝ)) (Z^((Submission20261012.Global.h:ℝ)+ζ))
  let floors := supportedFloorRows S hmax rows grid
  have hrows : ∀u∈floors,u.val≠1 ∧ Z^(1/100:ℝ) ≤ rowNorm u ∧
      (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u ≤ Z^(dmax-margin) := by
    intro u hu
    rcases (mem_supportedFloorRows S hmax rows grid u).mp hu with ⟨hur,hcal,hg⟩
    have hm := mem_rowBand.mp hur
    exact ⟨hm.1,hm.2.1,hcal,hm.2.2.le.trans (Real.rpow_le_rpow_of_exponent_le hZ hcap)⟩
  have hnorms : ∀u∈floors,rowNorm u ≤ Z^((Submission20261012.Global.h:ℝ)+ζ) := by
    intro u hu
    exact (mem_rowBand.mp ((mem_supportedFloorRows S hmax rows grid u).mp hu).1).2.2.le
  have hfloorbin : ∀u∈floors,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
      (3*(idx u+1:ℕ)*Z^τ)<51/100+2*e := by
    intro u hu
    have hg := ((mem_supportedFloorRows S hmax rows grid u).mp hu).2.2
    have hh := (hbins u).2.2.2.2.1
    simpa only [hg,Nat.cast_zero,mul_zero,add_zero] using hh
  have hb := (hf dmax hdRange le_rfl (Submission20261012.Global.h+ζ) (by linarith [Submission20261012.Global.h_interval]) (by linarith) floors hrows hnorms idx
    (fun u hu=>(hlabels u).2.1) hfloorbin).2
  have hsplit := finiteCentralCubeRows_supported_split S hS hmax η rows T hT WC Yp W0 W1
    (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z e grid (fun u=>(3*idx u+1:ℕ)*Z^τ)
  change _ ≤ Ct*Z^(HeckeZeroSupremum.beta-(4+Submission20261012.Global.b)/6-sigma) at herror
  rw [hsplit] at herror
  have hh := normalized_nonfloor_error _ _ _ _ _ _ _ herror hb
  apply hh.trans
  have hβlower := hβlo
  have hp : Z^(Submission20261012.Global.signal Submission20261012.Global.theta-sigma) ≤ Z^(HeckeZeroSupremum.beta-(4+Submission20261012.Global.b)/6-sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by dsimp [Submission20261012.Global.signal]; linarith)
  calc
    _ ≤ Ct*Z^(HeckeZeroSupremum.beta-(4+Submission20261012.Global.b)/6-sigma)+
      (Cf*(η.modulus.absNorm:ℝ)^(2*eps))*Z^(HeckeZeroSupremum.beta-(4+Submission20261012.Global.b)/6-sigma) := by gcongr
    _ = _ := by dsimp [C];ring

end Submission20261012.Global.HighRowFamily

end



#print axioms Submission20261012.Global.HighRowFamily.actual_nonfloor_probe_transport
end
/- END ORIGINAL MODULE Global.Transport.NonfloorTransport -/
