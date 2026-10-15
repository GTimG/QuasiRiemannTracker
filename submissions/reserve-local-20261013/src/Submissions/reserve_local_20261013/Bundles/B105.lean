/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B001
import Submissions.reserve_local_20261013.Bundles.B034
import Submissions.reserve_local_20261013.Bundles.B093
import Submissions.reserve_local_20261013.Bundles.B094
import Submissions.reserve_local_20261013.Bundles.B103
import Submissions.reserve_local_20261013.Bundles.B104
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondDyadicRowSupport
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalAggregate

/- BEGIN ORIGINAL MODULE Analytic.JointLowCommonBins ; sha256 7b3a367e3c11a9b54a7ddd7d5e9eb0bff659fcfd0545d6f0db98b79f181aff9b -/
section



/-! Exact coherent second transform with the original exceptional partEnergy
and one common finite row classifier. The low and high parts are physical
row sums; no common allocation is taken before this split. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentActiveSource CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit CenteredMomentCanonicalFirst
open CenteredMomentSecondRetainedRows CenteredMomentSectorLocalization CenteredMomentHeckeColumnWindow
open CenteredMomentSecondEnergySplit CenteredMomentSecondLiveBlock CenteredMomentChildRows
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput CenteredMomentFirstPhysicalSource
open CenteredMomentOriginalCommonHarmonic
open CenteredMomentSecondHeightFamily CenteredExceptionalProfile RayFourExpansion
open EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

lemma actualSecondRowBlocks_partEnergy (exceptional : Bool) (η : Character) (χ : RayCharacter)
    (Q : Ideal O) (m : O) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K T Z ξ H : ℝ) :
    actualSecondRowBlocks η t S β W K (frequencyRadius T Z ξ) H
      (fun q => partRows exceptional η χ Q m q.1.1.val.1 q.1.1.val.2 q.1.2 (frequencyRadius T Z ξ)) =
      partEnergy exceptional η χ Q m t S β W K T Z ξ H := by
  unfold actualSecondRowBlocks partEnergy
  rw [Fintype.sum_sigma,Fintype.sum_sigma]
  simp only [activePhysicalRows,Finset.mul_sum]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro p hp hn
  simp only [common_height_zero_of_not_live η t S β p hn,zero_mul,Finset.sum_const_zero]

/-- The source classifier is shared by every projector and ray. Its `none`
class is exactly the pinned exceptional physical energy. -/
theorem actual_common_second_exceptional_bins {ι κ : Type*} [Fintype ι] [Fintype κ]
    (src : Input ι) (Rmask seed C₁ L₁ : Ideal O) (hC₁ : Supported C₁) (hseed : seed ∣ C₁)
    {η : Character} (F : FirstSidePresentation η) (parent : Character) (hparent : parent = F.sourceParent)
    (bin : NonzeroElement → Option κ) (Q : Ideal O) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hbin : ∀ w,bin w = none ↔ FixedInducingRow η Q fixedBadMask 1 w.val)
    (χ : RayCharacter) (m : O) (hm : m ≠ 0) (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K T Z ξ H : ℝ) :
    let columns := commonSecondColumns (original src Rmask seed) C₁ hC₁
    let β := commonSecondBeta (original src Rmask seed) C₁ L₁
    let label := fun q : ActiveBlocks columns β K (frequencyRadius T Z ξ) H =>
      actualCommonBlockKernelLabel src Rmask seed C₁ L₁ hC₁ hseed parent K (frequencyRadius T Z ξ) H q 1 1 1
    actualSecondBlocks parent t columns β W K T Z ξ H =
      partEnergy true parent χ Q m t columns β W K T Z ξ H +
      ∑ b : κ,actualSecondRowBlocks parent t columns β W K (frequencyRadius T Z ξ) H
        (fun q => (sourceRows q.1.1.val.1 q.1.1.val.2 q.1.2 (frequencyRadius T Z ξ)).filter
          (fun z => F.sourceBin (label q) bin z = some b)) := by
  intro columns β label
  rw [actualSecondBlocks_eq_rows,←actualSecondRowBlocks_partEnergy true parent χ Q m]
  unfold actualSecondRowBlocks
  conv_rhs =>
    enter [2]
    rw [Finset.sum_comm]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [←Finset.mul_sum,←mul_add]
  congr 1
  have he := actual_retained_physicalBlock_exceptional_bin_partition F (label q) hparent bin Q hQ72 hbin
    χ m hm hmLam hm2 t (activeSource columns β) β (frequencyRadius T Z ξ) W K (fun i => (q.2 i : ℤ))
  exact he

theorem commonEnergy_exceptional_and_bins {ι κ : Type*} [Fintype ι] [Fintype κ]
    (src : Input ι) (Rmask seed C₁ L₁ : Ideal O) (hC₁ : Supported C₁) (hseed : seed ∣ C₁)
    {η : Character} (F : FirstSidePresentation η) (parent : Character) (hparent : parent = F.sourceParent)
    (bin : NonzeroElement → Option κ) (Q : Ideal O) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hbin : ∀ w,bin w = none ↔ FixedInducingRow η Q fixedBadMask 1 w.val)
    (χ : RayCharacter) (m : O) (hm : m ≠ 0) (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K T Z ξ H : ℝ) (hK : 0 < K)
    (hz₁ : src.W₁ 0 = 0) (hz₂ : src.W₂ 0 = 0)
    (hsource : sourceRadius src/(C₁.absNorm : ℝ) ≤ H) :
    let columns := commonSecondColumns (original src Rmask seed) C₁ hC₁
    let β := commonSecondBeta (original src Rmask seed) C₁ L₁
    let label := fun q : ActiveBlocks columns β K (frequencyRadius T Z ξ) H =>
      actualCommonBlockKernelLabel src Rmask seed C₁ L₁ hC₁ hseed parent K (frequencyRadius T Z ξ) H q 1 1 1
    commonEnergy (original src Rmask seed) C₁ hC₁ parent t L₁ W K =
      ((K : ℂ)*paperRadialFourier W 0)*
        CenteredMomentSourceSecondZeroEnergy.sourceSecondZero columns β parent t +
      (partEnergy true parent χ Q m t columns β W K T Z ξ H +
        ∑ b : κ,actualSecondRowBlocks parent t columns β W K (frequencyRadius T Z ξ) H
          (fun q => (sourceRows q.1.1.val.1 q.1.1.val.2 q.1.2 (frequencyRadius T Z ξ)).filter
            (fun z => F.sourceBin (label q) bin z = some b))) +
      CenteredMomentSupportedTailAggregate.secondDiscardedEnergy parent t columns β W K T Z ξ := by
  intro columns β label
  have hH : ∀ I ∈ columns,β I ≠ 0 → (I.absNorm : ℝ) ≤ H := by
    intro I hI hβ
    exact (commonSecond_source_norm_cap (original src Rmask seed) C₁ L₁ hC₁ (sourceRadius src)
      (fun J _ hJ => (original_column_norm src Rmask seed J hz₁ hz₂ hJ).2) I hI hβ).trans hsource
  rw [commonEnergy_second_blocks (original src Rmask seed) C₁ hC₁ parent t L₁ W K T Z ξ H hK hH,
    actual_common_second_exceptional_bins src Rmask seed C₁ L₁ hC₁ hseed F parent hparent bin Q hQ72 hbin χ m hm hmLam hm2]

#print axioms actualSecondRowBlocks_partEnergy
#print axioms actual_common_second_exceptional_bins
#print axioms commonEnergy_exceptional_and_bins
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowCommonBins -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowSeededHarmonic ; sha256 204cf6023bfa2896a61ca2e9db868c17e3fe0a79730dd82c6db4ca28c29d5f34 -/
section


/-! The literal first-projector divisibility seeds the second common
harmonic sum, retaining its reciprocal norm through all second projectors. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentActiveSource CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit CenteredMomentCanonicalFirst
open CenteredMomentMobiusHarmonicMass
open CenteredMomentMobiusRegroup CenteredMomentFixedRay RayFourExpansion
open CenteredMomentSecondSectorColumns CenteredMomentSectorLocalization
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput CenteredMomentOriginalCommonHarmonic
local notation "O" => HeckeFamily.O

theorem actual_seeded_second_projector_harmonic_mass
    (B Bproj L Cr ε : ℝ) (hB : 0 ≤ B) (hBproj : 0 ≤ Bproj) (hL : 0 ≤ L)
    (hCr : 0 < Cr) (hε : 0 < ε) :
    ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (src : Input ι) (R seed C₁ L₁ : Ideal O) (hC₁ : Supported C₁),
      Squarefree L₁ → src.W₁ 0 = 0 → src.W₂ 0 = 0 → sourceRadius src/(C₁.absNorm : ℝ) ≤ Z^B →
      ∀ K Radius Hsource : ℝ, 0 < K → Radius ≤ Cr*Z^L → Hsource ≤ Z^B →
      let columns := commonSecondColumns (original src R seed) C₁ hC₁
      let β := commonSecondBeta (original src R seed) C₁ L₁
      ∀ Ds : ActiveBlocks columns β K Radius Hsource → Finset (Ideal O),
      (∀ q, ∀ D ∈ Ds q, (UniqueFactorizationMonoid.moebius D : ℂ) ≠ 0 →
        (D.absNorm : ℝ) ≤ Z^Bproj) →
      (∑ q : ActiveBlocks columns β K Radius Hsource, ∑ D ∈ Ds q,
        (‖(UniqueFactorizationMonoid.moebius D : ℂ)‖/(D.absNorm : ℝ))*
          pairWeight q.1.1.val.1 q.1.1.val.2) ≤ Cbound*Z^ε/(L₁.absNorm : ℝ) := by
  obtain ⟨Cb,hCb,hblocks⟩ := actual_block_harmonic_mass B L Cr (ε/2) hB hL hCr (by positivity)
  obtain ⟨Cd,hCd,hdivs⟩ := full_mass_subpower Bproj (ε/2) hBproj (by positivity)
  refine ⟨Cd*Cb,mul_pos hCd hCb,?_⟩
  filter_upwards [hblocks,hdivs] with Z hblocks hdivs
  refine ⟨hdivs.1,?_⟩
  intro ι instF instD src R seed C₁ L₁ hC₁ hL₁ hz₁ hz₂ hsource K Radius Hsource hK hRadius hH columns β Ds hDs
  have hZ0 : 0 < Z := zero_lt_one.trans hdivs.1
  have hnorm : ∀ I ∈ columns, β I ≠ 0 → (I.absNorm : ℝ) ≤ Z^B := by
    intro I hI hβ
    exact (commonSecond_source_norm_cap (original src R seed) C₁ L₁ hC₁ (sourceRadius src)
      (fun J _ hJ => (original_column_norm src R seed J hz₁ hz₂ hJ).2) I hI hβ).trans hsource
  have hmask : ∀ I ∈ columns, β I ≠ 0 → L₁ ∣ I := by
    intro I hI hβ
    by_contra hd
    exact hβ (by simp only [β,commonSecondBeta,hd,and_false,ite_false])
  have hm := hblocks L₁ hL₁ hL₁.ne_zero columns β hmask hnorm K Radius Hsource hK hRadius hH
  have hi (q : ActiveBlocks columns β K Radius Hsource) :
      (∑ D ∈ Ds q, (‖(UniqueFactorizationMonoid.moebius D : ℂ)‖/(D.absNorm : ℝ))*
        pairWeight q.1.1.val.1 q.1.1.val.2) ≤
      (Cd*Z^(ε/2))*pairWeight q.1.1.val.1 q.1.1.val.2 := by
    rw [←Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hdivs.2 (Ds q) (hDs q)) (pairWeight_nonneg _ _)
  calc
    _ ≤ ∑ q : ActiveBlocks columns β K Radius Hsource,
        (Cd*Z^(ε/2))*pairWeight q.1.1.val.1 q.1.1.val.2 := Finset.sum_le_sum (fun q _ => hi q)
    _ = (Cd*Z^(ε/2))*∑ q : ActiveBlocks columns β K Radius Hsource,
        pairWeight q.1.1.val.1 q.1.1.val.2 := by rw [Finset.mul_sum]
    _ ≤ (Cd*Z^(ε/2))*(Cb*Z^(ε/2)/(L₁.absNorm : ℝ)) := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = (Cd*Cb)*(Z^(ε/2)*Z^(ε/2))/(L₁.absNorm : ℝ) := by ring
    _ = (Cd*Cb)*Z^ε/(L₁.absNorm : ℝ) := by rw [←Real.rpow_add hZ0,add_halves]

theorem actual_seeded_second_mixed_harmonic_mass
    (B Bproj L Cr ε : ℝ) (hB : 0 ≤ B) (hBproj : 0 ≤ Bproj) (hL : 0 ≤ L)
    (hCr : 0 < Cr) (hε : 0 < ε) :
    ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (src : Input ι) (R seed C₁ L₁ : Ideal O) (hC₁ : Supported C₁),
      Squarefree L₁ → src.W₁ 0 = 0 → src.W₂ 0 = 0 → sourceRadius src/(C₁.absNorm : ℝ) ≤ Z^B →
      ∀ K Radius Hsource : ℝ, 0 < K → Radius ≤ Cr*Z^L → Hsource ≤ Z^B →
      let columns := commonSecondColumns (original src R seed) C₁ hC₁
      let β := commonSecondBeta (original src R seed) C₁ L₁
      ∀ Ds : ActiveBlocks columns β K Radius Hsource → Finset (Ideal O),
      (∀ q, ∀ D ∈ Ds q, (UniqueFactorizationMonoid.moebius D : ℂ) ≠ 0 →
        (D.absNorm : ℝ) ≤ Z^Bproj) →
      ∀ E F saving : ℝ, 0 ≤ E → 0 ≤ F → Bproj ≤ saving →
      (∑ q : ActiveBlocks columns β K Radius Hsource, ∑ D ∈ Ds q,
        ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
          ‖(UniqueFactorizationMonoid.moebius D : ℂ)‖*
            ‖pairCoeff (phaseTable (primaryGenerator q.1.1.val.1) (primaryGenerator q.1.1.val.2)) χ ξ‖*
            pairWeight q.1.1.val.1 q.1.1.val.2*(E/(D.absNorm : ℝ)+F*Z^(-saving))) ≤
        Cbound*(E+F)*Z^ε/(L₁.absNorm : ℝ) := by
  obtain ⟨C,hC,hmain⟩ := actual_seeded_second_projector_harmonic_mass B Bproj L Cr ε hB hBproj hL hCr hε
  refine ⟨256*C,by positivity,?_⟩
  filter_upwards [hmain] with Z hmain
  refine ⟨hmain.1,?_⟩
  intro ι instF instD src R seed C₁ L₁ hC₁ hL₁ hz₁ hz₂ hsource K Radius Hsource hK hRadius hH columns β Ds hDs E F saving hE hF hsaving
  have hm := hmain.2 src R seed C₁ L₁ hC₁ hL₁ hz₁ hz₂ hsource K Radius Hsource hK hRadius hH Ds hDs
  calc
    _ ≤ ∑ q : ActiveBlocks columns β K Radius Hsource, ∑ D ∈ Ds q,
        (256*(E+F))*((‖(UniqueFactorizationMonoid.moebius D : ℂ)‖/(D.absNorm : ℝ))*
          pairWeight q.1.1.val.1 q.1.1.val.2) := by
      apply Finset.sum_le_sum
      intro q hq
      exact Finset.sum_le_sum (fun D hD => actual_second_ray_mixed_factor _ _ D Z E F Bproj saving
        hmain.1 hE hF hsaving (hDs q D hD))
    _ = (256*(E+F))*(∑ q : ActiveBlocks columns β K Radius Hsource, ∑ D ∈ Ds q,
        (‖(UniqueFactorizationMonoid.moebius D : ℂ)‖/(D.absNorm : ℝ))*pairWeight q.1.1.val.1 q.1.1.val.2) := by
      simp only [Finset.mul_sum]
    _ ≤ (256*(E+F))*(C*Z^ε/(L₁.absNorm : ℝ)) := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

theorem actual_seeded_second_low_rows
    (B Bproj L Cr ε : ℝ) (hB : 0 ≤ B) (hBproj : 0 ≤ Bproj) (hL : 0 ≤ L)
    (hCr : 0 < Cr) (hε : 0 < ε) (hBBproj : B ≤ Bproj) :
    ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (src : Input ι) (R seed C₁ L₁ : Ideal O) (hC₁ : Supported C₁) (hseed : seed ∣ C₁),
      Squarefree L₁ → src.W₁ 0 = 0 → src.W₂ 0 = 0 → sourceRadius src/(C₁.absNorm : ℝ) ≤ Z^B →
      ∀ (η : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K Radius Hsource V P E F saving target : ℝ),
      0 < K → Radius ≤ Cr*Z^L → Hsource ≤ Z^B → 0 < V → 0 < P → 0 ≤ E → 0 ≤ F → Bproj ≤ saving →
      let columns := commonSecondColumns (original src R seed) C₁ hC₁
      let β := commonSecondBeta (original src R seed) C₁ L₁
      let Ds := actualSecondProjectors columns β K Radius Hsource
      ∀ rows : ActiveBlocks columns β K Radius Hsource → Finset O,
      (∀ q, ∀ z ∈ rows q,z ≠ 0) →
      (∀ q, activePhysicalRows η t columns β W K Radius Hsource q (rows q) ≠ 0 →
        ∀ D ∈ Ds q, (UniqueFactorizationMonoid.moebius D : ℂ) ≠ 0 → ∀ χ ξ : RayCharacter,
        secondPrecountFactor V P q.1.1.val.1 q.1.1.val.2 q.1.2 K (fun i => (q.2 i : ℤ))*
          (∑ z ∈ rows q,‖(actualCommonBlockKernelLabel src R seed C₁ L₁ hC₁ hseed η K Radius Hsource q D χ ξ).toKernelLabel.kernelRow
            t z W K Radius (fun i => (q.2 i : ℤ))‖) ≤
          pairWeight q.1.1.val.1 q.1.1.val.2*(E/(D.absNorm : ℝ)+F*Z^(-saving))*Z^target) →
      ‖actualSecondRowBlocks η t columns β W K Radius Hsource rows‖/(V*P) ≤
        (Cbound*(E+F)/(L₁.absNorm : ℝ))*Z^(target+ε) := by
  obtain ⟨C,hC,hmain⟩ := actual_seeded_second_mixed_harmonic_mass B Bproj L Cr ε hB hBproj hL hCr hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hmain] with Z hmain
  refine ⟨hmain.1,?_⟩
  intro ι instF instD src R seed C₁ L₁ hC₁ hseed hL₁ hz₁ hz₂ hsource η t W K Radius Hsource V P E F saving target
    hK hRadius hH hV hP hE hF hsaving columns β Ds rows hrows hlocal
  have hZ0 : 0 < Z := zero_lt_one.trans hmain.1
  have hnorm : ∀ I ∈ columns,β I ≠ 0 → (I.absNorm : ℝ) ≤ Z^B := by
    intro I hI hβ
    exact (commonSecond_source_norm_cap (original src R seed) C₁ L₁ hC₁ (sourceRadius src)
      (fun J _ hJ => (original_column_norm src R seed J hz₁ hz₂ hJ).2) I hI hβ).trans hsource
  have hDs : ∀ q, ∀ D ∈ Ds q, (UniqueFactorizationMonoid.moebius D : ℂ) ≠ 0 →
      (D.absNorm : ℝ) ≤ Z^Bproj := by
    intro q D hD hμ
    exact (actualSecondProjectors_norm_cap columns β K Radius Hsource (Z^B) hnorm q D hD).trans
      (Real.rpow_le_rpow_of_exponent_le hmain.1.le hBBproj)
  let budget := fun q : ActiveBlocks columns β K Radius Hsource =>
    ∑ D ∈ Ds q, ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
      ‖(UniqueFactorizationMonoid.moebius D : ℂ)‖*
        ‖pairCoeff (phaseTable (primaryGenerator q.1.1.val.1) (primaryGenerator q.1.1.val.2)) χ ξ‖*
        pairWeight q.1.1.val.1 q.1.1.val.2*(E/(D.absNorm : ℝ)+F*Z^(-saving))
  have hm : (∑ q,budget q) ≤ C*(E+F)*Z^ε/(L₁.absNorm : ℝ) :=
    hmain.2 src R seed C₁ L₁ hC₁ hL₁ hz₁ hz₂ hsource K Radius Hsource hK hRadius hH Ds hDs E F saving hE hF hsaving
  have hb (q : ActiveBlocks columns β K Radius Hsource) :
      ‖activePhysicalRows η t columns β W K Radius Hsource q (rows q)‖/(V*P) ≤ budget q*Z^target := by
    by_cases hzero : activePhysicalRows η t columns β W K Radius Hsource q (rows q) = 0
    · rw [hzero,norm_zero,zero_div]
      have hpw := pairWeight_nonneg q.1.1.val.1 q.1.1.val.2
      dsimp [budget]
      positivity
    apply (activePhysicalRows_projected_majorant η t columns β W K Radius Hsource V P hK hV hP q (rows q) (hrows q)).trans
    dsimp [budget]
    simp only [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro D hD
    apply Finset.sum_le_sum
    intro χ hχ
    apply Finset.sum_le_sum
    intro ξ hξ
    by_cases hμ : (UniqueFactorizationMonoid.moebius D : ℂ) = 0
    · simp [hμ]
    have hl := hlocal q hzero D hD hμ χ ξ
    rw [CommonSecondKernelLabel.toKernelLabel_eq_projected] at hl
    have hh := mul_le_mul_of_nonneg_left hl
      (mul_nonneg (norm_nonneg (UniqueFactorizationMonoid.moebius D : ℂ))
        (norm_nonneg (pairCoeff (phaseTable (primaryGenerator q.1.1.val.1) (primaryGenerator q.1.1.val.2)) χ ξ)))
    convert hh using 1 <;> (try dsimp [actualCommonBlockKernelLabel]) <;> ring
  calc
    _ ≤ (∑ q,‖activePhysicalRows η t columns β W K Radius Hsource q (rows q)‖)/(V*P) :=
      div_le_div_of_nonneg_right (actualSecondRowBlocks_norm_le η t columns β W K Radius Hsource rows) (mul_pos hV hP).le
    _ ≤ ∑ q,budget q*Z^target := by
      rw [Finset.sum_div]
      exact Finset.sum_le_sum (fun q _ => hb q)
    _ = (∑ q,budget q)*Z^target := by rw [Finset.sum_mul]
    _ ≤ (C*(E+F)*Z^ε/(L₁.absNorm : ℝ))*Z^target := mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hZ0.le _)
    _ = _ := by rw [Real.rpow_add hZ0]; ring


#print axioms actual_seeded_second_projector_harmonic_mass
#print axioms actual_seeded_second_mixed_harmonic_mass
#print axioms actual_seeded_second_low_rows
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowSeededHarmonic -/

/- BEGIN ORIGINAL MODULE Global.Final.SourceContract ; sha256 2b6e577abe532f72f90838c4f0e77903e2b84b94d7ed7c5a68115c21680f598f -/
section



/-! Transfer the actual compensated source probe to the common-probe contract.
Adapted from weighted upstream HighRows/ConditionalFinal, revision
2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/
namespace Submission20261012.Global.FinalAssembly
noncomputable section
open Filter Asymptotics OAI.SevenEighths
open HeckeFamily ProbePhysical Cycle25ProbeFinalAssembly PrincipalSignalComparison
open Submission20261012.Global.ProbeAssembly

noncomputable def signalShift : ℝ := -(4+Submission20261012.Global.b)/6

theorem source_contract {Δ : ℝ} (D : HighParameters.HighData Δ)
    (F : WeightedSourceData D.toMomentData) (loss : ℝ) (hloss : 0 < loss)
    (herror : ∀η : Character,
      (fun Z=> sourceProbe D F η Z-HeckeSignal.signal
        (η.excludePrimes F.S F.exclusions.prime) (sourceCorrection η F.S) signalShift Z)
        =O[atTop](fun Z : ℝ=> Z^(HeckeZeroSupremum.beta+signalShift-D.sigma))) :
    Cycle25.PrimitiveProbeContract theta signalShift loss D.sigma := by
  intro η _hprimitive
  obtain ⟨hmask,hH,hHbound⟩ := actual_source_analytic F.S F.exclusions η
  refine ⟨η.excludePrimes F.S F.exclusions.prime,sourceCorrection η F.S,
    sourceProbe D F η,hmask,hH,hHbound,?_,herror η⟩
  convert sourceProbe_low D F loss hloss η using 1
  funext Z
  congr 1
  dsimp [Submission20261012.Global.signal,signalShift]
  ring
end
end Submission20261012.Global.FinalAssembly
end
/- END ORIGINAL MODULE Global.Final.SourceContract -/

/- BEGIN ORIGINAL MODULE Analytic.JointCoherentExceptionalEnergy ; sha256 634c22ee527fbea83df4f5a1fe00924504260412b118e8c943bf4d5fbb0abbef -/
section





/-! The original coherent exceptional partEnergy. Source support, actual
inducing rows, all second projectors and the first-projector radical seed
are discharged internally after the transformed exceptional split. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CanonicalRowCompletion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentSecondSectorColumns CenteredMomentActiveSource CenteredMomentFirstSectors
open CenteredMomentMobiusRegroup CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondHeightFamily CenteredMomentReflectedSource
open CenteredMomentSecondPhysicalBlock CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondLiveBlock CenteredMomentSecondEnergySplit
open CenteredMomentSecondExceptionalSourceFamily CenteredMomentSecondExceptionalAggregate
open CenteredMomentSecondBlockRadicalHarmonicMass CenteredMomentSecondDyadicRowSupport
open CenteredMomentFiniteProfileExceptional CenteredMomentExceptionalAmplitudePair CenteredMomentSectorLocalization
open CenteredMomentRankinRadical CenteredMomentChildRows RayFourExpansion CompletedGauss
local notation "O" => HeckeFamily.O
local instance coherentExceptionalEnergyDecidableSum {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem actual_common_coherent_exceptional_energy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (wlo whi : ℝ) (hwlo : 0 < wlo) (hwhi : 0 ≤ whi) (lo hi : ι → ℝ)
    (ε δ θ B Bsource L Cr εmass : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ) (hB : 0 ≤ B) (hBsource : 0 ≤ Bsource)
    (hL : 0 ≤ L) (hCr : 0 < Cr) (hεmass : 0 < εmass) (W : 𝓢(ℝ,ℂ)) :
    ∃ J : ℕ, ∃ Sprofile : Finset (ℕ×ℕ), (0,0) ∈ Sprofile ∧
    ∃ Cbound : ℝ, 0 ≤ Cbound ∧
    ∀ Q : Ideal O, Q ≠ 0 → Q ≠ ⊤ → Q ≤ Ideal.span {(72 : O)} →
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (src : Input ι) (profile : Profiles wlo whi),
    (∀ i, src.lo i = lo i) → (∀ i, src.hi i = hi i) → (∀ i, 1 ≤ src.P i) →
    src.W₁ = profile.profile 0 → src.W₂ = profile.profile 1 → sourceRadius src ≤ Z^Bsource →
    ∀ (R seed C₁ L₁ : Ideal O) (hC₁ : Supported C₁), R ≠ 0 → seed ∣ C₁ →
    Squarefree L₁ → L₁ ≠ 0 →
    ∀ (η : Character) (χ₀ : RayCharacter) (m : O), m ≠ 0 → goodLambda ∣ m → (2 : O) ∣ m →
    ∀ t Kphys Tsec ξ Hsource P r : ℝ, 0 < Kphys → 0 < P →
    frequencyRadius Tsec Z ξ ≤ Cr*Z^L → Hsource ≤ Z^Bsource →
    (expandedFactor η : ℝ)*R.absNorm*(sourceRadius src)^2*(4*frequencyRadius Tsec Z ξ) ≤ Z^B →
    Z^r ≤ src.X₁ → Z^r ≤ src.X₂ → Z^r ≤ src.Y₁ → Z^r ≤ src.Y₂ →
    ‖partEnergy true η χ₀ Q m t (commonSecondColumns (original src R seed) C₁ hC₁)
      (commonSecondBeta (original src R seed) C₁ L₁) W Kphys Tsec Z ξ Hsource‖/(volume src.toData*P) ≤
    Cbound*coherentExceptionalProfile Sprofile src profile J Q K t*
      (((C₁.absNorm : ℝ)*P)⁻¹*
        ((volume src.toData/(C₁.absNorm : ℝ))^(1/3:ℝ)*Kphys^(5/6:ℝ)*
          (originalLowerProfile src wlo wlo)^(-2/3:ℝ))*
        Z^(2*ε+δ+2*Bsource*θ+εmass-2*max (r-Real.logb Z (C₁.absNorm : ℝ)) 0/3)/
          (L₁.absNorm : ℝ)) := by
  obtain ⟨J,Sprofile,hSprofile,Ckernel,hCkernel,hbound⟩ := actual_coherent_exceptional_physical_uniform
    wlo whi hwlo hwhi lo hi ε δ θ B Bsource Bsource hε hδ hθ hB hBsource W
  obtain ⟨Cm,hCm,hmass⟩ := actual_common_second_radical_mass Bsource L Cr εmass hBsource hL hCr hεmass
  refine ⟨J,Sprofile,hSprofile,(256*Ckernel)*Cm,mul_nonneg (mul_nonneg (by norm_num) hCkernel) hCm.le,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩ := hbound Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound,hmass] with Z hZ hmassZ
  refine ⟨hZ.1,?_⟩
  intro src profile hlo hhi hP hW₁ hW₂ hsource R seed C₁ L₁ hC₁ hR hseed hL₁ hL₁0
    η χ₀ m hm hml hm2 t Kphys Tsec ξ Hsource P r hKphys hPcount hRadius hHsource hcond hX₁ hX₂ hY₁ hY₂
  let columns := commonSecondColumns (original src R seed) C₁ hC₁
  let β := commonSecondBeta (original src R seed) C₁ L₁
  let Radius := frequencyRadius Tsec Z ξ
  have hz := zero_lt_one.trans hZ.1
  have hv := CenteredMomentExceptionalAmplitudePair.volume_pos src.toData
  have hNC : 0 < (C₁.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC₁.1)
  have hNC1 : 1 ≤ (C₁.absNorm : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC₁.1)
  have hz₁ : src.W₁ 0 = 0 := by
    by_contra hh
    exact (not_le_of_gt hwlo) (profile.support 0 (by simpa only [←hW₁,Function.mem_support] using hh)).1
  have hz₂ : src.W₂ 0 = 0 := by
    by_contra hh
    exact (not_le_of_gt hwlo) (profile.support 1 (by simpa only [←hW₂,Function.mem_support] using hh)).1
  have hresidual : sourceRadius src/(C₁.absNorm : ℝ) ≤ Z^Bsource :=
    (div_le_iff₀ hNC).mpr (hsource.trans (le_mul_of_one_le_right (Real.rpow_nonneg hz.le _) hNC1))
  let E := ((256*Ckernel)*coherentExceptionalProfile Sprofile src profile J Q K t)*
    (((C₁.absNorm : ℝ)*P)⁻¹*
      ((volume src.toData/(C₁.absNorm : ℝ))^(1/3:ℝ)*Kphys^(5/6:ℝ)*
        (originalLowerProfile src wlo wlo)^(-2/3:ℝ))*
      Z^(2*ε+δ+2*Bsource*θ-2*max (r-Real.logb Z (C₁.absNorm : ℝ)) 0/3))
  have hprofile := coherentExceptionalProfile_nonneg Sprofile src profile J Q K t hK.le
  have ha := originalLowerProfile_pos src wlo wlo hwlo hwlo
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hlocal (p : ActiveLabel columns β) (hp : p ∈ liveLabels η columns β)
      (U : Finset (CommonIndex p.val.1 p.val.2))
      (n : SourceBlocks p.val.1 p.val.2 U Kphys Radius Hsource) :
      ‖physicalBlock η t (activeSource columns β) β p.val.1 p.val.2
        (lowActiveLeftSupported p) (lowActiveRightSupported p) U Radius
        (partRows true η χ₀ Q m p.val.1 p.val.2 U Radius) W Kphys (fun i => (n i : ℤ))‖/
        (volume src.toData*P) ≤ E*radicalWeight p.val.1 p.val.2 := by
    let rawRows := partRows true η χ₀ Q m p.val.1 p.val.2 U Radius
    let rows := dyadicRows rawRows (fun i => (n i : ℤ))
    have heq := physicalBlock_dyadic_rows η t (activeSource columns β) β p.val.1 p.val.2
      (lowActiveLeftSupported p) (lowActiveRightSupported p) U Radius rawRows W Kphys (fun i => (n i : ℤ))
    change _ = physicalBlock η t (activeSource columns β) β p.val.1 p.val.2
      (lowActiveLeftSupported p) (lowActiveRightSupported p) U Radius rows W Kphys (fun i => (n i : ℤ)) at heq
    by_cases hne : physicalBlock η t (activeSource columns β) β p.val.1 p.val.2
        (lowActiveLeftSupported p) (lowActiveRightSupported p) U Radius rows W Kphys (fun i => (n i : ℤ)) = 0
    · rw [heq,hne,norm_zero,zero_div]
      exact mul_nonneg hE (radicalWeight_nonneg _ _)
    obtain ⟨family,hfamily⟩ := CenteredMomentSecondExceptionalFamily.exists_exceptional_family η p.val.1 p.val.2
      (lowActiveLeftSupported p) (lowActiveRightSupported p)
      (commonLabels_data _ _ _ _ p.property).2.2 U
    have hrows (z : O) (hzr : z ∈ rows) : z ∈ rawRows := dyadicRows_subset _ _ hzr
    have hrow (z : O) (hzr : z ∈ rows) : (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ 4*Radius := by
      exact live_norm_le_four_radius p.val.1 p.val.2 U Radius rawRows z (by
        rw [exceptional_part_live]
        exact hrows z hzr)
    have hc (χ ξ : RayCharacter) (z : O) (hzr : z ∈ rows) :=
      actual_common_exceptional_conductor_caps src R seed C₁ L₁ hC₁ hz₁ hz₂ p η U family hfamily
        t Radius rows W Kphys hKphys (fun i => (n i : ℤ)) hne Z B hcond z (hrow z hzr) χ ξ
    have hb := hZ.2 src profile hlo hhi hP hW₁ hW₂ hsource R seed C₁ L₁ hC₁ hR hseed
      p η U family hfamily χ₀ t Kphys Radius r P (fun i => (n i : ℤ)) hKphys hPcount
      hX₁ hX₂ hY₁ hY₂ ((mem_liveLabels η columns β p).mp hp).1 m hm hml hm2 rows
      (dyadicRows_nonzero rawRows _) (fun z hz => exceptional_part_inducing η χ₀ Q m _ _ U Radius z (hrows z hz))
      (fun z hz => (dyadicRows_norm rawRows _ z hz).2.le)
      (fun χ z hz => (hc χ χ z hz).1) (fun χ z hz => (hc χ χ z hz).2)
      (fun L hL _ => (actual_common_second_projector_norm src R seed C₁ L₁ hC₁ hz₁ hz₂ p L hL).trans hsource)
    rw [heq]
    exact hb.trans_eq (by dsimp only [E,radicalWeight]; ring)
  have hs := part_energy_radical_bound true η χ₀ Q m t columns β W Kphys Tsec Z ξ Hsource
    (volume src.toData*P) E (mul_pos hv hPcount) hE hlocal
  have hm' := hmassZ src R seed C₁ L₁ hC₁ hL₁ hL₁0 hz₁ hz₂ hresidual Kphys Radius Hsource
    hKphys hRadius hHsource
  apply (hs.trans (mul_le_mul_of_nonneg_left hm' hE)).trans_eq
  have he : Z^(2*ε+δ+2*Bsource*θ-2*max (r-Real.logb Z (C₁.absNorm : ℝ)) 0/3)*Z^εmass =
      Z^(2*ε+δ+2*Bsource*θ+εmass-2*max (r-Real.logb Z (C₁.absNorm : ℝ)) 0/3) := by
    rw [←Real.rpow_add hz]
    congr 1
    ring
  dsimp only [E]
  calc
    _ = ((256*Ckernel)*Cm)*coherentExceptionalProfile Sprofile src profile J Q K t*
      (((C₁.absNorm : ℝ)*P)⁻¹*
        ((volume src.toData/(C₁.absNorm : ℝ))^(1/3:ℝ)*Kphys^(5/6:ℝ)*
          (originalLowerProfile src wlo wlo)^(-2/3:ℝ))*
        (Z^(2*ε+δ+2*Bsource*θ-2*max (r-Real.logb Z (C₁.absNorm : ℝ)) 0/3)*Z^εmass)/
        (L₁.absNorm : ℝ)) := by ring
    _ = _ := by rw [he]

#print axioms actual_common_coherent_exceptional_energy
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCoherentExceptionalEnergy -/

/- BEGIN ORIGINAL MODULE Analytic.JointCommonNormalizedSplit ; sha256 e7fac4f2c8c1b9623a255d78959cd9c7e496f5ea198f17aae016b9d43b63517e -/
section


/-! Exact coherent second transform with the original exceptional partEnergy
and one common finite row classifier. The low and high parts are physical
row sums; no common allocation is taken before this split. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentActiveSource CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit CenteredMomentCanonicalFirst
open CenteredMomentSecondRetainedRows CenteredMomentSectorLocalization CenteredMomentHeckeColumnWindow
open CenteredMomentSecondEnergySplit CenteredMomentSecondLiveBlock CenteredMomentChildRows
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput CenteredMomentFirstPhysicalSource
open CenteredMomentOriginalCommonHarmonic
open CenteredMomentSecondHeightFamily CenteredExceptionalProfile RayFourExpansion
open EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

theorem commonEnergy_normalized_bin_majorant {ι κ : Type*} [Fintype ι] [Fintype κ]
    (src : Input ι) (Rmask seed C₁ L₁ : Ideal O) (hC₁ : Supported C₁) (hseed : seed ∣ C₁)
    {η : Character} (F : FirstSidePresentation η) (parent : Character) (hparent : parent = F.sourceParent)
    (bin : NonzeroElement → Option κ) (Q : Ideal O) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hbin : ∀ w,bin w = none ↔ FixedInducingRow η Q fixedBadMask 1 w.val)
    (χ : RayCharacter) (m : O) (hm : m ≠ 0) (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K T Z ξ H : ℝ) (hK : 0 < K)
    (hz₁ : src.W₁ 0 = 0) (hz₂ : src.W₂ 0 = 0)
    (hsource : sourceRadius src/(C₁.absNorm : ℝ) ≤ H) (P : ℝ) (hP : 0 < P) :
    let columns := commonSecondColumns (original src Rmask seed) C₁ hC₁
    let β := commonSecondBeta (original src Rmask seed) C₁ L₁
    let label := fun q : ActiveBlocks columns β K (frequencyRadius T Z ξ) H =>
      actualCommonBlockKernelLabel src Rmask seed C₁ L₁ hC₁ hseed parent K (frequencyRadius T Z ξ) H q 1 1 1
    (commonEnergy (original src Rmask seed) C₁ hC₁ parent t L₁ W K).re /
      (CenteredMomentExceptionalAmplitudePair.volume src.toData*P) ≤
      ‖((K : ℂ)*paperRadialFourier W 0)*
        CenteredMomentSourceSecondZeroEnergy.sourceSecondZero columns β parent t‖ /
          (CenteredMomentExceptionalAmplitudePair.volume src.toData*P) +
      ‖partEnergy true parent χ Q m t columns β W K T Z ξ H‖ /
          (CenteredMomentExceptionalAmplitudePair.volume src.toData*P) +
      (∑ b : κ, ‖actualSecondRowBlocks parent t columns β W K (frequencyRadius T Z ξ) H
        (fun q => (sourceRows q.1.1.val.1 q.1.1.val.2 q.1.2 (frequencyRadius T Z ξ)).filter
          (fun z => F.sourceBin (label q) bin z = some b))‖ /
            (CenteredMomentExceptionalAmplitudePair.volume src.toData*P)) +
      ‖CenteredMomentSupportedTailAggregate.secondDiscardedEnergy parent t columns β W K T Z ξ‖ /
          (CenteredMomentExceptionalAmplitudePair.volume src.toData*P) := by
  intro columns β label
  have hv := CenteredMomentExceptionalAmplitudePair.volume_pos src.toData
  have heq := commonEnergy_exceptional_and_bins src Rmask seed C₁ L₁ hC₁ hseed F parent hparent
    bin Q hQ72 hbin χ m hm hmLam hm2 t W K T Z ξ H hK hz₁ hz₂ hsource
  rw [heq,←Finset.sum_div,←add_div,←add_div,←add_div]
  apply div_le_div_of_nonneg_right _ (mul_pos hv hP).le
  have htri (a b c d : ℂ) : (a+(b+c)+d).re ≤ ‖a‖+‖b‖+‖c‖+‖d‖ := by
    linarith [Complex.re_le_norm (a+(b+c)+d),norm_add_le (a+(b+c)) d,
      norm_add_le a (b+c),norm_add_le b c]
  apply (htri _ _ _ _).trans
  gcongr
  exact norm_sum_le _ _

#print axioms commonEnergy_normalized_bin_majorant

end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCommonNormalizedSplit -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstCoherentAmplification ; sha256 668fa58657ef924c0eeeb3c302f660c36fa3a947664c31f9a1e147b3438dabe4 -/
section



/-! The coherent amplifier on both literal first source domains. Its
prime family is fixed before the source and every live arithmetic label. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT RayFourExpansion
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentPrimePool CenteredMomentPrimeElements
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationGlobal CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSectorLocalization CenteredMomentSecondHeightFamily CenteredMomentChildRows
open CenteredMomentCommonAllocationSum CenteredMomentFirstScale
open CenteredMomentAmplificationActiveFactor CenteredMomentCommonProfile
open CenteredMomentCanonicalFirst CenteredMomentFirstNonexceptionalWeightSum ActualEisensteinCubic
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def FirstJointLabel.sideMainRadius (q : FirstJointLabel ι) (left : Bool)
    (Z K X sigma delta reserve : ℝ) : ℝ :=
  mainCommonRadius Z (q.sideWidth (!left) Z)
    (nominalLog (q.sideCommon left) (q.sideCommon (!left))
      (Ideal.span {q.puncture}) K X Z)
    (q.sideWidth left Z) sigma delta reserve

theorem actual_first_coherent_annular_amplification
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes ⊆ Sbad)
    (N : ℕ) (a b sigma loss BR Bs Mmax eta Csec xi reserve : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hsigma : 0 < sigma) (hloss : 0 < loss)
    (hM : 0 ≤ Mmax) (hgap : eta < sigma/6) (hCsec : 1 ≤ Csec)
    (hxi : 0 ≤ xi) (hreserve : 0 < reserve) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss) ≤ (P.card : ℝ) ∧
      ∃ τ : (J : Finset ι) → Character → elementPool P → Fin 3 → RayCharacter → Character,
        (∀ J η (p : elementPool P) i χ, ((τ J η p i χ).modulus.absNorm : ℝ) ≤
          radicalBound (childCharacter η χ) fixedBadMask p.val (errorMovingExponent (errorIndex i))) ∧
      ∀ (s : Input ι) (R seed : Ideal O), Squarefree seed → R ≠ 0 →
        s.W₁ 0 = 0 → s.W₂ 0 = 0 → sourceRadius s ≤ Z^Bs →
        (R.absNorm : ℝ) ≤ Z^BR →
        Fintype.card ι ≤ N → a ≤ s.lower → s.upper ≤ b →
      ∀ (z : ι → ℝ), (∀ j,z j ≤ eta) → (∀ j,s.P j = Z^(z j)) →
      ∀ (Kfirst : ℝ), 0 < Kfirst →
      ∀ radius : (p : Labels s R seed) →
        Finset (CommonIndex p.val.1 p.val.2) → ℝ,
      let q := firstSourceOuterLabel s R seed Kfirst radius
      ∀ (labels : Finset (FirstSourceOuterIndex s R seed Kfirst radius)) (left : Bool),
      let domain := firstSideSourceLabels labels q (fun _ => sourceRadius s) left
      ∀ (t Tsec H₀ : ((i : FirstSourceOuterIndex s R seed Kfirst radius) × (q i).SourceIndex) → ℝ),
        (∀ k ∈ domain, Tsec k ≤ Csec*firstNominalScale ((q k.1).sideCommon left)
          ((q k.1).sideCommon (!left)) (Ideal.span {(q k.1).puncture}) Kfirst (volume s)) →
        (∀ k ∈ domain, 0 < H₀ k ∧ H₀ k ≤ 4*frequencyRadius (Tsec k) Z xi ∧ 8*H₀ k ≤ Z^Mmax) →
      let delta := frequencyLoss Z (32*Csec) xi
      (∑ k ∈ firstSourceLabels labels q,
        ((q k.1).sourceChild k.2).sideEnergy left (t k)
          CenteredMomentFirstAnnularMajorant.profile (H₀ k)/volume s) ≤
        (56*((Mmax+2*sigma)/(sigma/6)))*
          (∑ k ∈ domain,
            ((q k.1).sourceChild k.2).sideEnergy left (t k) ballProfile
              ((q k.1).sideMainRadius left Z Kfirst (volume s) sigma delta reserve)/
                (volume s*(P.card : ℝ))) +
        ∑ k ∈ domain, allocatedExtractedErrors N s ((q k.1).sideCommon left) R k.2.1.val
          (((q k.1).sourceChild k.2).sideParent left) (t k) b Z ((q k.1).sideWidth (!left) Z)
          (nominalLog ((q k.1).sideCommon left) ((q k.1).sideCommon (!left))
            (Ideal.span {(q k.1).puncture}) Kfirst (volume s) Z)
          ((q k.1).sideWidth left Z) sigma delta reserve P
          (fun B => τ (liveIndices B.val) (((q k.1).sourceChild k.2).sideParent left)) := by
  filter_upwards [joint_direct_common_annular_amplification_literal (ι := ι)
    M H hH Sbad hbad N a b sigma loss (BR+Bs) Bs Mmax eta Csec xi reserve
    ha hb hsigma hloss hM hgap hCsec hxi hreserve] with Z hZ
  obtain ⟨hZ,hP,hcard,τ,hτ,hamp⟩ := hZ
  refine ⟨hZ,hP,hcard,τ,hτ,?_⟩
  intro s R seed hseed hR hz₁ hz₂ hsource hRcap hN hlo hhi z hz hlen
    Kfirst hKfirst radius q labels left domain t Tsec H₀ hsec hH₀ delta
  have hsupport : ∀ i ∈ labels, ∀ I, (q i).data.beta I ≠ 0 →
      (I.absNorm : ℝ) ≤ sourceRadius s := by
    intro i hi I hI
    exact (original_column_norm s R seed I hz₁ hz₂ hI).2
  have hg (k) (hk : k ∈ domain) :
      k.1 ∈ labels ∧ Squarefree k.2.1.val ∧ k.2.1.val ≠ 0 ∧
        ((k.2.1.val).absNorm : ℝ) ≤ Z^Bs := by
    cases left
    · exact firstRightSourceLabels_gates labels q _ Z Bs (zero_lt_one.trans hZ).le
        (fun _ _ => hsource) k hk
    · exact firstLeftSourceLabels_gates labels q _ Z Bs (zero_lt_one.trans hZ).le
        (fun _ _ => hsource) k hk
  have hcommon (i : FirstSourceOuterIndex s R seed Kfirst radius) :
      seed ∣ (q i).sideCommon left ∧ ((q i).sideCommon left).absNorm ≤ sourceRadius s := by
    have hh := actual_common_gates s R seed hseed hz₁ hz₂ i.1.val.1 i.1.val.2 i.1.property
    cases left
    · exact ⟨hh.2.2.2.2.1,hh.2.2.2.2.2.2⟩
    · exact ⟨hh.2.2.2.1,hh.2.2.2.2.2.1⟩
  have hRC (i : FirstSourceOuterIndex s R seed Kfirst radius) :
      ((R*(q i).sideCommon left).absNorm : ℝ) ≤ Z^(BR+Bs) := by
    simp only [map_mul,Nat.cast_mul,Real.rpow_add (zero_lt_one.trans hZ)]
    exact mul_le_mul hRcap ((hcommon i).2.trans hsource) (Nat.cast_nonneg _) (by positivity)
  have hE (i : FirstSourceOuterIndex s R seed Kfirst radius) :
      Ideal.span {(q i).puncture} ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr (primeSubsetGenerator_ne_zero _ _)
  have henergy (k : (i : FirstSourceOuterIndex s R seed Kfirst radius) × (q i).SourceIndex)
      (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
      ((q k.1).sourceChild k.2).sideEnergy left (t k) W K =
        (commonEnergy (original s R seed) ((q k.1).sideCommon left)
          ((q k.1).sideCommon_supported left) (((q k.1).sourceChild k.2).sideParent left)
          (t k) k.2.1.val W K).re := by cases left <;> rfl
  rw [←Finset.sum_div,first_sideEnergy_eq_supported labels q (fun _ => sourceRadius s)
    hsupport left t (fun _ => CenteredMomentFirstAnnularMajorant.profile) H₀,Finset.sum_div]
  have hh := hamp domain (fun _ => s) (fun _ => 1) hN
    (fun k => (q k.1).sideCommon left) (fun _ => R) (fun _ => seed) (fun k => k.2.1.val)
    (fun k => (q k.1).sideCommon left) (fun k => (q k.1).sideCommon (!left))
    (fun k => Ideal.span {(q k.1).puncture}) (fun k => (q k.1).sideCommon_supported left)
    (fun k => ((q k.1).sourceChild k.2).sideParent left) t (fun _ => Kfirst) (fun _ => volume s)
    Tsec H₀ (fun k => (q k.1).sideWidth (!left) Z) (fun k => (q k.1).sideWidth left Z) (fun _ => z)
    (fun _ _ => by norm_num) (fun _ _ => hlo) (fun _ _ => hhi)
    (fun k _ => (hcommon k.1).1) (fun _ _ => hz) (fun _ _ => hlen)
    (fun _ _ => hR) (fun k hk => (hg k hk).2.2.1) (fun k _ => hRC k.1)
    (fun k hk => (hg k hk).2.2.2) (fun k _ => hE k.1)
    (fun _ _ => hKfirst) (fun _ _ => volume_pos s) hsec
    (fun k hk => (hH₀ k hk).1) (fun k hk => (hH₀ k hk).2.1)
    (fun k hk => (hH₀ k hk).2.2)
  simpa only [one_mul,FirstJointLabel.sideMainRadius,henergy] using hh

#print axioms actual_first_coherent_annular_amplification
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstCoherentAmplification -/
