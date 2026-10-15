/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.affine_local_20261013.Bundles.B033
import Submissions.affine_local_20261013.Bundles.B055
import Submissions.affine_local_20261013.Bundles.B069
import Submissions.affine_local_20261013.Bundles.B077
import Submissions.affine_local_20261013.Bundles.B079
import Submissions.affine_local_20261013.Bundles.B083
import Submissions.affine_local_20261013.Bundles.B084
import Submissions.affine_local_20261013.Bundles.B085
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowNominalEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.FirstLiveAdmission

/- BEGIN ORIGINAL MODULE Analytic.JointSecondCostSectors ; sha256 f072a038d750468768eb05343999c0049dba4f1e38d96b359cc801cc83b35595 -/
section


/-! The actual common-frequency ideal is supported below both second
common ideals. Sector representatives can therefore enforce g₂ ≤ b₂
without fixing any of the actual ideal norms. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss CenteredMomentSourceRow
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentFirstSourceConductorCaps
local notation "O" => HeckeFamily.O

namespace CommonSecondKernelLabel
variable {Slot : Type*} [Fintype Slot]

theorem commonFrequency_norm_le (s : CommonSecondKernelLabel Slot) :
    ((Ideal.span {commonFrequencyGenerator s.second.val.1 s.second.val.2}).absNorm : ℝ) ≤
      (s.second.val.1.absNorm : ℝ) ∧
    ((Ideal.span {commonFrequencyGenerator s.second.val.1 s.second.val.2}).absNorm : ℝ) ≤
      (s.second.val.2.absNorm : ℝ) := by
  have hd := commonFrequencyGenerator_dvd s.second.val.1 s.second.val.2
    s.toKernelLabel.hC s.toKernelLabel.hD s.toKernelLabel.hCD
  have hC : Supported s.second.val.1 := s.toKernelLabel.hC
  have hD : Supported s.second.val.2 := s.toKernelLabel.hD
  constructor
  · apply divisor_norm_le _ _ hC.1
    simpa only [primary_span_supported s.second.val.1 hC] using
      (Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr hd.1)
  · apply divisor_norm_le _ _ hD.1
    simpa only [primary_span_supported s.second.val.2 hD] using
      (Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr hd.2)

theorem commonFrequency_log_le_average (s : CommonSecondKernelLabel Slot)
    (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z ((Ideal.span {commonFrequencyGenerator s.second.val.1 s.second.val.2}).absNorm : ℝ) ≤
      (Real.logb Z (s.second.val.1.absNorm : ℝ)+Real.logb Z (s.second.val.2.absNorm : ℝ))/2 := by
  have hg := CenteredMomentFirstScale.norm_pos
    (Ideal.span {commonFrequencyGenerator s.second.val.1 s.second.val.2})
    (Ideal.span_singleton_eq_bot.not.mpr
      (commonFrequencyGenerator_ne_zero _ _ s.toKernelLabel.hC))
  have h₁ := Real.logb_le_logb_of_le hZ hg s.commonFrequency_norm_le.1
  have h₂ := Real.logb_le_logb_of_le hZ hg s.commonFrequency_norm_le.2
  linarith

/-- Use min g b as the representative g₂. Its required g₂≤b inequality
is automatic, while the genuine scalar cost pays only the interval widths. -/
theorem secondLogCost_le_capped_sectors (s : CommonSecondKernelLabel Slot)
    (Z g t b eg et eb : ℝ) (hZ : 1 < Z) (heg : 0 ≤ eg) (heb : 0 ≤ eb)
    (hg : Real.logb Z ((Ideal.span {commonFrequencyGenerator s.second.val.1 s.second.val.2}).absNorm : ℝ) ≤ g+eg)
    (ht : t-et ≤ Real.logb Z ((∏ Q ∈ s.partition, Q.val).absNorm : ℝ))
    (hb : b-eb ≤ (Real.logb Z (s.second.val.1.absNorm : ℝ)+Real.logb Z (s.second.val.2.absNorm : ℝ))/2) :
    min g b ≤ b ∧ s.secondLogCost Z ≤ min g b-t-b+(eg+et+eb) := by
  refine ⟨min_le_right _ _,?_⟩
  rcases le_total g b with hgb | hbg
  · rw [min_eq_left hgb]
    exact s.secondLogCost_le_of_sectors Z g t b eg et eb hg ht hb
  · rw [min_eq_right hbg]
    have hactual := s.commonFrequency_log_le_average Z hZ
    unfold secondLogCost
    linarith

end CommonSecondKernelLabel
#print axioms CommonSecondKernelLabel.commonFrequency_log_le_average
#print axioms CommonSecondKernelLabel.secondLogCost_le_capped_sectors
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointSecondCostSectors -/

/- BEGIN ORIGINAL MODULE Analytic.JointSecondLowTransport ; sha256 c3f8eef42ad3af9881c76196dc1faaff45afdf7b37b23fbfcf993ca18e1d832b -/
section




/-! The actual second family agrees with the reconstructed first-family
row after the literal common puncture. Finite deletion then supplies the
low-bin gate without imposing a maskless coefficient identity. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge
open ActualEisensteinCubic CompletedGauss RayFourExpansion
open CenteredMomentHeckeExpansion CenteredMomentSourceRow CenteredMomentHeckeColumnWindow
open CenteredMomentSecondHeightFamily CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSourceRectangleMask CenteredMomentNaturalRowSource
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst
open CenteredMomentFixedRay CenteredMomentSecondCanonical
local notation "O" => HeckeFamily.O

/-- A complete common mask supplies precisely the coprimality required by
`Family.height_eq`; the result holds on every ideal, including zero. -/
theorem actual_second_family_masked_row
    (parent : Character) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (family : RayCharacter → Character)
    (hfamily : Family parent C D hC hD U family)
    (T : Ideal O) (hCT : C ∣ T ∨ D ∣ T) (χ : RayCharacter) (z : O) (t : ℝ) (I : Ideal O) :
    rowWeight (family χ) (fixedBadMask*idealGenerator T) 1 z t I =
      rowWeight (rayParent parent χ) (fixedBadMask*idealGenerator T) 1
        ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z) t I := by
  have hLam : goodLambda ∣ fixedBadMask := dvd_mul_right _ _
  have htwo : (2 : O) ∣ fixedBadMask := dvd_mul_left _ _
  rw [←rowWeight_ideal_mask _ _ _ _ _ hLam htwo,
    ←rowWeight_ideal_mask _ _ _ _ _ hLam htwo]
  by_cases hIT : IsCoprime I T
  · simp only [if_pos hIT,one_mul]
    by_cases hI : Supported I
    · have hCI : IsCoprime C I ∨ IsCoprime D I := by
        rcases hCT with hC | hD
        · exact Or.inl (hIT.of_isCoprime_of_dvd_right hC).symm
        · exact Or.inr (hIT.of_isCoprime_of_dvd_right hD).symm
      rw [rayParent_rowWeight,rowWeight_split (family χ),rowWeight_split parent,
        ←heightCoeff_eq_fixed_rowWeight (family χ) t I hI,
        ←heightCoeff_eq_fixed_rowWeight parent t I hI,
        hfamily.height_eq χ I hI hCI t]
      simp only [idealRowHom_argument_mul]
      ring
    · rw [rowWeight_zero_of_not_supported _ _ _ _ _ hLam htwo I hI,
        rowWeight_zero_of_not_supported _ _ _ _ _ hLam htwo I hI]
  · simp only [if_neg hIT,zero_mul]

/-- First-family natural rows and the genuine second family use one fixed
parent dictionary. The extra deletion is the actual cumulative common
mask, and the target retains its product with the canceled-prime mask. -/
theorem actual_second_family_deleted_natural_rows
    (η : Character) (C₁ D₁ : Ideal O) (hC₁ : Supported C₁)
    (E₁ : Finset (CommonIndex C₁ D₁)) (ξ₁ ξ₂ : RayCharacter)
    (F : FixedPair η C₁ D₁ hC₁ E₁ ξ₁ ξ₂) :
    ∃ u : Oˣ, ∃ τL ∈ fixedParentDictionary η, ∃ τR ∈ fixedParentDictionary η,
      activeConductor C₁ D₁ = (u : O)*∏ i,activePrimary C₁ D₁ i ∧
      ∀ (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
        (U : Finset (CommonIndex C₂ D₂)) (familyL familyR : RayCharacter → Character),
      Family F.left C₂ D₂ hC₂ hD₂ U familyL →
      Family F.right C₂ D₂ hC₂ hD₂ U familyR →
      ∀ (T : Ideal O), T ≠ 0 → (C₂ ∣ T ∨ D₂ ∣ T) → ∀ (χ : RayCharacter) (z : O), z ≠ 0 →
      let j := (commonFrequencyGenerator C₂ D₂*nonunitFrequencyGenerator C₂ D₂ U)*z
      let wL := primeSubsetGenerator (fun P : CommonIndex C₁ D₁ => P.val) E₁*
        (u : O)*leftEffectiveFactor C₁ D₁*j
      let wR := primeSubsetGenerator (fun P : CommonIndex C₁ D₁ => P.val) E₁*
        (u : O)*rightEffectiveFactor C₁ D₁*j
      ∃ NL : NaturalRow (rayParent τL χ) wL, ∃ NR : NaturalRow (rayParent τR χ) wR,
        ∀ (NsL : NaturalRow (familyL χ) z) (NsR : NaturalRow (familyR χ) z) (I : Ideal O),
        idealCoeff (excluded NsL.character T) I =
          idealCoeff (excluded NL.character (T*canceledIdeal C₁ D₁ 5)) I ∧
        idealCoeff (excluded NsR.character T) I =
          idealCoeff (excluded NR.character (T*canceledIdeal C₁ D₁ 1)) I := by
  obtain ⟨u,τL,hτL,τR,hτR,hu,hrows⟩ := actual_source_second_ray_natural_rows η C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F
  refine ⟨u,τL,hτL,τR,hτR,hu,?_⟩
  intro C₂ D₂ hC₂ hD₂ U familyL familyR hfamilyL hfamilyR T hT hCT χ z hz j wL wR
  have hj : j ≠ 0 := mul_ne_zero (mul_ne_zero
    (commonFrequencyGenerator_ne_zero C₂ D₂ hC₂) (nonunitFrequencyGenerator_ne_zero C₂ D₂ hC₂ U)) hz
  obtain ⟨NL,NR,hcoeff,_⟩ := hrows χ j hj
  refine ⟨NL,NR,?_⟩
  intro NsL NsR I
  have left (J : Ideal O) : rowWeight (rayParent F.left χ) fixedBadMask 1 j 0 J =
      heightCoeff (excluded NL.character (canceledIdeal C₁ D₁ 5)) 0 J :=
    (rayParent_rowWeight F.left χ j 0 J).trans (hcoeff 0 J).1
  have right (J : Ideal O) : rowWeight (rayParent F.right χ) fixedBadMask 1 j 0 J =
      heightCoeff (excluded NR.character (canceledIdeal C₁ D₁ 1)) 0 J :=
    (rayParent_rowWeight F.right χ j 0 J).trans (hcoeff 0 J).2
  have hleft := rowWeight_join_puncture (rayParent F.left χ) (rayParent τL χ) j wL 0
    (canceledIdeal C₁ D₁ 5) T (fun J => (left J).trans
      (naturalRow_masked_height NL _ (canceledIdeal_ne_zero C₁ D₁ hC₁ 5) 0 J)) I
  have hright := rowWeight_join_puncture (rayParent F.right χ) (rayParent τR χ) j wR 0
    (canceledIdeal C₁ D₁ 1) T (fun J => (right J).trans
      (naturalRow_masked_height NR _ (canceledIdeal_ne_zero C₁ D₁ hC₁ 1) 0 J)) I
  have hL := (naturalRow_masked_height NsL T hT 0 I).trans
    ((actual_second_family_masked_row F.left C₂ D₂ hC₂ hD₂ U familyL hfamilyL T hCT χ z 0 I).trans hleft)
  have hR := (naturalRow_masked_height NsR T hT 0 I).trans
    ((actual_second_family_masked_row F.right C₂ D₂ hC₂ hD₂ U familyR hfamilyR T hCT χ z 0 I).trans hright)
  rw [←naturalRow_masked_height NL _ (mul_ne_zero hT (canceledIdeal_ne_zero C₁ D₁ hC₁ 5)) 0 I] at hL
  rw [←naturalRow_masked_height NR _ (mul_ne_zero hT (canceledIdeal_ne_zero C₁ D₁ hC₁ 1)) 0 I] at hR
  simpa only [heightCoeff,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one] using And.intro hL hR


def firstSideCharacter {η : Character} {C D : Ideal O} {hC : Supported C}
    {E : Finset (CommonIndex C D)} {ξ₁ ξ₂ : RayCharacter}
    (F : FixedPair η C D hC E ξ₁ ξ₂) (left : Bool) : Character :=
  if left then F.left else F.right

def firstSideCanceled (C D : Ideal O) (left : Bool) : Ideal O :=
  canceledIdeal C D (if left then 5 else 1)

def secondReconstructedRow (C₁ D₁ : Ideal O) (hC₁ : Supported C₁)
    (E₁ : Finset (CommonIndex C₁ D₁)) (u : Oˣ)
    (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (U : Finset (CommonIndex C₂ D₂))
    (left : Bool) (z : O) (hz : z ≠ 0) : NonzeroElement :=
  ⟨primeSubsetGenerator (fun P : CommonIndex C₁ D₁ => P.val) E₁*(u : O)*
    (if left then leftEffectiveFactor C₁ D₁ else rightEffectiveFactor C₁ D₁)*
    ((commonFrequencyGenerator C₂ D₂*nonunitFrequencyGenerator C₂ D₂ U)*z),by
      apply mul_ne_zero
      · apply mul_ne_zero
        · exact mul_ne_zero (primeSubsetGenerator_ne_zero _ _) u.ne_zero
        · cases left <;> exact active_product_pow_ne_zero C₁ D₁ hC₁ _
      · exact mul_ne_zero (mul_ne_zero (commonFrequencyGenerator_ne_zero C₂ D₂ hC₂)
          (nonunitFrequencyGenerator_ne_zero C₂ D₂ hC₂ U)) hz⟩

/-- Both first sides, with no coefficient-equivalence premise. The unit is
chosen once from the first arithmetic label, before every second label. -/
theorem actual_second_side_deleted_dictionary
    (η : Character) (C₁ D₁ : Ideal O) (hC₁ : Supported C₁)
    (E₁ : Finset (CommonIndex C₁ D₁)) (ξ₁ ξ₂ : RayCharacter)
    (F : FixedPair η C₁ D₁ hC₁ E₁ ξ₁ ξ₂) :
    ∃ u : Oˣ, activeConductor C₁ D₁ = (u : O)*∏ i,activePrimary C₁ D₁ i ∧
      ∀ (left : Bool) (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂),
      primeSupport C₂ = primeSupport D₂ →
      ∀ (U : Finset (CommonIndex C₂ D₂)) (family : RayCharacter → Character),
      Family (firstSideCharacter F left) C₂ D₂ hC₂ hD₂ U family →
      ∀ (T : Ideal O), T ≠ 0 → (C₂ ∣ T ∨ D₂ ∣ T) → ∀ (χ : RayCharacter) (z : O) (hz : z ≠ 0),
      ∃ parent : JointParentLabel η,
      ∃ N : NaturalRow parent.val (secondReconstructedRow C₁ D₁ hC₁ E₁ u C₂ D₂ hC₂ U left z hz).val,
      ∀ (Ns : NaturalRow (family χ) z) (I : Ideal O),
        idealCoeff (excluded Ns.character T) I =
          idealCoeff (excluded N.character (T*firstSideCanceled C₁ D₁ left)) I := by
  obtain ⟨u,τL,hτL,τR,hτR,hu,hrows⟩ :=
    actual_second_family_deleted_natural_rows η C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F
  refine ⟨u,hu,?_⟩
  intro left C₂ D₂ hC₂ hD₂ hCD U family hfamily T hT hCT χ z hz
  cases left
  · obtain ⟨other,hother⟩ := exists_exceptional_family F.left C₂ D₂ hC₂ hD₂ hCD U
    obtain ⟨NL,NR,hcoeff⟩ := hrows C₂ D₂ hC₂ hD₂ U other family hother hfamily T hT hCT χ z hz
    refine ⟨⟨rayParent τR χ,jointParentDictionary_base_mem η _ (rayParent_mem _ τR hτR χ)⟩,NR,?_⟩
    intro Ns I
    exact (hcoeff (naturalRow (other χ) z hz) Ns I).2
  · obtain ⟨other,hother⟩ := exists_exceptional_family F.right C₂ D₂ hC₂ hD₂ hCD U
    obtain ⟨NL,NR,hcoeff⟩ := hrows C₂ D₂ hC₂ hD₂ U family other hfamily hother T hT hCT χ z hz
    refine ⟨⟨rayParent τL χ,jointParentDictionary_base_mem η _ (rayParent_mem _ τL hτL χ)⟩,NL,?_⟩
    intro Ns I
    exact (hcoeff Ns (naturalRow (other χ) z hz) I).1

/-- The reconstruction unit depends only on the fixed first source label. -/
def firstSideDictionaryUnit (η : Character) (C₁ D₁ : Ideal O) (hC₁ : Supported C₁)
    (E₁ : Finset (CommonIndex C₁ D₁)) (ξ₁ ξ₂ : RayCharacter)
    (F : FixedPair η C₁ D₁ hC₁ E₁ ξ₁ ξ₂) : Oˣ :=
  Classical.choose (actual_second_side_deleted_dictionary η C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F)

#print axioms actual_second_family_masked_row
#print axioms actual_second_family_deleted_natural_rows
#print axioms actual_second_side_deleted_dictionary
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointSecondLowTransport -/

/- BEGIN ORIGINAL MODULE Analytic.JointSourceTailEnvelope ; sha256 a71aa8873d114e96af0869f05219d6230cfac538441cb0b65ab766b50f4586b1 -/
section



/-! Coarse Fourier tails use literal Input mass and the existing nonzero
Möbius projector norm cap. No separate coefficient, column or projector
cardinality assumption is required. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSectorLocalization
open CenteredMomentSecondDiagonal CenteredMomentWholeDivisorShell
local notation "O" => HeckeFamily.O

 theorem moebius_mass_le_norm_cap (Ds : Finset (Ideal O)) (Y : ℝ) (hY : 0 ≤ Y)
    (hN : ∀ D ∈ Ds, (UniqueFactorizationMonoid.moebius D : ℂ) ≠ 0 →
      (D.absNorm : ℝ) ≤ Y) :
    (∑ D ∈ Ds, ‖(UniqueFactorizationMonoid.moebius D : ℂ)‖) ≤ 128*Y := by
  let S := Ds.filter (fun D => (UniqueFactorizationMonoid.moebius D : ℂ) ≠ 0)
  have hc := divisible_ideal_card S 1 one_ne_zero
    (fun D hD => (squarefree_of_moebius_ne_zero D (Finset.mem_filter.mp hD).2).ne_zero)
    (fun _ _ => one_dvd _) Y hY
    (fun D hD => hN D (Finset.mem_filter.mp hD).1 (Finset.mem_filter.mp hD).2)
  have he : (∑ D ∈ Ds, ‖(UniqueFactorizationMonoid.moebius D : ℂ)‖) =
      ∑ D ∈ S, ‖(UniqueFactorizationMonoid.moebius D : ℂ)‖ := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro D hD
    by_cases h : (UniqueFactorizationMonoid.moebius D : ℂ) = 0 <;> simp [h]
  rw [he]
  apply le_trans _ (by simpa using hc)
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using
    Finset.sum_le_sum (fun D (_ : D ∈ S) => moebius_norm_le_one D)

 def originalAbsoluteEnvelope {ι α : Type*} [Fintype ι]
    (S : Finset α) (s : α → CommonSecondKernelLabel ι) (B₁ B₂ : ℝ) : ℝ :=
  if h : S.Nonempty then max 1 (S.sup' h (fun v => originalAbsoluteProfile (s v).input B₁ B₂)) else 1

 theorem originalAbsoluteEnvelope_nonneg {ι α : Type*} [Fintype ι]
    (S : Finset α) (s : α → CommonSecondKernelLabel ι) (B₁ B₂ : ℝ) :
    0 ≤ originalAbsoluteEnvelope S s B₁ B₂ := by
  unfold originalAbsoluteEnvelope
  split_ifs <;> positivity

 theorem originalAbsoluteEnvelope_bound {ι α : Type*} [Fintype ι]
    (S : Finset α) (s : α → CommonSecondKernelLabel ι) (B₁ B₂ : ℝ) (v : α) (hv : v ∈ S) :
    originalAbsoluteProfile (s v).input B₁ B₂ ≤ originalAbsoluteEnvelope S s B₁ B₂ := by
  rw [originalAbsoluteEnvelope,dif_pos ⟨v,hv⟩]
  exact (Finset.le_sup' (fun v => originalAbsoluteProfile (s v).input B₁ B₂) hv).trans
    (le_max_right _ _)

 theorem second_projected_absolute_input_power
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset α) (s : α → CommonSecondKernelLabel ι) (Ds : α → Finset (Ideal O))
    (n : α → Fin 4 → ℤ) (Z scale A B C F V B₁ B₂ : ℝ)
    (hZ : 0 < Z) (hscale : 0 ≤ scale) (hscale' : scale ≤ Z^A)
    (hcard : (S.card : ℝ) ≤ Z^B)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hplain : ∀ v ∈ S, (s v).input.W₁ 0 = 0 ∧ (s v).input.W₂ 0 = 0 ∧
      (∀ x, ‖(s v).input.W₁ x‖ ≤ B₁) ∧ (∀ x, ‖(s v).input.W₂ x‖ ≤ B₂))
    (hvolume : ∀ v ∈ S, CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData ≤ Z^V)
    (hprojectors : ∀ v ∈ S, ∀ D ∈ Ds v, (UniqueFactorizationMonoid.moebius D : ℂ) ≠ 0 →
      (D.absNorm : ℝ) ≤ Z^C)
    (hdyad : ∀ v ∈ S, (Real.sqrt (dyadicScale (n v 2)))⁻¹ ≤ Z^F ∧
      (Real.sqrt (dyadicScale (n v 3)))⁻¹ ≤ Z^F) :
    secondProjectedAbsoluteEnvelope S s Ds n scale ≤
      (128*(originalAbsoluteEnvelope S s B₁ B₂)^2)*Z^(A+B+C+2*F+2*V) := by
  let E := originalAbsoluteEnvelope S s B₁ B₂
  have hE : 0 ≤ E := originalAbsoluteEnvelope_nonneg S s B₁ B₂
  have hmass (v) (hv : v ∈ S) :
      sourceAbsoluteMass (s v).toKernelLabel.columns (s v).toKernelLabel.beta ≤ E*Z^V := by
    have hh := hplain v hv
    apply (actual_common_absolute_mass (s v) B₁ B₂ hB₁ hB₂ hh.1 hh.2.1 hh.2.2.1 hh.2.2.2).trans
    exact mul_le_mul (originalAbsoluteEnvelope_bound S s B₁ B₂ v hv) (hvolume v hv)
      (CenteredMomentSourceInputTailUniform.volume_pos (s v).input).le hE
  have henv (v) (hv : v ∈ S) :
      (s v).toKernelLabel.absoluteEnvelope (dyadicScale (n v 2)) (dyadicScale (n v 3)) ≤
        E^2*Z^(2*F+2*V) := by
    have hh := hdyad v hv
    have hsq := pow_le_pow_left₀ (sourceAbsoluteMass_nonneg _ _) (hmass v hv) 2
    unfold SecondKernelLabel.absoluteEnvelope
    apply (mul_le_mul (mul_le_mul hh.1 hh.2 (by positivity) (by positivity)) hsq
      (by positivity) (by positivity)).trans_eq
    rw [mul_pow,← Real.rpow_two (Z^V),← Real.rpow_mul hZ.le,
      ← Real.rpow_add hZ]
    rw [show F+F = 2*F by ring]
    rw [show V*2 = 2*V by ring,Real.rpow_add hZ]
    ring
  have hinner (v) (hv : v ∈ S) :
      (∑ D ∈ Ds v, ‖(UniqueFactorizationMonoid.moebius D : ℂ)‖ *
        (s v).toKernelLabel.absoluteEnvelope (dyadicScale (n v 2)) (dyadicScale (n v 3))) ≤
      (128*E^2)*Z^(C+(2*F+2*V)) := by
    rw [← Finset.sum_mul]
    have hm := moebius_mass_le_norm_cap (Ds v) (Z^C) (by positivity) (hprojectors v hv)
    apply (mul_le_mul hm (henv v hv) ((s v).toKernelLabel.absoluteEnvelope_nonneg _ _) (by positivity)).trans_eq
    simp only [Real.rpow_add hZ]
    ring
  unfold secondProjectedAbsoluteEnvelope
  calc
    _ ≤ scale*((S.card : ℝ)*((128*E^2)*Z^(C+(2*F+2*V)))) := by
      apply mul_le_mul_of_nonneg_left _ hscale
      simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum hinner
    _ ≤ Z^A*(Z^B*((128*E^2)*Z^(C+(2*F+2*V)))) :=
      mul_le_mul hscale' (mul_le_mul_of_nonneg_right hcard (by positivity)) (by positivity) (by positivity)
    _ = _ := by
      change _ = (128*E^2)*Z^(A+B+C+2*F+2*V)
      simp only [Real.rpow_add hZ]
      ring

#print axioms moebius_mass_le_norm_cap
#print axioms second_projected_absolute_input_power
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointSourceTailEnvelope -/

/- BEGIN ORIGINAL MODULE Global.Low.Detector.LowNominalEnergy ; sha256 6cb9a4bf5ca7be3fdbaed1b49a37f8180aa7af81e1f27fde88163c8c2215d92d -/
section




/-! Adapted from OpenAI/math family003, pinned original module Detector.LowNominalEnergy.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace Submission20261012.Global
open OAI OAI.SevenEighths

noncomputable section
open scoped Classical
namespace LowProbe
open ProbePhysical
open CompletedGauss CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem low_selected_nominal_energy (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤ Submission20261012.Global.ell)
    (Ck b ε : ℝ) (hCk : 0< Ck) (hε : 0<ε) (hε1 : ε≤1) :
    ∃degree : ℕ,∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in Filter.atTop,1< Z ∧
    ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=> Disjoint (T i) (T j))→
      (∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤ b*Z^(ell i))→
    ∀(J : Finset (Fin K))(R : Finset O),
      (∀z∈R,z≠0 ∧ elementNorm z≤ Ck*Z^((1-Submission20261012.Global.ell)-2*lowUnselectedLength ell J))→
    ∀X : ℝ,0< X→Z^(1+lowSelectedLength ell J-ε/2)≤ X→X≤ Z^(1+lowSelectedLength ell J+ε/2)→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→∀(Y : Fin K→ℝ)(t : ℝ)(σ : RayRing),
      (∑z∈R,‖lowSelectedInverseRow Finset.univ
        (lowSelectedWeight η (fun i=> canonicalSlotSupport (T i)) J W Y t)
        η S hS (lowSelectedIdeal (fun i=> canonicalSlotSupport (T i)) J) X t σ z‖^2)≤
        C*(1+‖t‖)^degree*Z^(((1-Submission20261012.Global.ell)-lowUnselectedLength ell J)+507*ε) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := low_selected_physical_energy η S hS hbad K Ck ε hCk hε hε1
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [eventually_low_selected_caps ell hell b ε hε,Filter.eventually_ge_atTop Z₀] with Z hc hZ
  refine ⟨hc.1,?_⟩
  intro T hT hout hdis hnorm J R hR X hX hXlo hXhi W hW Y t σ
  obtain ⟨hd,hd1,hs,hscap⟩ := lowLength_bounds ell hell hsum J
  have hscale := lowCentralShift_scale Z X (lowSelectedLength ell J+ε/2) hc.1 hX
  rw [←hscale]
  apply he Z (lowUnselectedLength ell J) (lowSelectedLength ell J+ε/2)
    (lowCentralShift Z X (lowSelectedLength ell J+ε/2)) hZ hd hd1 (by linarith) (by linarith)
    (lowCentralShift_bound Z X (lowSelectedLength ell J) ε hc.1 hX hε.le hXlo hXhi)
    R hR T hT hout hdis J (fun i=> max 1 (b*Z^(ell i.val)))
    (fun i=> le_max_left _ _)
    (fun i P hP=>(hnorm i.val P hP).trans (le_max_right _ _)) (hc.2 J) W hW Y t σ

end LowProbe
end

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Detector.LowNominalEnergy -/

/- BEGIN ORIGINAL MODULE Global.Numerator.SourceBin ; sha256 7032d4db0f658c70d4c6965a1b690278bd501d9c9dd3e5dd5678916f017e0449 -/
section



/-! Actual source packet estimates with the original physical fourth moment
fully discharged. Remaining bin premises are finite count and prime-amplitude
inequalities, supplied by the certified source amplitude partition. -/
noncomputable section
set_option maxHeartbeats 2400000
open scoped BigOperators Classical ContDiff
open Filter
namespace Submission20261012.Global.Numerator
open Cycle25.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open ProbeRowRadicalConductor Cycle25DetectorRowCount
local notation "O" => HeckeFamily.O

theorem source_packet_selected_bin {Δ : ℝ} (D : HighParameters.HighData Δ)
    (F : WeightedSourceData D.toMomentData) (hbeta : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hfine : ∀j,D.ell j≤ Cycle25.sourceMesh D.t/200) (J : Finset (Fin D.N)) :
    ∃degree : ℕ,∃C : ℝ,0 < C ∧ ∀ᶠU : ℝ in atTop,
      1 < U ∧ ∀(Z d : ℝ),1 < Z → (1/2:ℝ)≤ d → d≤ Submission20261012.Global.h+rowExtension → U=Z^d →
      ∀(η : Character) (x z : ℂ) (a height : ℝ), (51/100:ℝ)≤ a → a≤7/8 →
      x.re=a+16*D.e → z.re=17/50 → 0≤ height → |z.im|≤ height →
      ∀(rows : Finset FreeRow),
      (∀u∈rows,U^(1/100:ℝ)≤ rowNorm u ∧ rowNorm u≤ U) →
      (∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1) →
      (∀P:∀i:J,sourcePrimePool F Z i.val,Function.Injective (fun i=>(P i).val)) →
      (∀i P,P∈sourcePrimePool F Z i→IsCoprime P.val η.modulus) →
      (∀i:J,sourcePrimePool F Z i.val) →
      ∀(selected : ℕ→Finset (Fin D.N)) (P : rows→ℂ) (q R selLoss Ccount : ℝ),
      0≤ q → q≤(2*a-1)/2 → 1≤ Ccount → (rows.card:ℝ)≤ Ccount*U^R →
      (∀i,‖P i‖≤ U^(q*(ell/d))) →
      (∀j∈Finset.range (coefficientBoxCount D.t+1),
        (∑s∈selected j,D.ell s/d)≤ selectedCapacity D.momentKappa ((2*(ly/d)-1)/(6*D.momentKappa)-D.t/(3*D.momentKappa)) ((j:ℝ)*D.t+D.t)) →
      (∀j∈Finset.range (coefficientBoxCount D.t+1),∀i:rows,
        U^(q*selectedCapacity D.momentKappa ((2*(ly/d)-1)/(6*D.momentKappa)-D.t/(3*D.momentKappa)) ((j:ℝ)*D.t+D.t)-selLoss)≤
          ‖∏s∈selected j,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2 (Z^(D.ell s)) z‖) →
      (∀j∈Finset.range (coefficientBoxCount D.t+1),∀i:rows,
        ‖∏s∈selected j,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2 (Z^(D.ell s)) z‖≤ U) →
      (∑i:rows,‖labelPolynomialPacket F.S F.exclusions η i.val
        (fun s:J=> sourcePrimePool F Z s.val) (fun s=> source_prime_pool_outside F Z s.val)
        (fun _=> F.W) (fun s=> Z^(D.ell s.val)) x z F.W (U^(ly/d))*P i‖) ≤
        C*Ccount*(1+height)^degree*(U^(ly/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.ell s.val))^(-(4/25:ℝ)))*
          U^(D.t+q*(ell/d)-q*((2*(ly/d)-1)/(6*D.momentKappa)-D.t/(3*D.momentKappa))/2+
            (3*R+1+2*D.t)/4+selLoss/2+(2*a-1)*D.t/4) := by
  obtain ⟨Cm,hCm,hpacket⟩ := actual_label_packet_bin_bound (ι:=J) D.momentKappa D.t 1 2 1 D.momentKappa_lo D.t_pos
    (by norm_num) (by norm_num) (by norm_num)
  have hsmall : 2*D.t+D.t≤1/2 := by have := D.t_small;linarith
  obtain ⟨degree,Cr,hCr,hmoment⟩ := certified_active_box_fourth F D.momentKappa D.momentKappa_lo D.momentKappa_hi D.momentKappa_beta hbeta F.W D.t D.t D.t 2
    D.t_pos D.t_pos D.t_pos (by norm_num) hsmall
  let Cr' : ℝ := max 1 Cr
  have hCr' : 1≤ Cr' := le_max_left _ _
  let C : ℝ := ((coefficientBoxCount D.t+1:ℕ):ℝ)*Cm*Cr'
  have hC : 0 < C := by dsimp [C];have := zero_lt_one.trans_le hCr';positivity
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hmoment,eventually_physical_cutoff_le_base 2 (by norm_num)] with U hmom hcutU
  dsimp only [HighParameters.HighData.toMomentData] at hmom
  refine ⟨hmom.1,?_⟩
  intro Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hheight hzim rows hrows hrow
    hdis hη Pbase selected P q R selLoss Ccount hq hqtop hCc hcard hfull hcap hselected hcrude
  have hd0 : 0 < d := by linarith
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hU0 : 0 < U := zero_lt_one.trans hmom.1
  have hscale (s : Fin D.N) : U^(D.ell s/d)=Z^(D.ell s) := by
    rw [hUZ,←Real.rpow_mul hZ0.le,mul_div_cancel₀ _ hd0.ne']
  let data (i : rows) : PhysicalReflectionData F.S F.exclusions.prime i.val :=
    Classical.choice (physical_reflection_data_exists F.S F.exclusions.prime i.val (hrow i.val i.property))
  let Cu (i : rows) := (data i).combinedConductor
  let Ccond : ℝ := fixedConductorConstant F.S
  have hCcond : 0 < Ccond := by dsimp only [Ccond];exact_mod_cast fixedConductorConstant_pos F.S F.exclusions.prime
  let Ts (s : J) := sourcePrimePool F Z s.val
  let hTs := fun s:J=> source_prime_pool_outside F Z s.val
  let Q (j : ℕ) (i : rows) := ∏s∈selected j,
    HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2 (Z^(D.ell s)) z
  have hQprod (j : ℕ) (i : rows) :
      (∏s:selected j,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
        (U^(D.ell s.val/d)) z) = Q j i := by
    calc
      _ = ∏s:selected j,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (Z^(D.ell s.val)) z := by
        apply Finset.prod_congr rfl
        intro s hs
        rw [hscale s.val]
      _ = _ := by
        exact Finset.prod_coe_sort (selected j)
          (fun s=> HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2 (Z^(D.ell s)) z)
  have hwpos (s : Fin D.N) : 0 < D.ell s/d := div_pos (D.slots_bounds s).1 hd0
  have hwmax (s : Fin D.N) : D.ell s/d≤ Cycle25.sourceMesh D.t := by
    apply (div_le_iff₀ hd0).mpr
    have ht := Cycle25.sourceMesh_pos D.t_pos
    have hs := hfine s
    nlinarith
  have hYp (s : J) : 1≤ Z^(D.ell s.val) := Real.one_le_rpow hZ.le (D.slots_bounds s.val).1.le
  have hY : 0< U^(ly/d) := Real.rpow_pos_of_pos hU0 _
  have hcut : 2*U^(ly/d)≤ U^((coefficientBoxCount D.t:ℝ)*D.t) := by
    apply (hcutU.2 d hd).trans
    simpa using Real.rpow_le_rpow_of_exponent_le hmom.1.le (coefficientBoxCount_extent D.t D.t_pos).1
  obtain ⟨hrho,hrho1,hline,hleft,hmargin⟩ := source_packet_lines D a ha hatop
  have hmomentInput (j : ℕ) (hj : j∈Finset.range (coefficientBoxCount D.t+1))
      (e : ∀i:rows,LabelPacketIndex F.S i.val Ts) :
      (∑i:rows,‖if (labelPacketScale F.S i.val Ts (e i):ℝ)≤2*U^(ly/d) ∧
        dilationBox U D.t (coefficientBoxCount D.t)
          (max 1 ((Cu i/(Ccond*((Ideal.span {i.val.val}:Ideal O).absNorm:ℝ)))*
            (labelPacketScale F.S i.val Ts (e i):ℝ)))=j
        then HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime i.val) false F.W
          (U^(ly/d)/(labelPacketScale F.S i.val Ts (e i):ℝ)) 0 0 else 0‖^4*‖Q j i‖^2) ≤
      (Cr'*(1+height)^degree)*U^(1+2*D.t) := by
    have hh := hmom.2 rows hrows data (fun i=>(labelPacketScale F.S i.val Ts (e i):ℝ))
      (fun i=> lt_of_lt_of_le zero_lt_one (by exact_mod_cast labelPacketScale_one_le F.S i.val Ts (e i)))
      d hd hdmax j hj (selected j) (fun s=> D.ell s.val/d) (fun _=> z) height
      (fun s=> hwpos s.val) (fun s=> hwmax s.val) (fun _=> hz) hheight (fun _=> hzim)
      ((Finset.sum_coe_sort (selected j) (fun s=> D.ell s/d)).le.trans (hcap j hj))
      (by
        intro i
        change ‖(∏s:selected j,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (U^(D.ell s.val/d)) z)‖≤ U
        rw [hQprod]
        exact hcrude j hj i)
    have hh' : _ ≤ (Cr'*(1+height)^degree)*U^(1+D.t+D.t) := hh.trans (by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hU0.le _)
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (by linarith) _))
    simp only [show 1+D.t+D.t=1+2*D.t by ring] at hh'
    convert hh' using 1
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (fun qq : ℂ => ‖if (labelPacketScale F.S i.val Ts (e i):ℝ)≤2*U^(ly/d) ∧
      dilationBox U D.t (coefficientBoxCount D.t)
        (max 1 ((Cu i/(Ccond*((Ideal.span {i.val.val}:Ideal O).absNorm:ℝ)))*
          (labelPacketScale F.S i.val Ts (e i):ℝ)))=j
      then HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime i.val) false F.W
        (U^(ly/d)/(labelPacketScale F.S i.val Ts (e i):ℝ)) 0 0 else 0‖^4*‖qq‖^2) (hQprod j i).symm

  have hCM : 1≤ Cr'*(1+height)^degree := one_le_mul_of_one_le_of_one_le hCr' (one_le_pow₀ (by linarith))
  have hb := hpacket F.S F.exclusions (4*D.e) F.first η Ts hTs hdis
    (fun s Q hQ=> hη s.val Q hQ) Pbase (fun _=> F.W) (fun s=> Z^(D.ell s.val)) hYp
    (fun _=> F.complex_support) (fun _ y=> source_complex_profile_norm F y) x z a D.e ha
    (by linarith) D.e_pos D.e_small.le hx hz rows Subtype.val F.W 1 2 (U^(ly/d))
    (by norm_num) F.complex_support (F.W.smooth ⊤) hY U D.t (coefficientBoxCount D.t) Cu Ccond Q P
    R q (ell/d) ((2*(ly/d)-1)/(6*D.momentKappa)-D.t/(3*D.momentKappa)) (2*a-1) selLoss (2*D.t) Ccount
    (Cr'*(1+height)^degree) hmom.1.le D.t_pos.le hCc hCM hq hqtop hrho hrho1 hline hleft
    (by simpa only [hx] using hmargin) hCcond (fun i=>(data i).combined_pos.le)
    (fun i=>(data i).combined_le_radical) (fun i=>(hrows i.val i.property).2)
    (fun i=> hrow i.val i.property) hcut (by simpa using hcard) hselected hfull hmomentInput
  apply hb.trans_eq
  dsimp only [C]
  have hp : U^(D.t+q*(ell/d)-q*((2*(ly/d)-1)/(6*D.momentKappa)-D.t/(3*D.momentKappa))/2+
      (3*R+1+2*D.t)/4+selLoss/2+(2*a-1)*D.t/4) =
      U^D.t*U^(q*(ell/d)-q*((2*(ly/d)-1)/(6*D.momentKappa)-D.t/(3*D.momentKappa))/2+
      (3*R+1+2*D.t)/4+selLoss/2+(2*a-1)*D.t/4) := by
    rw [←Real.rpow_add hU0]
    congr 1
    ring
  rw [hp]
  ring

end Submission20261012.Global.Numerator

/- Adapted from weighted-numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. Variable moment parameter, genuine physical source. -/

-- New geometry wrapper, 13 October 2026; inherited analytic core unchanged.
end
/- END ORIGINAL MODULE Global.Numerator.SourceBin -/

/- BEGIN ORIGINAL MODULE Analytic.ActualExtractedErrorAverage ; sha256 8483d9a3c3cfbd6ee267e57e0ba813c1e609c38b0deb762850f9978c1bf63636 -/
section



/-! Actual extracted error estimates with Ready discharged by source caps.
Dead extracted sources vanish exactly. Every live extracted source receives
its Ready packet from the pinned source theorem before the genuine analytic
estimate is used. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.Local44.Analytic
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=> HeckeFamily.O
local instance actualExtractedErrorAverageDecEq {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid CenteredMomentEnergyBandSubtypeTransport
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
local instance actualExtractedErrorAverageFinite : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

open CenteredMomentEnergyCanonicalUniformReference CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentFirstAmplifiedPaidAdmission CenteredMomentFirstAmplifiedCapacityCommon
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss
open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)
open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization
open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource
open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization
open CenteredMomentFirstNestedSeededGaussianPower CenteredMomentFirstSecondInputGates


open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstAmplificationChoice
open CenteredMomentEnergyFirstLiveAdmission

open CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentFirstMixedAllowance
open CenteredMomentFirstPhysicalSource CenteredMomentPrimeElements CenteredMomentPrimePool

theorem actual_firstExtractedErrors_local_average
    (Wslot:ℝ→ℂ)(aslot bslot Mcap εremove lo hi εchild:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤ Mslot)(hεmask:0<εmask)(haPlain:0< a)(haUpper:a≤1/4)(hbPlain:1≤ b)
    (L:ℝ)(hL:0≤ L)
    (ha:0< aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hbslot:0≤ bslot)(hMcap:0< Mcap)
    (hεchild:0<εchild)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)(hbetaTop:HeckeZeroSupremum.beta≤7/8)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0< lower)(hupper:1≤ upper)
    (ha0:0< a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤ highs i)
    (εsrc δsrc θsrc Bcap Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hBcap:0≤ Bcap)(hξ:0<ξ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes ⊆ Sbad)
    (sigma cost:ℝ)(hsigma:0< sigma)(hξsmall:ξ≤ sigma/4)(hcost:1≤ cost) (hsigma_eq : sigma=9/500)
    (Avol Dscale Pmask qmoving εgeo : ℝ) (hεgeo : 0 < εgeo)
    (hbudget : CenteredMomentFirstSecondInputGates.exponent Avol Dscale Pmask qmoving εgeo ξ ≤ Bcap):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤ M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃Cbound:ℝ,0< Cbound ∧ ∀ᶠ Z : ℝ in atTop, 1< Z ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤ mesh → (∀i,0≤ w i) → (∀i,w i≤ mesh) →
    (∀i,w i≤(Cycle25.Energy.commonMesh Mcap 0 L εchild)) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) → 0≤ height → (∀i,|freq i|≤ height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤ bslot) → (∀i,src.M i≤ Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤ N → lower≤ src.lower → src.upper≤ upper →
    0≤ src.b₁ → 0≤ src.b₂ → src.b₁≤ max 1 b → src.b₂≤ max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D} →
    ∀K delta reserve asource:ℝ,0< K → 0< asource →
    0≤ delta → 0≤ reserve → a0≤ asource →
    let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
    P.Nonempty →
    (∀ (prime : elementPool P) i, ∀ I∈(activeInput (child src C R0 B τ t)).slots i,
      IsCoprime (Ideal.span {prime.val}) I) →
    ∀ family : elementPool P → Fin 3 → RayCharacter → Character,
    (∀ prime i χ, (family prime i χ).modulus.absNorm≤ CenteredMomentAmplificationRadicalFamily.radicalBound
      (CenteredMomentChildRows.childCharacter τ χ) fixedBadMask prime
      (CenteredMomentAmplificationActiveFactor.errorMovingExponent (errorIndex i))) →
    (∀ prime i χ, ((family prime i χ).modulus.absNorm:ℝ)≤
      cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z (errorIndex i+1))) →
    let radius := fun (prime : elementPool P) (i : Fin 3) => errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime (errorIndex i+1)
    src.W₁ 0=0 → src.W₂ 0=0 → volume src≤ Z^Avol →
    (R0.absNorm : ℝ)≤ Z^Pmask → R0≠0 →
    (∀ prime i, (radius prime i)⁻¹≤ Z^Dscale) →
    (∀ prime i χ, ((family prime i χ).modulus.absNorm : ℝ)≤ Z^qmoving) →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤ Z^Bseed →
    ∀profile:Profiles a b,profile.profile 0=src.W₁ → profile.profile 1=src.W₂ →
    src.X₁≤ Z^L → src.X₂≤ Z^L → src.Y₁≤ Z^L → src.Y₂≤ Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*(3/4)*(∑i,w i)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mwidth →
    Mwidth-sigma/2≤ Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤ CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀ Mgeom Mvolume : ℝ, 1≤ Mgeom →
    Z^(Mgeom/4)≤ src.X₁ → Z^(Mgeom/4)≤ src.X₂ →
    Z^(Mgeom/4)≤ src.Y₁ → Z^(Mgeom/4)≤ src.Y₂ →
    Mgeom≤ Real.logb Z K+Real.logb Z (src.η.modulus.absNorm : ℝ)+Real.logb Z fixedPresentationCost →
    Real.logb Z (volume src)≤(883/1000)*Mgeom →
    Real.logb Z (volume src)≤ Mvolume →
    Real.logb Z fixedPresentationCost≤1/1000 →
    Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm : ℝ))≤37/10000 →
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+(3/4)*mesh
    (56/(P.card : ℝ))*(∑ prime : elementPool P,
      firstExtractedErrors (child src C R0 B τ t) (R0*C) seed Z
      (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime (family prime)) ≤
      mass (child src C R0 B τ t)^2*
        (reference (τ.modulus.absNorm : ℝ) (volume src) (C.absNorm : ℝ) Z
          (allowance C D Z)/(volume src/(C.absNorm : ℝ)))*
        (56*1872*(Fintype.card RayCharacter : ℝ))*
          ∑ j : Fin 4,
            (Cbound*(profile.control Uprofile)^2*(1+|t|+height)^Jheight*
              Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm : ℝ))*
            (upper^N)^(powers εsrc j)*
            Z^(localErrorExponents paid εsrc Mvolume saving delta reserve j) := by
  subst sigma
  obtain ⟨Uprofile,Jheight,hactual⟩ := actual_firstExtractedErrors_local_bound (α := α) M H hH
    Wslot aslot bslot Mcap εremove lo hi εchild a b Mslot εmask hMslot hεmask haPlain haUpper hbPlain
    L hL ha hWs hW hbslot hMcap hεchild hε hbeta hbetaTop N lower upper a0 θsource
    hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
    hεsrc hδsrc hθsrc hBcap hξ Sbad hbad (9/500) cost hsigma hξsmall hcost rfl
    Avol Dscale Pmask qmoving εgeo hεgeo hbudget
  refine ⟨Uprofile,Jheight,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hactualZ⟩ := hactual η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cbound,hCbound,?_⟩
  filter_upwards [hactualZ,
    eventually_pool_prime_quarter_lower M H Sbad hbad (9/500) (by norm_num)] with Z hZ hpZ
  refine ⟨hZ.1,?_⟩
  intro Aorig θ w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max
    C D R0 hC hD hCD E B τ t hB hmod K delta reserve asource hK hasource hdelta hreserve haSource
  dsimp only at *
  intro hP hslot family hrad hfamily
  intro hzero1 hzero2 hvolumeCap hmaskCap hR0 hradInv hconductorCap seed hseed hseed0 hseedcap
    profile hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip hcap hMdecl hMwidth hdrop hclip
    hsourceLower Mgeom Mvolume hgeom hplainX₁ hplainX₂ hplainY₁ hplainY₂ hwidth hvolGeom hvolCap hfixed hdef
  let P := primePool M H Sbad (1/2) 1 (Z^((9/500 : ℝ)/3))
  have hprime : ∀ Q∈P, Prime Q := fun Q hQ => (primePool_data M H Sbad hbad _ _ _ Q hQ).1
  have hbadP : ∀ Q∈P, Q∉fixedBadPrimes := fun Q hQ => (primePool_data M H Sbad hbad _ _ _ Q hQ).2
  have hbound (prime : elementPool P) := by
    have hd := elementPool_data P hprime hbadP prime.val prime.property
    have hp : Prime (Ideal.span {prime.val}) := hprime _ hd.2.1
    exact hZ.2 Aorig θ w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
      src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max
      C D R0 hC hD hCD E B τ t hB hmod K delta reserve asource hK hasource hdelta hreserve haSource
      prime hp (by linarith [(hpZ.2 prime prime.property).1]) prime.property
      (by linarith [(hpZ.2 prime prime.property).1]) (hslot prime) (family prime) (hrad prime) (hfamily prime)
      hzero1 hzero2 hvolumeCap hmaskCap hR0 (hradInv prime) (hconductorCap prime) seed hseed hseed0 hseedcap
      profile hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip hcap hMdecl hMwidth hdrop hclip
      hsourceLower Mgeom Mvolume hgeom hplainX₁ hplainX₂ hplainY₁ hplainY₂ hwidth hvolGeom hvolCap hfixed hdef
  have hh := normalized_prime_average_le P hP hprime hbadP _ _ hbound
  convert hh using 1 <;> ring

#print axioms actual_firstExtractedErrors_local_average
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.ActualExtractedErrorAverage -/
