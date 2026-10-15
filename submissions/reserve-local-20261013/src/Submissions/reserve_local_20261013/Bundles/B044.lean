/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B009
import Submissions.reserve_local_20261013.Bundles.B026
import Submissions.reserve_local_20261013.Bundles.B027
import Submissions.reserve_local_20261013.Bundles.B029
import Submissions.reserve_local_20261013.Bundles.B031
import Submissions.reserve_local_20261013.Bundles.B035
import Submissions.reserve_local_20261013.Bundles.B040
import Submissions.reserve_local_20261013.Bundles.B041
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentMono
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceSlots

/- BEGIN ORIGINAL MODULE Analytic.JointPopulation ; sha256 7d456101c2ea873aa9b344ceaf714d36a8f0952e17ffa982edb6f912c2069385 -/
section


/-! The full joint arithmetic population is counted once over (w,Rmiss).
The finite set W can be the actual raw zero-bin set furnished by density. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open CanonicalQuadraticSieve IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

theorem joint_population_count (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (u : Oˣ) (W : Finset O) (S : Finset JointReconstructionLabel),
      (∀ w ∈ W, w ≠ 0) →
      (∀ v ∈ S, Supported v.C₁ ∧ Supported v.D₁ ∧ Supported v.C₂ ∧ Supported v.D₂) →
      (∀ v ∈ S, primeSupport v.C₁ = primeSupport v.D₁ ∧
        primeSupport v.C₂ = primeSupport v.D₂) →
      (∀ v ∈ S, Squarefree v.L ∧ v.L ∣ v.C₂ ∧ v.L ∣ v.D₂) →
      (∀ v ∈ S, v.row u ∈ W) →
      ∀ X₁ Y₁ X₂ Y₂ Yw Yr : ℝ,
      0 < X₁ → 0 < Y₁ → 0 < X₂ → 0 < Y₂ → 0 ≤ Yw → 0 ≤ Yr →
      (∀ v ∈ S, (Ideal.absNorm v.C₁ : ℝ) ≤ X₁ ∧
        (Ideal.absNorm v.D₁ : ℝ) ≤ Y₁ ∧
        (Ideal.absNorm v.C₂ : ℝ) ≤ X₂ ∧ (Ideal.absNorm v.D₂ : ℝ) ≤ Y₂) →
      (∀ w ∈ W, (Ideal.absNorm (Ideal.span {w}) : ℝ) ≤ Yw) →
      (∀ v ∈ S, (Ideal.absNorm (jointMissingRadical v.C₁ (v.row u)) : ℝ) ≤ Yr) →
      (S.card : ℝ) ≤ K * W.card * Yr * X₁^a * Y₁^a * X₂^a * Y₂^a * (Yr*Yw)^(5*ε) := by
  obtain ⟨K, hK, hfiber⟩ := joint_reconstruction_fiber_count a ε ha hε
  refine ⟨128*K, by positivity, ?_⟩
  intro u W S hW hsup heq hproj hrow X₁ Y₁ X₂ Y₂ Yw Yr hX₁ hY₁ hX₂ hY₂ hYw hYr hnorm hNw hNr
  let missing := fun v : JointReconstructionLabel => jointMissingRadical v.C₁ (v.row u)
  let Rset := S.image missing
  let code := fun v : JointReconstructionLabel => (v.row u, missing v)
  let B : ℝ := K * X₁^a * Y₁^a * X₂^a * Y₂^a * (Yr*Yw)^(5*ε)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hR0 : ∀ R ∈ Rset, R ≠ 0 := by
    intro R hR
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hR
    exact jointMissingRadical_ne_zero _ _
  have hNR : ∀ R ∈ Rset, (Ideal.absNorm R : ℝ) ≤ Yr := by
    intro R hR
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hR
    exact hNr v hv
  have hRcount := joint_missing_radical_count Rset Yr hYr hR0 hNR
  have hcode : ∀ v ∈ S, code v ∈ W ×ˢ Rset := by
    intro v hv
    exact Finset.mem_product.mpr ⟨hrow v hv, Finset.mem_image_of_mem _ hv⟩
  have hcount (p : O × Ideal O) (hp : p ∈ W ×ˢ Rset) :
      ((S.filter (fun v => code v = p)).card : ℝ) ≤ B := by
    have hpw := (Finset.mem_product.mp hp).1
    have hpr := (Finset.mem_product.mp hp).2
    have hvrow (v : JointReconstructionLabel) (hv : v ∈ S.filter (fun v => code v = p)) :
        v.row u = p.1 ∧ jointMissingRadical v.C₁ p.1 = p.2 := by
      have he := (Finset.mem_filter.mp hv).2
      have hew := congrArg Prod.fst he
      have her := congrArg Prod.snd he
      change v.row u = p.1 at hew
      change jointMissingRadical v.C₁ (v.row u) = p.2 at her
      exact ⟨hew, hew ▸ her⟩
    have hh := hfiber u p.1 (hW _ hpw) p.2 (hR0 _ hpr)
      (S.filter (fun v => code v = p))
      (fun v hv => hsup v (Finset.mem_filter.mp hv).1)
      (fun v hv => heq v (Finset.mem_filter.mp hv).1)
      (fun v hv => hproj v (Finset.mem_filter.mp hv).1) hvrow
      X₁ Y₁ X₂ Y₂ hX₁ hY₁ hX₂ hY₂
      (fun v hv => hnorm v (Finset.mem_filter.mp hv).1)
    apply hh.trans
    have hn : (Ideal.absNorm (p.2 * Ideal.span {p.1}) : ℝ) ≤ Yr * Yw := by
      rw [map_mul, Nat.cast_mul]
      exact mul_le_mul (hNR _ hpr) (hNw _ hpw) (Nat.cast_nonneg _) hYr
    dsimp only [B]
    gcongr
  calc
    (S.card : ℝ) = ∑ p ∈ W ×ˢ Rset, ((S.filter (fun v => code v = p)).card : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_fiberwise hcode
    _ ≤ ∑ _p ∈ W ×ˢ Rset, B := Finset.sum_le_sum hcount
    _ = (W.card : ℝ) * Rset.card * B := by simp [Finset.card_product]
    _ ≤ (W.card : ℝ) * (128 * Yr) * B := by gcongr
    _ = _ := by dsimp [B]; ring

#print axioms joint_population_count
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointPopulation -/

/- BEGIN ORIGINAL MODULE Analytic.JointRelativeDictionary ; sha256 d0443e1ae6db4f38a151197a090d9987c56834a547370f06edbcc177b130a062 -/
section



/-! Fixed finite translates of the full first/second ray dictionary. These
include the relative characters used by actual prime slots, without adding
arithmetic labels or live inducing characters to the density family. -/

set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeRowClosure HeckeInverseAmplification HeckeDetectorZeros HeckeFiniteDeletion
open CenteredExceptionalProfile CenteredMomentFixedRayInducingTransport
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open ProbeHighRowFamily LocalMoment ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

abbrev JointRelativeLabel (η : Character) (SlotLabel : Type*) := JointParentLabel η × SlotLabel

def jointRelativeParent {SlotLabel : Type*} (η : Character) (ν : SlotLabel → Character)
    (label : JointRelativeLabel η SlotLabel) : Character := label.1.val.product (ν label.2)

theorem jointRelativeParent_fixedQ {SlotLabel : Type*} (η : Character) (ν : SlotLabel → Character)
    (Q : Ideal O) (hQη : Q ≤ η.modulus) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hQν : ∀ j, Q ≤ (ν j).modulus) (label : JointRelativeLabel η SlotLabel) :
    Q ≤ (jointRelativeParent η ν label).modulus :=
  le_inf (jointParentDictionary_fixedQ η Q hQη hQ72 label.1) (hQν label.2)

theorem jointRelativeParent_inducing_iff {SlotLabel : Type*} (η : Character) (ν : SlotLabel → Character)
    (Q : Ideal O) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQν : ∀ j, Q ≤ (ν j).modulus)
    (label : JointRelativeLabel η SlotLabel) (w : O) (hw : w ≠ 0) :
    FixedInducingRow (jointRelativeParent η ν label) Q fixedBadMask 1 w ↔
      FixedInducingRow η Q fixedBadMask 1 w :=
  (fixedInducingRow_product_iff label.1.val (ν label.2) Q fixedBadMask 1 w
    (hQν label.2) fixedBadMask_ne_zero one_ne_zero hw
    (dvd_mul_right _ _) (dvd_mul_left _ _)).trans
      (jointParentDictionary_inducing_iff η label.1 Q hQ72 w hw)

def jointRelativeNaturalFamily {SlotLabel : Type*} (η : Character) (ν : SlotLabel → Character)
    (w : NonzeroElement) : JointRelativeLabel η SlotLabel → Character :=
  fun label => (naturalRow (jointRelativeParent η ν label) w.val w.property).character

theorem jointRelativeNatural_nonprincipal {SlotLabel : Type*} (η : Character) (ν : SlotLabel → Character)
    (Q : Ideal O) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQν : ∀ j, Q ≤ (ν j).modulus)
    (w : NonzeroElement) (hex : ¬FixedInducingRow η Q fixedBadMask 1 w.val) :
    ∀ label : JointRelativeLabel η SlotLabel, (jointRelativeNaturalFamily η ν w label).residue ≠ 1 := by
  intro label
  apply CenteredMomentNonprincipalGate.actual_row_nonprincipal (jointRelativeParent η ν label)
    (jointRelativeNaturalFamily η ν w label) Q fixedBadMask 1 w.val
  · intro n
    simpa only [jointRelativeNaturalFamily, one_mul] using
      (naturalRow (jointRelativeParent η ν label) w.val w.property).element n
  · exact fun h => hex ((jointRelativeParent_inducing_iff η ν Q hQ72 hQν label w.val w.property).mp h)

lemma jointRelativeNatural_momentData_mask {SlotLabel : Type*} (η : Character) (ν : SlotLabel → Character)
    (w : NonzeroElement) (label : JointRelativeLabel η SlotLabel) (I : Ideal O) :
    idealCoeff (jointRelativeNaturalFamily η ν w label) I =
      if IsCoprime I (jointRelativeNaturalFamily η ν w label).modulus then
        idealCoeff ((momentData (jointRelativeParent η ν label)).character w) I else 0 := by
  calc
    _ = if IsCoprime I (jointRelativeNaturalFamily η ν w label).modulus then
      idealCoeff (jointRelativeNaturalFamily η ν w label) I else 0 := idealCoeff_source_mask _ I
    _ = _ := by
      dsimp only [jointRelativeNaturalFamily]
      rw [natural_momentData_coeff_nonzero (jointRelativeParent η ν label) w
        (naturalRow (jointRelativeParent η ν label) w.val w.property) I]

theorem jointRelativeMoment_nonprincipal {SlotLabel : Type*} (η : Character) (ν : SlotLabel → Character)
    (Q : Ideal O) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQν : ∀ j, Q ≤ (ν j).modulus)
    (w : NonzeroElement) (hex : ¬FixedInducingRow η Q fixedBadMask 1 w.val) :
    ∀ label : JointRelativeLabel η SlotLabel,
      ((momentData (jointRelativeParent η ν label)).character w).residue ≠ 1 := by
  intro label hp
  exact jointRelativeNatural_nonprincipal η ν Q hQ72 hQν w hex label
    ((principal_iff_of_mask _ _ (jointRelativeNatural_momentData_mask η ν w label)).mpr hp)

/-- Multiplication by each fixed translate is an exact all-ideal identity,
including the arithmetic zeros and the retained canceled-prime puncture. -/
theorem jointRelative_canceled_coeff {SlotLabel : Type*} (η : Character) (ν : SlotLabel → Character)
    (w : NonzeroElement) (label : JointRelativeLabel η SlotLabel)
    (N : NaturalRow label.1.val w.val) (R : Ideal O) (hR : R ≠ 0) (I : Ideal O) :
    idealCoeff ((excluded N.character R).product (ν label.2)) I =
      idealCoeff (excluded (jointRelativeNaturalFamily η ν w label) R) I := by
  rw [idealCoeff_product, excluded_ideal N.character R hR I,
    excluded_ideal (jointRelativeNaturalFamily η ν w label) R hR I]
  split_ifs with hc
  · rw [N.ideal]
    dsimp only [jointRelativeNaturalFamily]
    rw [NaturalRow.ideal, jointRelativeParent, idealCoeff_product]
    ring
  · simp only [zero_mul]

def jointRelativeSourceFamily {SlotLabel : Type*} (η : Character) (ν : SlotLabel → Character)
    (w : NonzeroElement) (R : JointRelativeLabel η SlotLabel → Ideal O) :
    JointRelativeLabel η SlotLabel → Character :=
  fun label => (excluded (jointNaturalFamily η w label.1) (R label)).product (ν label.2)

lemma jointRelativeSource_canceled_mask {SlotLabel : Type*} (η : Character) (ν : SlotLabel → Character)
    (w : NonzeroElement) (R : JointRelativeLabel η SlotLabel → Ideal O)
    (hR : ∀ label, R label ≠ 0) (label : JointRelativeLabel η SlotLabel) (I : Ideal O) :
    idealCoeff (jointRelativeSourceFamily η ν w R label) I =
      if IsCoprime I (jointRelativeSourceFamily η ν w R label).modulus then
        idealCoeff (excluded (jointRelativeNaturalFamily η ν w label) (R label)) I else 0 := by
  calc
    _ = if IsCoprime I (jointRelativeSourceFamily η ν w R label).modulus then
      idealCoeff (jointRelativeSourceFamily η ν w R label) I else 0 := idealCoeff_source_mask _ I
    _ = _ := by
      dsimp only [jointRelativeSourceFamily, jointNaturalFamily]
      rw [jointRelative_canceled_coeff η ν w label
        (naturalRow label.1.val w.val w.property) (R label) (hR label) I]

theorem jointRelativeSource_nonprincipal {SlotLabel : Type*} (η : Character) (ν : SlotLabel → Character)
    (Q : Ideal O) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQν : ∀ j, Q ≤ (ν j).modulus)
    (w : NonzeroElement) (hex : ¬FixedInducingRow η Q fixedBadMask 1 w.val)
    (R : JointRelativeLabel η SlotLabel → Ideal O) (hR : ∀ label, R label ≠ 0) :
    ∀ label, (jointRelativeSourceFamily η ν w R label).residue ≠ 1 := by
  intro label hp
  exact excluded_nonprincipal _ _ (jointRelativeNatural_nonprincipal η ν Q hQ72 hQν w hex label)
    ((principal_iff_of_mask _ _ (jointRelativeSource_canceled_mask η ν w R hR label)).mp hp)

/-- The full family of literal translated source characters has precisely
the same zero maximum as the fixed moment dictionary, at every height. -/
theorem jointRelativeSource_zeroMaximum {SlotLabel : Type*} [Fintype SlotLabel]
    (η : Character) (ν : SlotLabel → Character)
    (Q : Ideal O) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQν : ∀ j, Q ≤ (ν j).modulus)
    (w : NonzeroElement) (hex : ¬FixedInducingRow η Q fixedBadMask 1 w.val)
    (R : JointRelativeLabel η SlotLabel → Ideal O) (hR : ∀ label, R label ≠ 0) (T : ℝ) :
    zeroMaximum (jointRelativeSourceFamily η ν w R)
      (jointRelativeSource_nonprincipal η ν Q hQ72 hQν w hex R hR) T =
      zeroMaximum (fun label => (momentData (jointRelativeParent η ν label)).character w)
        (jointRelativeMoment_nonprincipal η ν Q hQ72 hQν w hex) T := by
  have hnp := jointRelativeNatural_nonprincipal η ν Q hQ72 hQν w hex
  exact (zeroMaximum_eq_of_mask _ _ _ _ T (jointRelativeSource_canceled_mask η ν w R hR)).trans
    ((excluded_zeroMaximum (jointRelativeNaturalFamily η ν w) R hnp T).trans
      (zeroMaximum_eq_of_mask _ _ _ _ T (jointRelativeNatural_momentData_mask η ν w)))

/-- A complete bin for the literal relative-slot source family. -/
def jointRelativeSourceZeroBin {SlotLabel : Type*} [Fintype SlotLabel]
    (η : Character) (ν : SlotLabel → Character)
    (Q : Ideal O) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQν : ∀ j, Q ≤ (ν j).modulus)
    (R : JointRelativeLabel η SlotLabel → Ideal O) (hR : ∀ label, R label ≠ 0)
    (a b T : ℝ) (w : NonzeroElement) : Prop :=
  ∃ hex : ¬FixedInducingRow η Q fixedBadMask 1 w.val,
    a ≤ zeroMaximum (jointRelativeSourceFamily η ν w R)
      (jointRelativeSource_nonprincipal η ν Q hQ72 hQν w hex R hR) T ∧
    zeroMaximum (jointRelativeSourceFamily η ν w R)
      (jointRelativeSource_nonprincipal η ν Q hQ72 hQν w hex R hR) T ≤ b

theorem jointRelativeSourceZeroBin_iff {SlotLabel : Type*} [Fintype SlotLabel]
    (η : Character) (ν : SlotLabel → Character)
    (Q : Ideal O) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQν : ∀ j, Q ≤ (ν j).modulus)
    (R : JointRelativeLabel η SlotLabel → Ideal O) (hR : ∀ label, R label ≠ 0)
    (a b T : ℝ) (w : NonzeroElement) :
    jointRelativeSourceZeroBin η ν Q hQ72 hQν R hR a b T w ↔
      (¬FixedInducingRow η Q fixedBadMask 1 w.val) ∧
        rawZeroBin (fun label => momentData (jointRelativeParent η ν label)) a b T w := by
  constructor
  · rintro ⟨hex, hlo, hhi⟩
    rw [jointRelativeSource_zeroMaximum η ν Q hQ72 hQν w hex R hR T] at hlo hhi
    exact ⟨hex, jointRelativeMoment_nonprincipal η ν Q hQ72 hQν w hex, hlo, hhi⟩
  · rintro ⟨hex, hn, hlo, hhi⟩
    refine ⟨hex, ?_, ?_⟩ <;> rw [jointRelativeSource_zeroMaximum η ν Q hQ72 hQν w hex R hR T]
    · exact hlo
    · exact hhi

/-- Density for the finite union of all fixed relative-slot translates.
The punctures may vary with the arithmetic row and dictionary label. The
constant and polynomial height exponent precede all these choices. -/
theorem actual_joint_relative_density {SlotLabel : Type*} [Fintype SlotLabel]
    (η : Character) (ν : SlotLabel → Character) (Q : Ideal O) [NeZero Q]
    (hQtop : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hQη : Q ≤ η.modulus) (hQν : ∀ j, Q ≤ (ν j).modulus)
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (hβupper : HeckeZeroSupremum.beta ≤ 7/8)
    (loss : ℝ) (hlosspos : 0 < loss) :
    ∃ (A : ℕ) (K : ℝ), 0 < K ∧
      (∀ Y : ℝ, 1 ≤ Y → ∀ p : DensityWindow, ∀ F : Finset FreeRow,
        (∀ u ∈ F, rowNorm u ≤ Y ∧
          ∃ (R : JointRelativeLabel η SlotLabel → Ideal O) (hR : ∀ label, R label ≠ 0),
          jointRelativeSourceZeroBin η ν Q hQ72 hQν R hR
            p.lower p.upper p.height ⟨u.val, u.property.1⟩) →
        (F.card : ℝ) ≤ K*(1+|p.height|)^A*Y^(unmarkedDensity (2*p.lower-1)+loss)) ∧
      (∀ p : DensityWindow, ∀ Y : ℝ, 0 < Y →
        ∀ F : Finset ProbePhysical.NonzeroFrequency,
        (∀ u ∈ F, rawFrequencyNorm u ≤ Y ∧
          ∃ (R : JointRelativeLabel η SlotLabel → Ideal O) (hR : ∀ label, R label ≠ 0),
          jointRelativeSourceZeroBin η ν Q hQ72 hQν R hR p.lower p.upper p.height u) →
        (F.card : ℝ) ≤ K*(1+|p.height|)^A*Y^(unmarkedDensity (2*p.lower-1)+loss)) := by
  obtain ⟨A, K, hK, hfree, hraw⟩ := actual_momentData_density
    (jointRelativeParent η ν) Q hQtop hQ72
    (jointRelativeParent_fixedQ η ν Q hQη hQ72 hQν) hβ M H hH S
    φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB hβupper loss hlosspos
  refine ⟨A, K, hK, ?_, ?_⟩
  · intro Y hY p F hF
    apply hfree Y hY p F
    intro u hu
    obtain ⟨hnorm, R, hR, hbin⟩ := hF u hu
    exact ⟨hnorm, ((jointRelativeSourceZeroBin_iff η ν Q hQ72 hQν R hR _ _ _ _).mp hbin).2⟩
  · intro p Y hY F hF
    apply hraw p Y hY F
    intro u hu
    obtain ⟨hnorm, R, hR, hbin⟩ := hF u hu
    exact ⟨hnorm, ((jointRelativeSourceZeroBin_iff η ν Q hQ72 hQν R hR _ _ _ _).mp hbin).2⟩

lemma jointRelative_selected_mask {SlotLabel : Type*} (η : Character) (ν : SlotLabel → Character)
    (w : NonzeroElement) (label : JointRelativeLabel η SlotLabel)
    (N : NaturalRow label.1.val w.val) (R : Ideal O) (hR : R ≠ 0) (I : Ideal O) :
    idealCoeff ((excluded N.character R).product (ν label.2)) I =
      if IsCoprime I ((excluded N.character R).product (ν label.2)).modulus then
        idealCoeff (excluded (jointRelativeNaturalFamily η ν w label) R) I else 0 := by
  calc
    _ = if IsCoprime I ((excluded N.character R).product (ν label.2)).modulus then
      idealCoeff ((excluded N.character R).product (ν label.2)) I else 0 := idealCoeff_source_mask _ I
    _ = _ := by rw [jointRelative_canceled_coeff η ν w label N R hR I]

theorem jointRelative_selected_nonprincipal {SlotLabel : Type*} (η : Character) (ν : SlotLabel → Character)
    (Q : Ideal O) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQν : ∀ j, Q ≤ (ν j).modulus)
    (w : NonzeroElement) (hex : ¬FixedInducingRow η Q fixedBadMask 1 w.val)
    (label : JointRelativeLabel η SlotLabel) (N : NaturalRow label.1.val w.val)
    (R : Ideal O) (hR : R ≠ 0) : ((excluded N.character R).product (ν label.2)).residue ≠ 1 := by
  intro hp
  exact excluded_nonprincipal _ _ (jointRelativeNatural_nonprincipal η ν Q hQ72 hQν w hex label)
    ((principal_iff_of_mask _ _ (jointRelative_selected_mask η ν w label N R hR)).mp hp)

/-- Every literal relative translate of any natural representative has the
same positive-real zeros as its fixed momentData member. -/
theorem jointRelative_selected_positive_zeros {SlotLabel : Type*} (η : Character) (ν : SlotLabel → Character)
    (Q : Ideal O) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQν : ∀ j, Q ≤ (ν j).modulus)
    (w : NonzeroElement) (hex : ¬FixedInducingRow η Q fixedBadMask 1 w.val)
    (label : JointRelativeLabel η SlotLabel) (N : NaturalRow label.1.val w.val)
    (R : Ideal O) (hR : R ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    LFunction ((excluded N.character R).product (ν label.2)) s = 0 ↔
      LFunction ((momentData (jointRelativeParent η ν label)).character w) s = 0 := by
  have hn := jointRelativeNatural_nonprincipal η ν Q hQ72 hQν w hex label
  exact (positive_zeros_eq_of_mask _ _
    (jointRelative_selected_nonprincipal η ν Q hQ72 hQν w hex label N R hR)
    (jointRelative_selected_mask η ν w label N R hR) hs).trans
      ((excluded_positive_zeros _ R hn hs).trans
        (positive_zeros_eq_of_mask _ _ hn (jointRelativeNatural_momentData_mask η ν w label) hs))

/-- Any high selected relative slot enters the complete fixed dictionary
bin. This is the high-some counterpart to a common low-all family bound. -/
theorem jointRelative_selected_mem_rawZeroBin {SlotLabel : Type*} [Fintype SlotLabel]
    (η : Character) (ν : SlotLabel → Character)
    (Q : Ideal O) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQν : ∀ j, Q ≤ (ν j).modulus)
    (w : NonzeroElement) (hex : ¬FixedInducingRow η Q fixedBadMask 1 w.val)
    (label : JointRelativeLabel η SlotLabel) (N : NaturalRow label.1.val w.val)
    (R : Ideal O) (hR : R ≠ 0) (a T : ℝ)
    (hβupper : HeckeZeroSupremum.beta ≤ 7/8)
    (hhigh : a ≤ zeroMaximum (fun _ : Unit => (excluded N.character R).product (ν label.2))
      (fun _ => jointRelative_selected_nonprincipal η ν Q hQ72 hQν w hex label N R hR) T) :
    rawZeroBin (fun label => momentData (jointRelativeParent η ν label)) a (7/8) T w := by
  refine ⟨jointRelativeMoment_nonprincipal η ν Q hQ72 hQν w hex, ?_, ?_⟩
  · apply hhigh.trans
    apply zeroMaximum_le_of_zero_inclusion
    intro _
    exact ⟨label, fun s hs hz => (jointRelative_selected_positive_zeros η ν Q hQ72 hQν
      w hex label N R hR hs).mp hz⟩
  · exact zeroMaximum_le_seven_eighths _ _ T hβupper

lemma coefficient_equality_mask (χ ψ : Character)
    (hc : ∀ I : Ideal O, idealCoeff χ I = idealCoeff ψ I) (I : Ideal O) :
    idealCoeff χ I = if IsCoprime I χ.modulus then idealCoeff ψ I else 0 := by
  calc
    _ = if IsCoprime I χ.modulus then idealCoeff χ I else 0 := idealCoeff_source_mask χ I
    _ = _ := by rw [hc I]

lemma coefficient_equality_nonprincipal (χ ψ : Character)
    (hc : ∀ I : Ideal O, idealCoeff χ I = idealCoeff ψ I) (hψ : ψ.residue ≠ 1) : χ.residue ≠ 1 :=
  fun hχ => hψ ((principal_iff_of_mask χ ψ (coefficient_equality_mask χ ψ hc)).mp hχ)

lemma coefficient_equality_positive_zeros (χ ψ : Character)
    (hc : ∀ I : Ideal O, idealCoeff χ I = idealCoeff ψ I) (hψ : ψ.residue ≠ 1)
    {s : ℂ} (hs : 0 < s.re) : LFunction χ s = 0 ↔ LFunction ψ s = 0 :=
  positive_zeros_eq_of_mask χ ψ (coefficient_equality_nonprincipal χ ψ hc hψ)
    (coefficient_equality_mask χ ψ hc) hs

section ActualRelativeSlots
open CenteredMomentNaturalFixedRaySource HeckePrimeRay
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The single fixed translate tuple contains the plain character and every
ray sector of each fixed relative slot. It is independent of arithmetic rows. -/
def relativeSlotTranslate {Slot : Type*} (η₀ : Slot → Character) :
    Option (Slot × RayQuotient.Characters M H) → Character
  | none => CenteredMomentNonprincipalGate.unitCharacter
  | some (j, θ) => relativeCharacter M H hH (η₀ j) θ

theorem relativeSlotTranslate_fixedQ {Slot : Type*} (η₀ : Slot → Character)
    (Q : Ideal O) (hQM : Q ≤ M) (hQη₀ : ∀ j, Q ≤ (η₀ j).modulus) :
    ∀ j, Q ≤ (relativeSlotTranslate M H hH η₀ j).modulus := by
  intro j
  rcases j with _ | ⟨j, θ⟩
  · exact le_top
  · exact relativeCharacter_fixedQ M H hH (η₀ j) θ Q hQM (hQη₀ j)

/-- The actual ray-sector character of a relative prime slot has the exact
coefficients of its fixed translated natural row with the original puncture. -/
theorem jointRelative_ray_sector_coeff {Slot : Type*}
    (η : Character) (η₀ : Slot → Character) (w : NonzeroElement)
    (τ : JointParentLabel η) (N : NaturalRow τ.val w.val)
    (j : Slot) (θ : RayQuotient.Characters M H) (R : Ideal O) (hR : R ≠ 0) (I : Ideal O) :
    idealCoeff (twistedFamily M H hH ((excluded N.character R).product (η₀ j).inverse) θ) I =
      idealCoeff (excluded (jointRelativeNaturalFamily η (relativeSlotTranslate M H hH η₀)
        w (τ, some (j, θ))) R) I := by
  have he : idealCoeff (twistedFamily M H hH ((excluded N.character R).product (η₀ j).inverse) θ) I =
      idealCoeff ((excluded N.character R).product (relativeCharacter M H hH (η₀ j) θ)) I := by
    simp only [twistedFamily, relativeCharacter, idealCoeff_product]
    ring
  exact he.trans (jointRelative_canceled_coeff η (relativeSlotTranslate M H hH η₀)
    w (τ, some (j, θ)) N R hR I)

/-- The `none` member is the literal plain row, on every ideal including zero. -/
theorem jointRelative_plain_coeff {Slot : Type*}
    (η : Character) (η₀ : Slot → Character) (w : NonzeroElement)
    (τ : JointParentLabel η) (N : NaturalRow τ.val w.val)
    (R : Ideal O) (hR : R ≠ 0) (I : Ideal O) :
    idealCoeff (excluded N.character R) I =
      idealCoeff (excluded (jointRelativeNaturalFamily η (relativeSlotTranslate M H hH η₀)
        w (τ, none)) R) I := by
  have he := jointRelative_canceled_coeff η (relativeSlotTranslate M H hH η₀)
    w (τ, none) N R hR I
  rw [idealCoeff_product] at he
  by_cases hI : I = 0
  · subst I
    simp only [map_zero]
  · simpa only [relativeSlotTranslate, CenteredMomentNonprincipalGate.unitCharacter_ideal I hI, mul_one] using he
/-- Nonprincipality for the literal ray-sector family follows from the
same base eligibility gate used for plain rows. -/
theorem jointRelative_ray_nonprincipal {Slot : Type*}
    (η : Character) (η₀ : Slot → Character) (Q : Ideal O)
    (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQM : Q ≤ M) (hQη₀ : ∀ j, Q ≤ (η₀ j).modulus)
    (w : NonzeroElement) (hex : ¬FixedInducingRow η Q fixedBadMask 1 w.val)
    (τ : JointParentLabel η) (N : NaturalRow τ.val w.val)
    (j : Slot) (R : Ideal O) (hR : R ≠ 0) :
    ∀ θ, (twistedFamily M H hH ((excluded N.character R).product (η₀ j).inverse) θ).residue ≠ 1 := by
  intro θ
  exact coefficient_equality_nonprincipal _ _
    (jointRelative_ray_sector_coeff M H hH η η₀ w τ N j θ R hR)
    (excluded_nonprincipal _ _ (jointRelativeNatural_nonprincipal η
      (relativeSlotTranslate M H hH η₀) Q hQ72
      (relativeSlotTranslate_fixedQ M H hH η₀ Q hQM hQη₀) w hex (τ, some (j, θ))))

/-- A common upper bin for the fixed union controls each actual relative
prime family; conversely, any high ray family is covered by the union. -/
theorem jointRelative_ray_zeroMaximum_le {Slot : Type*} [Fintype Slot]
    (η : Character) (η₀ : Slot → Character) (Q : Ideal O)
    (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQM : Q ≤ M) (hQη₀ : ∀ j, Q ≤ (η₀ j).modulus)
    (w : NonzeroElement) (hex : ¬FixedInducingRow η Q fixedBadMask 1 w.val)
    (τ : JointParentLabel η) (N : NaturalRow τ.val w.val)
    (j : Slot) (R : Ideal O) (hR : R ≠ 0) (T : ℝ) :
    zeroMaximum (twistedFamily M H hH ((excluded N.character R).product (η₀ j).inverse))
      (jointRelative_ray_nonprincipal M H hH η η₀ Q hQ72 hQM hQη₀ w hex τ N j R hR) T ≤
      zeroMaximum (fun label => (momentData (jointRelativeParent η
        (relativeSlotTranslate M H hH η₀) label)).character w)
        (jointRelativeMoment_nonprincipal η (relativeSlotTranslate M H hH η₀) Q hQ72
          (relativeSlotTranslate_fixedQ M H hH η₀ Q hQM hQη₀) w hex) T := by
  apply zeroMaximum_le_of_zero_inclusion
  intro θ
  refine ⟨(τ, some (j, θ)), ?_⟩
  intro s hs hz
  have hc (I : Ideal O) :
      idealCoeff (twistedFamily M H hH ((excluded N.character R).product (η₀ j).inverse) θ) I =
        idealCoeff ((excluded N.character R).product (relativeCharacter M H hH (η₀ j) θ)) I := by
    simp only [twistedFamily, relativeCharacter, idealCoeff_product]
    ring
  have hνQ := relativeSlotTranslate_fixedQ M H hH η₀ Q hQM hQη₀
  have hn := jointRelative_selected_nonprincipal η (relativeSlotTranslate M H hH η₀)
    Q hQ72 hνQ w hex (τ, some (j, θ)) N R hR
  have hz' := (coefficient_equality_positive_zeros _ _ hc hn hs).mp hz
  exact (jointRelative_selected_positive_zeros η (relativeSlotTranslate M H hH η₀)
    Q hQ72 hνQ w hex (τ, some (j, θ)) N R hR hs).mp hz'

end ActualRelativeSlots

#print axioms jointRelative_canceled_coeff
#print axioms jointRelativeSourceZeroBin_iff
#print axioms jointRelative_selected_positive_zeros
#print axioms jointRelative_selected_mem_rawZeroBin
#print axioms actual_joint_relative_density
#print axioms jointRelative_ray_sector_coeff
#print axioms jointRelative_plain_coeff
#print axioms jointRelative_ray_zeroMaximum_le
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointRelativeDictionary -/

/- BEGIN ORIGINAL MODULE Analytic.JointRowGeometry ; sha256 4fe0c98e4d828124651aa26de9cdf9c769e048b26ea95a82cfc15c4037c10d67 -/
section



/-! Actual reconstructed-row geometry.  The frequency gate is the nonzero
retained Fourier weight, not membership in its larger integer-ceiling disk.
The nominal radius uses the literal residual source cap H / N(C₁). -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.Local44.Analytic
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CenteredMomentCanonicalFirst CenteredMomentActive
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalLedger
open CenteredMomentCompleteCommon CenteredMomentRankinRadical
open CenteredMomentSectorLocalization CenteredMomentSecondSectorRetained
open IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

lemma joint_normValue_unit (u : Oˣ) : normValue (u : O) = 1 := by
  simp only [normValue, Ideal.span_singleton_eq_top.mpr u.isUnit,
    Ideal.absNorm_top, Nat.cast_one]

theorem jointLeftRow_norm (C₁ D₁ C₂ D₂ : Ideal O)
    (E : Finset (CommonIndex C₁ D₁)) (u : Oˣ)
    (U : Finset (CommonIndex C₂ D₂)) (h : O) :
    normValue (jointLeftRow C₁ D₁ C₂ D₂ E u U h) =
      normValue (primeSubsetGenerator (fun P : CommonIndex C₁ D₁ => P.val) E) *
      normValue (leftEffectiveFactor C₁ D₁) *
      normValue (commonFrequencyGenerator C₂ D₂ * nonunitFrequencyGenerator C₂ D₂ U * h) := by
  simp only [jointLeftRow, normValue_mul, joint_normValue_unit, mul_one]

/-- The enlarged second ball used by `commonEnergy_enlarged_second_blocks`. -/
def jointSecondBall (Z A c d R E M a ω : ℝ) : ℝ :=
  Z ^ (2*A-c-d+R+E-M+max (d-c) 0+6*a+ω)

/-- Nominal Fourier radius from the actual residual source cap. -/
def jointSecondNominal (C : Ideal O) (H Z A c d R E M a ω : ℝ) : ℝ :=
  (H/(C.absNorm : ℝ))^2 / jointSecondBall Z A c d R E M a ω

/-- All first and second labels remain live. The only size premise is the
original source cap H, before the exact common-ideal division. -/
theorem actual_joint_row_geometry (C₁ D₁ C₂ D₂ : Ideal O)
    (E : Finset (CommonIndex C₁ D₁)) (u : Oˣ)
    (U : Finset (CommonIndex C₂ D₂)) (h : O)
    (Z A c d R e M a ω Lc H εH ξ : ℝ) (hZ : 1 < Z)
    (hH₀ : 0 ≤ H) (hH : H ≤ Z^(A+εH))
    (hC : (C₁.absNorm : ℝ) = Z^c)
    (hE : normValue (primeSubsetGenerator (fun P : CommonIndex C₁ D₁ => P.val) E) = Z^e)
    (hF : normValue (leftEffectiveFactor C₁ D₁) = Z^Lc)
    (hret : retainedWeight
      (frequencyRadius (jointSecondNominal C₁ H Z A c d R e M a ω) Z ξ)
      (normValue (commonFrequencyGenerator C₂ D₂ * nonunitFrequencyGenerator C₂ D₂ U * h)) ≠ 0) :
    normValue (jointLeftRow C₁ D₁ C₂ D₂ E u U h) ≤
      4*Z^(M-R-max (c-d) 0+Lc-6*a-ω+2*εH+ξ/2) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hpow : 0 < Z^c := Real.rpow_pos_of_pos hz _
  have hsq : (H/Z^c)^2 ≤ (Z^(A+εH)/Z^c)^2 := by
    apply pow_le_pow_left₀ (div_nonneg hH₀ hpow.le)
    exact div_le_div_of_nonneg_right hH hpow.le
  have hr := (retainedWeight_enclosure _ _ hret).2
  rw [jointLeftRow_norm, hE, hF]
  calc
    _ ≤ Z^e * Z^Lc * (4*frequencyRadius
        (jointSecondNominal C₁ H Z A c d R e M a ω) Z ξ) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    _ ≤ Z^e * Z^Lc * (4*((Z^(A+εH)/Z^c)^2 /
        jointSecondBall Z A c d R e M a ω * Z^(ξ/2))) := by
      unfold frequencyRadius jointSecondNominal
      rw [hC]
      gcongr
      exact Real.rpow_nonneg hz.le _
    _ = _ := by
      unfold jointSecondBall
      rw [← Real.rpow_sub hz, ← Real.rpow_natCast (Z^(A+εH-c)) 2,
        ← Real.rpow_mul hz.le, ← Real.rpow_sub hz]
      simp only [mul_assoc]
      rw [mul_left_comm (Z^Lc) 4, ← mul_assoc, mul_comm (Z^e) 4,
        mul_assoc, ← Real.rpow_add hz, ← Real.rpow_add hz, ← Real.rpow_add hz]
      congr 2
      have hm : max (c-d) 0 - max (d-c) 0 = c-d := by
        rcases le_total c d with hcd | hdc
        · rw [max_eq_right (sub_nonpos.mpr hcd), max_eq_left (sub_nonneg.mpr hcd)]
          ring
        · rw [max_eq_left (sub_nonneg.mpr hdc), max_eq_right (sub_nonpos.mpr hdc)]
          ring
      push_cast
      linarith

/-- Exact logarithmic source labels discharge every norm identity in the
geometric bound. No reconstructed-row size estimate is assumed. -/
theorem actual_joint_row_geometry_log (C₁ D₁ C₂ D₂ : Ideal O)
    (hC₁ : Supported C₁) (E : Finset (CommonIndex C₁ D₁)) (u : Oˣ)
    (U : Finset (CommonIndex C₂ D₂)) (h : O)
    (Z A d R M a ω H εH ξ : ℝ) (hZ : 1 < Z)
    (hH₀ : 0 ≤ H) (hH : H ≤ Z^(A+εH))
    (hret : retainedWeight
      (frequencyRadius (jointSecondNominal C₁ H Z A
        (Real.logb Z (C₁.absNorm : ℝ)) d R
        (Real.logb Z (normValue (primeSubsetGenerator (fun P : CommonIndex C₁ D₁ => P.val) E)))
        M a ω) Z ξ)
      (normValue (commonFrequencyGenerator C₂ D₂ * nonunitFrequencyGenerator C₂ D₂ U * h)) ≠ 0) :
    normValue (jointLeftRow C₁ D₁ C₂ D₂ E u U h) ≤
      4*Z^(M-R-max (Real.logb Z (C₁.absNorm : ℝ)-d) 0+
        Real.logb Z (normValue (leftEffectiveFactor C₁ D₁))-6*a-ω+2*εH+ξ/2) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  apply actual_joint_row_geometry C₁ D₁ C₂ D₂ E u U h Z A
    (Real.logb Z (C₁.absNorm : ℝ)) d R
    (Real.logb Z (normValue (primeSubsetGenerator (fun P : CommonIndex C₁ D₁ => P.val) E)))
    M a ω (Real.logb Z (normValue (leftEffectiveFactor C₁ D₁))) H εH ξ hZ hH₀ hH
  · exact (Real.rpow_logb hz (ne_of_gt hZ) (by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC₁.1))).symm
  · exact (Real.rpow_logb hz (ne_of_gt hZ) (normValue_pos _
      (primeSubsetGenerator_ne_zero _ _))).symm
  · exact (Real.rpow_logb hz (ne_of_gt hZ) (normValue_pos _
      (active_product_pow_ne_zero C₁ D₁ hC₁ _))).symm
  · exact hret

/-- The constant four is absorbed before all common labels and source
parameters. Source and frequency support losses remain explicit in the gate. -/
theorem eventually_actual_joint_row_geometry (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (C₁ D₁ C₂ D₂ : Ideal O) (E : Finset (CommonIndex C₁ D₁)) (u : Oˣ)
      (U : Finset (CommonIndex C₂ D₂)) (h : O)
      (A c d R e M a ω Lc H εH ξ : ℝ),
      0 ≤ H → H ≤ Z^(A+εH) → (C₁.absNorm : ℝ) = Z^c →
      normValue (primeSubsetGenerator (fun P : CommonIndex C₁ D₁ => P.val) E) = Z^e →
      normValue (leftEffectiveFactor C₁ D₁) = Z^Lc →
      2*εH+ξ/2-ω ≤ ε/2 →
      retainedWeight
        (frequencyRadius (jointSecondNominal C₁ H Z A c d R e M a ω) Z ξ)
        (normValue (commonFrequencyGenerator C₂ D₂ * nonunitFrequencyGenerator C₂ D₂ U * h)) ≠ 0 →
      normValue (jointLeftRow C₁ D₁ C₂ D₂ E u U h) ≤
        Z^(M-R-max (c-d) 0+Lc-6*a+ε) := by
  filter_upwards [(tendsto_rpow_atTop (by linarith : 0 < ε/2)).eventually
    (eventually_ge_atTop (4 : ℝ)), eventually_gt_atTop (1 : ℝ)] with Z h4 hZ
  refine ⟨hZ, ?_⟩
  intro C₁ D₁ C₂ D₂ E u U h A c d R e M a ω Lc H εH ξ hH₀ hH hC hE hF hloss hret
  calc
    _ ≤ 4*Z^(M-R-max (c-d) 0+Lc-6*a-ω+2*εH+ξ/2) :=
      actual_joint_row_geometry C₁ D₁ C₂ D₂ E u U h Z A c d R e M a ω Lc H εH ξ
        hZ hH₀ hH hC hE hF hret
    _ ≤ Z^(ε/2)*Z^(M-R-max (c-d) 0+Lc-6*a-ω+2*εH+ξ/2) := by
      gcongr
    _ = Z^(ε/2+(M-R-max (c-d) 0+Lc-6*a-ω+2*εH+ξ/2)) :=
      (Real.rpow_add (zero_lt_one.trans hZ) _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)

/-- The principal-support restriction saves both the active conductor and
the selected principal mask from the missing-radical size. -/
theorem actual_joint_missing_geometry (C₁ D₁ C₂ D₂ : Ideal O) (hC₁ : Supported C₁)
    (hCD₁ : CompletedGauss.primeSupport C₁ = CompletedGauss.primeSupport D₁)
    (E : Finset (CommonIndex C₁ D₁))
    (hE : E ∈ (principalSupport Finset.univ (leftExponent C₁ D₁)
      (rightExponent C₁ D₁)).powerset)
    (u : Oˣ) (U : Finset (CommonIndex C₂ D₂)) (h : O)
    (hw : jointLeftRow C₁ D₁ C₂ D₂ E u U h ≠ 0)
    (Z p R e R₀ : ℝ) (hZ : 1 < Z)
    (hR : normValue (activeConductor C₁ D₁) = Z^R)
    (he : normValue (primeSubsetGenerator (fun P : CommonIndex C₁ D₁ => P.val) E) = Z^e)
    (hp : ((commonRadical C₁ D₁).absNorm : ℝ) = Z^p)
    (hR₀ : ((canceledIdeal C₁ D₁ 5).absNorm : ℝ) = Z^R₀) :
    ((jointMissingRadical C₁ (jointLeftRow C₁ D₁ C₂ D₂ E u U h)).absNorm : ℝ) ≤
      Z^(p-R-e+R₀) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hb := joint_missing_radical_norm C₁ D₁ C₂ D₂ hC₁ hCD₁ E hE u U h hw
  rw [← joint_canceledIdeal_eq C₁ D₁ hC₁] at hb
  have hb' : ((jointMissingRadical C₁ (jointLeftRow C₁ D₁ C₂ D₂ E u U h)).absNorm : ℝ) *
      normValue (activeConductor C₁ D₁) *
      normValue (primeSubsetGenerator (fun P : CommonIndex C₁ D₁ => P.val) E) ≤
      ((commonRadical C₁ D₁).absNorm : ℝ) * (canceledIdeal C₁ D₁ 5).absNorm := by
    unfold normValue
    exact_mod_cast hb
  rw [hR, he, hp, hR₀] at hb'
  have hd : 0 < Z^R * Z^e := by positivity
  calc
    _ ≤ (Z^p*Z^R₀)/(Z^R*Z^e) := (le_div_iff₀ hd).mpr (by simpa only [mul_assoc] using hb')
    _ = _ := by
      rw [← Real.rpow_add hz, ← Real.rpow_add hz, ← Real.rpow_sub hz]
      congr 1
      ring

/-- Every width here is the logarithm of its literal source ideal norm. -/
theorem actual_joint_missing_geometry_log (C₁ D₁ C₂ D₂ : Ideal O) (hC₁ : Supported C₁)
    (hCD₁ : CompletedGauss.primeSupport C₁ = CompletedGauss.primeSupport D₁)
    (E : Finset (CommonIndex C₁ D₁))
    (hE : E ∈ (principalSupport Finset.univ (leftExponent C₁ D₁)
      (rightExponent C₁ D₁)).powerset)
    (u : Oˣ) (U : Finset (CommonIndex C₂ D₂)) (h : O)
    (hw : jointLeftRow C₁ D₁ C₂ D₂ E u U h ≠ 0)
    (Z : ℝ) (hZ : 1 < Z) :
    ((jointMissingRadical C₁ (jointLeftRow C₁ D₁ C₂ D₂ E u U h)).absNorm : ℝ) ≤
      Z^(Real.logb Z ((commonRadical C₁ D₁).absNorm : ℝ) -
        Real.logb Z (normValue (activeConductor C₁ D₁)) -
        Real.logb Z (normValue (primeSubsetGenerator (fun P : CommonIndex C₁ D₁ => P.val) E)) +
        Real.logb Z ((canceledIdeal C₁ D₁ 5).absNorm : ℝ)) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hcanceled : canceledIdeal C₁ D₁ 5 ≠ 0 := by
    rw [joint_canceledIdeal_eq C₁ D₁ hC₁]
    exact Finset.prod_ne_zero_iff.mpr (fun P _ =>
      (support_prime (Finset.mem_inter.mp P.property).1).ne_zero)
  apply actual_joint_missing_geometry C₁ D₁ C₂ D₂ hC₁ hCD₁ E hE u U h hw Z
    (Real.logb Z ((commonRadical C₁ D₁).absNorm : ℝ))
    (Real.logb Z (normValue (activeConductor C₁ D₁)))
    (Real.logb Z (normValue (primeSubsetGenerator (fun P : CommonIndex C₁ D₁ => P.val) E)))
    (Real.logb Z ((canceledIdeal C₁ D₁ 5).absNorm : ℝ)) hZ
  · exact (Real.rpow_logb hz (ne_of_gt hZ) (normValue_pos _ (finitePrimeModulus_ne_zero _))).symm
  · exact (Real.rpow_logb hz (ne_of_gt hZ) (normValue_pos _ (primeSubsetGenerator_ne_zero _ _))).symm
  · exact (Real.rpow_logb hz (ne_of_gt hZ) (by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (commonRadical_ne_zero _ _)))).symm
  · exact (Real.rpow_logb hz (ne_of_gt hZ) (by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hcanceled))).symm

#print axioms actual_joint_row_geometry
#print axioms actual_joint_row_geometry_log
#print axioms eventually_actual_joint_row_geometry
#print axioms actual_joint_missing_geometry
#print axioms actual_joint_missing_geometry_log
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointRowGeometry -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.CertifiedMoments ; sha256 9d124c3f3492ea2d981fdc689da256c910c548fd4e7614dfbf086347027c88b7 -/
section





namespace OAI.SevenEighths.Cycle25ProbeFinalAssemblyCertifiedBands
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open CenteredMomentEnergyBands ProbeHighRowFamily
open Cycle25ProbeFinalAssembly ProbeFinalAssembly
open Cycle25ProbeDetectorPlainMarkedFineField Cycle25ProbeDetectorPlainUnmarkedField
open CenteredMomentNaturalFixedRaySource Cycle25CenteredMomentNaturalFixedRaySource
theorem weighted_source_moments {D:Cycle25.Weighted.MomentData}(F:WeightedSourceData D)
    (κplain:ℝ)(hk1:κplain≤3/4)(counts:Cycle25ProbeHighRowFamily.CountParameters F.modulus ⊤ D.t)(mesh:ℝ)(hmesh:0< mesh)
    (hfine:∀j,D.ell j ≤ mesh/200)
    (hpositive:weighted_PositiveFineSourceInput F κplain mesh)
    (hzero:∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,∃A:ℝ,0< A ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (weighted_sourceFixedIdeal F) η₀) (1/4) (9/4) weighted_radialSupportUpper
        0 1 2 (D.t/4) U degree control A):
    ∃J:ℝ,0 ≤ J ∧ ∀η:Character,∃C:ℝ,0< C ∧
      ∀τ:ℝ,0<τ→τ ≤ 1→∀ᶠZ:ℝ in atTop,
        weighted_SourceMomentBound F κplain counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ)):=by
  obtain ⟨Ji,hi⟩:=Cycle25ProbeDetectorInverseFields.weighted_source_batch_inverse_fields F.modulus ⊤ le_top F counts
  obtain ⟨Jm,hm⟩:=weighted_source_batch_plain_marked_fine F κplain mesh hmesh hfine hpositive
  obtain ⟨Ju,hu⟩:=Cycle25ProbeDetectorPlainUnmarkedRestrictedField.weighted_source_batch_plain_unmarked D F hzero
  refine ⟨(Ji+Jm+Ju:ℕ),by positivity,?_⟩
  intro η
  obtain ⟨Ci,hCi,hi⟩:=hi η
  obtain ⟨Cm,hCm,hm⟩:=hm η
  obtain ⟨Cu,hCu,hu⟩:=hu η
  refine ⟨Ci+Cm+Cu,by positivity,?_⟩
  intro τ hτ hτ1
  filter_upwards [hi,hm,hu] with Z hi hm hu
  have hZ:0< Z:=zero_lt_one.trans hi.1
  let height:ℝ:=Z^(2*τ)
  have hh:0 ≤ height:=Real.rpow_nonneg hZ.le _
  have hbase:1 ≤ 1+height:=by linarith
  have hCi':Ci*(1+height)^Ji ≤ (Ci+Cm+Cu)*(1+height)^(Ji+Jm+Ju):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  have hCm':Cm*(1+height)^Jm ≤ (Ci+Cm+Cu)*(1+height)^(Ji+Jm+Ju):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  have hCu':Cu*(1+height)^Ju ≤ (Ci+Cm+Cu)*(1+height)^(Ji+Jm+Ju):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  simp only [Real.rpow_natCast]
  intro rows d a hd hdmax ha hamax hrows i z hz hzim q B hB hdata hreverse hslots hwidth
    hprofile hupper hexternal hslotMesh hbinWidth hfamily bin label left right hne
  have hrows':∀u∈rows,Z^(1/100:ℝ) ≤ rowNorm u:=fun u hu=>(hrows u hu).2.1
  have hext:∀s,(B.external s).re=17/50:=by intro s;rw [hexternal];exact hz
  have hheight:∀s,|(B.external s).im| ≤ height:=by intro s;rw [hexternal];exact hzim
  have hinv:=hi.2 d hd a D.ε _ _ _ i B hdata hprofile hupper hwidth hext
    bin label left right hne height hh
  have hmarked:=hm.2 rows hrows' d hd a _ _ _ i B hB hdata hprofile hwidth
    (fun s=> by rw [hupper]) hext bin label left right hne height hh hheight
  have hunmarked:=hu.2 rows hrows' d hd a _ _ _ i B hB hdata hprofile hwidth
    bin label left right hne height hh
  have hU:0 ≤ Z^d:=Real.rpow_nonneg hZ.le _
  apply Cycle25DetectorRawFiber.Moments.of_fields (B.fiber bin label left right hne) hk1
  · constructor
    · intro n hn σ hσ t ht
      exact ⟨rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).1 hCi',
        rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).2 hCi'⟩
    · intro selected hselected hfirst hsecond n hn σ hσ t ht
      exact (hinv.2 selected hselected hfirst hsecond n hn σ hσ t ht).trans
        (mul_le_mul_of_nonneg_right hCi' (Real.rpow_nonneg hU _))
    · intro j k hjk σ hσ t ht
      exact (hunmarked j k hjk σ hσ t ht).1.trans
        (mul_le_mul_of_nonneg_right hCu' (Real.rpow_nonneg hU _))
  · intro selected hselected hcap j k hjk σ hσ t ht
    exact (hmarked selected hselected hcap j k hjk σ hσ t ht).trans
      (mul_le_mul_of_nonneg_right hCm' (Real.rpow_nonneg hU _))

end
end OAI.SevenEighths.Cycle25ProbeFinalAssemblyCertifiedBands
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.CertifiedMoments -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.OriginalCertifiedMoments ; sha256 d5ef60808ea6e8dd503650a6e27bbdc53f604298de37e852ab011a59cab0ab31 -/
section





namespace OAI.SevenEighths.Cycle25ProbeFinalAssemblyCertifiedBands
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open CenteredMomentEnergyBands ProbeHighRowFamily
open Cycle25ProbeFinalAssembly ProbeFinalAssembly
open Cycle25ProbeDetectorPlainMarkedFineField Cycle25ProbeDetectorPlainUnmarkedField
open CenteredMomentNaturalFixedRaySource Cycle25CenteredMomentNaturalFixedRaySource
theorem old_source_moments {D:Cycle25.Weighted.MomentData}(F:WeightedSourceData D)
    (κplain:ℝ)(hk1:κplain≤3/4)(counts:ProbeFinalAssembly.CountParameters F.modulus ⊤ D.t)(mesh:ℝ)(hmesh:0< mesh)
    (hfine:∀j,D.ell j ≤ mesh/200)
    (hpositive:weighted_PositiveFineSourceInput F κplain mesh)
    (hzero:∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,∃A:ℝ,0< A ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (weighted_sourceFixedIdeal F) η₀) (1/4) (9/4) weighted_radialSupportUpper
        0 1 2 (D.t/4) U degree control A):
    ∃J:ℝ,0 ≤ J ∧ ∀η:Character,∃C:ℝ,0< C ∧
      ∀τ:ℝ,0<τ→τ ≤ 1→∀ᶠZ:ℝ in atTop,
        old_sourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ)):=by
  obtain ⟨Ji,hi⟩:=Cycle25OriginalDetectorInverseFields.weighted_source_batch_inverse_fields F.modulus ⊤ le_top F counts
  obtain ⟨Jm,hm⟩:=weighted_source_batch_plain_marked_fine F κplain mesh hmesh hfine hpositive
  obtain ⟨Ju,hu⟩:=Cycle25ProbeDetectorPlainUnmarkedRestrictedField.weighted_source_batch_plain_unmarked D F hzero
  refine ⟨(Ji+Jm+Ju:ℕ),by positivity,?_⟩
  intro η
  obtain ⟨Ci,hCi,hi⟩:=hi η
  obtain ⟨Cm,hCm,hm⟩:=hm η
  obtain ⟨Cu,hCu,hu⟩:=hu η
  refine ⟨Ci+Cm+Cu,by positivity,?_⟩
  intro τ hτ hτ1
  filter_upwards [hi,hm,hu] with Z hi hm hu
  have hZ:0< Z:=zero_lt_one.trans hi.1
  let height:ℝ:=Z^(2*τ)
  have hh:0 ≤ height:=Real.rpow_nonneg hZ.le _
  have hbase:1 ≤ 1+height:=by linarith
  have hCi':Ci*(1+height)^Ji ≤ (Ci+Cm+Cu)*(1+height)^(Ji+Jm+Ju):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  have hCm':Cm*(1+height)^Jm ≤ (Ci+Cm+Cu)*(1+height)^(Ji+Jm+Ju):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  have hCu':Cu*(1+height)^Ju ≤ (Ci+Cm+Cu)*(1+height)^(Ji+Jm+Ju):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  simp only [Real.rpow_natCast]
  intro rows d a hd hdmax ha hamax hrows i z hz hzim q B hB hdata hreverse hslots hwidth
    hprofile hupper hexternal hslotMesh hbinWidth hfamily bin label left right hne
  have hrows':∀u∈rows,Z^(1/100:ℝ) ≤ rowNorm u:=fun u hu=>(hrows u hu).2.1
  have hext:∀s,(B.external s).re=17/50:=by intro s;rw [hexternal];exact hz
  have hheight:∀s,|(B.external s).im| ≤ height:=by intro s;rw [hexternal];exact hzim
  have hinv:=hi.2 d hd a D.ε _ _ _ i B hdata hprofile hupper hwidth hext
    bin label left right hne height hh
  have hmarked:=hm.2 rows hrows' d hd a _ _ _ i B hB hdata hprofile hwidth
    (fun s=> by rw [hupper]) hext bin label left right hne height hh hheight
  have hunmarked:=hu.2 rows hrows' d hd a _ _ _ i B hB hdata hprofile hwidth
    bin label left right hne height hh
  have hU:0 ≤ Z^d:=Real.rpow_nonneg hZ.le _
  apply Cycle25DetectorRawFiber.Moments.original (κplain:=κplain)
  apply Cycle25DetectorRawFiber.Moments.of_fields (B.fiber bin label left right hne) hk1
  · constructor
    · intro n hn σ hσ t ht
      exact ⟨rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).1 hCi',
        rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).2 hCi'⟩
    · intro selected hselected hfirst hsecond n hn σ hσ t ht
      exact (hinv.2 selected hselected hfirst hsecond n hn σ hσ t ht).trans
        (mul_le_mul_of_nonneg_right hCi' (Real.rpow_nonneg hU _))
    · intro j k hjk σ hσ t ht
      exact (hunmarked j k hjk σ hσ t ht).1.trans
        (mul_le_mul_of_nonneg_right hCu' (Real.rpow_nonneg hU _))
  · intro selected hselected hcap j k hjk σ hσ t ht
    exact (hmarked selected hselected hcap j k hjk σ hσ t ht).trans
      (mul_le_mul_of_nonneg_right hCm' (Real.rpow_nonneg hU _))

end
end OAI.SevenEighths.Cycle25ProbeFinalAssemblyCertifiedBands
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.OriginalCertifiedMoments -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.OriginalHighReflectionSymmetricBounded ; sha256 1ef1636e22a673acbb0c2ab990cea9ca745307220867fb7c2f8fcd5264c70524 -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/OriginalHighReflectionSymmetricBounded.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.Cycle25CenteredMomentEnergyOriginalHighReflectionSymmetricBounded
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open Cycle25CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open Cycle25CenteredMomentEnergyOriginalHighReflectionBounded
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
open CenteredMomentRetainedEnergy
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

open Cycle25CenteredMomentEnergyOriginalHighReflectionSymmetric

variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem original_unbalanced_from_low
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask):
    ∃d xi L:ℝ,0< d ∧ 0< xi ∧ xi≤ rho/100 ∧ Mcap+Bmask+xi≤ L ∧ L≤ Mcap+Bmask+rho/100 ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(e Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ e → 0≤ K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap e κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) → 7/10≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → rho≤ s.width → s.width≤ Mcap →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀X₁ X₂:ℝ,0< X₁ → 0< X₂ →
      min (length Z X₁) (length Z X₂)≤ s.width/4 →
      5*s.width/6≤ length Z X₁+length Z X₂+(∑i,w i) →
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=> primePool M H bslot (Z^(w i)))
        (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=> Z^(w i)) X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale ≤
      C*(K+1)*diagonalControl s.radial.profile*(sourceControl U W₁*sourceControl U W₂)^2*
        (1+|t|+height)^J*Z^(s.width+e+ε) :=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,hstage⟩:=original_high_power (α:=α) M H hH
    Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,?_⟩
  intro degree S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage degree S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  rcases min_le_iff.mp hshort with hshort|hshort
  · exact hZ.2 e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  · rw [energy_swap]
    have hh:=hZ.2 e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs W₂ W₁ hs₂ hs₁ X₂ X₁ hX₂ hX₁ hshort (by linarith) (by linarith)
    simpa only [mul_comm (sourceControl U W₂) (sourceControl U W₁)] using hh

end SevenEighths.Cycle25CenteredMomentEnergyOriginalHighReflectionSymmetricBounded

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Energy.OriginalHighReflectionSymmetricBounded -/
