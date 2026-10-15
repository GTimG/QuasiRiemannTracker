/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B044
import Submissions.local44_20261013.Bundles.B050
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.PrimeScale
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AllocatedNaturalSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryUniformTests
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalUniformSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SlotClassTransport
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SlotNormalization
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.QuadraticSieve.GreenIntegrals

/- BEGIN ORIGINAL MODULE Analytic.JointAllocatedProduct ; sha256 ff1bd6437ed607b9ca02e0bddd2bc851ac6455e48bac288f2cd63a24619c33ae -/
section





/-! Exact norm transport from the source allocated retained row to the
normalized plain/prime products used by the buffered estimates. Clipped
scales, dilated profiles and every surviving relative character remain. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeDyadic HeckePrimeAnnular HeckeInverseAmplification
open CenteredMomentHeckeHeight CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile CenteredMomentSlotNormalization
open CenteredMomentDetectorDictionary CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentDivisorRetained CenteredMomentHeckeVolume
open CenteredMomentPrimeSlot ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma positive_row_normalized_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (pool : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hP : ∀ i, 0 ≤ P i) :
    positiveSlotRow η m A z W₁ W₂ pool β P t X₁ X₂ =
      ((Real.sqrt X₁ : ℂ)⁻¹*rowTwistedSum η m A z W₁ t X₁)*
      ((Real.sqrt X₂ : ℂ)⁻¹*rowTwistedSum η m A z W₂ t X₂)*
      ∏ i, normalizedSlot η m A z (pool i) (β i) t (P i) := by
  rw [← selectedProduct_univ η m A z W₁ W₂ pool β P t X₁ X₂ (mul_pos hX₁ hX₂).le hP]
  unfold selectedProduct
  rw [Real.sqrt_mul hX₁.le, Complex.ofReal_mul, mul_inv_rev]
  ring

lemma positive_row_height_norm_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (pool : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hP : ∀ i, 0 ≤ P i) :
    ‖positiveSlotRow η m A z W₁ W₂ pool β P t X₁ X₂‖^2 =
      ‖((Real.sqrt X₁ : ℂ)⁻¹*rowTwistedSum η m A z (twistProfile W₁ 0 t) 0 X₁)*
      ((Real.sqrt X₂ : ℂ)⁻¹*rowTwistedSum η m A z (twistProfile W₂ 0 t) 0 X₂)*
      ∏ i, normalizedSlot η m A z (pool i) (β i) t (P i)‖^2 := by
  rw [positive_row_normalized_pair η m A z W₁ W₂ pool β P t X₁ X₂ hX₁ hX₂ hP]
  simpa only [twistProfile_zero, add_zero] using
    normalized_plain_pair_height_norm_sq η m A z W₁ W₂ X₁ X₂ 0 0 t t 0 0
      hX₁ hX₂ (∏ i, normalizedSlot η m A z (pool i) (β i) t (P i))

/-- The exact buffered expression for an allocated source row. It uses the
original inverse relative character of each surviving prime slot. -/
def allocatedBufferedValue {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ)
    (η : Character) (m A z : O) (η₀ : ι → Character)
    (W₁ W₂ : ℝ → ℂ) (V : ι → ℝ → ℂ) (b P : ι → ℝ) (t X₁ X₂ : ℝ)
    (D : Ideal O) (allocation : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) : ℂ :=
  let U₁ := X₁/(Ideal.absNorm (selectedPlain D allocation 0) : ℝ)
  let U₂ := X₂/(Ideal.absNorm (selectedPlain D allocation 1) : ℝ)
  ((Real.sqrt (clippedScale U₁) : ℂ)⁻¹ * rowTwistedSum η m A z
    (twistProfile (dilated W₁ (clipDilation U₁)) 0 t) 0 (clippedScale U₁)) *
  ((Real.sqrt (clippedScale U₂) : ℂ)⁻¹ * rowTwistedSum η m A z
    (twistProfile (dilated W₂ (clipDilation U₂)) 0 t) 0 (clippedScale U₂)) *
  ∏ i : liveIndices D allocation, normalizedSlot η m A z
    (primePool M H (b i) (P i))
    (fun I => idealCoeff (η₀ i).inverse I*annularWeight (V i) (P i) 0 0 I) t (P i)

/-- No coefficient identity is assumed: the literal allocated source
coefficients are converted by expanding `annularWeight` at zero shift. -/
theorem allocated_positive_norm_sq_eq_buffered {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ)
    (η : Character) (m A z : O) (η₀ : ι → Character)
    (W₁ W₂ : ℝ → ℂ) (V : ι → ℝ → ℂ) (b P : ι → ℝ) (hP : ∀ i, 0 ≤ P i)
    (t X₁ X₂ : ℝ) (D : Ideal O)
    (allocation : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) :
    ‖allocatedPositiveRow η m A z t (fun i => primePool M H (b i) (P i))
      (fun i I => idealCoeff (η₀ i).inverse I*V i ((I.absNorm : ℝ)/P i)) P
      D allocation W₁ W₂ X₁ X₂‖^2 =
    ‖allocatedBufferedValue M H η m A z η₀ W₁ W₂ V b P t X₁ X₂ D allocation‖^2 := by
  unfold allocatedPositiveRow retainedPositiveRow allocatedBufferedValue
  rw [positive_row_height_norm_sq (ι := liveIndices D allocation) _ _ _ _ _ _ _ _ _ _ _ _
    (zero_lt_one.trans_le (clippedScale_ge_one _))
    (zero_lt_one.trans_le (clippedScale_ge_one _)) (fun i => hP i.val)]
  simp only [annularWeight, HeckeDyadic.shift, Complex.ofReal_zero, zero_mul, sub_zero,
    neg_zero, Complex.cpow_zero, mul_one]

#print axioms allocated_positive_norm_sq_eq_buffered
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointAllocatedProduct -/

/- BEGIN ORIGINAL MODULE Analytic.JointBufferedConductor ; sha256 8aca1eb4d23eeaa134f388607386d0220eebc24086a3fe3180b3421b8ce189c9 -/
section




/-! The presentation-conductor gate follows from literal row and puncture
norm bounds. Its constant is chosen from the fixed parent/slot dictionary,
before the reconstructed row or any common label. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckePrimeScale CenteredMomentNaturalRowSource
open HeckeInverseAmplification
local notation "O" => HeckeFamily.O

lemma excluded_modulus_norm (χ : Character) (R : Ideal O) (hR : R ≠ 0) :
    (excluded χ R).modulus.absNorm = χ.modulus.absNorm*R.radical.absNorm := by
  change (χ.modulus * ∏ P ∈ CompletedGauss.primeSupport R, P).absNorm = _
  rw [CenteredMomentAllocatedNaturalSource.primeSupport_product_radical R hR, map_mul]

lemma buffered_family_modulus_norm {Slot : Type*} (M : Ideal O) [NeZero M]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (η₀ : Slot → Character) (χ : Character) (R : Ideal O) (hR : R ≠ 0)
    (B : ℕ) (hB : 1 ≤ B) (hη₀ : ∀ j, (η₀ j).modulus.absNorm ≤ B)
    (hM : 1 ≤ M.absNorm)
    (label : Option (Slot × RayQuotient.Characters M H)) :
    (bufferedProductFamily M H hH η₀ (excluded χ R) label).modulus.absNorm ≤
      χ.modulus.absNorm*R.radical.absNorm*B*M.absNorm := by
  rcases label with _ | ⟨j, θ⟩
  · change (excluded χ R).modulus.absNorm ≤ _
    rw [excluded_modulus_norm χ R hR]
    calc
      _ ≤ χ.modulus.absNorm*R.radical.absNorm*B := Nat.le_mul_of_pos_right _ (by omega)
      _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
  · apply (twisted_modulus_bound M H hH _ θ).trans
    apply Nat.mul_le_mul_right M.absNorm
    apply (product_modulus_bound (excluded χ R) (η₀ j).inverse).trans
    rw [excluded_modulus_norm χ R hR]
    exact Nat.mul_le_mul_left _ (hη₀ j)

theorem fixed_buffered_conductor_constant {Slot : Type*} [Fintype Slot]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (η : Character) (η₀ : Slot → Character) :
    ∃ C : ℝ, 0 < C ∧ ∀ (parent : JointParentLabel η) (w : O)
      (N : NaturalRow parent.val w) (R : Ideal O), R ≠ 0 →
      ∀ label, ((bufferedProductFamily M H hH η₀ (excluded N.character R) label).modulus.absNorm : ℝ)
        ≤ C * ((Ideal.span {w}).absNorm : ℝ) * (R.radical.absNorm : ℝ) := by
  let P : ℕ := 1+∑ parent : JointParentLabel η, parent.val.modulus.absNorm
  let B : ℕ := 1+∑ j, (η₀ j).modulus.absNorm
  have hP : 1 ≤ P := by dsimp [P]; omega
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hM : 1 ≤ M.absNorm := Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (NeZero.ne M))
  have hp (parent : JointParentLabel η) : parent.val.modulus.absNorm ≤ P := by
    apply (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ parent)).trans
    dsimp [P]
    omega
  have hb (j : Slot) : (η₀ j).modulus.absNorm ≤ B := by
    apply (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
    dsimp [B]
    omega
  let C : ℕ := P*fixedConductorFactor*B*M.absNorm
  refine ⟨(C : ℝ)+1, add_pos_of_nonneg_of_pos (Nat.cast_nonneg C) zero_lt_one, ?_⟩
  intro parent w N R hR label
  have hnat := (buffered_family_modulus_norm M H hH η₀ N.character R hR B hB hb hM label).trans
    (Nat.mul_le_mul_right M.absNorm (Nat.mul_le_mul_right B
      (Nat.mul_le_mul_right R.radical.absNorm N.natural_modulus_bound)))
  have hpar := Nat.mul_le_mul_right M.absNorm (Nat.mul_le_mul_right B
    (Nat.mul_le_mul_right R.radical.absNorm
      (Nat.mul_le_mul_right (Ideal.span {w}).absNorm
        (Nat.mul_le_mul_right fixedConductorFactor (hp parent)))))
  have hfinal : (bufferedProductFamily M H hH η₀ (excluded N.character R) label).modulus.absNorm ≤
      C*(Ideal.span {w}).absNorm*R.radical.absNorm := by
    have halg (a b c d e f : ℕ) : a*b*c*d*e*f = (a*b*e*f)*c*d := by ring
    exact (hnat.trans hpar).trans_eq
      (halg P fixedConductorFactor (Ideal.span {w}).absNorm R.radical.absNorm B M.absNorm)
  have hreal : ((bufferedProductFamily M H hH η₀ (excluded N.character R) label).modulus.absNorm : ℝ) ≤
      (C : ℝ)*((Ideal.span {w}).absNorm : ℝ)*(R.radical.absNorm : ℝ) := by
    exact_mod_cast hfinal
  apply hreal.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (Nat.cast_nonneg _))
    (Nat.cast_nonneg _)

/-- A fixed arbitrarily small conductor reserve absorbs every fixed
dictionary constant, uniformly in the live row, puncture and bin. -/
theorem eventually_buffered_conductor {Slot : Type*} [Fintype Slot]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (η : Character) (η₀ : Slot → Character)
    (ξ : ℝ) (hξ : 0 < ξ) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (W B d : ℝ), W+B+ξ ≤ d →
      ∀ (parent : JointParentLabel η) (w : O) (N : NaturalRow parent.val w)
        (R : Ideal O), R ≠ 0 →
      ((Ideal.span {w}).absNorm : ℝ) ≤ Z^W → (R.radical.absNorm : ℝ) ≤ Z^B →
      ∀ label, ((bufferedProductFamily M H hH η₀ (excluded N.character R) label).modulus.absNorm : ℝ)
        ≤ Z^d := by
  obtain ⟨C, hC, hbound⟩ := fixed_buffered_conductor_constant M H hH η η₀
  filter_upwards [(tendsto_rpow_atTop hξ).eventually (eventually_ge_atTop C),
    eventually_gt_atTop (1 : ℝ)] with Z hCZ hZ
  refine ⟨hZ, ?_⟩
  intro W B d hd parent w N R hR hw hr label
  calc
    _ ≤ C*((Ideal.span {w}).absNorm : ℝ)*(R.radical.absNorm : ℝ) :=
      hbound parent w N R hR label
    _ ≤ Z^ξ*Z^W*Z^B := mul_le_mul
      (mul_le_mul hCZ hw (Nat.cast_nonneg _) (Real.rpow_nonneg (by linarith) _))
      hr (Nat.cast_nonneg _) (by positivity)
    _ = Z^(W+B+ξ) := by
      rw [← Real.rpow_add (by linarith : 0 < Z), ← Real.rpow_add (by linarith : 0 < Z)]
      congr 1
      ring
    _ ≤ Z^d := Real.rpow_le_rpow_of_exponent_le hZ.le hd

#print axioms eventually_buffered_conductor
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointBufferedConductor -/

/- BEGIN ORIGINAL MODULE Analytic.JointCoarsePopulation ; sha256 6cd1d764a03af4212183bc6ec7b8368b596f41268fcbeeaa7949413ee07fe747 -/
section



/-! A polynomial count for Fourier tails, independent of zero density,
bin heights and live profiles. The sharper count is kept for the main. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.Local44.Analytic
open CanonicalQuadraticSieve IdealMobiusDivisorSum ConcreteTraceCRT
open ActualEisensteinCubic ActualEisensteinCoordinates
local notation "O" => ActualEisensteinCubic.O
local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

theorem joint_fixed_unit_coarse_population :
    ∃ K : ℝ, 0 < K ∧ ∀ (X : ℝ), 1 ≤ X → ∀ (u : Oˣ) (S : Finset JointReconstructionLabel),
      (∀ v ∈ S, v.row u ≠ 0) →
      (∀ v ∈ S, Supported v.C₁ ∧ Supported v.D₁ ∧ Supported v.C₂ ∧ Supported v.D₂) →
      (∀ v ∈ S, primeSupport v.C₁ = primeSupport v.D₁ ∧ primeSupport v.C₂ = primeSupport v.D₂) →
      (∀ v ∈ S, Squarefree v.L ∧ v.L ∣ v.C₂ ∧ v.L ∣ v.D₂) →
      (∀ v ∈ S, (v.C₁.absNorm : ℝ) ≤ X ∧ (v.D₁.absNorm : ℝ) ≤ X ∧
        (v.C₂.absNorm : ℝ) ≤ X ∧ (v.D₂.absNorm : ℝ) ≤ X) →
      (∀ v ∈ S, ((Ideal.span {v.row u}).absNorm : ℝ) ≤ X) →
      (∀ v ∈ S, ((jointMissingRadical v.C₁ (v.row u)).absNorm : ℝ) ≤ X) →
      (S.card : ℝ) ≤ K*X^16 := by
  obtain ⟨K,hK,hcount⟩ := joint_population_count 1 1 (by norm_num) (by norm_num)
  refine ⟨128*K,by positivity,?_⟩
  intro X hX u S hrow hsup heq hproj hnorm hNw hNr
  let rows := S.image (fun v => v.row u)
  have hrows : ∀ w ∈ rows, w ≠ 0 := by
    intro w hw
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
    exact hrow v hv
  have hrowsNorm : ∀ w ∈ rows, ((Ideal.span {w}).absNorm : ℝ) ≤ X := by
    intro w hw
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
    exact hNw v hv
  have hrowsCard := DescentFiberCost.finite_element_count_real rows X hX (by
    intro w hw
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    exact hrowsNorm w hw)
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hh := hcount u rows S hrows hsup heq hproj
    (fun v hv => Finset.mem_image_of_mem _ hv)
    X X X X X X hXpos hXpos hXpos hXpos hXpos.le hXpos.le hnorm hrowsNorm hNr
  apply hh.trans
  calc
    _ ≤ K*(128*X)*X*X^(1:ℝ)*X^(1:ℝ)*X^(1:ℝ)*X^(1:ℝ)*(X*X)^(5*(1:ℝ)) := by
      gcongr
    _ = _ := by norm_num [Real.rpow_ofNat]; ring

theorem joint_variable_unit_coarse_population :
    ∃ K : ℝ, 0 < K ∧ ∀ (X : ℝ), 1 ≤ X →
      ∀ (unit : JointReconstructionLabel → Oˣ) (S : Finset JointReconstructionLabel),
      (∀ v ∈ S, v.row (unit v) ≠ 0) →
      (∀ v ∈ S, Supported v.C₁ ∧ Supported v.D₁ ∧ Supported v.C₂ ∧ Supported v.D₂) →
      (∀ v ∈ S, primeSupport v.C₁ = primeSupport v.D₁ ∧ primeSupport v.C₂ = primeSupport v.D₂) →
      (∀ v ∈ S, Squarefree v.L ∧ v.L ∣ v.C₂ ∧ v.L ∣ v.D₂) →
      (∀ v ∈ S, (v.C₁.absNorm : ℝ) ≤ X ∧ (v.D₁.absNorm : ℝ) ≤ X ∧
        (v.C₂.absNorm : ℝ) ≤ X ∧ (v.D₂.absNorm : ℝ) ≤ X) →
      (∀ v ∈ S, ((Ideal.span {v.row (unit v)}).absNorm : ℝ) ≤ X) →
      (∀ v ∈ S, ((jointMissingRadical v.C₁ (v.row (unit v))).absNorm : ℝ) ≤ X) →
      (S.card : ℝ) ≤ K*X^16 := by
  obtain ⟨K,hK,hcount⟩ := joint_fixed_unit_coarse_population
  refine ⟨6*K,by positivity,?_⟩
  intro X hX unit S hrow hsup heq hproj hnorm hNw hNr
  have hfiber (u : Oˣ) : ((S.filter (fun v => unit v=u)).card : ℝ) ≤ K*X^16 := by
    apply hcount X hX u
    · intro v hv
      simpa only [(Finset.mem_filter.mp hv).2] using hrow v (Finset.mem_filter.mp hv).1
    · exact fun v hv => hsup v (Finset.mem_filter.mp hv).1
    · exact fun v hv => heq v (Finset.mem_filter.mp hv).1
    · exact fun v hv => hproj v (Finset.mem_filter.mp hv).1
    · exact fun v hv => hnorm v (Finset.mem_filter.mp hv).1
    · intro v hv
      simpa only [(Finset.mem_filter.mp hv).2] using hNw v (Finset.mem_filter.mp hv).1
    · intro v hv
      simpa only [(Finset.mem_filter.mp hv).2] using hNr v (Finset.mem_filter.mp hv).1
  have hcard : Fintype.card Oˣ = 6 := by
    simpa only [Nat.card_eq_fintype_card] using PrimaryIdealUnitReindex.card_units_eq_six
  calc
    (S.card : ℝ) = ∑ u : Oˣ, ((S.filter (fun v => unit v=u)).card : ℝ) := by
      exact_mod_cast card_eq_sum_buffered_fibers S unit
    _ ≤ ∑ _u : Oˣ, K*X^16 := Finset.sum_le_sum (fun u _ => hfiber u)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,hcard,nsmul_eq_mul]; ring

theorem eventually_joint_coarse_population (B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ Z : ℝ in atTop, 1 ≤ Z ∧
      ∀ (unit : JointReconstructionLabel → Oˣ) (S : Finset JointReconstructionLabel),
      (∀ v ∈ S, v.row (unit v) ≠ 0) →
      (∀ v ∈ S, Supported v.C₁ ∧ Supported v.D₁ ∧ Supported v.C₂ ∧ Supported v.D₂) →
      (∀ v ∈ S, primeSupport v.C₁ = primeSupport v.D₁ ∧ primeSupport v.C₂ = primeSupport v.D₂) →
      (∀ v ∈ S, Squarefree v.L ∧ v.L ∣ v.C₂ ∧ v.L ∣ v.D₂) →
      (∀ v ∈ S, (v.C₁.absNorm : ℝ) ≤ Z^B ∧ (v.D₁.absNorm : ℝ) ≤ Z^B ∧
        (v.C₂.absNorm : ℝ) ≤ Z^B ∧ (v.D₂.absNorm : ℝ) ≤ Z^B) →
      (∀ v ∈ S, ((Ideal.span {v.row (unit v)}).absNorm : ℝ) ≤ Z^B) →
      (∀ v ∈ S, ((jointMissingRadical v.C₁ (v.row (unit v))).absNorm : ℝ) ≤ Z^B) →
      (S.card : ℝ) ≤ Z^(16*B+1) := by
  obtain ⟨K,hK,hcount⟩ := joint_variable_unit_coarse_population
  filter_upwards [eventually_ge_atTop (max 1 K)] with Z hZ
  have hz : 1 ≤ Z := (le_max_left _ _).trans hZ
  have hKZ : K ≤ Z := (le_max_right _ _).trans hZ
  have hzpos : 0 < Z := zero_lt_one.trans_le hz
  refine ⟨hz,?_⟩
  intro unit S hrow hsup heq hproj hnorm hNw hNr
  have hh := hcount (Z^B) (Real.one_le_rpow hz hB) unit S hrow hsup heq hproj hnorm hNw hNr
  apply hh.trans
  calc
    K*(Z^B)^16 ≤ Z*(Z^B)^16 := mul_le_mul_of_nonneg_right hKZ (by positivity)
    _ = Z^(16*B+1) := by
      rw [←Real.rpow_mul_natCast hzpos.le]
      calc
        _ = Z^(1+B*(16:ℕ)) := by rw [Real.rpow_add hzpos,Real.rpow_one]
        _ = _ := by congr 1; norm_num; ring

#print axioms eventually_joint_coarse_population
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCoarsePopulation -/

/- BEGIN ORIGINAL MODULE Analytic.JointExceptionalChild ; sha256 0412c0d2461d790f4644659fe99c90baf358958657cc9850214cec16bc5b6775 -/
section



/-! Actual exceptional first children, with source-derived normalization,
profile control and the local negative exponent. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstMixedAllowance CenteredMomentFirstExceptionalChildPaid
open CenteredMomentFirstPhysicalSource CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSectorLocalization CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentFirstChildProfileControl CenteredMomentSecondHeightFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondExceptionalUniformSource CenteredMomentFiniteProfileExceptional
open CenteredMomentFiniteProfileExceptionalPhysical CenteredMomentSecondEnergySplit
open CenteredMomentSourceMass CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open ConcretePrimeRowBridge RayFourExpansion
local notation "O" => HeckeFamily.O
local instance jointExceptionalChildDecEq1 {κ : Type*} : DecidableEq κ := Classical.decEq _
local instance jointExceptionalChildDecEq2 {κ : Type*} : DecidableEq (κ ⊕ Fin 2) := Classical.decEq _

lemma normalized_exceptional_from_core
    (energy V K Z a α β γ ref L F G N : ℝ) (hZ : 0 < Z)
    (href : 0 ≤ ref) (hL : 0 ≤ L) (hF : 0 ≤ F) (hN : 0 ≤ N)
    (hsource : energy/V ≤ L*Z^(α-β)*V^(1/3 : ℝ)*K^(5/6 : ℝ)*F/N)
    (hcore : V^(1/3 : ℝ)*K^(5/6 : ℝ)*Z^(-a)*Z^(-β)/ref ≤ G*Z^γ) :
    energy/(V*Z^a*ref) ≤ L*F*G*Z^(α+γ)/N := by
  have hh := div_le_div_of_nonneg_right hsource (mul_nonneg (Real.rpow_nonneg hZ.le a) href)
  rw [div_div,←mul_assoc] at hh
  apply hh.trans
  calc
    _ = ((L*F/N)*Z^α)*(V^(1/3 : ℝ)*K^(5/6 : ℝ)*Z^(-a)*Z^(-β)/ref) := by
      rw [Real.rpow_sub hZ,Real.rpow_neg hZ.le,Real.rpow_neg hZ.le]
      ring
    _ ≤ ((L*F/N)*Z^α)*(G*Z^γ) :=
      mul_le_mul_of_nonneg_left hcore (mul_nonneg (div_nonneg (mul_nonneg hL hF) hN)
        (Real.rpow_nonneg hZ.le _))
    _ = _ := by rw [Real.rpow_add hZ]; ring

/-- Actual exceptional energy at the enlarged main ball, for every literal
first allocation. Its constant and Fourier degree are fixed before all
first labels; the only remaining inputs are source/geometric gates. -/
theorem actual_local_main_exceptional_child
    {Slot : Type*} [Fintype Slot]
    (wlo whi : ℝ) (hwlo : 0 < wlo) (hwhi : 0 ≤ whi)
    (lo hi : Slot → ℝ) (ε δ θ Bcap : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ) (hBcap : 0 ≤ Bcap) :
    ∃ orders : Finset Slot → ℕ, ∃ seminorms : Finset Slot → Finset (ℕ × ℕ),
      (∀ I, (0,0) ∈ seminorms I) ∧
      ∃ Cs : Finset Slot → ℝ, (∀ I, 0 ≤ Cs I) ∧
      ∀ Q : Ideal O, Q ≠ 0 → Q ≠ ⊤ → Q ≤ Ideal.span {(72 : O)} →
      ∃ Ks : Finset Slot → ℝ, (∀ I, 0 < Ks I) ∧
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (s : Input Slot) (p : Profiles wlo whi),
      (∀ i, s.lo i = lo i) → (∀ i, s.hi i = hi i) →
      s.W₁ = p.profile 0 → s.W₂ = p.profile 1 →
      ∀ (η τ : Character) (C D E : Ideal O) (hC : Supported C) (hD : Supported D),
      primeSupport C = primeSupport D →
      ∀ U : Finset (CommonIndex C D),
      E = Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) U} →
      ∀ (K omega M : ℝ), 0 < K →
      τ.modulus = η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72 : O)}*
        Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) U*activeConductor C D} →
      ∀ (Rmask seed : Ideal O) (B : actualAllocations s.pools (commonPart C D)) (t : ℝ)
        (N : ℕ) (b : ℝ),
      1 ≤ b → Fintype.card Slot ≤ N → s.upper ≤ b →
      frozenCoefficient B.val (commonPart C D) Rmask s.ν s.W s.P ≠ 0 →
      1 ≤ M → M ≤ Real.logb Z K+Real.logb Z (η.modulus.absNorm : ℝ)+Real.logb Z fixedPresentationCost →
      Real.logb Z (CenteredMomentAmplificationChildInput.volume s) ≤ (883/1000)*M →
      Z^(M/4) ≤ s.X₁ → Z^(M/4) ≤ s.X₂ → Z^(M/4) ≤ s.Y₁ → Z^(M/4) ≤ s.Y₂ →
      Rmask ≠ 0 → Squarefree seed → seed ≠ 0 →
      let d := child s (commonPart C D) Rmask B τ t
      let V := CenteredMomentAmplificationChildInput.volume s
      let I := liveIndices B.val
      let Rmain := mainCommonRadius Z (Real.logb Z (D.absNorm : ℝ))
        (nominalLog C D E K V Z) (Real.logb Z (C.absNorm : ℝ)) (9/500) omega 0
      (∀ i, 1 ≤ d.P i) → 0 ≤ sourceRadius d → sourceRadius d ≤ Z^Bcap →
      (τ.modulus.absNorm : ℝ) ≤ Z^Bcap → ((Rmask*commonPart C D).absNorm : ℝ) ≤ Z^Bcap →
      ∀ (ray : RayCharacter) (m : O), m ≠ 0 → goodLambda ∣ m → (2 : O) ∣ m →
      ∀ Tsec ξ : ℝ, 0 < frequencyRadius Tsec Z ξ → frequencyRadius Tsec Z ξ ≤ Z^Bcap →
      ‖partEnergy true τ ray Q m t (finiteColumns (Fintype.piFinset d.pools))
        (coefficient d (Rmask*commonPart C D) seed) ballProfile Rmain
        Tsec Z ξ (sourceRadius d)‖ /
        (CenteredMomentAmplificationChildInput.volume d*Z^(3/500 : ℝ)*
          ((τ.modulus.absNorm : ℝ)*(V/(C.absNorm : ℝ))*Z^(allowance C D Z))) ≤
      (Cs I*exceptionalConstant N b (orders I) Q (Ks I)*(b^N)^(1/3 : ℝ)*
        ((∏ i : I, lo i.val)*wlo*wlo)^(-2/3 : ℝ)) *
        p.control (seminorms I)^2*(1+‖t‖)^(2*orders I)*mass s^4*mass d^2*
        Z^(2*ε+2*δ+2*(5*Bcap+1)*θ-93/1000+5*omega/6)/(seed.absNorm : ℝ) := by
  have hchoice (I : Finset Slot) := original_exceptional_energy wlo whi hwlo hwhi
    (fun i : I => lo i.val) (fun i : I => hi i.val) ballProfile ε δ θ Bcap
    hε hδ hθ hBcap
  choose orders seminorms hsem Cs hCs hmain using hchoice
  refine ⟨orders,seminorms,hsem,Cs,hCs,?_⟩
  intro Q hQ hQt hQ72
  choose Ks hKs hmain using fun I => hmain I Q hQ hQt hQ72
  refine ⟨Ks,hKs,?_⟩
  filter_upwards [Filter.eventually_all.mpr hmain] with Z hmain
  refine ⟨(hmain ∅).1,?_⟩
  intro s p hlo hhi hW₁ hW₂ η τ C D E hC hD hCD U hE K omega M hK hmod
    Rmask seed B t N b hb hcard hupper hne hM hwidth hvolume hX₁ hX₂ hY₁ hY₂
    hRmask hseed hseed0 d V I Rmain hP hH0 hH hτ hRnorm ray m hm hml hm2 Tsec ξ hfreq hfreqcap
  have hZ : 1 < Z := (hmain ∅).1
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hrad : 0 < Rmain := by dsimp [Rmain,mainCommonRadius]; positivity
  have hscales := input_cap_scales Z hZ d
  have hsource := (hmain I).2 d p (fun i => hlo i.val) (fun i => hhi i.val) hP hW₁ hW₂
    (Rmask*commonPart C D) seed (mul_ne_zero hRmask (commonPart_ne_zero C D)) hseed hseed0
    hH0 hH hτ hRnorm ray m hm hml hm2 Tsec ξ Rmain hrad hfreq hfreqcap
    (inputCap Z d) hscales.1 hscales.2.1 hscales.2.2.1 hscales.2.2.2
  have hvEq : CenteredMomentExceptionalAmplitudePair.volume d.toData =
      CenteredMomentAmplificationChildInput.volume d := by
    unfold CenteredMomentExceptionalAmplitudePair.volume CenteredMomentAmplificationChildInput.volume
    ring
  rw [hvEq] at hsource
  have hdη : d.η = τ := rfl
  have hdt : d.t = t := rfl
  rw [hdη,hdt] at hsource
  have hcore := actual_local_main_exceptional_child_core η τ C D E hC hD hCD U hE
    K Z omega M hZ hK hmod s Rmask B t N b hb hcard hupper hne hM hwidth hvolume
    hX₁ hX₂ hY₁ hY₂
  have hlower : 0 ≤ ((∏ i : I, lo i.val)*wlo*wlo)^(-2/3 : ℝ) := by
    apply Real.rpow_nonneg
    have he : (∏ i : I, lo i.val) = ∏ i : I, s.lo i.val := by simp_rw [hlo]
    rw [he]
    have hp : 0 ≤ ∏ i : I, s.lo i.val :=
      Finset.prod_nonneg (fun (i : I) _ => (s.lo_pos i.val).le)
    positivity
  have href : 0 ≤ (τ.modulus.absNorm : ℝ)*(V/(C.absNorm : ℝ))*Z^(allowance C D Z) := by
    have hv := (CenteredMomentAmplificationChildInput.volume_pos s).le
    dsimp [V]
    positivity
  have hp0 := profileFactor_nonneg (seminorms I) d p (orders I) Q (Ks I) (hKs I).le
  have hh := normalized_exceptional_from_core _ (CenteredMomentAmplificationChildInput.volume d)
    Rmain Z (3/500) (2*ε+2*δ+2*(5*Bcap+1)*θ) (2*max (inputCap Z d) 0/3)
    (-93/1000+5*omega/6) _ (Cs I*profileFactor (seminorms I) d p (orders I) Q (Ks I))
    (((∏ i : I, lo i.val)*wlo*wlo)^(-2/3 : ℝ)) ((b^N)^(1/3 : ℝ)) (seed.absNorm : ℝ)
    hz href (mul_nonneg (hCs I) hp0) hlower (Nat.cast_nonneg _) (by
      simpa only [show ∀ i : I, d.lo i = lo i.val from fun i => hlo i.val] using hsource) (by
      simpa only [d,V,Rmain,neg_div,neg_mul] using hcore)
  have hprof := exceptional_factor_bound (seminorms I) p (orders I) Q (Ks I) (hKs I).le
    d N b (mass s) hb hupper ((child_card B.val).trans hcard) (child_mass s _ Rmask B τ t)
  apply hh.trans
  have hm := mul_le_mul_of_nonneg_left hprof (hCs I)
  let F : ℝ := (((∏ i : I, lo i.val)*wlo*wlo)^(-2/3 : ℝ))*(b^N)^(1/3 : ℝ)*
    Z^(2*ε+2*δ+2*(5*Bcap+1)*θ+(-93/1000+5*omega/6))/(seed.absNorm : ℝ)
  have hF : 0 ≤ F := div_nonneg (mul_nonneg
    (mul_nonneg hlower (Real.rpow_nonneg (pow_nonneg (zero_le_one.trans hb) N) _))
    (Real.rpow_nonneg hz.le _)) (Nat.cast_nonneg _)
  have hfactor := mul_le_mul_of_nonneg_right hm hF
  rw [hdt] at hfactor
  dsimp only [F] at hfactor
  have hexp : 2*ε+2*δ+2*(5*Bcap+1)*θ+(-93/1000+5*omega/6) =
      2*ε+2*δ+2*(5*Bcap+1)*θ-93/1000+5*omega/6 := by ring
  convert hfactor using 1 <;> rw [hexp] <;> ring

#print axioms actual_local_main_exceptional_child
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointExceptionalChild -/

/- BEGIN ORIGINAL MODULE Analytic.JointExceptionalErrorNormalization ; sha256 3ba097aa7d54c01182c2915f6399b61d4eb5df68f986f7126ae7ea6915a1010c -/
section


/-! The actual twice-extracted exceptional reference retains the moving
prime scalar and improves the local error reserve without a low-width gate. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstMixedAllowance CenteredMomentFirstMixedChild
open CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstExceptionalChildPaid
open CenteredMomentFirstPhysicalSource CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstScale
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentCompleteCommon CenteredMomentCanonicalFirst CenteredMomentFirstMixedExceptionalCap
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentSecondHeightFamily
open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstAmplificationChoice
local notation "O" => HeckeFamily.O
local instance jointExceptionalErrorNormalizationDecEq1 {κ : Type*} : DecidableEq κ := Classical.decEq _

theorem actual_local_error_exceptional_reference
    {ι : Type*} [Fintype ι]
    (η τ : Character) (C D E : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D)
    (U : Finset (CommonIndex C D))
    (hE : E = Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) U})
    (K V Z sigma omega M : ℝ) (hZ : 1 < Z) (hK : 0 < K) (hV : 0 < V)
    (hsigma : sigma ≤ 9/500)
    (hmod : τ.modulus = η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72 : O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) U*activeConductor C D})
    (Mray : Ideal O) [NeZero Mray] (H : Subgroup (O ⧸ Mray)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes ⊆ Sbad)
    (p0 : O) (hp0 : p0 ∈ elementPool (primePool Mray H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k = 1 ∨ k = 6 ∨ k = 7)
    (s : Input ι) (Rmask : Ideal O)
    (B : actualAllocations s.pools (commonPart C D)) (t : ℝ)
    (Bp : actualAllocations (child s (commonPart C D) Rmask B τ t).pools ((Ideal.span {p0})^k))
    (υ : Character) (v : ℝ)
    (hM : 1 ≤ M) (hwidth : M ≤ Real.logb Z K+Real.logb Z (η.modulus.absNorm : ℝ)+
      Real.logb Z fixedPresentationCost)
    (hvolume : Real.logb Z V ≤ (883/1000)*M)
    (hX₁ : Z^(M/4) ≤ s.X₁) (hX₂ : Z^(M/4) ≤ s.X₂)
    (hY₁ : Z^(M/4) ≤ s.Y₁) (hY₂ : Z^(M/4) ≤ s.Y₂) :
    let d := twiceChild s (commonPart C D) Rmask B τ t (Ideal.span {p0}) k Bp υ v
    let Rerror := errorCommonRadius Z (Real.logb Z (D.absNorm : ℝ))
      (nominalLog C D E K V Z) (Real.logb Z (C.absNorm : ℝ)) sigma omega 0 p0 k
    ((V/(C.absNorm : ℝ))*localErrorCost p0 (k-1)*
      (V/(C.absNorm : ℝ)/(normValue p0)^k)^(1/3 : ℝ)*Rerror^(5/6 : ℝ)/
      ((τ.modulus.absNorm : ℝ)*(V/(C.absNorm : ℝ))^2*Z^(allowance C D Z)))*
        Z^(-2*max (inputCap Z d) 0/3) ≤ Z^(-9/100+5*omega/6) := by
  dsimp only
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hc := commonPart_of_equal_support C D hC.1 hCD
  have hd := commonPart_of_equal_support D C hD.1 hCD.symm
  let Rerror := errorCommonRadius Z (Real.logb Z (D.absNorm : ℝ))
    (nominalLog C D E K V Z) (Real.logb Z (C.absNorm : ℝ)) sigma omega 0 p0 k
  have hr : 0 < Rerror := by unfold Rerror errorCommonRadius; positivity
  have hs := actual_error_child_stage η τ fixedBadMask C D E hC hD U
    K V Z 0 sigma omega 0 hZ hmod Mray H Sbad hbad p0 hp0 k hk
    s Rmask B t (Real.logb Z V) M Bp υ v hX₁ hX₂ hY₁ hY₂
  dsimp only at hs
  simp only [hc,hd,extracted_allowance_eq C D hC.1 hD.1 hCD Z] at hs
  have hp := elementPool_data _
    (fun P hP => (primePool_data Mray H Sbad hbad (1/2) 1 (Z^(sigma/3)) P hP).1)
    (fun P hP => (primePool_data Mray H Sbad hbad (1/2) 1 (Z^(sigma/3)) P hP).2) p0 hp0
  have he := actual_error_reference_le η τ C D hC hD hCD U K V Z 0
    (Real.logb Z Rerror) hK hV hZ hmod p0 hp.1.ne_zero k hk
  dsimp only at he
  rw [←hE] at he
  simp only [zero_add] at he
  rw [Real.rpow_logb hz hZ.ne' hr] at he
  have hh := mul_le_mul_of_nonneg_right he
    (Real.rpow_nonneg hz.le (-2*max (inputCap Z
      (twiceChild s (commonPart C D) Rmask B τ t (Ideal.span {p0}) k Bp υ v)) 0/3))
  apply hh.trans
  rw [←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  dsimp only [Rerror] at *
  simp only [nominalLog,sub_zero,add_zero] at hs ⊢
  linarith

#print axioms actual_local_error_exceptional_reference
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointExceptionalErrorNormalization -/

/- BEGIN ORIGINAL MODULE Analytic.JointSourcePopulation ; sha256 9037d62ac31c57864eddd59d4cd6ea08c2c691bc0abd4bbf9925f55544044287 -/
section



/-! The joint arithmetic population for the actual relative natural
families, with variable units and canceled Euler masks. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Set
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification CanonicalQuadraticSieve
open IdealMobiusDivisorSum LocalMoment ProbeHighRowFamily
local notation "O" => HeckeFamily.O

section FixedDensityData
variable {SlotLabel : Type*} [Fintype SlotLabel]
variable (η : Character) (ν : SlotLabel → Character) (Q : Ideal O) [NeZero Q]
  (hQtop : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
  (hQη : Q ≤ η.modulus) (hQν : ∀ j, Q ≤ (ν j).modulus)
  (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
  (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
  (hH : RayOrthogonality.globalUnits M ≤ H) (S₀ : Finset (Ideal O))
  (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
  (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
  (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
  (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
  (hβupper : HeckeZeroSupremum.beta ≤ 7/8)
include hQtop hQ72 hQη hQν hβ hH S₀ hφ hφc hφp hφ0 hφne ha₀ hab₀ hB₀ hφs hφB hβupper

/-- High-bin population of the actual relative natural family. Its literal
source bin discharges all coefficient and nonprincipality requirements of
the raw density theorem. Negative supported windows are handled as empty. -/
theorem actual_joint_natural_population (B loss : ℝ) (hB : 0 ≤ B) (hloss : 0 < loss) :
    ∃ (A : ℕ) (K : ℝ), 0 < K ∧
      ∀ (Z P W : ℝ), 1 < Z → P ≤ B → W ≤ B →
      ∀ (p : DensityWindow) (unit : JointReconstructionLabel → Oˣ)
        (S : Finset JointReconstructionLabel)
        (R : JointReconstructionLabel → JointRelativeLabel η SlotLabel → Ideal O)
        (hR : ∀ v label, R v label ≠ 0),
      (∀ v ∈ S, Supported v.C₁ ∧ Supported v.D₁ ∧ Supported v.C₂ ∧ Supported v.D₂) →
      (∀ v ∈ S, primeSupport v.C₁ = primeSupport v.D₁ ∧
        primeSupport v.C₂ = primeSupport v.D₂) →
      (∀ v ∈ S, Squarefree v.L ∧ v.L ∣ v.C₂ ∧ v.L ∣ v.D₂) →
      (∀ v ∈ S, ∃ hw : v.row (unit v) ≠ 0,
        jointRelativeSourceZeroBin η ν Q hQ72 hQν (R v) (hR v)
          p.lower p.upper p.height ⟨v.row (unit v),hw⟩) →
      (∀ v ∈ S, (Ideal.absNorm v.C₁ : ℝ) ≤ Z^B ∧
        (Ideal.absNorm v.D₁ : ℝ) ≤ Z^B ∧
        (Ideal.absNorm v.C₂ : ℝ) ≤ Z^B ∧ (Ideal.absNorm v.D₂ : ℝ) ≤ Z^B) →
      (∀ v ∈ S, (Ideal.absNorm (Ideal.span {v.row (unit v)}) : ℝ) ≤ Z^W) →
      (∀ v ∈ S, (Ideal.absNorm (jointMissingRadical v.C₁ (v.row (unit v))) : ℝ) ≤ Z^P) →
      (S.card : ℝ) ≤ K*(1+|p.height|)^A*Z^(unmarkedDensity (2*p.lower-1)*W+P+loss) := by
  obtain ⟨A,K,hK,hcount⟩ := actual_joint_variable_unit_population
    (jointRelativeParent η ν) Q hQtop hQ72 (jointRelativeParent_fixedQ η ν Q hQη hQ72 hQν)
    hβ M H hH S₀ φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
    hβupper B loss hB hloss
  refine ⟨A,K,hK,?_⟩
  intro Z P W hZ hPB hWB p unit S R hR hsup heq hproj hbin hnorm hNw hNr
  by_cases hne : S.Nonempty
  · have hn := joint_nonempty_window_nonnegative S unit Z P W hZ hne
      (fun v hv => (hbin v hv).choose) hNw hNr
    apply hcount Z P W hZ.le hn.1 hPB hn.2 hWB p unit S hsup heq hproj _ hnorm hNw hNr
    intro v hv
    obtain ⟨hw,hvbin⟩ := hbin v hv
    exact ⟨hw, ((jointRelativeSourceZeroBin_iff η ν Q hQ72 hQν (R v) (hR v)
      p.lower p.upper p.height ⟨v.row (unit v),hw⟩).mp hvbin).2⟩
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.card_empty,Nat.cast_zero]
    have hzpos : 0 < Z := zero_lt_one.trans hZ
    positivity

end FixedDensityData
#print axioms actual_joint_natural_population
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointSourcePopulation -/
