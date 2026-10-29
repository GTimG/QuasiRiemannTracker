/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.SourceReflection
import Candidate.Local.Qrh.JointDetector.BadFrequencySectors
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.UnitRows
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.Mask

/-! Exact finite gcd and retained-divisor assembly for selected sextic rows.
The arrays on the two sides are independent. The selected set is fixed before
source summation; no coprime selector is removed by matrix monotonicity. -/
namespace Qrh.JointDetector
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ActualEisensteinCubic ActualEisensteinCoordinates
open CanonicalRowCompletion CanonicalQuadraticSieve ConcreteTraceCRT CompletedGauss
open ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

/-- Division by a common good ideal preserves the FULL ray modulo 36. -/
theorem primaryQuotient_congruent_mod36 (D I J : Ideal O)
    (hI : Admissible I) (hDI : D ∣ I) (hDJ : D ∣ J)
    (hmod : primaryGenerator I - primaryGenerator J ∈
      (Ideal.span {(36 : O)} : Ideal O)) :
    primaryGenerator (idealQuotient D I) - primaryGenerator (idealQuotient D J) ∈
      (Ideal.span {(36 : O)} : Ideal O) := by
  have hD : Admissible D := admissible_of_dvd hI hDI
  have hspec := primaryGenerator_spec D (primaryGenerator_admissible D hD)
  have hs : Supported (Ideal.span {primaryGenerator D}) := hspec.1.symm ▸ admissible_supported hD
  obtain ⟨u, hu⟩ := HeckeUnitRows.supported_unit_thirty_six (primaryGenerator D) hs
  have he := Ideal.Quotient.eq.mpr hmod
  have hi : primaryGenerator I = primaryGenerator D * primaryGenerator (idealQuotient D I) := by
    rw [← primaryGenerator_mul, idealQuotient_mul hDI]
  have hj : primaryGenerator J = primaryGenerator D * primaryGenerator (idealQuotient D J) := by
    rw [← primaryGenerator_mul, idealQuotient_mul hDJ]
  rw [hi, hj, map_mul, map_mul, ← hu] at he
  exact Ideal.Quotient.eq.mp ((Units.mul_right_inj u).mp he)

/-- Each pair belongs to exactly one gcd block. -/
def sexticGcdTerm {R : Type*} (D : Ideal O) (row : R → Ideal O)
    (a c : R → ℂ) (z : O) (j k : R) : ℂ :=
  if gcd (row j) (row k) = D then a j * c k * primitivePair (row j) (row k) z else 0

theorem sum_sexticGcdTerm {R : Type*} [Fintype R]
    (row : R → Ideal O) (a c : R → ℂ) (z : O) (j k : R) :
    (∑ D ∈ gcdPool row, sexticGcdTerm D row a c z j k) =
      a j * c k * primitivePair (row j) (row k) z := by
  rw [Finset.sum_eq_single (gcd (row j) (row k))]
  · simp only [sexticGcdTerm, ite_true]
  · intro D hD hne
    exact ite_eq_right (Ne.symm hne)
  · exact fun h => (h (mem_gcdPool row j k)).elim

theorem sextic_bilinear_eq_gcd_blocks {R : Type*} [Fintype R]
    (sources : Finset O) (w : O → ℂ) (row : R → Ideal O) (a c : R → ℂ) :
    (∑ z ∈ sources, w z * ∑ j, ∑ k, a j * c k * primitivePair (row j) (row k) z) =
      ∑ D ∈ gcdPool row, ∑ z ∈ sources, w z * ∑ j, ∑ k,
        sexticGcdTerm D row a c z j k := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [← Finset.mul_sum]
  congr 1
  conv_rhs => rw [Finset.sum_comm]; arg 2; ext j; rw [Finset.sum_comm]
  simp_rw [sum_sexticGcdTerm]

/-- The full shared factor becomes its natural zero mask, including the unit
and diagonal blocks. The quotient coprime selector remains explicit. -/
theorem sexticGcdTerm_eq_quotient {R : Type*}
    (D : Ideal O) (hD : Admissible D) (row : R → Ideal O)
    (a c : R → ℂ) (z : O) (j k : R) :
    sexticGcdTerm D row a c z j k = idealZeroMask D z *
      (if IsCoprime (totalQuotient D (row j)) (totalQuotient D (row k)) then
        (if D ∣ row j then a j else 0) * (if D ∣ row k then c k else 0) *
          primitivePair (totalQuotient D (row j)) (totalQuotient D (row k)) z else 0) := by
  by_cases hj : D ∣ row j
  · by_cases hk : D ∣ row k
    · simp only [sexticGcdTerm, totalQuotient, ite_eq_left hj, ite_eq_left hk]
      rw [← gcd_eq_iff_quotient_coprime D (row j) (row k) hD.1 hj hk]
      by_cases hg : gcd (row j) (row k) = D
      · simp only [ite_eq_left hg]
        have hp := shared_pair_mask D (idealQuotient D (row j)) (idealQuotient D (row k)) hD z
        rw [idealQuotient_mul hj, idealQuotient_mul hk] at hp
        rw [hp]
        ring
      · simp only [ite_eq_right hg, mul_zero]
    · have hg : gcd (row j) (row k) ≠ D := fun he => hk (he ▸ gcd_dvd_right _ _)
      simp only [sexticGcdTerm, ite_eq_right hg, ite_eq_right hk, mul_zero]
      split_ifs <;> simp
  · have hg : gcd (row j) (row k) ≠ D := fun he => hj (he ▸ gcd_dvd_left _ _)
    simp only [sexticGcdTerm, ite_eq_right hg, ite_eq_right hj, zero_mul]
    split_ifs <;> simp

/-- A common divisor label set, fixed before the two rows are summed. -/
def rowDivisorPool {R : Type*} [Fintype R] (row : R → Ideal O) : Finset (Ideal O) :=
  Finset.univ.biUnion (fun j => idealDivisors (row j))

theorem coprime_indicator_common_divisors {R : Type*} [Fintype R]
    (row : R → Ideal O) (hn : ∀ j, row j ≠ 0) (j k : R) :
    (if IsCoprime (row j) (row k) then (1 : ℂ) else 0) =
      ∑ e ∈ rowDivisorPool row,
        if e ∣ row j ∧ e ∣ row k then (UniqueFactorizationMonoid.moebius e : ℂ) else 0 := by
  rw [CenteredMomentMask.ideal_coprime_mobius (row j) (row k) (hn k)]
  have hs : idealDivisors (row k) ⊆ rowDivisorPool row := by
    intro e he
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, he⟩
  symm
  calc
    _ = ∑ e ∈ idealDivisors (row k),
        if e ∣ row j ∧ e ∣ row k then (UniqueFactorizationMonoid.moebius e : ℂ) else 0 := by
      symm
      apply Finset.sum_subset hs
      intro e he hnot
      have hnd : ¬ e ∣ row k := fun hd => hnot ((mem_idealDivisors (hn k)).2 hd)
      simp only [hnd, and_false, ite_false]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e he
      simp only [(mem_idealDivisors (hn k)).1 he, and_true]

/-- Exact Möbius expansion for ANY signed pair kernel and independent arrays.
This identity precedes, and licenses, the divisor Cauchy estimate. -/
theorem coprime_bilinear_common_divisors {R : Type*} [Fintype R]
    (row : R → Ideal O) (hn : ∀ j, row j ≠ 0) (v : R → R → ℂ) :
    (∑ j, ∑ k, if IsCoprime (row j) (row k) then v j k else 0) =
      ∑ e ∈ rowDivisorPool row, (UniqueFactorizationMonoid.moebius e : ℂ) *
        ∑ j, ∑ k, if e ∣ row j ∧ e ∣ row k then v j k else 0 := by
  have hp (j k : R) : (if IsCoprime (row j) (row k) then v j k else 0) =
      ∑ e ∈ rowDivisorPool row,
        (UniqueFactorizationMonoid.moebius e : ℂ) *
          (if e ∣ row j ∧ e ∣ row k then v j k else 0) := by
    calc
      _ = (if IsCoprime (row j) (row k) then (1 : ℂ) else 0) * v j k := by split_ifs <;> simp
      _ = _ := by
        rw [coprime_indicator_common_divisors row hn, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro e he
        split_ifs <;> simp
  simp_rw [hp]
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := rowDivisorPool row)]
  simp only [Finset.mul_sum]



/-- The descendant row family is fixed before either pair index or source. -/
def quotientSelectedFamily {R : Type*} [Fintype R]
    (row : R → Ideal O) (D : Ideal O) : Finset (Ideal O) :=
  (Finset.univ.filter fun j => D ∣ row j).image (fun j => idealQuotient D (row j))

theorem quotientSelectedFamily_admissible {R : Type*} [Fintype R]
    (row : R → Ideal O) (hrow : ∀ j, Admissible (row j)) (D : Ideal O) :
    ∀ I ∈ quotientSelectedFamily row D, Admissible I := by
  intro I hI
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hI
  exact admissible_idealQuotient (hrow j) (Finset.mem_filter.mp hj).2

theorem mem_quotientSelectedFamily {R : Type*} [Fintype R]
    (row : R → Ideal O) (D : Ideal O) (j : R) (hj : D ∣ row j) :
    idealQuotient D (row j) ∈ quotientSelectedFamily row D :=
  Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩

/-- The original row pair, with its original bad-place mask, is transformed
using one common descendant family. Full-mod36 inheritance is proved above,
not an additional pairwise hypothesis on the descendants. -/
theorem selected_gcd_pair_poisson {R : Type*} [Fintype R]
    (row : R → Ideal O) (hrow : ∀ j, Admissible (row j))
    (hmod : ∀ j k, primaryGenerator (row j) - primaryGenerator (row k) ∈
      (Ideal.span {(36 : O)} : Ideal O))
    (D : Ideal O) (j k : R) (hgcd : gcd (row j) (row k) = D)
    (W : 𝓢(ℝ, ℂ)) (L : ℝ) (hL : 0 < L) :
    (∑' z : O, rowCoprimeMask badPrime Finset.univ z *
      primitivePair (row j) (row k) z * W (‖eisEmbedding z‖^2/L)) =
      ((L : ℂ) / (Real.sqrt
        ((Ideal.absNorm (idealQuotient D (row j)) : ℝ) *
          (Ideal.absNorm (idealQuotient D (row k)) : ℝ)) : ℂ) *
        MixedCrossSeparation.quadraticRayPair
          (residue (primaryGenerator (idealQuotient D (row k))))
          (residue (primaryGenerator (idealQuotient D (row k)))) *
        admissibleUnaryGauss (quotientSelectedFamily row D)
          (quotientSelectedFamily_admissible row hrow D) (idealQuotient D (row j)) 1 *
        admissibleUnaryGauss (quotientSelectedFamily row D)
          (quotientSelectedFamily_admissible row hrow D) (idealQuotient D (row k)) 5) *
      maskedPairDual (fun P : gcdMaskPrimes D => P.val) Finset.univ
        (idealQuotient D (row j)) (idealQuotient D (row k)) W L := by
  have hj : D ∣ row j := hgcd ▸ gcd_dvd_left _ _
  have hk : D ∣ row k := hgcd ▸ gcd_dvd_right _ _
  have hD := admissible_of_dvd (hrow j) hj
  have hp := admissible_shared_masked_pair_poisson D hD
    (quotientSelectedFamily row D) (quotientSelectedFamily_admissible row hrow D)
    (idealQuotient D (row j)) (idealQuotient D (row k))
    (mem_quotientSelectedFamily row D j hj) (mem_quotientSelectedFamily row D k hk)
    ((gcd_eq_iff_quotient_coprime D _ _ hD.1 hj hk).mp hgcd)
    (primaryQuotient_congruent_mod36 D _ _ (hrow j) hj hk (hmod j k))
    (residue (primaryGenerator (idealQuotient D (row k)))) rfl W L hL
  simpa only [idealQuotient_mul hj, idealQuotient_mul hk] using hp

/-- Non-diagonal original pairs have no zero-frequency term, even after
shared-row removal. The diagonal remains an explicit separate contribution. -/
theorem selected_gcd_pair_zero_frequency {R : Type*} [Fintype R]
    (row : R → Ideal O) (hrow : ∀ j, Admissible (row j))
    (D : Ideal O) (j k : R) (hj : D ∣ row j) (hk : D ∣ row k)
    (hne : row j ≠ row k) :
    primitivePair (idealQuotient D (row j)) (idealQuotient D (row k)) 0 = 0 := by
  obtain hi | hi := residual_pair_nontrivial D _ _ hj hk hne
  · unfold primitivePair
    rw [admissibleIdealRow_zero (quotientSelectedFamily row D)
      (quotientSelectedFamily_admissible row hrow D) _
      (mem_quotientSelectedFamily row D j hj) hi, zero_mul]
  · unfold primitivePair
    rw [admissibleIdealRow_zero (quotientSelectedFamily row D)
      (quotientSelectedFamily_admissible row hrow D) _
      (mem_quotientSelectedFamily row D k hk) hi, star_zero, mul_zero]

/-- Fixed positive Schwartz majorant of an arbitrary finite ordinary-source
selection. The larger set can contain every ideal in the support of the bump. -/
def selectedSmoothEnergy (rows : Finset O) (sources : Finset (Ideal O))
    (a : rows → ℂ) (L : ℝ) : ℝ :=
  ∑ I : sources, QuadraticInitialBound.sieveBump ((Ideal.absNorm I.val : ℝ)/L) *
    ‖∑ r : rows, idealRowHom r.val I.val * a r‖^2

theorem selectedDualEnergy_le_smooth (rows : Finset O)
    (sources larger : Finset (Ideal O)) (a : rows → ℂ) (L : ℝ) (hL : 0 < L)
    (hsub : sources ⊆ larger) (hN : ∀ I ∈ sources, (Ideal.absNorm I : ℝ) ≤ L) :
    selectedDualEnergy rows sources a ≤ selectedSmoothEnergy rows larger a L := by
  unfold selectedDualEnergy selectedMatrix selectedSmoothEnergy
  rw [Finset.sum_coe_sort sources (fun I => ‖∑ r : rows, idealRowHom r.val I * a r‖^2),
    Finset.sum_coe_sort larger (fun I => QuadraticInitialBound.sieveBump ((Ideal.absNorm I : ℝ)/L) *
      ‖∑ r : rows, idealRowHom r.val I * a r‖^2)]
  calc
    _ = ∑ I ∈ sources, QuadraticInitialBound.sieveBump ((Ideal.absNorm I : ℝ)/L) *
        ‖∑ r : rows, idealRowHom r.val I * a r‖^2 := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [QuadraticInitialBound.sieveBump_eq_one
        (div_nonneg (Nat.cast_nonneg _) hL.le) ((div_le_one hL).mpr (hN I hI)), one_mul]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun I hI hnot =>
      mul_nonneg QuadraticInitialBound.sieveBump.nonneg (sq_nonneg _))

/-- Exact orientation of the selected norm's Gram matrix, with arbitrary dual
coefficients and natural zeros. Only the finite reciprocity ray is needed. -/
theorem selected_energy_pair_expansion (rows : Finset O) (a : rows → ℂ)
    (hr : ∀ r : rows, Supported (Ideal.span {r.val}))
    (hp : ∀ r : rows, lambda^2 ∣ r.val - 1)
    (hray : ∀ r s : rows, residue r.val = residue s.val)
    (H : Ideal O) (hH : Supported H) :
    ((‖∑ r : rows, idealRowHom r.val H * a r‖^2 : ℝ) : ℂ) =
      ∑ r : rows, ∑ s : rows, a r * star (a s) *
        primitivePair (Ideal.span {r.val}) (Ideal.span {s.val}) (primaryGenerator H) := by
  have hspec := primaryGenerator_spec H (supported_primaryGenerator_ne_zero H hH)
  rw [CoprimeSieveOperator.square_norm_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  have he := same_ray_pair_orientation r.val s.val (primaryGenerator H)
    (hp r) (hp s) hspec.2 (hr r) (hr s) (hspec.1.symm ▸ hH) (hray r s)
  rw [hspec.1] at he
  unfold primitivePair
  rw [← he, star_mul]
  ring


/-- The subset-of-primes expansion is exactly the ordinary ideal-divisor
expansion. The generator of a bad divisor is retained, with its true norm. -/
theorem maskedPairDual_eq_idealDivisors (D I J : Ideal O)
    (W : 𝓢(ℝ, ℂ)) (L : ℝ) :
    maskedPairDual (fun P : gcdMaskPrimes D => P.val) Finset.univ I J W L =
      ∑ e ∈ idealDivisors (commonMaskIdeal D),
        ((UniqueFactorizationMonoid.moebius e : ℂ) * primitivePair I J (idealGenerator e) /
          (Ideal.absNorm e : ℂ)) *
        ∑' h : O, star (primitivePair I J h) * paperRadialFourier W
          (L * ‖eisEmbedding h‖^2 /
            ((Ideal.absNorm e : ℝ) * ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ)))) := by
  unfold maskedPairDual primeSubsetGenerator
  simp_rw [idealGenerator_norm_sq, Complex.ofReal_natCast]
  exact commonMask_subset_sum_eq_divisors D (fun e =>
    ((UniqueFactorizationMonoid.moebius e : ℂ) * primitivePair I J (idealGenerator e) /
      (Ideal.absNorm e : ℂ)) * ∑' h : O, star (primitivePair I J h) *
      paperRadialFourier W (L * ‖eisEmbedding h‖^2 /
        ((Ideal.absNorm e : ℝ) * ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ)))))

/-- Inserting any fixed ideal into every source multiplies each row's dual
coefficient by its actual bounded character. Bad factors are NOT discarded. -/
theorem selectedNorm_mul_sources_le (rows : Finset O) (sources : Finset (Ideal O))
    (d : Ideal O) (hd : d ≠ 0) :
    selectedNorm rows (sources.image (fun I => d * I)) ≤ selectedNorm rows sources := by
  apply selectedNorm_le_of_energy _ _ _ (sq_nonneg _)
  intro a
  let c : rows → ℂ := fun r => idealRowHom r.val d * a r
  have he : selectedDualEnergy rows (sources.image (fun I => d * I)) a =
      selectedDualEnergy rows sources c := by
    unfold selectedDualEnergy selectedMatrix
    rw [Finset.sum_coe_sort (sources.image (fun I => d * I))
      (fun I => ‖∑ r : rows, idealRowHom r.val I * a r‖^2),
      Finset.sum_coe_sort sources (fun I => ‖∑ r : rows, idealRowHom r.val I * c r‖^2),
      Finset.sum_image (fun I hI J hJ he => mul_left_cancel₀ hd he)]
    apply Finset.sum_congr rfl
    intro I hI
    congr 2
    apply Finset.sum_congr rfl
    intro r hr
    simp only [map_mul, c]
    ring
  rw [he]
  apply (selectedDualEnergy_le rows sources c).trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro r hr
  have hc : ‖c r‖ ≤ ‖a r‖ := by
    dsimp only [c]
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (idealRowHom_norm _ _)
  exact pow_le_pow_left₀ (norm_nonneg _) hc 2

private theorem sum_biUnion_nonneg_le {T U : Type*} [DecidableEq U]
    (labels : Finset T) (S : T → Finset U) (f : U → ℝ) (hf : ∀ u, 0 ≤ f u) :
    ∑ u ∈ labels.biUnion S, f u ≤ ∑ t ∈ labels, ∑ u ∈ S t, f u := by
  induction labels using Finset.induction_on with
  | empty => simp
  | @insert t ts ht ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ht]
    have hh := Finset.sum_union_inter (s₁ := S t) (s₂ := ts.biUnion S) (f := f)
    have hn : 0 ≤ ∑ u ∈ S t ∩ ts.biUnion S, f u := Finset.sum_nonneg fun u _ => hf u
    linarith

/-- A finite union of source sectors costs their summed operator bounds.
This remains true with overlap, since the source energies are nonnegative. -/
theorem selectedNorm_sources_biUnion_le {T : Type*}
    (rows : Finset O) (labels : Finset T) (sources : T → Finset (Ideal O)) :
    selectedNorm rows (labels.biUnion sources) ≤ ∑ t ∈ labels, selectedNorm rows (sources t) := by
  apply selectedNorm_le_of_energy _ _ _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  intro a
  unfold selectedDualEnergy selectedMatrix
  rw [Finset.sum_coe_sort (labels.biUnion sources)
    (fun I => ‖∑ r : rows, idealRowHom r.val I * a r‖^2)]
  calc
    _ ≤ ∑ t ∈ labels, ∑ I ∈ sources t, ‖∑ r : rows, idealRowHom r.val I * a r‖^2 :=
      sum_biUnion_nonneg_le labels sources _ (fun I => sq_nonneg _)
    _ ≤ ∑ t ∈ labels, selectedNorm rows (sources t) * ∑ r, ‖a r‖^2 := by
      apply Finset.sum_le_sum
      intro t ht
      rw [← Finset.sum_coe_sort (sources t)
        (fun I => ‖∑ r : rows, idealRowHom r.val I * a r‖^2)]
      exact selectedDualEnergy_le rows (sources t) a
    _ = _ := (Finset.sum_mul ..).symm


theorem selectedNorm_erase_zero (rows : Finset O) (sources : Finset (Ideal O)) :
    selectedNorm rows (sources.erase 0) = selectedNorm rows sources := by
  apply le_antisymm (selectedNorm_mono_sources rows (Finset.erase_subset _ _))
  apply selectedNorm_le_of_energy _ _ _ (sq_nonneg _)
  intro a
  have he : selectedDualEnergy rows sources a = selectedDualEnergy rows (sources.erase 0) a := by
    unfold selectedDualEnergy selectedMatrix
    rw [Finset.sum_coe_sort sources (fun I => ‖∑ r : rows, idealRowHom r.val I * a r‖^2),
      Finset.sum_coe_sort (sources.erase 0) (fun I => ‖∑ r : rows, idealRowHom r.val I * a r‖^2)]
    symm
    apply Finset.sum_subset (Finset.erase_subset _ _)
    intro I hI hn
    have hz : I = 0 := by simpa only [Finset.mem_erase, hI, and_true, not_not] using hn
    simp only [hz, map_zero, zero_mul, Finset.sum_const_zero, norm_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  rw [he]
  exact selectedDualEnergy_le rows (sources.erase 0) a

/-- Literal nonzero-frequency pair kernel after freezing the source-mask
ideal generator and the bad-frequency factor. -/
def selectedPhysicalPairKernel
    (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (W : 𝓢(ℝ, ℂ)) (L : ℝ) (d b : O) (H : Ideal O) (r s : O) : ℂ :=
  ((L / (‖eisEmbedding d‖^2 * Real.sqrt
    ((Ideal.absNorm (Ideal.span {r}) : ℝ) * (Ideal.absNorm (Ideal.span {s}) : ℝ)))) : ℝ) *
    (admissibleUnaryGauss F hF (Ideal.span {r}) 1 *
      admissibleUnaryGauss F hF (Ideal.span {s}) 5 *
      primitivePair (Ideal.span {r}) (Ideal.span {s}) d *
      star (primitivePair (Ideal.span {r}) (Ideal.span {s}) (b * primaryGenerator H))) *
    paperRadialFourier W (L * ‖eisEmbedding (b * primaryGenerator H)‖^2 /
      (‖eisEmbedding d‖^2 * ((Ideal.absNorm (Ideal.span {r}) : ℝ) *
        (Ideal.absNorm (Ideal.span {s}) : ℝ))))

def selectedCoprimePhysicalPacket
    (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (rows : Finset O) (sources : Finset (Ideal O))
    (a c : rows → ℂ) (w : sources → ℂ)
    (W : 𝓢(ℝ, ℂ)) (L : ℝ) (d b : O) : ℂ :=
  ∑ H : sources, ∑ r : rows, ∑ s : rows,
    if IsCoprime (Ideal.span {r.val}) (Ideal.span {s.val}) then
      w H * a r * c s * selectedPhysicalPairKernel F hF W L d b H.val r.val s.val else 0

/-- The exact coprime packet is the divisor-labelled quadform already bounded
in `SourceReflection`; Möbius expansion occurs before either dual norm. -/
theorem selectedCoprimePhysicalPacket_eq
    (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (rows : Finset O) (sources : Finset (Ideal O)) (hn : ∀ r : rows, r.val ≠ 0)
    (a c : rows → ℂ) (w : sources → ℂ)
    (W : 𝓢(ℝ, ℂ)) (L : ℝ) (d b : O) :
    selectedCoprimePhysicalPacket F hF rows sources a c w W L d b =
      ∑ u : rowDivisorPool (fun r : rows => Ideal.span {r.val}) × sources × rows × rows,
        ((L / (‖eisEmbedding d‖ ^ 2 * Real.sqrt
          ((Ideal.absNorm (Ideal.span {u.2.2.1.val}) : ℝ) *
            (Ideal.absNorm (Ideal.span {u.2.2.2.val}) : ℝ))) : ℝ) : ℂ) *
        frozenPairQuadCoefficient F hF rows sources
          (rowDivisorPool (fun r : rows => Ideal.span {r.val})) a c w
          (fun e => (UniqueFactorizationMonoid.moebius e.val : ℂ)) d b u *
        paperRadialFourier W (L * ‖eisEmbedding (b * primaryGenerator u.2.1.val)‖ ^ 2 /
          (‖eisEmbedding d‖ ^ 2 * ((Ideal.absNorm (Ideal.span {u.2.2.1.val}) : ℝ) *
            (Ideal.absNorm (Ideal.span {u.2.2.2.val}) : ℝ)))) := by
  let row := fun r : rows => (Ideal.span {r.val} : Ideal O)
  have hr : ∀ r, row r ≠ 0 := fun r => Ideal.span_singleton_eq_bot.not.mpr (hn r)
  unfold selectedCoprimePhysicalPacket
  conv_lhs =>
    arg 2
    ext H
    rw [coprime_bilinear_common_divisors (fun r : rows => Ideal.span {r.val}) hr
      (fun r s => w H * a r * c s * selectedPhysicalPairKernel F hF W L d b H.val r.val s.val)]
  simp only [Fintype.sum_prod_type]
  conv_lhs =>
    arg 2
    ext H
    rw [← Finset.sum_coe_sort (rowDivisorPool row) (fun e =>
      (UniqueFactorizationMonoid.moebius e : ℂ) * ∑ r : rows, ∑ s : rows,
        if e ∣ Ideal.span {r.val} ∧ e ∣ Ideal.span {s.val} then
          w H * a r * c s * selectedPhysicalPairKernel F hF W L d b H.val r.val s.val else 0)]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro H hH
  apply Finset.sum_congr rfl
  intro e he
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  unfold frozenPairQuadCoefficient selectedPhysicalPairKernel
  dsimp only
  split_ifs <;> ring

/-- Closed finite reflection bound for the actual coprime, masked, frozen
physical packet. Constants are uniform before sets, masks and both vectors. -/
theorem selected_coprime_physical_bound (W : 𝓢(ℝ, ℂ)) (decay : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
        (rows : Finset O) (sources : Finset (Ideal O))
        (_hrows : ∀ r : rows, Ideal.span {r.val} ∈ F)
        (_hn : ∀ r : rows, r.val ≠ 0)
        (_hp : ∀ r : rows, lambda^2 ∣ r.val - 1)
        (_hmod : ∀ r s : rows, r.val-s.val ∈ (Ideal.span {(36 : O)} : Ideal O))
        (_hsource : ∀ H : sources, Supported H.val)
        (a c : rows → ℂ) (w : sources → ℂ) (d b : O)
        (_hd : d ≠ 0) (_hb : b ≠ 0) (L B Y ε : ℝ)
        (_hL : 0 < L) (_hB : 0 < B) (_hY : 0 < Y) (hε : 0 < ε)
        (_hrowNorm : ∀ r : rows, (Ideal.absNorm (Ideal.span {r.val}) : ℝ) ∈ Set.Icc B (2*B))
        (_hsourceNorm : ∀ H : sources, (Ideal.absNorm H.val : ℝ) ∈ Set.Icc Y (2*Y))
        (_hw : ∀ H, ‖w H‖ ≤ 1),
      ‖selectedCoprimePhysicalPacket F hF rows sources a c w W L d b‖ ≤
        (L / (‖eisEmbedding d‖^2 * B)) *
          (C / (1 + frozenPhysicalScale L B Y d b)^decay) * selectedNorm rows sources *
          (idealDivisorConstant ε hε * (2*B)^ε) *
          Real.sqrt (∑ r, ‖a r‖^2) * Real.sqrt (∑ r, ‖c r‖^2) := by
  obtain ⟨C, hC, hc⟩ := frozen_pair_physical_bound W decay
  refine ⟨C, hC, ?_⟩
  intro F hF rows sources hrows hn hp hmod hsource a c w d b hd hb L B Y ε hL hB hY hε hrowNorm hsourceNorm hw
  rw [selectedCoprimePhysicalPacket_eq F hF rows sources hn]
  apply hc F hF rows sources (rowDivisorPool (fun r : rows => Ideal.span {r.val}))
    hrows hn hp hmod hsource a c w (fun e => (UniqueFactorizationMonoid.moebius e.val : ℂ))
    d b hd hb L B Y ε hL hB hY hε hrowNorm hsourceNorm hw
  intro e
  unfold UniqueFactorizationMonoid.moebius
  split_ifs <;> simp


/-- Exact ideal-source dyadic decomposition with the original common mask. -/
theorem selectedCoprimePhysicalPacket_dyads
    (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (rows : Finset O) (sources : Finset (Ideal O)) (a c : rows → ℂ)
    (w : Ideal O → ℂ) (W : 𝓢(ℝ, ℂ)) (L T : ℝ) (d b : O) :
    selectedCoprimePhysicalPacket F hF rows sources a c (fun H => w H.val) W L d b =
      ∑ j : Fin (columnDyadicLength T + 1),
        selectedCoprimePhysicalPacket F hF rows (divisorDyadicBin sources T j)
          a c (fun H => w H.val) W L d b := by
  unfold selectedCoprimePhysicalPacket
  let f := fun H : Ideal O => ∑ r : rows, ∑ s : rows,
    if IsCoprime (Ideal.span {r.val}) (Ideal.span {s.val}) then
      w H * a r * c s * selectedPhysicalPairKernel F hF W L d b H r.val s.val else 0
  change (∑ H : sources, f H.val) =
    ∑ j : Fin (columnDyadicLength T + 1), ∑ H : divisorDyadicBin sources T j, f H.val
  simp_rw [Finset.sum_coe_sort]
  exact sum_divisorDyadicBins sources T f

/-- Summed finite coprime reflection, for ALL supported ordinary ideals in a
bounded source set, with its original bounded common mask and two independent
dual vectors. No source-squarefree projection and no unproved norm bound. -/
theorem selected_coprime_finite_reflection (W : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
        (rows : Finset O) (sources : Finset (Ideal O))
        (_hrows : ∀ r : rows, Ideal.span {r.val} ∈ F)
        (_hn : ∀ r : rows, r.val ≠ 0)
        (_hp : ∀ r : rows, lambda^2 ∣ r.val - 1)
        (_hmod : ∀ r s : rows, r.val-s.val ∈ (Ideal.span {(36 : O)} : Ideal O))
        (_hsource : ∀ H ∈ sources, Supported H)
        (a c : rows → ℂ) (w : Ideal O → ℂ) (d b : O)
        (_hd : d ≠ 0) (_hb : b ≠ 0) (L B T ε : ℝ)
        (_hL : 0 < L) (_hB : 0 < B) (hε : 0 < ε)
        (_hrowNorm : ∀ r : rows, (Ideal.absNorm (Ideal.span {r.val}) : ℝ) ∈ Set.Icc B (2*B))
        (_hsourceNorm : ∀ H ∈ sources, (Ideal.absNorm H : ℝ) ≤ T)
        (_hw : ∀ H ∈ sources, ‖w H‖ ≤ 1),
      ‖selectedCoprimePhysicalPacket F hF rows sources a c (fun H => w H.val) W L d b‖ ≤
        (columnDyadicLength T + 1 : ℕ) *
          ((L / (‖eisEmbedding d‖^2 * B)) * C * selectedNorm rows sources *
            (idealDivisorConstant ε hε * (2*B)^ε) *
            Real.sqrt (∑ r, ‖a r‖^2) * Real.sqrt (∑ r, ‖c r‖^2)) := by
  obtain ⟨C, hC, hc⟩ := selected_coprime_physical_bound W 0
  refine ⟨C, hC, ?_⟩
  intro F hF rows sources hrows hn hp hmod hsource a c w d b hd hb L B T ε hL hB hε hrowNorm hsourceNorm hw
  have hsourceBounds (H : Ideal O) (hH : H ∈ sources) :
      1 ≤ (Ideal.absNorm H : ℝ) ∧ (Ideal.absNorm H : ℝ) ≤ T := by
    refine ⟨?_, hsourceNorm H hH⟩
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (hsource H hH).1)
  have hlocal (j : Fin (columnDyadicLength T + 1)) :
      ‖selectedCoprimePhysicalPacket F hF rows (divisorDyadicBin sources T j)
        a c (fun H => w H.val) W L d b‖ ≤
        (L / (‖eisEmbedding d‖^2 * B)) * C * selectedNorm rows sources *
          (idealDivisorConstant ε hε * (2*B)^ε) *
          Real.sqrt (∑ r, ‖a r‖^2) * Real.sqrt (∑ r, ‖c r‖^2) := by
    have hh := hc F hF rows (divisorDyadicBin sources T j) hrows hn hp hmod
      (fun H => hsource H.val (Finset.mem_filter.mp H.property).1)
      a c (fun H => w H.val) d b hd hb L B (divisorDyadicScale j.val) ε hL hB
      (lt_of_lt_of_le (by norm_num) (divisorDyadicScale_ge_one j.val)) hε hrowNorm
      (fun H => divisorDyadicBin_bounds sources T hsourceBounds j H.val H.property)
      (fun H => hw H.val (Finset.mem_filter.mp H.property).1)
    simp only [pow_zero, div_one] at hh
    apply hh.trans
    have hm := selectedNorm_mono_sources rows (Finset.filter_subset
      (fun H => divisorDyadicLabel T H = j) sources)
    have hf : 0 ≤ (L / (‖eisEmbedding d‖^2 * B)) * C := by positivity
    have hg : 0 ≤ idealDivisorConstant ε hε * (2*B)^ε :=
      mul_nonneg (idealDivisorConstant_pos ε hε).le (Real.rpow_nonneg (by positivity) ε)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hf) hg)
        (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  rw [selectedCoprimePhysicalPacket_dyads F hF rows sources a c w W L T d b]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _j : Fin (columnDyadicLength T + 1),
        (L / (‖eisEmbedding d‖^2 * B)) * C * selectedNorm rows sources *
          (idealDivisorConstant ε hε * (2*B)^ε) *
          Real.sqrt (∑ r, ‖a r‖^2) * Real.sqrt (∑ r, ‖c r‖^2) :=
      Finset.sum_le_sum fun j _ => hlocal j
    _ = _ := by simp


/-- Actual physical kernel at a raw Eisenstein Fourier frequency. -/
def selectedRawPhysicalPairKernel
    (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (W : 𝓢(ℝ, ℂ)) (L : ℝ) (d h : O) (r s : O) : ℂ :=
  ((L / (‖eisEmbedding d‖^2 * Real.sqrt
    ((Ideal.absNorm (Ideal.span {r}) : ℝ) * (Ideal.absNorm (Ideal.span {s}) : ℝ)))) : ℝ) *
    (admissibleUnaryGauss F hF (Ideal.span {r}) 1 *
      admissibleUnaryGauss F hF (Ideal.span {s}) 5 *
      primitivePair (Ideal.span {r}) (Ideal.span {s}) d *
      star (primitivePair (Ideal.span {r}) (Ideal.span {s}) h)) *
    paperRadialFourier W (L * ‖eisEmbedding h‖^2 /
      (‖eisEmbedding d‖^2 * ((Ideal.absNorm (Ideal.span {r}) : ℝ) *
        (Ideal.absNorm (Ideal.span {s}) : ℝ))))

def selectedRawCoprimePacket
    (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I) (rows : Finset O)
    (frequencies : Finset BadFrequencySectors.NonzeroFrequency)
    (a c : rows → ℂ) (w : O → ℂ) (W : 𝓢(ℝ, ℂ)) (L : ℝ) (d : O) : ℂ :=
  ∑ h ∈ frequencies, ∑ r : rows, ∑ s : rows,
    if IsCoprime (Ideal.span {r.val}) (Ideal.span {s.val}) then
      w h.val * a r * c s * selectedRawPhysicalPairKernel F hF W L d h.val r.val s.val else 0

def selectedFrequencySources (frequencies : Finset BadFrequencySectors.NonzeroFrequency)
    (k : Oˣ × ℕ × ℕ) : Finset (Ideal O) :=
  (BadFrequencySectors.fiberSources frequencies k).image Subtype.val

def selectedFrequencyPool (frequencies : Finset BadFrequencySectors.NonzeroFrequency)
    (T : ℝ) : Finset (Ideal O) :=
  (BadFrequencySectors.boundedKeys T).biUnion (selectedFrequencySources frequencies)

theorem selectedFrequencySources_supported
    (frequencies : Finset BadFrequencySectors.NonzeroFrequency) (k : Oˣ × ℕ × ℕ)
    (H : Ideal O) (hH : H ∈ selectedFrequencySources frequencies k) : Supported H := by
  obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hH
  exact I.property

theorem selectedFrequencySources_norm_le
    (frequencies : Finset BadFrequencySectors.NonzeroFrequency) (T : ℝ)
    (hT : ∀ h ∈ frequencies, ‖eisEmbedding h.val‖^2 ≤ T) (k : Oˣ × ℕ × ℕ)
    (H : Ideal O) (hH : H ∈ selectedFrequencySources frequencies k) :
    (Ideal.absNorm H : ℝ) ≤ T := by
  obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hH
  have hh := BadFrequencySectors.fiberSource_norm_le frequencies T hT k I hI
  have hb : 1 ≤ (3 : ℝ)^k.2.1 * (4 : ℝ)^k.2.2 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))
  exact (le_mul_of_one_le_left (Nat.cast_nonneg _) hb).trans hh

theorem selectedFrequencyPool_spec
    (frequencies : Finset BadFrequencySectors.NonzeroFrequency) (T : ℝ)
    (hT : ∀ h ∈ frequencies, ‖eisEmbedding h.val‖^2 ≤ T)
    (H : Ideal O) (hH : H ∈ selectedFrequencyPool frequencies T) :
    Supported H ∧ (Ideal.absNorm H : ℝ) ≤ T := by
  obtain ⟨k, hk, hH⟩ := Finset.mem_biUnion.mp hH
  exact ⟨selectedFrequencySources_supported frequencies k H hH,
    selectedFrequencySources_norm_le frequencies T hT k H hH⟩

/-- All raw nonzero frequencies, including every2/3-adic and unit sector,
are present exactly once. The induced ideal-source masks are common. -/
theorem selectedRawCoprimePacket_eq_sectors
    (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I) (rows : Finset O)
    (frequencies : Finset BadFrequencySectors.NonzeroFrequency) (T : ℝ)
    (hT : ∀ h ∈ frequencies, ‖eisEmbedding h.val‖^2 ≤ T)
    (a c : rows → ℂ) (w : O → ℂ) (W : 𝓢(ℝ, ℂ)) (L : ℝ) (d : O) :
    selectedRawCoprimePacket F hF rows frequencies a c w W L d =
      ∑ k ∈ BadFrequencySectors.boundedKeys T,
        selectedCoprimePhysicalPacket F hF rows (selectedFrequencySources frequencies k) a c
          (fun H => w (BadFrequencySectors.keyFactor k * primaryGenerator H.val))
          W L d (BadFrequencySectors.keyFactor k) := by
  unfold selectedRawCoprimePacket
  rw [BadFrequencySectors.sum_by_bounded_sectors frequencies T hT
    (fun h => ∑ r : rows, ∑ s : rows,
      if IsCoprime (Ideal.span {r.val}) (Ideal.span {s.val}) then
        w h * a r * c s * selectedRawPhysicalPairKernel F hF W L d h r.val s.val else 0)]
  apply Finset.sum_congr rfl
  intro k hk
  unfold selectedCoprimePhysicalPacket
  rw [Finset.sum_coe_sort (selectedFrequencySources frequencies k)
    (fun H => ∑ r : rows, ∑ s : rows,
      if IsCoprime (Ideal.span {r.val}) (Ideal.span {s.val}) then
        w (BadFrequencySectors.keyFactor k * primaryGenerator H) * a r * c s *
          selectedPhysicalPairKernel F hF W L d (BadFrequencySectors.keyFactor k) H r.val s.val else 0)]
  unfold selectedFrequencySources
  rw [Finset.sum_image (fun I hI J hJ he => Subtype.val_injective he)]
  rfl

/-- Closed finite reflection for all actual nonzero Fourier frequencies up
to a common cutoff. The only norm on the right is the literal selected norm
on the explicitly constructed ordinary source pool, whose norms are ≤ T. -/
theorem selected_coprime_raw_finite_reflection (W : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
        (rows : Finset O) (frequencies : Finset BadFrequencySectors.NonzeroFrequency)
        (_hrows : ∀ r : rows, Ideal.span {r.val} ∈ F)
        (_hn : ∀ r : rows, r.val ≠ 0)
        (_hp : ∀ r : rows, lambda^2 ∣ r.val - 1)
        (_hmod : ∀ r s : rows, r.val-s.val ∈ (Ideal.span {(36 : O)} : Ideal O))
        (a c : rows → ℂ) (w : O → ℂ) (d : O) (_hd : d ≠ 0)
        (L B T ε : ℝ) (_hL : 0 < L) (_hB : 0 < B) (hε : 0 < ε)
        (_hrowNorm : ∀ r : rows, (Ideal.absNorm (Ideal.span {r.val}) : ℝ) ∈ Set.Icc B (2*B))
        (_hfreqNorm : ∀ h ∈ frequencies, ‖eisEmbedding h.val‖^2 ≤ T)
        (_hw : ∀ h, ‖w h‖ ≤ 1),
      ‖selectedRawCoprimePacket F hF rows frequencies a c w W L d‖ ≤
        ((BadFrequencySectors.boundedKeys T).card : ℝ) * (columnDyadicLength T + 1 : ℕ) *
          ((L / (‖eisEmbedding d‖^2 * B)) * C *
            selectedNorm rows (selectedFrequencyPool frequencies T) *
            (idealDivisorConstant ε hε * (2*B)^ε) *
            Real.sqrt (∑ r, ‖a r‖^2) * Real.sqrt (∑ r, ‖c r‖^2)) := by
  obtain ⟨C, hC, hc⟩ := selected_coprime_finite_reflection W
  refine ⟨C, hC, ?_⟩
  intro F hF rows frequencies hrows hn hp hmod a c w d hd L B T ε hL hB hε hrowNorm hfreqNorm hw
  let V : ℝ := (L / (‖eisEmbedding d‖^2 * B)) * C *
    selectedNorm rows (selectedFrequencyPool frequencies T) *
      (idealDivisorConstant ε hε * (2*B)^ε) *
      Real.sqrt (∑ r, ‖a r‖^2) * Real.sqrt (∑ r, ‖c r‖^2)
  have hlocal (k : Oˣ × ℕ × ℕ) (hk : k ∈ BadFrequencySectors.boundedKeys T) :
      ‖selectedCoprimePhysicalPacket F hF rows (selectedFrequencySources frequencies k) a c
        (fun H => w (BadFrequencySectors.keyFactor k * primaryGenerator H.val))
        W L d (BadFrequencySectors.keyFactor k)‖ ≤ (columnDyadicLength T + 1 : ℕ) * V := by
    have hb : BadFrequencySectors.keyFactor k ≠ 0 :=
      mul_ne_zero (mul_ne_zero k.1.ne_zero
        (pow_ne_zero _ PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero))
        (pow_ne_zero _ (by norm_num))
    have hh := hc F hF rows (selectedFrequencySources frequencies k) hrows hn hp hmod
      (selectedFrequencySources_supported frequencies k) a c
      (fun H => w (BadFrequencySectors.keyFactor k * primaryGenerator H)) d
      (BadFrequencySectors.keyFactor k) hd hb L B T ε hL hB hε hrowNorm
      (selectedFrequencySources_norm_le frequencies T hfreqNorm k) (fun H hH => hw _)
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have hm : selectedNorm rows (selectedFrequencySources frequencies k) ≤
        selectedNorm rows (selectedFrequencyPool frequencies T) :=
      selectedNorm_mono_sources rows (fun H hH => Finset.mem_biUnion.mpr ⟨k, hk, hH⟩)
    have hf : 0 ≤ (L / (‖eisEmbedding d‖^2 * B)) * C := by positivity
    have hg : 0 ≤ idealDivisorConstant ε hε * (2*B)^ε :=
      mul_nonneg (idealDivisorConstant_pos ε hε).le (Real.rpow_nonneg (by positivity) ε)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hf) hg)
        (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  rw [selectedRawCoprimePacket_eq_sectors F hF rows frequencies T hfreqNorm a c w W L d]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k ∈ BadFrequencySectors.boundedKeys T, (columnDyadicLength T + 1 : ℕ) * V :=
      Finset.sum_le_sum hlocal
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, V]; ring


/-- Literal descendant rows obtained from the fixed selected ideal family. -/
def selectedQuotientRows (F : Finset (Ideal O)) (D : Ideal O) : Finset O :=
  (F.filter fun I => D ∣ I).image (fun I => primaryGenerator (idealQuotient D I))

def selectedQuotientMap (F : Finset (Ideal O)) (D : Ideal O)
    (I : F.filter fun I => D ∣ I) : selectedQuotientRows F D :=
  ⟨primaryGenerator (idealQuotient D I.val), Finset.mem_image.mpr ⟨I.val, I.property, rfl⟩⟩

theorem selectedQuotientMap_bijective (F : Finset (Ideal O))
    (hF : ∀ I ∈ F, Admissible I) (D : Ideal O) :
    Function.Bijective (selectedQuotientMap F D) := by
  constructor
  · intro I J he
    have hi := Finset.mem_filter.mp I.property
    have hj := Finset.mem_filter.mp J.property
    have hq := primaryGenerator_inj_on_admissible
      (admissible_idealQuotient (hF I.val hi.1) hi.2)
      (admissible_idealQuotient (hF J.val hj.1) hj.2)
      (congrArg Subtype.val he)
    exact Subtype.ext (idealQuotient_injective_on D hi.2 hj.2 hq)
  · intro z
    obtain ⟨I, hI, he⟩ := Finset.mem_image.mp z.property
    exact ⟨⟨I, hI⟩, Subtype.ext he⟩

def selectedQuotientEquiv (F : Finset (Ideal O))
    (hF : ∀ I ∈ F, Admissible I) (D : Ideal O) :
    (F.filter fun I => D ∣ I) ≃ selectedQuotientRows F D :=
  Equiv.ofBijective (selectedQuotientMap F D) (selectedQuotientMap_bijective F hF D)

def selectedDescendantCoefficient (F : Finset (Ideal O))
    (hF : ∀ I ∈ F, Admissible I) (D : Ideal O) (a : F → ℂ)
    (z : selectedQuotientRows F D) : ℂ :=
  let I := (selectedQuotientEquiv F hF D).symm z
  a ⟨I.val, (Finset.mem_filter.mp I.property).1⟩

/-- Arbitrary dual vectors transport isometrically onto the actual quotient
rows. The mass is the original divisibility mask, with no multiplicity loss. -/
theorem selectedDescendantCoefficient_energy (F : Finset (Ideal O))
    (hF : ∀ I ∈ F, Admissible I) (D : Ideal O) (a : F → ℂ) :
    (∑ z : selectedQuotientRows F D, ‖selectedDescendantCoefficient F hF D a z‖^2) =
      ∑ I : F, if D ∣ I.val then ‖a I‖^2 else 0 := by
  unfold selectedDescendantCoefficient
  dsimp only
  rw [(selectedQuotientEquiv F hF D).symm.sum_comp
    (fun I : F.filter fun I => D ∣ I => ‖a ⟨I.val,(Finset.mem_filter.mp I.property).1⟩‖^2)]
  let f : Ideal O → ℝ := fun I => if h : I ∈ F then ‖a ⟨I,h⟩‖^2 else 0
  have he : (∑ I : F.filter fun I => D ∣ I,
      ‖a ⟨I.val,(Finset.mem_filter.mp I.property).1⟩‖^2) =
      ∑ I : F.filter fun I => D ∣ I, f I.val := by
    apply Finset.sum_congr rfl
    intro I hI
    simp only [f, dite_eq_left (Finset.mem_filter.mp I.property).1]
  rw [he, Finset.sum_coe_sort (F.filter fun I => D ∣ I) f, Finset.sum_filter]
  rw [← Finset.sum_coe_sort F (fun I => if D ∣ I then f I else 0)]
  apply Finset.sum_congr rfl
  intro I hI
  simp only [f, dite_eq_left I.property]

theorem selectedQuotientRows_spec (F : Finset (Ideal O))
    (hF : ∀ I ∈ F, Admissible I) (D : Ideal O) (z : selectedQuotientRows F D) :
    z.val ≠ 0 ∧ lambda^2 ∣ z.val - 1 ∧ Admissible (Ideal.span {z.val}) := by
  obtain ⟨I, hI, he⟩ := Finset.mem_image.mp z.property
  have hq := admissible_idealQuotient (hF I (Finset.mem_filter.mp hI).1)
    (Finset.mem_filter.mp hI).2
  have hn := primaryGenerator_admissible (idealQuotient D I) hq
  have hs := primaryGenerator_spec (idealQuotient D I) hn
  rw [← he]
  exact ⟨hn, hs.2, hs.1.symm ▸ hq⟩

theorem selectedQuotientRows_mod36 (F : Finset (Ideal O))
    (hF : ∀ I ∈ F, Admissible I) (D : Ideal O)
    (hmod : ∀ I ∈ F, ∀ J ∈ F, primaryGenerator I - primaryGenerator J ∈
      (Ideal.span {(36 : O)} : Ideal O)) (z w : selectedQuotientRows F D) :
    z.val-w.val ∈ (Ideal.span {(36 : O)} : Ideal O) := by
  obtain ⟨I, hI, hi⟩ := Finset.mem_image.mp z.property
  obtain ⟨J, hJ, hj⟩ := Finset.mem_image.mp w.property
  rw [← hi, ← hj]
  exact primaryQuotient_congruent_mod36 D I J (hF I (Finset.mem_filter.mp hI).1)
    (Finset.mem_filter.mp hI).2 (Finset.mem_filter.mp hJ).2
    (hmod I (Finset.mem_filter.mp hI).1 J (Finset.mem_filter.mp hJ).1)

theorem selectedQuotientRows_norm (F : Finset (Ideal O))
    (hF : ∀ I ∈ F, Admissible I) (D : Ideal O) (hD : D ≠ 0) (B : ℝ)
    (hN : ∀ I ∈ F, (Ideal.absNorm I : ℝ) ∈ Set.Icc B (2*B))
    (z : selectedQuotientRows F D) :
    (Ideal.absNorm (Ideal.span {z.val}) : ℝ) ∈
      Set.Icc (B/(Ideal.absNorm D : ℝ)) (2*(B/(Ideal.absNorm D : ℝ))) := by
  obtain ⟨I, hI, he⟩ := Finset.mem_image.mp z.property
  have hi := Finset.mem_filter.mp hI
  have hq := admissible_idealQuotient (hF I hi.1) hi.2
  rw [← he, (primaryGenerator_spec _ (primaryGenerator_admissible _ hq)).1,
    idealQuotient_norm_eq D I hD hi.2]
  have hd : 0 ≤ (Ideal.absNorm D : ℝ) := Nat.cast_nonneg _
  refine ⟨div_le_div_of_nonneg_right (hN I hi.1).1 hd, ?_⟩
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right (hN I hi.1).2 hd

/-- Every original selection polynomial is exactly a residual selection
polynomial with common coefficients. This algebraic identity holds for any
power; it makes NO analytic natural-row claim for powers other than±1. -/
theorem selected_word_quotient_identity (D I : Ideal O) (hDI : D ∣ I)
    (sources : Finset (Ideal O)) (α : Ideal O → ℂ) (j : ℕ) :
    (∑ P ∈ sources, α P * (idealRowHom (primaryGenerator I) P)^j) =
      ∑ P ∈ sources, (α P * (idealRowHom (primaryGenerator D) P)^j) *
        (idealRowHom (primaryGenerator (idealQuotient D I)) P)^j := by
  have hi : primaryGenerator I = primaryGenerator D * primaryGenerator (idealQuotient D I) := by
    rw [← primaryGenerator_mul, idealQuotient_mul hDI]
  rw [hi]
  apply Finset.sum_congr rfl
  intro P hP
  rw [idealRowHom_argument_mul, mul_pow, mul_assoc]

theorem selected_word_quotient_coefficient_norm (D P : Ideal O) (α : ℂ) (j : ℕ) :
    ‖α * (idealRowHom (primaryGenerator D) P)^j‖ ≤ ‖α‖ := by
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg _) (idealRowHom_norm _ _))


/-- Original ordinary-ideal pair sum. The support mask belongs to this
supported-source stage; the preceding input-sector reduction restores all ideals. -/
def selectedSupportedPairSource (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (L : ℝ) : ℂ :=
  ∑' H : Ideal O, if Supported H then
    (idealRowHom (primaryGenerator I) H * star (idealRowHom (primaryGenerator J) H)) *
      W ((Ideal.absNorm H : ℝ)/L) else 0

/-- Exact six-unit conversion of the actual selected source pair to the
original bad-masked element source. It retains the diagonal and the unit ideal. -/
theorem selectedSupportedPairSource_eq_element (I J : Ideal O)
    (hI : Admissible I) (hJ : Admissible J)
    (hmod : primaryGenerator I-primaryGenerator J ∈ (Ideal.span {(36 : O)} : Ideal O))
    (W : 𝓢(ℝ, ℂ)) (L : ℝ) (hL : 0 < L) :
    selectedSupportedPairSource I J W L = (6 : ℂ)⁻¹ *
      ∑' z : O, rowCoprimeMask badPrime Finset.univ z * primitivePair I J z *
        W (‖eisEmbedding z‖^2/L) := by
  let mask : Ideal O → ℂ := fun H => if Supported H then 1 else 0
  have hi := primaryGenerator_spec I (primaryGenerator_admissible I hI)
  have hj := primaryGenerator_spec J (primaryGenerator_admissible J hJ)
  have he := masked_actual_pair_mod36 (primaryGenerator I) (primaryGenerator J)
    hi.2 hj.2 (hi.1.symm ▸ admissible_supported hI) (hj.1.symm ▸ admissible_supported hJ)
    hmod mask (fun H hn => ite_eq_right hn) (fun H => by dsimp [mask]; split_ifs <;> simp) W L hL
  have hl : (∑' z : O, if lambda ∣ z then 0 else
      maskedPairRadial (Ideal.span {primaryGenerator I}) (Ideal.span {primaryGenerator J}) mask W L z) =
      ∑' z : O, rowCoprimeMask badPrime Finset.univ z * primitivePair I J z *
        W (‖eisEmbedding z‖^2/L) := by
    apply tsum_congr
    intro z
    rw [badPrime_mask]
    unfold maskedPairRadial mask
    rw [hi.1, hj.1]
    by_cases hs : Supported (Ideal.span {z})
    · have hn := (supported_span_iff z).mp hs
      simp only [hs, hn.1, ite_false, ite_true, one_mul]
    · simp only [hs, ite_false, zero_mul]
      split_ifs <;> rfl
  rw [hl] at he
  have hr : (∑' H : Ideal O, mask H *
      (idealRowHom (primaryGenerator I) H * star (idealRowHom (primaryGenerator J) H)) *
        W ((Ideal.absNorm H : ℝ)/L)) = selectedSupportedPairSource I J W L := by
    unfold selectedSupportedPairSource
    apply tsum_congr
    intro H
    dsimp only [mask]
    split_ifs <;> simp
  rw [hr] at he
  rw [he]
  ring

theorem actual_commonMask_divisor (D e : Ideal O) (hD : Admissible D)
    (he : e ∈ idealDivisors (commonMaskIdeal D)) :
    e ∣ D * (∏ P ∈ fixedBadPrimes, P) := by
  have hd := (mem_idealDivisors (commonMaskIdeal_squarefree D).ne_zero).1 he
  rwa [commonMaskIdeal_eq_fixed_mul D hD, mul_comm] at hd

/-- Outer shared-row and source-mask labels. Both coordinates remain visible
until after Cauchy; in particular no total label count is charged. -/
def sharedDivisorMask {R : Type*} (labels : Finset (Ideal O × Ideal O))
    (bad : Ideal O) (row : R → Ideal O) (e : labels) (j : R) : Prop :=
  e.val.1 ∣ row j ∧ e.val.2 ∣ e.val.1 * bad

theorem sharedDivisorMask_incidence_le {R : Type*}
    (labels : Finset (Ideal O × Ideal O)) (bad : Ideal O) (hb : bad ≠ 0)
    (row : R → Ideal O) (j : R) (hn : row j ≠ 0) :
    (Finset.univ.filter fun e => sharedDivisorMask labels bad row e j).card ≤
      (idealDivisors (row j)).card * (idealDivisors (row j * bad)).card := by
  rw [← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun e : labels => e.val)
  · intro e he
    have hh := (Finset.mem_filter.mp he).2
    exact Finset.mem_product.mpr ⟨(mem_idealDivisors hn).2 hh.1,
      (mem_idealDivisors (mul_ne_zero hn hb)).2
        (dvd_trans hh.2 (mul_dvd_mul hh.1 (dvd_refl bad)))⟩
  · intro e he f hf hef
    exact Subtype.ext hef

def sharedDivisorCost (bad : Ideal O) (B ε : ℝ) (hε : 0 < ε) : ℝ :=
  (idealDivisorConstant ε hε * B^ε) *
    (idealDivisorConstant ε hε * (B * (Ideal.absNorm bad : ℝ))^ε)

theorem sharedDivisorMask_incidence_small_power {R : Type*}
    (labels : Finset (Ideal O × Ideal O)) (bad : Ideal O) (hb : bad ≠ 0)
    (row : R → Ideal O) (j : R) (hn : row j ≠ 0)
    (B ε : ℝ) (hε : 0 < ε) (hN : (Ideal.absNorm (row j) : ℝ) ≤ B) :
    ((Finset.univ.filter fun e => sharedDivisorMask labels bad row e j).card : ℝ) ≤
      sharedDivisorCost bad B ε hε := by
  have hN' : (Ideal.absNorm (row j * bad) : ℝ) ≤ B * (Ideal.absNorm bad : ℝ) := by
    rw [map_mul, Nat.cast_mul]
    exact mul_le_mul_of_nonneg_right hN (Nat.cast_nonneg _)
  have h1 : ((idealDivisors (row j)).card : ℝ) ≤ idealDivisorConstant ε hε * B^ε :=
    (idealDivisorConstant_bound ε hε _ hn).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hN hε.le)
        (idealDivisorConstant_pos ε hε).le)
  have h2 : ((idealDivisors (row j * bad)).card : ℝ) ≤
      idealDivisorConstant ε hε * (B * (Ideal.absNorm bad : ℝ))^ε :=
    (idealDivisorConstant_bound ε hε _ (mul_ne_zero hn hb)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hN' hε.le)
        (idealDivisorConstant_pos ε hε).le)
  calc
    _ ≤ ((idealDivisors (row j)).card : ℝ) * ((idealDivisors (row j * bad)).card : ℝ) := by
      exact_mod_cast sharedDivisorMask_incidence_le labels bad hb row j hn
    _ ≤ _ := mul_le_mul h1 h2 (Nat.cast_nonneg _) ((Nat.cast_nonneg _).trans h1)

/-- The two outer divisor labels cost only two small powers of row height,
for arbitrary independent dual vectors. Fixed bad places are in the constant. -/
theorem sharedDivisor_bilinear_sum_le {R : Type*} [Fintype R]
    (labels : Finset (Ideal O × Ideal O)) (bad : Ideal O) (hb : bad ≠ 0)
    (row : R → Ideal O) (a c : R → ℂ) (v : labels → ℂ)
    (B ε K : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) (hK : 0 ≤ K)
    (hn : ∀ j, row j ≠ 0) (hN : ∀ j, (Ideal.absNorm (row j) : ℝ) ≤ B)
    (hv : ∀ e, ‖v e‖ ≤ K * Real.sqrt (maskedEnergy (sharedDivisorMask labels bad row) a e) *
      Real.sqrt (maskedEnergy (sharedDivisorMask labels bad row) c e)) :
    ‖∑ e, v e‖ ≤ K * sharedDivisorCost bad B ε hε *
      Real.sqrt (∑ j, ‖a j‖^2) * Real.sqrt (∑ j, ‖c j‖^2) := by
  apply coprime_mask_bilinear_sum_le (sharedDivisorMask labels bad row) a c v
    (sharedDivisorCost bad B ε hε) K _ hK _ hv
  · unfold sharedDivisorCost
    exact mul_nonneg
      (mul_nonneg (idealDivisorConstant_pos ε hε).le (Real.rpow_nonneg hB ε))
      (mul_nonneg (idealDivisorConstant_pos ε hε).le
        (Real.rpow_nonneg (mul_nonneg hB (Nat.cast_nonneg _)) ε))
  · intro j
    exact sharedDivisorMask_incidence_small_power labels bad hb row j (hn j) B ε hε (hN j)

end
end Qrh.JointDetector

#print axioms Qrh.JointDetector.primaryQuotient_congruent_mod36
#print axioms Qrh.JointDetector.sexticGcdTerm_eq_quotient
#print axioms Qrh.JointDetector.coprime_bilinear_common_divisors

#print axioms Qrh.JointDetector.sharedDivisor_bilinear_sum_le

#print axioms Qrh.JointDetector.selected_gcd_pair_poisson
#print axioms Qrh.JointDetector.selected_gcd_pair_zero_frequency
#print axioms Qrh.JointDetector.selectedDualEnergy_le_smooth
#print axioms Qrh.JointDetector.selected_energy_pair_expansion

#print axioms Qrh.JointDetector.maskedPairDual_eq_idealDivisors
#print axioms Qrh.JointDetector.selectedNorm_mul_sources_le
#print axioms Qrh.JointDetector.selectedNorm_sources_biUnion_le

#print axioms Qrh.JointDetector.selectedNorm_erase_zero
#print axioms Qrh.JointDetector.selected_coprime_physical_bound

#print axioms Qrh.JointDetector.selected_coprime_finite_reflection

#print axioms Qrh.JointDetector.selected_coprime_raw_finite_reflection

#print axioms Qrh.JointDetector.selectedDescendantCoefficient_energy
#print axioms Qrh.JointDetector.selectedQuotientRows_mod36
#print axioms Qrh.JointDetector.selected_word_quotient_identity

#print axioms Qrh.JointDetector.selectedSupportedPairSource_eq_element
