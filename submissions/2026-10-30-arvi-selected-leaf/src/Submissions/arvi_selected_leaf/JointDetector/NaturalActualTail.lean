/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.arvi_selected_leaf.JointDetector.NaturalPairPackets
import Submissions.arvi_selected_leaf.JointDetector.NaturalTuplePartition
import Submissions.arvi_selected_leaf.JointDetector.NaturalTupleCount
import Submissions.arvi_selected_leaf.JointDetector.NaturalPacketTail

/-! Concrete conductor and puncture bounds for the complete raw packet.
Only the far-frequency complement uses these absolute counts.
-/
namespace Qrh.JointDetector.NaturalActualTail
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open GaussGeneratorTransport FiniteGaussPhase
open IdealMobiusDivisorSum CenteredExceptionalCount
open NaturalSelectedNorm NaturalPairPackets FiveColourIncidence
local notation "O" => ActualEisensteinCubic.O

def badIdeal : Ideal O := ∏ b : Bool, badPrime b
def badNorm : ℝ := Ideal.absNorm badIdeal
def maskIdeal (F : Finset ColourTuple) (E : Finset (SourceMaskIndex F)) : Ideal O :=
  ∏ i ∈ E, sourceMaskPrime F i
def primitiveIdeal (F : Finset ColourTuple) (c d : ColourTuple) : Ideal O :=
  ∏ i : primitivePrimes F c d, i.val.val

theorem badPrime_ne_zero (b : Bool) : badPrime b ≠ 0 := by
  cases b with
  | false => simpa only [badPrime,Bool.false_eq_true,ite_false,Ideal.zero_eq_bot] using
      Ideal.span_singleton_eq_bot.not.mpr PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero
  | true => simpa only [badPrime,ite_true,Ideal.zero_eq_bot] using
      Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (2:O) ≠ 0)

theorem badIdeal_ne_zero : badIdeal ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun b _ => badPrime_ne_zero b)

theorem badNorm_pos : 0 < badNorm := norm_pos badIdeal_ne_zero

theorem pool_prime (F : Finset ColourTuple) (i : PrimeIndex F) : Prime i.val := by
  obtain ⟨I,hI,hi⟩ := mem_primePool_iff.mp i.property
  exact UniqueFactorizationMonoid.prime_of_normalized_factor i.val hi

theorem mask_prime (F : Finset ColourTuple) (i : SourceMaskIndex F) :
    Prime (sourceMaskPrime F i) := by
  cases i with
  | inl b => exact Ideal.prime_of_isPrime (badPrime_ne_zero b) inferInstance
  | inr i => exact pool_prime F i

theorem maskIdeal_ne_zero (F : Finset ColourTuple) (E : Finset (SourceMaskIndex F)) :
    maskIdeal F E ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => (mask_prime F i).ne_zero)

theorem support_prime_dvd_radical (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c : ColourTuple) (hc : c ∈ F)
    (i : PrimeIndex F) (hi : i ∈ tupleSupport F c) :
    i.val ∣ TuplePartition.radical c := by
  obtain ⟨j,hj,hij⟩ := Finset.mem_biUnion.mp hi
  have hd : i.val ∣ c j := by
    rw [mem_idealSupport_iff,Ideal.mem_normalizedFactors_iff (hF c hc j).1] at hij
    exact Ideal.dvd_iff_le.mpr hij.2
  exact hd.trans (Finset.dvd_prod_of_mem (fun j => c j) (Finset.mem_univ j))

theorem positive_in_support (F : Finset ColourTuple) (c : ColourTuple) (i : PrimeIndex F)
    (hi : 0 < colourExponent F c i) : i ∈ tupleSupport F c := by
  by_contra hnot
  rw [colourExponent_outside F c i hnot] at hi
  omega

/-- Every actual source-mask divisor belongs to the original left radical
with the fixed bad-prime product, independent of the right row. -/
theorem mask_support_product_dvd (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) :
    maskIdeal F (sourceMaskSupport F c d) ∣ badIdeal*TuplePartition.radical c := by
  rw [maskIdeal,← Finset.prod_coe_sort]
  apply distinct_prime_product_dvd (fun i : sourceMaskSupport F c d => sourceMaskPrime F i.val)
    (fun i => mask_prime F i.val)
    (fun i j he => Subtype.ext (sourceMaskPrime_injective F hF he))
  intro i
  rcases Finset.mem_union.mp i.property with hb | hg
  · obtain ⟨b,hb,he⟩ := Finset.mem_image.mp hb
    have hd : badPrime b ∣ badIdeal := Finset.dvd_prod_of_mem _ (Finset.mem_univ b)
    simpa only [← he,sourceMaskPrime,Sum.elim_inl] using dvd_mul_of_dvd_left hd (TuplePartition.radical c)
  · obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hg
    have hpos := (Finset.mem_filter.mp hj).2.2
    have hd := support_prime_dvd_radical F hF c hc j (positive_in_support F c j hpos)
    simpa only [← he,sourceMaskPrime,Sum.elim_inr] using dvd_mul_of_dvd_right hd badIdeal

theorem mask_subset_dvd (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F)
    (E : Finset (SourceMaskIndex F)) (hE : E ∈ (sourceMaskSupport F c d).powerset) :
    maskIdeal F E ∣ badIdeal*TuplePartition.radical c :=
  (puncture_subset_divides (sourceMaskPrime F) _ E hE).trans
    (mask_support_product_dvd F hF c d hc)

theorem weighted_norm_le (c : ColourTuple) (hc : ∀ j, Admissible (c j))
    (Y : ℝ) (hY : ((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y) :
    (Ideal.absNorm (weightedIdeal c):ℝ) ≤ Y := by
  have hs : Ideal.span {tupleRow c}=weightedIdeal c := by
    rw [tupleRow_eq_primary]
    exact (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _
      (tuple_weighted_supported c hc))).1
  simpa only [hs] using hY

/-- The entire mixed primitive conductor divides the original weighted pair. -/
theorem primitiveIdeal_dvd (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F) :
    primitiveIdeal F c d ∣ weightedIdeal c*weightedIdeal d := by
  apply distinct_prime_product_dvd (fun i : primitivePrimes F c d => i.val.val)
    (fun i => pool_prime F i.val) (fun i j he => Subtype.ext (Subtype.ext he))
  intro i
  have hne := (Finset.mem_filter.mp i.property).2
  have hn : colourExponent F c i.val+colourExponent F d i.val ≠ 0 := by omega
  have hprod : weightedIdeal c*weightedIdeal d =
      ∏ j : PrimeIndex F, j.val^(colourExponent F c j+colourExponent F d j) := by
    rw [weightedIdeal,weightedIdeal,weightedIdeal_common_pool F hF c hc,
      weightedIdeal_common_pool F hF d hd,← Finset.prod_mul_distrib]
    simp only [pow_add]
  rw [hprod]
  exact (dvd_pow_self _ hn).trans
    (Finset.dvd_prod_of_mem (fun j : PrimeIndex F => j.val^(colourExponent F c j+colourExponent F d j))
      (Finset.mem_univ i.val))

theorem primitiveIdeal_ne_zero (F : Finset ColourTuple) (c d : ColourTuple) :
    primitiveIdeal F c d ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => (pool_prime F i.val).ne_zero)

theorem primitiveElement_norm_sq (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) :
    ‖eisEmbedding (primitiveElement F c d)‖^2=(Ideal.absNorm (primitiveIdeal F c d):ℝ) := by
  simp only [primitiveElement,map_prod,norm_prod]
  rw [← Finset.prod_pow]
  simp only [eisEmbedding_norm_sq_eq_absNorm_span,primitivePrimary_span F hF,
    primitiveIdeal,map_prod,Nat.cast_prod]

theorem primitive_norm_le (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (Y : ℝ) (hY : 1 ≤ Y)
    (hcY : ((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y)
    (hdY : ((Ideal.span {tupleRow d}).absNorm:ℝ) ≤ Y) :
    ‖eisEmbedding (primitiveElement F c d)‖^2 ≤ Y^2 := by
  rw [primitiveElement_norm_sq F hF]
  have hdiv := norm_le_of_dvd (mul_ne_zero (tuple_weighted_supported c (hF c hc)).1
    (tuple_weighted_supported d (hF d hd)).1) (primitiveIdeal_dvd F hF c d hc hd)
  have hmul : ((weightedIdeal c*weightedIdeal d).absNorm:ℝ)=
      (Ideal.absNorm (weightedIdeal c):ℝ)*(Ideal.absNorm (weightedIdeal d):ℝ) := by simp only [map_mul,Nat.cast_mul]
  rw [hmul] at hdiv
  exact hdiv.trans ((mul_le_mul (weighted_norm_le c (hF c hc) Y hcY)
    (weighted_norm_le d (hF d hd) Y hdY) (Nat.cast_nonneg _) (by linarith)).trans_eq (by ring))

theorem badNorm_one_le : 1 ≤ badNorm := by
  change (1:ℝ) ≤ (Ideal.absNorm badIdeal:ℝ)
  have hn : 0 < Ideal.absNorm badIdeal := by
    exact_mod_cast (show (0:ℝ) < (Ideal.absNorm badIdeal:ℝ) from badNorm_pos)
  exact_mod_cast hn

theorem mask_norm_bounds (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F)
    (Y : ℝ) (hcY : ((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y)
    (E : Finset (SourceMaskIndex F)) (hE : E ∈ (sourceMaskSupport F c d).powerset) :
    (Ideal.absNorm (maskIdeal F E):ℝ) ∈ Set.Icc (1:ℝ) (badNorm*Y) := by
  constructor
  · have hn : 0 < Ideal.absNorm (maskIdeal F E) := by
      exact_mod_cast norm_pos (maskIdeal_ne_zero F E)
    exact_mod_cast hn
  · have hdiv := norm_le_of_dvd (mul_ne_zero badIdeal_ne_zero
      (TuplePartition.radical_ne_zero c (hF c hc))) (mask_subset_dvd F hF c d hc E hE)
    have hnrad := (TuplePartition.norms_le_height c (hF c hc) Y hcY).2
    have hmul : ((badIdeal*TuplePartition.radical c).absNorm:ℝ)=
        badNorm*(Ideal.absNorm (TuplePartition.radical c):ℝ) := by
      simp only [map_mul,Nat.cast_mul,badNorm]
    rw [hmul] at hdiv
    exact hdiv.trans (mul_le_mul_of_nonneg_left hnrad badNorm_pos.le)

theorem mask_generator_norm_bounds (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F)
    (Y : ℝ) (hcY : ((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y)
    (E : Finset (SourceMaskIndex F)) (hE : E ∈ (sourceMaskSupport F c d).powerset) :
    ‖eisEmbedding (primeSubsetGenerator (sourceMaskPrime F) E)‖^2 ∈
      Set.Icc (1:ℝ) (badNorm*Y) := by
  rw [primeSubsetGenerator_norm_sq]
  exact mask_norm_bounds F hF c d hc Y hcY E hE

/-- Puncture subsets retain their full support under the actual ideal map. -/
theorem mask_labels_card_le (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F)
    (Y : ℝ) (hY : 1 ≤ Y) (hcY : ((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y) :
    ((sourceMaskSupport F c d).powerset.card:ℝ) ≤ 128*badNorm*Y := by
  let labels := (sourceMaskSupport F c d).powerset
  let ideals := labels.image (maskIdeal F)
  have hinj : Function.Injective (maskIdeal F) :=
    primeSubsetProduct_injective (sourceMaskPrime F) (mask_prime F) (sourceMaskPrime_injective F hF)
  have hcard : ideals.card=labels.card := Finset.card_image_of_injective _ hinj
  have hbounds : ∀ I ∈ ideals, (Ideal.absNorm I:ℝ) ≤ badNorm*Y := by
    intro I hI
    obtain ⟨E,hE,rfl⟩ := Finset.mem_image.mp hI
    exact (mask_norm_bounds F hF c d hc Y hcY E hE).2
  have hn : ∀ I ∈ ideals, I ≠ 0 := by
    intro I hI
    obtain ⟨E,hE,rfl⟩ := Finset.mem_image.mp hI
    exact maskIdeal_ne_zero F E
  have hBY : 1 ≤ badNorm*Y := one_le_mul_of_one_le_of_one_le badNorm_one_le hY
  have hh := DescentFiberCost.finite_ideal_count_real ideals (badNorm*Y) hBY hn hbounds
  rw [hcard] at hh
  simpa only [labels,mul_assoc] using hh

theorem primitive_norm_one_le (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) :
    1 ≤ ‖eisEmbedding (primitiveElement F c d)‖ := by
  have hn : 0 < Ideal.absNorm (primitiveIdeal F c d) := by
    exact_mod_cast norm_pos (primitiveIdeal_ne_zero F c d)
  have hnorm : (1:ℝ) ≤ (Ideal.absNorm (primitiveIdeal F c d):ℝ) := by exact_mod_cast hn
  rw [← primitiveElement_norm_sq F hF] at hnorm
  nlinarith [norm_nonneg (eisEmbedding (primitiveElement F c d))]

theorem primitiveGauss_norm (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple)
    (hc : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hd : Pairwise (fun j k => IsCoprime (d j) (d k))) :
    ‖primitiveGauss F hF c d‖=1 := by
  letI := primitivePrimary_maximal F hF c d
  exact norm_canonicalProductGauss _ _ _ _ (primitivePrimary_odd F hF c d) _
    (fun i => (primitiveExponent_range F c d hc hd i).1.ne')
    (fun i => (primitiveExponent_range F c d hc hd i).2)

theorem primitiveRow_norm_le (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (n : O) :
    ‖primitiveRow F hF c d n‖ ≤ 1 := by
  letI := primitivePrimary_maximal F hF c d
  exact QuadraticInitialBound.finiteSexticRow_norm_le_one _ _ _ _

def packetScale (F : Finset ColourTuple) (c d : ColourTuple) (L : ℝ)
    (E : Finset (SourceMaskIndex F)) : ℝ :=
  L/(‖eisEmbedding (primeSubsetGenerator (sourceMaskPrime F) E)‖^2*
    ‖eisEmbedding (primitiveElement F c d)‖^2)

def packetCoefficient (F : Finset ColourTuple) (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (c d : ColourTuple) (L : ℝ) (E : Finset (SourceMaskIndex F)) (h : O) : ℂ :=
  ((L:ℂ)*primitiveGauss F hF c d/(‖eisEmbedding (primitiveElement F c d)‖:ℂ))*
    (((UniqueFactorizationMonoid.moebius (maskIdeal F E):ℂ)*
      primitiveRow F hF c d (primeSubsetGenerator (sourceMaskPrime F) E)/
      (‖eisEmbedding (primeSubsetGenerator (sourceMaskPrime F) E)‖^2:ℝ))*
      star (primitiveRow F hF c d h))

theorem packetCoefficient_norm_le (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k)))
    (L Y : ℝ) (hL : 0 ≤ L) (hcY : ((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y)
    (E : Finset (SourceMaskIndex F)) (hE : E ∈ (sourceMaskSupport F c d).powerset) (h : O) :
    ‖packetCoefficient F hF c d L E h‖ ≤ L := by
  have hnorm := primitive_norm_one_le F hF c d
  have hnorm0 : 0 < ‖eisEmbedding (primitiveElement F c d)‖ := by linarith
  have hmask := (mask_generator_norm_bounds F hF c d hc Y hcY E hE).1
  have hmask0 : 0 < ‖eisEmbedding (primeSubsetGenerator (sourceMaskPrime F) E)‖^2 := by linarith
  have hpref : ‖(L:ℂ)*primitiveGauss F hF c d/
      (‖eisEmbedding (primitiveElement F c d)‖:ℂ)‖ ≤ L := by
    rw [norm_div,norm_mul,primitiveGauss_norm F hF c d hcPair hdPair,
      Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg hL,abs_of_nonneg (norm_nonneg _),mul_one]
    exact (div_le_iff₀ hnorm0).mpr (le_mul_of_one_le_right hL hnorm)
  have hnum : ‖(UniqueFactorizationMonoid.moebius (maskIdeal F E):ℂ)*
      primitiveRow F hF c d (primeSubsetGenerator (sourceMaskPrime F) E)‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul (QuadraticInitialBound.norm_ideal_moebius_le_one _)
      (primitiveRow_norm_le F hF c d _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hlabel : ‖(UniqueFactorizationMonoid.moebius (maskIdeal F E):ℂ)*
      primitiveRow F hF c d (primeSubsetGenerator (sourceMaskPrime F) E)/
      (‖eisEmbedding (primeSubsetGenerator (sourceMaskPrime F) E)‖^2:ℝ)‖ ≤ 1 := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact (div_le_one hmask0).mpr (hnum.trans hmask)
  unfold packetCoefficient
  rw [norm_mul,norm_mul,norm_star]
  have hh := (mul_le_mul hlabel (primitiveRow_norm_le F hF c d h)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  exact (mul_le_of_le_one_right (norm_nonneg _) hh).trans hpref

theorem packetScale_lower (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (Z A η L Y : ℝ) (hZ : 1 ≤ Z) (hY : 1 ≤ Y) (hYA : Y ≤ Z^A)
    (hYL : Y ≤ L) (hbad : badNorm ≤ Z^η)
    (hcY : ((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y)
    (hdY : ((Ideal.span {tupleRow d}).absNorm:ℝ) ≤ Y)
    (E : Finset (SourceMaskIndex F)) (hE : E ∈ (sourceMaskSupport F c d).powerset) :
    Z^(-(2*A+η)) ≤ packetScale F c d L E := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hL0 : 0 < L := hY0.trans_le hYL
  have hm := mask_generator_norm_bounds F hF c d hc Y hcY E hE
  have hp := primitive_norm_le F hF c d hc hd Y hY hcY hdY
  have hp1 := primitive_norm_one_le F hF c d
  have hprim0 : 0 < ‖eisEmbedding (primitiveElement F c d)‖^2 :=
    sq_pos_of_pos (by linarith)
  have hmask0 : 0 < ‖eisEmbedding (primeSubsetGenerator (sourceMaskPrime F) E)‖^2 := by linarith [hm.1]
  have hbY : badNorm*Y^2 ≤ Z^(2*A+η) := by
    have hpow := pow_le_pow_left₀ hY0.le hYA 2
    have hh := mul_le_mul hbad hpow (sq_nonneg Y) (Real.rpow_pos_of_pos hZ0 η).le
    have he : Z^η*(Z^A)^2=Z^(2*A+η) := by
      rw [← Real.rpow_mul_natCast hZ0.le,← Real.rpow_add hZ0]
      congr 1
      norm_num
      ring
    exact hh.trans_eq he
  have hden : ‖eisEmbedding (primeSubsetGenerator (sourceMaskPrime F) E)‖^2*
      ‖eisEmbedding (primitiveElement F c d)‖^2 ≤ Z^(2*A+η)*L := by
    calc
      _ ≤ (badNorm*Y)*Y^2 := mul_le_mul hm.2 hp (sq_nonneg _) (mul_pos badNorm_pos hY0).le
      _ = (badNorm*Y^2)*Y := by ring
      _ ≤ Z^(2*A+η)*L := mul_le_mul hbY hYL hY0.le (Real.rpow_pos_of_pos hZ0 _).le
  unfold packetScale
  apply (le_div_iff₀ (mul_pos hmask0 hprim0)).mpr
  calc
    _ ≤ Z^(-(2*A+η))*(Z^(2*A+η)*L) :=
      mul_le_mul_of_nonneg_left hden (Real.rpow_pos_of_pos hZ0 _).le
    _ = L := by rw [← mul_assoc,← Real.rpow_add hZ0]; simp

/-- The literal far-frequency part of the original raw mixed packet, with
every original puncture divisor and both original dual coefficients. -/
def actualFarTail (F : Finset ColourTuple) (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (W : 𝓢(ℝ,ℂ)) (L H : ℝ) (keep : F → F → ℂ) (a : F → ℂ) : ℂ :=
  NaturalPacketTail.maskedTail
    (fun c d : F => ↥(sourceMaskSupport F c.val d.val).powerset)
    W {h : O | H < ‖eisEmbedding h‖^2}
    (fun c d E => packetScale F c.val d.val L E.val)
    (fun c d E h => keep c d*packetCoefficient F hF c.val d.val L E.val h) a

theorem badNorm_eventually_le_rpow (η : ℝ) (hη : 0 < η) :
    ∃ Z₀ : ℝ, ∀ Z : ℝ, Z₀ ≤ Z → 1 ≤ Z ∧ badNorm ≤ Z^η := by
  refine ⟨max 1 (badNorm^(1/η)),?_⟩
  intro Z hZ
  refine ⟨(le_max_left _ _).trans hZ,?_⟩
  have hp := Real.rpow_le_rpow (Real.rpow_pos_of_pos badNorm_pos (1/η)).le
    ((le_max_right _ _).trans hZ) hη.le
  have he : (badNorm^(1/η))^η=badNorm := by
    rw [← Real.rpow_mul badNorm_pos.le]
    have hh : (1/η)*η=1 := by field_simp
    rw [hh,Real.rpow_one]
  simpa only [he] using hp

/-- The complete actual raw-frequency complement has any requested negative
power. Its fixed cutoff fits the original source cap by cutoff_le_source_cap.
No coprimality selector or original pair-dependent puncture is deleted. -/
theorem actual_far_packet_tail (A P η M : ℝ) (hA : 0 ≤ A) (hη : 0 < η)
    (W : 𝓢(ℝ,ℂ)) :
    ∃ C Z₀ : ℝ, 0 < C ∧ ∀ Z Y L : ℝ, Z₀ ≤ Z →
      1 ≤ Y → Y ≤ Z^A → Y ≤ L → L ≤ Z^P →
      ∀ (F : Finset ColourTuple) (hF : ∀ c ∈ F, ∀ j, Admissible (c j)),
      (∀ c ∈ F, Pairwise (fun j k => IsCoprime (c j) (c k))) →
      (∀ c ∈ F, ((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y) →
      ∀ keep : F → F → ℂ, (∀ c d, ‖keep c d‖ ≤ 1) → ∀ a : F → ℂ,
      ‖actualFarTail F hF W L (Z^(2*A+2*η)) keep a‖ ≤ C*Z^(-M)*(∑ c, ‖a c‖^2) := by
  obtain ⟨s,C,hC,htail⟩ := NaturalPacketTail.polynomial_masked_tail A P η M hA hη
  obtain ⟨Z₀,hbad⟩ := badNorm_eventually_le_rpow η hη
  let D : ℝ := 128^6*C*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg (by positivity) (apply_nonneg _ _)
  refine ⟨1+D,Z₀,by linarith,?_⟩
  intro Z Y L hZ hY hYA hYL hLP F hF hp hheight keep hkeep a
  obtain ⟨hZ1,hbad⟩ := hbad Z hZ
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ1
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hrows : (Fintype.card F:ℝ) ≤ (128:ℝ)^5*Z^(5*A) := by
    have hc := ideal_tuple_count_crude F Y hY
      (fun c hc j => (hF c hc j).1)
      (fun c hc => (TuplePartition.norms_le_height c (hF c hc) Y (hheight c hc)).1)
    simp only [Fintype.card_coe]
    calc
      _ ≤ (128*Y)^5 := hc
      _ = (128:ℝ)^5*Y^5 := mul_pow _ _ _
      _ ≤ (128:ℝ)^5*(Z^A)^5 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hY0.le hYA 5) (by positivity)
      _ = _ := by
        rw [← Real.rpow_mul_natCast hZ0.le]
        congr 2
        norm_num
        ring
  have hlabels (c d : F) :
      (Fintype.card ↥(sourceMaskSupport F c.val d.val).powerset:ℝ) ≤
        128*Z^(A+η) := by
    simp only [Fintype.card_coe]
    calc
      _ ≤ 128*badNorm*Y := mask_labels_card_le F hF c.val d.val c.property Y hY (hheight c.val c.property)
      _ ≤ 128*Z^η*Z^A := mul_le_mul (mul_le_mul_of_nonneg_left hbad (by norm_num))
        hYA hY0.le (by positivity)
      _ = _ := by rw [mul_assoc,← Real.rpow_add hZ0,add_comm η A]
  have hscale (c d : F) (E : ↥(sourceMaskSupport F c.val d.val).powerset) :
      Z^(-(2*A+η)) ≤ packetScale F c.val d.val L E.val :=
    packetScale_lower F hF c.val d.val c.property d.property Z A η L Y hZ1 hY hYA hYL hbad
      (hheight c.val c.property) (hheight d.val d.property) E.val E.property
  have hcoeff (c d : F) (E : ↥(sourceMaskSupport F c.val d.val).powerset) (h : O)
      (_ : Z^(2*A+2*η) < ‖eisEmbedding h‖^2) :
      ‖keep c d*packetCoefficient F hF c.val d.val L E.val h‖ ≤ Z^P := by
    rw [norm_mul]
    apply (mul_le_of_le_one_left (norm_nonneg _) (hkeep c d)).trans
    exact (packetCoefficient_norm_le F hF c.val d.val c.property
      (hp c.val c.property) (hp d.val d.property) L Y (hY0.trans_le hYL).le
      (hheight c.val c.property) E.val E.property h).trans hLP
  have hh := htail (fun c d : F => ↥(sourceMaskSupport F c.val d.val).powerset)
    W {h : O | Z^(2*A+2*η) < ‖eisEmbedding h‖^2} Z (128^5) 128 hZ1
    (by positivity) (by norm_num) hrows hlabels (fun h hh => hh.le)
    (fun c d E => packetScale F c.val d.val L E.val) hscale
    (fun c d E h => keep c d*packetCoefficient F hF c.val d.val L E.val h) hcoeff a
  change ‖actualFarTail F hF W L (Z^(2*A+2*η)) keep a‖ ≤
    C*(128^5)*128*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*Z^(-M)*(∑ c, ‖a c‖^2) at hh
  have he : C*(128^5)*128*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)=D := by dsimp [D]; ring
  rw [he] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith : D ≤ 1+D) (Real.rpow_pos_of_pos hZ0 _).le)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _))

def packetTerm (F : Finset ColourTuple) (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (c d : ColourTuple) (W : 𝓢(ℝ,ℂ)) (L : ℝ)
    (E : Finset (SourceMaskIndex F)) (h : O) : ℂ :=
  packetCoefficient F hF c d L E h*
    paperRadialFourier W (packetScale F c d L E*‖eisEmbedding h‖^2)

/-- Moving constants inside the actual complete Poisson sum is exact. -/
theorem rawDualPacket_eq_terms (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple)
    (W : 𝓢(ℝ,ℂ)) (L : ℝ) :
    rawDualPacket F hF c d W L=
      ∑ E ∈ (sourceMaskSupport F c d).powerset, ∑' h : O, packetTerm F hF c d W L E h := by
  unfold rawDualPacket
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro E hE
  rw [← tsum_mul_left,← tsum_mul_left]
  apply tsum_congr
  intro h
  unfold packetTerm packetCoefficient packetScale maskIdeal
  rw [div_mul_eq_mul_div]
  ring

theorem packetTerm_summable (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k)))
    (W : 𝓢(ℝ,ℂ)) (L : ℝ) (hL : 0 < L)
    (E : Finset (SourceMaskIndex F)) (hE : E ∈ (sourceMaskSupport F c d).powerset) :
    Summable (packetTerm F hF c d W L E) := by
  have hprim : 0 < ‖eisEmbedding (primitiveElement F c d)‖^2 :=
    sq_pos_of_pos (lt_of_lt_of_le zero_lt_one (primitive_norm_one_le F hF c d))
  have hm := (mask_generator_norm_bounds F hF c d hc _ le_rfl E hE).1
  have hmpos : 0 < ‖eisEmbedding (primeSubsetGenerator (sourceMaskPrime F) E)‖^2 := by linarith
  have hscale : 0 < packetScale F c d L E := div_pos hL (mul_pos hmpos hprim)
  have hs := paperRadialFourier_lattice_summable_norm W (packetScale F c d L E) hscale
  apply (Summable.of_nonneg_of_le (fun h => norm_nonneg (packetTerm F hF c d W L E h))
    (fun h => ?_) (hs.mul_left L)).of_norm
  unfold packetTerm
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (packetCoefficient_norm_le F hF c d hc hcPair hdPair L _ hL.le le_rfl E hE h)
    (norm_nonneg _)

theorem mem_reflectionCutoff_iff (H : ℝ) (hH : 0 ≤ H) (h : O) :
    h ∈ reflectionCutoff H ↔ ‖eisEmbedding h‖^2 ≤ H := by
  by_cases hh : h=0
  · subst h
    simp [reflectionCutoff,hH]
  · simp [reflectionCutoff,TruncatedPrincipalPoisson.mem_rowNormDisk_floor hH,hh]

def nearPacket (F : Finset ColourTuple) (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (c d : ColourTuple) (W : 𝓢(ℝ,ℂ)) (L H : ℝ) : ℂ :=
  ∑ E ∈ (sourceMaskSupport F c d).powerset, ∑ h ∈ reflectionCutoff H,
    packetTerm F hF c d W L E h

/-- Exact complete pair split, including frequency zero in the finite part. -/
theorem rawDualPacket_near_far (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k)))
    (W : 𝓢(ℝ,ℂ)) (L H : ℝ) (hL : 0 < L) (hH : 0 ≤ H) :
    rawDualPacket F hF c d W L=nearPacket F hF c d W L H+
      ∑ E ∈ (sourceMaskSupport F c d).powerset,
        ∑' h : {h : O | H < ‖eisEmbedding h‖^2}, packetTerm F hF c d W L E h.val := by
  rw [rawDualPacket_eq_terms]
  unfold nearPacket
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro E hE
  have he := (packetTerm_summable F hF c d hc hcPair hdPair W L hL E hE).sum_add_tsum_subtype_compl
    (reflectionCutoff H)
  let e : {h : O // h ∉ reflectionCutoff H} ≃ {h : O | H < ‖eisEmbedding h‖^2} :=
    Equiv.subtypeEquivRight (fun h => by
      change h ∉ reflectionCutoff H ↔ H < ‖eisEmbedding h‖^2
      rw [mem_reflectionCutoff_iff H hH h,not_le])
  have ht := e.tsum_eq (fun h => packetTerm F hF c d W L E h.val)
  change (∑' h : {h : O // h ∉ reflectionCutoff H}, packetTerm F hF c d W L E h.val)=
    (∑' h : {h : O | H < ‖eisEmbedding h‖^2}, packetTerm F hF c d W L E h.val) at ht
  rw [ht] at he
  exact he.symm

theorem actualFarTail_eq (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (W : 𝓢(ℝ,ℂ)) (L H : ℝ)
    (keep : F → F → ℂ) (a : F → ℂ) :
    actualFarTail F hF W L H keep a=
      ∑ c : F, ∑ d : F, (a c*star (a d))*keep c d*
        ∑ E ∈ (sourceMaskSupport F c.val d.val).powerset,
          ∑' h : {h : O | H < ‖eisEmbedding h‖^2}, packetTerm F hF c.val d.val W L E h.val := by
  unfold actualFarTail NaturalPacketTail.maskedTail
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  simp only [mul_assoc,tsum_mul_left]
  rw [← Finset.mul_sum]
  change a c*(star (a d)*(keep c d*
    ∑ E : ↥(sourceMaskSupport F c.val d.val).powerset,
      ∑' h : {h : O | H < ‖eisEmbedding h‖^2}, packetTerm F hF c.val d.val W L E.val h.val))= _
  rw [Finset.sum_coe_sort (sourceMaskSupport F c.val d.val).powerset
    (fun E => ∑' h : {h : O | H < ‖eisEmbedding h‖^2}, packetTerm F hF c.val d.val W L E h.val)]

/-- Complete signed finite/tail identity for any original dual array and
pair selector, including the offdiagonal selector. -/
theorem weighted_packet_split (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (hp : ∀ c ∈ F, Pairwise (fun j k => IsCoprime (c j) (c k)))
    (W : 𝓢(ℝ,ℂ)) (L H : ℝ) (hL : 0 < L) (hH : 0 ≤ H)
    (keep : F → F → ℂ) (a : F → ℂ) :
    (∑ c : F, ∑ d : F, (a c*star (a d))*keep c d*rawDualPacket F hF c.val d.val W L)=
      (∑ c : F, ∑ d : F, (a c*star (a d))*keep c d*nearPacket F hF c.val d.val W L H)+
        actualFarTail F hF W L H keep a := by
  rw [actualFarTail_eq,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [rawDualPacket_near_far F hF c.val d.val c.property
    (hp c.val c.property) (hp d.val d.property) W L H hL hH]
  ring

end
end Qrh.JointDetector.NaturalActualTail

#print axioms Qrh.JointDetector.NaturalActualTail.mask_support_product_dvd
#print axioms Qrh.JointDetector.NaturalActualTail.primitive_norm_le
#print axioms Qrh.JointDetector.NaturalActualTail.actual_far_packet_tail
#print axioms Qrh.JointDetector.NaturalActualTail.weighted_packet_split
