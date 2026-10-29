/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.AdmissiblePairPoisson
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Eisenstein.ConstantTermSupport

/-! Exact retained-mask expansion for the sextic pair (colors 1 and 5).
Every mask divisor remains a separate label. In particular, the common-row
factor is a coprimality mask, not a term deleted from a norm envelope. -/
namespace Qrh.JointDetector
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ActualEisensteinCubic ActualEisensteinCoordinates
open CanonicalRowCompletion CanonicalQuadraticSieve ConcreteTraceCRT CompletedGauss
open ConcretePrimeRowBridge GaussGeneratorTransport FiniteGaussPhase
open MixedCrossSeparation MixedGaussConversion EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O
local instance (F : Finset (Ideal O)) : DecidableEq (primePool F) := Classical.decEq _

/-- The literal divisor-labelled dual sum; no restriction or absolute value
has yet been applied to the individual terms. -/
def maskedPairDual {α : Type*} [DecidableEq α]
    (R : α → Ideal O) (S : Finset α) (I J : Ideal O)
    (W : 𝓢(ℝ, ℂ)) (L : ℝ) : ℂ :=
  ∑ E ∈ S.powerset,
    let d := primeSubsetGenerator R E
    ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) *
      primitivePair I J d / (‖eisEmbedding d‖ ^ 2 : ℝ)) *
      ∑' h : O, star (primitivePair I J h) * paperRadialFourier W
        (L * ‖eisEmbedding h‖ ^ 2 /
          (‖eisEmbedding d‖ ^ 2 * ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ))))

theorem admissible_masked_pair_poisson {α : Type*} [DecidableEq α]
    (R : α → Ideal O) [∀ i, (R i).IsMaximal]
    (hinj : Function.Injective R) (S : Finset α)
    (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (I J : Ideal O) (hIF : I ∈ F) (hJF : J ∈ F) (hIJ : IsCoprime I J)
    (hmod : primaryGenerator I - primaryGenerator J ∈ (Ideal.span {(36 : O)} : Ideal O))
    (r : EisensteinEPrimaryPhase.Coord) (hr : residue (primaryGenerator J) = r)
    (W : 𝓢(ℝ, ℂ)) (L : ℝ) (hL : 0 < L) :
    (∑' z : O, rowCoprimeMask R S z * primitivePair I J z *
      W (‖eisEmbedding z‖ ^ 2 / L)) =
      ((L : ℂ) / (Real.sqrt ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ)) : ℂ) *
        quadraticRayPair r r * admissibleUnaryGauss F hF I 1 *
          admissibleUnaryGauss F hF J 5) * maskedPairDual R S I J W L := by
  let := admissiblePoolMaximal F hF
  let A := idealSupport F I
  let B := idealSupport F J
  let P := fun i : (A ∪ B : Finset (primePool F)) => Ideal.span {poolPrimary F i.val}
  have hcop := selectedPrimeCoprime (poolPrimary F) (poolPrimary_coprime F hF) (A ∪ B)
  have hrow (n : O) : finiteSexticRow P (fun i => poolPrimary_good F hF i.val)
      (fun i => if i.val ∈ B then 5 else 1) n = primitivePair I J n := by
    have hh := selectedPairRow_actual (poolPrimary F) (poolPrimary_coprime F hF)
      (poolPrimary_good F hF) A B (idealSupport_disjoint_of_coprime F I J hIJ) n
    rw [show A = idealSupport F I from rfl, show B = idealSupport F J from rfl,
      admissiblePoolProduct_span F hF I hIF, admissiblePoolProduct_span F hF J hJF] at hh
    exact hh
  have hh := canonical_masked_radial_poisson_collected R hinj S P hcop
    (fun i => poolPrimary_good F hF i.val) (fun i => poolPrimary_odd F hF i.val)
    (fun i => if i.val ∈ B then 5 else 1) (fun i => by split_ifs <;> decide)
    (fun i => by split_ifs <;> decide) W L hL
  change (∑' z : O, rowCoprimeMask R S z * finiteSexticRow P _ _ z * _) =
    ((L : ℂ) * admissiblePairGauss F hF I J /
      (‖eisEmbedding (admissiblePairConductor F I J)‖ : ℂ)) *
      ∑ E ∈ S.powerset,
        let d := primeSubsetGenerator R E
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) * finiteSexticRow P _ _ d /
          (‖eisEmbedding d‖ ^ 2 : ℝ)) *
          ∑' h : O, star (finiteSexticRow P _ _ h) * paperRadialFourier W
            (L * ‖eisEmbedding h‖ ^ 2 /
              (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding (admissiblePairConductor F I J)‖ ^ 2)) at hh
  simp_rw [hrow] at hh
  rw [admissiblePairConductor_norm_sq F hF I J hIF hJF hIJ,
    admissiblePairConductor_norm F hF I J hIF hJF hIJ,
    admissiblePairGauss_fixed_ray F hF I J hIF hJF hIJ hmod r hr] at hh
  rw [hh]
  unfold maskedPairDual
  ring

/-- Left and right divisor factors are independent row arrays. The exponent-5
Gauss factor and conjugated right character are both retained literally. -/
def maskedLeftGauss (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (d : O) (I : Ideal O) : ℂ := admissibleUnaryGauss F hF I 1 * idealRowHom d I

def maskedRightGauss (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (d : O) (I : Ideal O) : ℂ := admissibleUnaryGauss F hF I 5 * star (idealRowHom d I)

theorem maskedGauss_separated (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (d : O) (I J : Ideal O) :
    admissibleUnaryGauss F hF I 1 * admissibleUnaryGauss F hF J 5 *
      primitivePair I J d = maskedLeftGauss F hF d I * maskedRightGauss F hF d J := by
  unfold primitivePair maskedLeftGauss maskedRightGauss
  ring

theorem maskedLeftGauss_norm_le (F : Finset (Ideal O))
    (hF : ∀ I ∈ F, Admissible I) (d : O) (I : Ideal O) :
    ‖maskedLeftGauss F hF d I‖ ≤ 1 := by
  rw [maskedLeftGauss, norm_mul, admissibleUnaryGauss_norm F hF I 1 (by decide) (by decide),
    one_mul]
  exact idealRowHom_norm d I

theorem maskedRightGauss_norm_le (F : Finset (Ideal O))
    (hF : ∀ I ∈ F, Admissible I) (d : O) (I : Ideal O) :
    ‖maskedRightGauss F hF d I‖ ≤ 1 := by
  rw [maskedRightGauss, norm_mul, admissibleUnaryGauss_norm F hF I 5 (by decide) (by decide),
    one_mul, norm_star]
  exact idealRowHom_norm d I

theorem primitivePair_argument_mul (I J : Ideal O) (a b : O) :
    primitivePair I J (a * b) = primitivePair I J a * primitivePair I J b := by
  unfold primitivePair
  rw [idealRowHom_argument_mul, idealRowHom_argument_mul, star_mul]
  ring

/-- A frozen bad-prime/unit factor is absorbed into the left row vector.
It is not inserted into the ordinary source ideal, where natural zeros would
incorrectly erase the packet. -/
def maskedLeftDualCoefficient (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (d b : O) (I : Ideal O) : ℂ := maskedLeftGauss F hF d I * star (idealRowHom b I)

def maskedRightDualCoefficient (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (d b : O) (I : Ideal O) : ℂ := maskedRightGauss F hF d I * idealRowHom b I

theorem maskedLeftDualCoefficient_norm_le (F : Finset (Ideal O))
    (hF : ∀ I ∈ F, Admissible I) (d b : O) (I : Ideal O) :
    ‖maskedLeftDualCoefficient F hF d b I‖ ≤ 1 := by
  rw [maskedLeftDualCoefficient, norm_mul, norm_star]
  simpa only [one_mul] using mul_le_mul (maskedLeftGauss_norm_le F hF d I)
    (idealRowHom_norm b I) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

theorem maskedRightDualCoefficient_norm_le (F : Finset (Ideal O))
    (hF : ∀ I ∈ F, Admissible I) (d b : O) (I : Ideal O) :
    ‖maskedRightDualCoefficient F hF d b I‖ ≤ 1 := by
  rw [maskedRightDualCoefficient, norm_mul]
  simpa only [one_mul] using mul_le_mul (maskedRightGauss_norm_le F hF d I)
    (idealRowHom_norm b I) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

/-- Exact supported-core reciprocity after freezing an arbitrary element
factor `b`. No assertion that the raw Poisson frequencies are supported is
made: the bad-prime powers and unit may all be retained in `b`. -/
theorem primitivePair_frozen_frequency (I J H : Ideal O)
    (hI : Supported I) (hJ : Supported J) (hH : Supported H)
    (hmod : primaryGenerator I - primaryGenerator J ∈ (Ideal.span {(36 : O)} : Ideal O))
    (b : O) :
    star (primitivePair I J (b * primaryGenerator H)) =
      star (idealRowHom b I) * idealRowHom b J *
        star (idealRowHom (primaryGenerator I) H) * idealRowHom (primaryGenerator J) H := by
  have hi := primaryGenerator_spec I (supported_primaryGenerator_ne_zero I hI)
  have hj := primaryGenerator_spec J (supported_primaryGenerator_ne_zero J hJ)
  have hh := primaryGenerator_spec H (supported_primaryGenerator_ne_zero H hH)
  have hfour : (4 : O) ∣ primaryGenerator I - primaryGenerator J :=
    (show (4 : O) ∣ (36 : O) from ⟨9, by norm_num⟩).trans (Ideal.mem_span_singleton.mp hmod)
  have he := same_ray_pair_orientation (primaryGenerator I) (primaryGenerator J)
    (primaryGenerator H) hi.2 hj.2 hh.2 (hi.1.symm ▸ hI) (hj.1.symm ▸ hJ)
    (hh.1.symm ▸ hH) (QuadraticGaussRay.residue_eq_of_four_dvd_sub _ _ hfour)
  rw [hi.1, hj.1, hh.1] at he
  rw [primitivePair_argument_mul, star_mul]
  unfold primitivePair
  rw [← he]
  simp only [star_mul, star_star]
  ring

/-- The actual Poisson/Gauss/divisor coefficient on a frozen frequency sector
has the two independent row vectors used by the selected bilinear estimate. -/
theorem masked_pair_actual_dual_arrays (F : Finset (Ideal O))
    (hF : ∀ I ∈ F, Admissible I) (I J : Ideal O) (hIF : I ∈ F) (hJF : J ∈ F)
    (H : Ideal O) (hH : Supported H)
    (hmod : primaryGenerator I - primaryGenerator J ∈ (Ideal.span {(36 : O)} : Ideal O))
    (d b : O) :
    admissibleUnaryGauss F hF I 1 * admissibleUnaryGauss F hF J 5 *
      primitivePair I J d * star (primitivePair I J (b * primaryGenerator H)) =
      maskedLeftDualCoefficient F hF d b I * maskedRightDualCoefficient F hF d b J *
        star (idealRowHom (primaryGenerator I) H) * idealRowHom (primaryGenerator J) H := by
  rw [maskedGauss_separated,
    primitivePair_frozen_frequency I J H (admissible_supported (hF I hIF))
      (admissible_supported (hF J hJF)) hH hmod b]
  unfold maskedLeftDualCoefficient maskedRightDualCoefficient
  ring

theorem admissible_self_pair_mask (D : Ideal O) (hD : Admissible D) (z : O) :
    primitivePair D D z = idealZeroMask D z := by
  let F : Finset (Ideal O) := {D}
  have hDF : D ∈ F := Finset.mem_singleton_self D
  have hF : ∀ I ∈ F, Admissible I := by
    intro I hI
    simpa only [Finset.mem_singleton.mp hI] using hD
  have hproduct := idealSupport_product_eq F hDF hD.2.1
  unfold primitivePair
  conv_lhs => rw [← hproduct]
  rw [idealRow_prime_product (fun i : primePool F => i.val) (poolGood F hF)]
  rw [mul_comm, finiteSquarefreeRow_self_pair (fun i : primePool F => i.val)
    (poolGood F hF) (idealSupport F D) z]
  change rowCoprimeMask (fun i : primePool {D} => i.val) (idealSupport {D} D) z = _
  rw [idealSupport_singleton_univ, singleton_rowCoprimeMask_eq_idealZeroMask]

/-- Exact shared-row factorization; no coprime selector is dropped. -/
theorem shared_pair_mask (D I J : Ideal O) (hD : Admissible D) (z : O) :
    primitivePair (D * I) (D * J) z = idealZeroMask D z * primitivePair I J z := by
  have hh := admissible_self_pair_mask D hD z
  unfold primitivePair at *
  rw [map_mul, map_mul, star_mul]
  calc
    _ = (idealRowHom z D * star (idealRowHom z D)) *
      (idealRowHom z I * star (idealRowHom z J)) := by ring
    _ = _ := by rw [hh]

theorem shared_bad_pair_mask (D I J : Ideal O) (hD : Admissible D) (z : O) :
    rowCoprimeMask badPrime Finset.univ z * primitivePair (D * I) (D * J) z =
      rowCoprimeMask (fun P : gcdMaskPrimes D => P.val) Finset.univ z * primitivePair I J z := by
  rw [shared_pair_mask D I J hD z, gcdMaskPrimes_mask]
  ring

/-- Original bad primes and the entire shared factor survive in the exact
Möbius expansion, including their overlaps with the primitive conductor. -/
theorem admissible_shared_masked_pair_poisson
    (D : Ideal O) (hD : Admissible D)
    (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (I J : Ideal O) (hIF : I ∈ F) (hJF : J ∈ F) (hIJ : IsCoprime I J)
    (hmod : primaryGenerator I - primaryGenerator J ∈ (Ideal.span {(36 : O)} : Ideal O))
    (r : EisensteinEPrimaryPhase.Coord) (hr : residue (primaryGenerator J) = r)
    (W : 𝓢(ℝ, ℂ)) (L : ℝ) (hL : 0 < L) :
    (∑' z : O, rowCoprimeMask badPrime Finset.univ z *
      primitivePair (D * I) (D * J) z * W (‖eisEmbedding z‖ ^ 2 / L)) =
      ((L : ℂ) / (Real.sqrt ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ)) : ℂ) *
        quadraticRayPair r r * admissibleUnaryGauss F hF I 1 *
          admissibleUnaryGauss F hF J 5) *
      maskedPairDual (fun P : gcdMaskPrimes D => P.val) Finset.univ I J W L := by
  simp_rw [shared_bad_pair_mask D I J hD]
  exact admissible_masked_pair_poisson (fun P : gcdMaskPrimes D => P.val)
    Subtype.val_injective Finset.univ F hF I J hIF hJF hIJ hmod r hr W L hL

end
end Qrh.JointDetector

#print axioms Qrh.JointDetector.admissible_masked_pair_poisson
#print axioms Qrh.JointDetector.maskedGauss_separated
#print axioms Qrh.JointDetector.masked_pair_actual_dual_arrays
#print axioms Qrh.JointDetector.admissible_shared_masked_pair_poisson
