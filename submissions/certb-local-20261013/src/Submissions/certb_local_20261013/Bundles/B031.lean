/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B000
import Submissions.local44_20261013.Bundles.B001
import Submissions.reserve_local_20261013.Bundles.B012
import Submissions.certb_local_20261013.Bundles.B013
import Submissions.certb_local_20261013.Bundles.B020
import Submissions.certb_local_20261013.Bundles.B024
import Submissions.certb_local_20261013.Bundles.B028
import Submissions.certb_local_20261013.Bundles.B029
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DyadicSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorDictionary
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainMarkedState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainMomentParameters
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainUnmarkedState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstAnnularInputAmplification
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondBlockAggregate
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondPhysicalCost

/- BEGIN ORIGINAL MODULE Analytic.BufferedPlain ; sha256 ba5f756c3b1eee1a636d481f8b6621ed9c908e3704bd7d38d50af55ed253f9db -/
section




/-! Buffered pointwise estimates for the literal normalized natural plain
rows. The source dyadic theorem supplies the estimate itself. The two
plain profiles and their frequency parameters may be chosen independently. -/

set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Set
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeDyadic HeckeRowClosure HeckeInverseAmplification
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredExceptionalProfile CenteredMomentDetectorDictionary
open CenteredMomentHeckeHeight HeckeDetectorCoefficientTransfer
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma natural_plain_family_nonprincipal {Label : Type*}
    (ηrow : Label → Character) (z : Label → O)
    (N : ∀ j, NaturalRow (ηrow j) (z j))
    (Q : Ideal O) (puncture : Label → Ideal O)
    (hz : ∀ j, z j ≠ 0) (hpuncture : ∀ j, puncture j ≠ 0)
    (hex : ∀ j, ¬FixedInducingRow (ηrow j) Q
      (fixedBadMask*idealGenerator (puncture j)) 1 (z j)) :
    ∀ j, (excluded (N j).character (puncture j)).residue ≠ 1 :=
  fun j => excluded_nonprincipal _ _ ((N j).nonprincipal (hz j) Q (puncture j) (hpuncture j) (hex j))

/-- A complete finite natural family with its actual punctures satisfies the
buffered plain estimate. Nonprincipality comes from the literal source gate;
there is no pointwise analytic estimate among the hypotheses. The Mellin,
conductor and height gates are exactly those of `source_dyadic_bounds`. -/
theorem natural_plain_buffered_bound
    (Rwidth dmax τ ε e κ ηaux : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hκone : κ ≤ 1) (hη : 0 ≤ ηaux)
    (hbudget : 12*e*(Rwidth+2)+8*κ+2*ηaux ≤ ε)
    (profileBound : ℕ → ℝ) (hprofile : ∀ k, 0 ≤ profileBound k) :
    ∃ n : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ Z d : ℝ, 1 ≤ Z → 0 ≤ d → d ≤ dmax → 2 < Z^τ →
      ∀ {Label : Type*} [Fintype Label]
        (ηrow : Label → Character) (z : Label → O) (N : ∀ j, NaturalRow (ηrow j) (z j))
        (Q : Ideal O) (puncture : Label → Ideal O)
        (hz : ∀ j, z j ≠ 0) (hpuncture : ∀ j, puncture j ≠ 0)
        (hex : ∀ j, ¬FixedInducingRow (ηrow j) Q
          (fixedBadMask*idealGenerator (puncture j)) 1 (z j)),
      let χ := fun j => excluded (N j).character (puncture j)
      let hχ := natural_plain_family_nonprincipal ηrow z N Q puncture hz hpuncture hex
      ∀ (a : ℝ) (i : ℕ), 51/100 ≤ a → a ≤ 1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*Z^τ) < a+2*e →
      ∀ (j : Label) (W : ℝ → ℂ) (A B : ℝ),
      0 < A → Function.support W ⊆ Icc A B → ContDiff ℝ ∞ W →
      ∀ r σ freq : ℝ, (χ j).modulus.absNorm ≤ Z^d → 0 ≤ r → r ≤ Rwidth →
      |freq|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^4 ≤ (Z^d)^ηaux →
      (∀ x ∈ Icc (1-a-6*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^2*‖mellin W ((x : ℂ)+t*Complex.I)‖ ≤ profileBound 2) →
      (∀ x ∈ Icc (1-a-6*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*Complex.I)‖ ≤ profileBound (n+2)) →
      (‖(Real.sqrt ((Z^d)^r) : ℂ)⁻¹ *
        rowTwistedSum (ηrow j) (fixedBadMask*idealGenerator (puncture j)) 1 (z j)
          (twistProfile W σ freq) 0 ((Z^d)^r)‖^2 ≤
        C*(Z^d)^((2*a-1)*r+ε)) ∧
      (‖(Real.sqrt ((Z^d)^r) : ℂ)⁻¹ *
        rowTwistedSum (ηrow j) (fixedBadMask*idealGenerator (puncture j)) 1 (z j)
          (twistProfile W σ freq) 0 ((Z^d)^r)‖^2 ≤
        C*(Z^d)^((2*a-1)*min r (1-r)+ε)) := by
  obtain ⟨n, C, hC, hbound⟩ := source_dyadic_bounds Rwidth dmax τ ε e κ ηaux
    hRw hdmax hτ hε he he' hκ hκone hη hbudget profileBound hprofile
  refine ⟨n, C, hC, ?_⟩
  intro Z d hZ hd hdmax' hT Label _ ηrow z N Q puncture hz hpuncture hex χ hχ
    a i ha ha' hmax j W A B hA hWs hW r σ freq hmod hr hrmax hfreq hheight hm₂ hmn
  have hb := hbound Z d hZ hd hdmax' hT χ hχ a i ha ha' hmax
    j false W A B hA hWs hW r σ freq hmod hr hrmax hfreq hheight hm₂ hmn
  have heq := plain_polynomial_eq_row (ηrow j) (χ j)
    (fixedBadMask*idealGenerator (puncture j)) 1 (z j)
    (by simpa only [one_mul] using (N j).masked_element (puncture j) (hpuncture j))
    W ((Z^d)^r) σ freq (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) d) r)
  rw [heq] at hb
  exact hb

#print axioms natural_plain_buffered_bound
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.BufferedPlain -/

/- BEGIN ORIGINAL MODULE Analytic.JointAmplification ; sha256 493ddc9a2fc52c3d5a84c76c9cf536d088dbaeb8d23358ab13743ae922cab22c -/
section



set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Set Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentPrimeElements CenteredMomentPrimePool
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationEnergy
open CenteredMomentGaussNormalization CenteredMomentAmplificationGlobal
open CenteredMomentSectorLocalization CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstAnnularInput CenteredMomentAmplificationChildInput
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentSecondHeightFamily CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplificationErrorEnergy CenteredMomentSourceRow
open CenteredMomentFirstScale RayFourExpansion CenteredMomentGaussEnergy
open CenteredMomentChildRows CenteredMomentAmplificationActiveFactor
open CenteredMomentAmplificationShortening
local notation "O" => HeckeFamily.O

/-- The three literal extracted sources; `errorIndex + 1` is exactly 1, 6 or 7.
Their normalization is the shortened source volume, supplied by `child`. -/
def firstExtractedErrors {ι : Type*} [Fintype ι] (s : Input ι) (R seed : Ideal O)
    (Z d K₀ c sigma δ reserve : ℝ) (p : O) (τ : Fin 3 → RayCharacter → Character) : ℝ :=
  ∑ i : Fin 3, (16*(errorIndex i+2 : ℝ)*localErrorCost p (errorIndex i))*
    ∑ χ : RayCharacter, ∑ B : actualAllocations (activeInput s).pools
        ((Ideal.span {p})^(errorIndex i+1)),
      childNormalizedGaussSource (activeInput s) ((Ideal.span {p})^(errorIndex i+1)) R seed B
        (τ i χ) s.t ballProfile (errorCommonRadius Z d K₀ c sigma δ reserve p (errorIndex i+1))

lemma normalizedGaussSource_ball_nonneg {ι : Type*} [Fintype ι]
    (s : Input ι) (R seed : Ideal O) (K : ℝ) (hK : 0 < K) :
    0 ≤ normalizedGaussSource s R seed ballProfile K := by
  unfold normalizedGaussSource
  exact div_nonneg (sourceGaussEnergy_nonneg _ _ _ _ _ hK (fun _ => ballProfile_nonneg _))
    (CenteredMomentSourceInputTailUniform.volume_pos s).le

/-- A single source threshold and one family for every parent precede every
joint label. The main reciprocal prime count is paid by `Z^(-sigma/3+loss)`;
the actual three errors retain their normalized prime average. -/
theorem joint_first_annular_amplification {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes ⊆ Sbad)
    (sigma loss BR Bs Mmax b eta Csec xi reserve : ℝ)
    (hsigma : 0 < sigma) (hloss : 0 < loss) (hM : 0 ≤ Mmax) (hb : 0 ≤ b)
    (hgap : eta < sigma/6) (hC : 1 ≤ Csec) (hxi : 0 ≤ xi) (hreserve : 0 < reserve) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss) ≤ (P.card : ℝ) ∧
      ∃ τ : Character → (elementPool P) → Fin 3 → RayCharacter → Character,
        (∀ η (p : elementPool P) i χ, ((τ η p i χ).modulus.absNorm : ℝ) ≤
          radicalBound (childCharacter η χ) fixedBadMask p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ {Λ : Type*} (labels : Finset Λ) (s : Λ → Input ι) (weight : Λ → ℝ)
          (R seed I J E : Λ → Ideal O) (K X Tsec H₀ d c : Λ → ℝ) (z : Λ → ι → ℝ),
          (∀ l ∈ labels, 0 ≤ weight l) →
          (∀ l ∈ labels, ∀ j, Function.support ((s l).W j) ⊆ Iic b) →
          (∀ l ∈ labels, ∀ j, z l j ≤ eta) →
          (∀ l ∈ labels, ∀ j, (s l).P j = Z^(z l j)) →
          (∀ l ∈ labels, R l ≠ 0) → (∀ l ∈ labels, seed l ≠ 0) →
          (∀ l ∈ labels, ((R l).absNorm : ℝ) ≤ Z^BR) →
          (∀ l ∈ labels, ((seed l).absNorm : ℝ) ≤ Z^Bs) →
          (∀ l ∈ labels, E l ≠ 0) → (∀ l ∈ labels, 0 < K l) → (∀ l ∈ labels, 0 < X l) →
          (∀ l ∈ labels, Tsec l ≤ Csec*firstNominalScale (I l) (J l) (E l) (K l) (X l)) →
          (∀ l ∈ labels, 0 < H₀ l) →
          (∀ l ∈ labels, H₀ l ≤ 4*frequencyRadius (Tsec l) Z xi) →
          (∀ l ∈ labels, 8*H₀ l ≤ Z^Mmax) →
          (∑ l ∈ labels, weight l*normalizedGaussSource (s l) (R l) (seed l)
            CenteredMomentFirstAnnularMajorant.profile (H₀ l)) ≤
            (56*((Mmax+2*sigma)/(sigma/6))*Z^(-sigma/3+loss))*
              (∑ l ∈ labels, weight l*normalizedGaussSource (s l) (R l) (seed l) ballProfile
                (mainCommonRadius Z (d l) (nominalLog (I l) (J l) (E l) (K l) (X l) Z)
                  (c l) sigma (frequencyLoss Z (32*Csec) xi) reserve)) +
            (56/(P.card : ℝ))*(∑ p : elementPool P, ∑ l ∈ labels, weight l*
              firstExtractedErrors (s l) (R l) (seed l) Z (d l)
                (nominalLog (I l) (J l) (E l) (K l) (X l) Z) (c l) sigma
                (frequencyLoss Z (32*Csec) xi) reserve p (τ (s l).η p)) := by
  have hsource := eventually_input_amplification (ι := ι) M H hH Sbad hbad
    sigma loss BR Bs Mmax b eta Csec xi reserve hsigma hloss hM hb
    (by linarith) hC hxi hreserve
  filter_upwards [hsource] with Z hz
  obtain ⟨hZ,hP,hcard,hfam⟩ := hz
  let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
  choose τ hτ hbound using hfam
  refine ⟨hZ,hP,hcard,τ,?_,?_⟩
  · intro η p i χ
    exact_mod_cast hτ η p i χ
  · intro Λ labels s weight R seed I J E K X Tsec H₀ d c z hw hsupp hz hlen
      hR0 hseed0 hR hseed hE hK hX hsec hH₀ houter hcap
    let Main (l : Λ) := normalizedGaussSource (s l) (R l) (seed l) ballProfile
      (mainCommonRadius Z (d l) (nominalLog (I l) (J l) (E l) (K l) (X l) Z)
        (c l) sigma (frequencyLoss Z (32*Csec) xi) reserve)
    let Err (l : Λ) (p : elementPool P) := firstExtractedErrors (s l) (R l) (seed l)
      Z (d l) (nominalLog (I l) (J l) (E l) (K l) (X l) Z) (c l) sigma
      (frequencyLoss Z (32*Csec) xi) reserve p (τ (s l).η p)
    let F : ℝ := (Mmax+2*sigma)/(sigma/6)
    have hF : 0 ≤ F := by dsimp [F]; positivity
    have hmain (l : Λ) : 0 ≤ Main l := normalizedGaussSource_ball_nonneg _ _ _ _
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    have hmainSum : 0 ≤ ∑ l ∈ labels, weight l*Main l :=
      Finset.sum_nonneg (fun l hl => mul_nonneg (hw l hl) (hmain l))
    have hpoint (l : Λ) (hl : l ∈ labels) :
        normalizedGaussSource (s l) (R l) (seed l) CenteredMomentFirstAnnularMajorant.profile (H₀ l) ≤
          (56/(P.card : ℝ))*(F*Main l+∑ p : elementPool P, Err l p) := by
      exact hbound (s l).η (s l) rfl (hsupp l hl) (z l) (hz l hl) (hlen l hl)
        (R l) (seed l) (hR0 l hl) (hseed0 l hl) (hR l hl) (hseed l hl)
        (d l) (c l) (I l) (J l) (E l) (hE l hl) (K l) (X l) (Tsec l)
        (hK l hl) (hX l hl) (hsec l hl) (H₀ l) (hH₀ l hl) (houter l hl) (hcap l hl)
    have hrecip : (P.card : ℝ)⁻¹ ≤ Z^(-sigma/3+loss) :=
      by simpa only [neg_div] using
        reciprocal_pool_bound M H Sbad (sigma/3) loss Z (zero_lt_one.trans hZ) hcard
    change _ ≤ (56*F*Z^(-sigma/3+loss))*(∑ l ∈ labels, weight l*Main l)+
      (56/(P.card : ℝ))*(∑ p : elementPool P, ∑ l ∈ labels, weight l*Err l p)
    calc
      _ ≤ ∑ l ∈ labels, weight l*((56/(P.card : ℝ)))*(F*Main l+∑ p : elementPool P, Err l p) := by
        apply Finset.sum_le_sum
        intro l hl
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hpoint l hl) (hw l hl)
      _ = (56*F*(P.card : ℝ)⁻¹)*(∑ l ∈ labels, weight l*Main l)+
          (56/(P.card : ℝ))*(∑ p : elementPool P, ∑ l ∈ labels, weight l*Err l p) := by
        simp only [mul_add,Finset.sum_add_distrib]
        congr 1
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l hl
          rw [div_eq_mul_inv]
          ring
        · simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro p hp
          apply Finset.sum_congr rfl
          intro l hl
          ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrecip (show 0 ≤ 56*F by positivity)) hmainSum) le_rfl

/-- Finite powerset uniformity permits the actual live slots to vary with
every first allocation. The constants stay unchanged and no subset count is paid. The main reciprocal prime count is paid by `Z^(-sigma/3+loss)`;
the actual three errors retain their normalized prime average. -/
theorem joint_first_annular_amplification_subsets {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes ⊆ Sbad)
    (sigma loss BR Bs Mmax b eta Csec xi reserve : ℝ)
    (hsigma : 0 < sigma) (hloss : 0 < loss) (hM : 0 ≤ Mmax) (hb : 0 ≤ b)
    (hgap : eta < sigma/6) (hC : 1 ≤ Csec) (hxi : 0 ≤ xi) (hreserve : 0 < reserve) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss) ≤ (P.card : ℝ) ∧
      ∃ τ : (J : Finset ι) → Character → (elementPool P) → Fin 3 → RayCharacter → Character,
        (∀ J η (p : elementPool P) i χ, ((τ J η p i χ).modulus.absNorm : ℝ) ≤
          radicalBound (childCharacter η χ) fixedBadMask p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ {Λ : Type*} (labels : Finset Λ) (slots : Λ → Finset ι) (s : (l : Λ) → Input (slots l)) (weight : Λ → ℝ)
          (R seed I J E : Λ → Ideal O) (K X Tsec H₀ d c : Λ → ℝ) (z : (l : Λ) → slots l → ℝ),
          (∀ l ∈ labels, 0 ≤ weight l) →
          (∀ l ∈ labels, ∀ j, Function.support ((s l).W j) ⊆ Iic b) →
          (∀ l ∈ labels, ∀ j, z l j ≤ eta) →
          (∀ l ∈ labels, ∀ j, (s l).P j = Z^(z l j)) →
          (∀ l ∈ labels, R l ≠ 0) → (∀ l ∈ labels, seed l ≠ 0) →
          (∀ l ∈ labels, ((R l).absNorm : ℝ) ≤ Z^BR) →
          (∀ l ∈ labels, ((seed l).absNorm : ℝ) ≤ Z^Bs) →
          (∀ l ∈ labels, E l ≠ 0) → (∀ l ∈ labels, 0 < K l) → (∀ l ∈ labels, 0 < X l) →
          (∀ l ∈ labels, Tsec l ≤ Csec*firstNominalScale (I l) (J l) (E l) (K l) (X l)) →
          (∀ l ∈ labels, 0 < H₀ l) →
          (∀ l ∈ labels, H₀ l ≤ 4*frequencyRadius (Tsec l) Z xi) →
          (∀ l ∈ labels, 8*H₀ l ≤ Z^Mmax) →
          (∑ l ∈ labels, weight l*normalizedGaussSource (s l) (R l) (seed l)
            CenteredMomentFirstAnnularMajorant.profile (H₀ l)) ≤
            (56*((Mmax+2*sigma)/(sigma/6))*Z^(-sigma/3+loss))*
              (∑ l ∈ labels, weight l*normalizedGaussSource (s l) (R l) (seed l) ballProfile
                (mainCommonRadius Z (d l) (nominalLog (I l) (J l) (E l) (K l) (X l) Z)
                  (c l) sigma (frequencyLoss Z (32*Csec) xi) reserve)) +
            (56/(P.card : ℝ))*(∑ p : elementPool P, ∑ l ∈ labels, weight l*
              firstExtractedErrors (s l) (R l) (seed l) Z (d l)
                (nominalLog (I l) (J l) (E l) (K l) (X l) Z) (c l) sigma
                (frequencyLoss Z (32*Csec) xi) reserve p (τ (slots l) (s l).η p)) := by
  have hsource := Filter.eventually_all.mpr (fun J : Finset ι =>
    eventually_input_amplification (ι := J) M H hH Sbad hbad
      sigma loss BR Bs Mmax b eta Csec xi reserve hsigma hloss hM hb hgap hC hxi hreserve)
  filter_upwards [hsource] with Z hz
  obtain ⟨hZ,hP,hcard,_⟩ := hz (∅ : Finset ι)
  have hfam := fun J : Finset ι => (hz J).2.2.2
  let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
  choose τ hτ hbound using hfam
  refine ⟨hZ,hP,hcard,τ,?_,?_⟩
  · intro J η p i χ
    exact_mod_cast hτ J η p i χ
  · intro Λ labels slots s weight R seed I J E K X Tsec H₀ d c z hw hsupp hz hlen
      hR0 hseed0 hR hseed hE hK hX hsec hH₀ houter hcap
    let Main (l : Λ) := normalizedGaussSource (s l) (R l) (seed l) ballProfile
      (mainCommonRadius Z (d l) (nominalLog (I l) (J l) (E l) (K l) (X l) Z)
        (c l) sigma (frequencyLoss Z (32*Csec) xi) reserve)
    let Err (l : Λ) (p : elementPool P) := firstExtractedErrors (s l) (R l) (seed l)
      Z (d l) (nominalLog (I l) (J l) (E l) (K l) (X l) Z) (c l) sigma
      (frequencyLoss Z (32*Csec) xi) reserve p (τ (slots l) (s l).η p)
    let F : ℝ := (Mmax+2*sigma)/(sigma/6)
    have hF : 0 ≤ F := by dsimp [F]; positivity
    have hmain (l : Λ) : 0 ≤ Main l := normalizedGaussSource_ball_nonneg _ _ _ _
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    have hmainSum : 0 ≤ ∑ l ∈ labels, weight l*Main l :=
      Finset.sum_nonneg (fun l hl => mul_nonneg (hw l hl) (hmain l))
    have hpoint (l : Λ) (hl : l ∈ labels) :
        normalizedGaussSource (s l) (R l) (seed l) CenteredMomentFirstAnnularMajorant.profile (H₀ l) ≤
          (56/(P.card : ℝ))*(F*Main l+∑ p : elementPool P, Err l p) := by
      exact hbound (slots l) (s l).η (s l) rfl (hsupp l hl) (z l) (hz l hl) (hlen l hl)
        (R l) (seed l) (hR0 l hl) (hseed0 l hl) (hR l hl) (hseed l hl)
        (d l) (c l) (I l) (J l) (E l) (hE l hl) (K l) (X l) (Tsec l)
        (hK l hl) (hX l hl) (hsec l hl) (H₀ l) (hH₀ l hl) (houter l hl) (hcap l hl)
    have hrecip : (P.card : ℝ)⁻¹ ≤ Z^(-sigma/3+loss) :=
      by simpa only [neg_div] using
        reciprocal_pool_bound M H Sbad (sigma/3) loss Z (zero_lt_one.trans hZ) hcard
    change _ ≤ (56*F*Z^(-sigma/3+loss))*(∑ l ∈ labels, weight l*Main l)+
      (56/(P.card : ℝ))*(∑ p : elementPool P, ∑ l ∈ labels, weight l*Err l p)
    calc
      _ ≤ ∑ l ∈ labels, weight l*((56/(P.card : ℝ)))*(F*Main l+∑ p : elementPool P, Err l p) := by
        apply Finset.sum_le_sum
        intro l hl
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hpoint l hl) (hw l hl)
      _ = (56*F*(P.card : ℝ)⁻¹)*(∑ l ∈ labels, weight l*Main l)+
          (56/(P.card : ℝ))*(∑ p : elementPool P, ∑ l ∈ labels, weight l*Err l p) := by
        simp only [mul_add,Finset.sum_add_distrib]
        congr 1
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l hl
          rw [div_eq_mul_inv]
          ring
        · simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro p hp
          apply Finset.sum_congr rfl
          intro l hl
          ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrecip (show 0 ≤ 56*F by positivity)) hmainSum) le_rfl


lemma first_extracted_error_indices (i : Fin 3) :
    errorIndex i+1 = 1 ∨ errorIndex i+1 = 6 ∨ errorIndex i+1 = 7 := by
  rcases errorIndex_cases i with h|h|h <;> simp [h]

/-- Exact local scalars; the middle extracted error retains its different
prime dependence. -/
lemma first_extracted_error_scalars (p : O) :
    16*(errorIndex (0 : Fin 3)+2 : ℝ)*localErrorCost p (errorIndex 0) =
        32*(Ideal.absNorm (Ideal.span {p}) : ℝ)⁻¹ ∧
    16*(errorIndex (1 : Fin 3)+2 : ℝ)*localErrorCost p (errorIndex 1) =
        112*(1-(Ideal.absNorm (Ideal.span {p}) : ℝ)⁻¹)^2 ∧
    16*(errorIndex (2 : Fin 3)+2 : ℝ)*localErrorCost p (errorIndex 2) =
        128*(Ideal.absNorm (Ideal.span {p}) : ℝ)⁻¹ := by
  norm_num [errorIndex,localErrorCost]

/-- In prime-length notation, the enlarged main radius contains `6*a`.
The three errors keep their genuine shortening/moving exponents. -/
lemma first_amplification_exact_radii (Z d K₀ c a δ reserve : ℝ) (p : O) :
    mainCommonRadius Z d K₀ c (3*a) δ reserve =
      Z^(K₀+max (d-c) 0+6*a+δ+reserve) ∧
    errorCommonRadius Z d K₀ c (3*a) δ reserve p 1 =
      Z^(K₀+max (d-c-Real.logb Z (normValue p)) 0+3*a+δ+reserve) ∧
    errorCommonRadius Z d K₀ c (3*a) δ reserve p 6 =
      Z^(K₀+max (d-c-12*Real.logb Z (normValue p)) 0+3*a+δ+reserve) ∧
    errorCommonRadius Z d K₀ c (3*a) δ reserve p 7 =
      Z^(K₀+max (d-c-13*Real.logb Z (normValue p)) 0+3*a+δ+reserve) := by
  simp only [mainCommonRadius,errorCommonRadius,errorRemoval,errorMoving]
  norm_num
  constructor
  · congr 1
    ring
  constructor
  · congr 3
    ring
  constructor
  · congr 3
    ring
  · congr 3
    ring

/-- Extraction uses the actual shortened volume, not the parent volume. -/
lemma first_extracted_child_volume {ι : Type*} [Fintype ι]
    (s : Input ι) (p : O) (hp : p ≠ 0) (k : ℕ)
    (hslot : ∀ j, ∀ I ∈ (activeInput s).slots j, IsCoprime (Ideal.span {p}) I)
    (R : Ideal O) (B : actualAllocations (activeInput s).pools ((Ideal.span {p})^k))
    (τ : Character) (t : ℝ) :
    volume (child (activeInput s) ((Ideal.span {p})^k) R B τ t) =
      volume s/(Ideal.absNorm (Ideal.span {p}) : ℝ)^k := by
  rw [child_volume (activeInput s) (Ideal.span {p})
    (Ideal.span_singleton_eq_bot.not.mpr hp) k hslot R B τ t,active_volume]

#print axioms joint_first_annular_amplification_subsets
#print axioms joint_first_annular_amplification
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointAmplification -/

/- BEGIN ORIGINAL MODULE Analytic.JointFiberCount ; sha256 0136860bf2ec87eda3aac557b0e1f1bc5d9a58091293845f3cea5b8f6a5a578c -/
section


/-! A Rankin count for the two complete common pairs and the three squarefree
choices in one reconstruction fiber. No population estimate is a premise. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open IdealMobiusDivisorSum CenteredMomentRankinSubset
local notation "O" => ActualEisensteinCubic.O

abbrev JointArithmeticCode := (Ideal O × Ideal O) ×
  ((Ideal O × Ideal O) × (Finset (Ideal O) × (Finset (Ideal O) × Finset (Ideal O))))

/-- Arbitrary valuations are counted by Rankin twice. The three finite subsets
encode the first principal mask, second unit partition and first projector. -/
theorem joint_arithmetic_fiber_count (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Q : Ideal O), Q ≠ 0 → ∀ S : Finset JointArithmeticCode,
      (∀ v ∈ S, v.1.1 ≠ 0 ∧ v.1.2 ≠ 0 ∧ v.2.1.1 ≠ 0 ∧ v.2.1.2 ≠ 0) →
      (∀ v ∈ S, primeSupport v.1.1 ⊆ primeSupport Q ∧
        primeSupport v.1.2 ⊆ primeSupport Q ∧
        primeSupport v.2.1.1 ⊆ primeSupport Q ∧
        primeSupport v.2.1.2 ⊆ primeSupport Q ∧
        v.2.2.1 ⊆ primeSupport Q ∧ v.2.2.2.1 ⊆ primeSupport Q ∧
        v.2.2.2.2 ⊆ primeSupport Q) →
      ∀ X₁ Y₁ X₂ Y₂ : ℝ, 0 < X₁ → 0 < Y₁ → 0 < X₂ → 0 < Y₂ →
      (∀ v ∈ S, (Ideal.absNorm v.1.1 : ℝ) ≤ X₁ ∧
        (Ideal.absNorm v.1.2 : ℝ) ≤ Y₁ ∧
        (Ideal.absNorm v.2.1.1 : ℝ) ≤ X₂ ∧
        (Ideal.absNorm v.2.1.2 : ℝ) ≤ Y₂) →
      (S.card : ℝ) ≤ K * X₁^a * Y₁^a * X₂^a * Y₂^a * (Ideal.absNorm Q : ℝ)^(5*ε) := by
  obtain ⟨C, hC, hpair⟩ := supported_power_pair_count a ε ha hε
  obtain ⟨D, hD, hsub⟩ := SquarefreeDivisorBound.prime_support_subsets_bound ε hε
  refine ⟨C^2 * D^3, by positivity, ?_⟩
  intro Q hQ S hnonzero hs X₁ Y₁ X₂ Y₂ hX₁ hY₁ hX₂ hY₂ hnorm
  let A := S.image Prod.fst
  let B := S.image (fun v => v.2.1)
  let P := (primeSupport Q).powerset
  have hA : (A.card : ℝ) ≤ C * X₁^a * Y₁^a * (Ideal.absNorm Q : ℝ)^ε := by
    apply hpair Q hQ A
    · intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      exact ⟨(hnonzero w hw).1, (hnonzero w hw).2.1⟩
    · intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      exact ⟨(hs w hw).1, (hs w hw).2.1⟩
    · exact hX₁
    · exact hY₁
    · intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      exact ⟨(hnorm w hw).1, (hnorm w hw).2.1⟩
  have hB : (B.card : ℝ) ≤ C * X₂^a * Y₂^a * (Ideal.absNorm Q : ℝ)^ε := by
    apply hpair Q hQ B
    · intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      exact ⟨(hnonzero w hw).2.2.1, (hnonzero w hw).2.2.2⟩
    · intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      exact ⟨(hs w hw).2.2.1, (hs w hw).2.2.2.1⟩
    · exact hX₂
    · exact hY₂
    · intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      exact ⟨(hnorm w hw).2.2.1, (hnorm w hw).2.2.2⟩
  have hP : (P.card : ℝ) ≤ D * (Ideal.absNorm Q : ℝ)^ε := by
    simpa only [P, Finset.card_powerset, Nat.cast_pow, Nat.cast_ofNat] using hsub Q hQ
  have hin : S ⊆ A ×ˢ (B ×ˢ (P ×ˢ (P ×ˢ P))) := by
    intro v hv
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hv,
      Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hv,
        Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr (hs v hv).2.2.2.2.1,
          Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr (hs v hv).2.2.2.2.2.1,
            Finset.mem_powerset.mpr (hs v hv).2.2.2.2.2.2⟩⟩⟩⟩
  have hnQ : (0 : ℝ) < Ideal.absNorm Q := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hQ)
  have hc : (S.card : ℝ) ≤ A.card * (B.card * (P.card * (P.card * P.card))) := by
    exact_mod_cast (Finset.card_le_card hin).trans_eq (by simp only [Finset.card_product])
  calc
    (S.card : ℝ) ≤ A.card * (B.card * (P.card * (P.card * P.card))) := hc
    _ ≤ (C * X₁^a * Y₁^a * (Ideal.absNorm Q : ℝ)^ε) *
        ((C * X₂^a * Y₂^a * (Ideal.absNorm Q : ℝ)^ε) *
          ((D * (Ideal.absNorm Q : ℝ)^ε) *
            ((D * (Ideal.absNorm Q : ℝ)^ε) * (D * (Ideal.absNorm Q : ℝ)^ε)))) := by
      gcongr
    _ = C^2 * D^3 * X₁^a * Y₁^a * X₂^a * Y₂^a *
        ((Ideal.absNorm Q : ℝ)^ε * ((Ideal.absNorm Q : ℝ)^ε *
          ((Ideal.absNorm Q : ℝ)^ε * ((Ideal.absNorm Q : ℝ)^ε *
            (Ideal.absNorm Q : ℝ)^ε)))) := by ring
    _ = _ := by
      simp only [← Real.rpow_add hnQ]
      congr 1
      congr 1
      ring

/-- A finite set of missing squarefree radicals of norm at most Y has the
literal ideal-lattice population bound. No row or first-label count is added. -/
theorem joint_missing_radical_count (S : Finset (Ideal O)) (Y : ℝ) (hY : 0 ≤ Y)
    (hS : ∀ R ∈ S, R ≠ 0) (hN : ∀ R ∈ S, (Ideal.absNorm R : ℝ) ≤ Y) :
    (S.card : ℝ) ≤ 128 * Y := by
  simpa using CenteredMomentSecondDiagonal.divisible_ideal_card S 1 one_ne_zero hS
    (fun _ _ => one_dvd _) Y hY hN

#print axioms joint_arithmetic_fiber_count
#print axioms joint_missing_radical_count
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFiberCount -/

/- BEGIN ORIGINAL MODULE Analytic.JointSecondBlock ; sha256 87735ad84ec5888dee720486cdc9a567dd344d6570e80e83bb86f73be0b119f8 -/
section






/-! Exact second Poisson blocks for the literal first common-energy
coefficients. Every first label, second common pair, partition, and physical
dyadic block remains inside the sums. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
open EisensteinSchwartzPoisson CenteredMomentGaussNormalization
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalChildEnergy CenteredMomentSourceRow CenteredMomentFirstSectors
open CenteredMomentSecondSectorColumns CenteredMomentSecondLocalization
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondPhysicalCost
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondRetainedRows CenteredMomentActiveSource
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst CenteredMomentSecondSectorRetained
open CenteredMomentSourceSecondZeroEnergy CenteredMomentSupportedTailAggregate
open CenteredMomentSecondTail CenteredMomentSupport
open CenteredMomentSecondSectorChildren CenteredMomentSecondWholeKernel
open CenteredMomentSmooth CenteredMomentLogDyadic CenteredMomentMobiusRegroup
open CenteredMomentSecondScaled CenteredMomentChildAssembly RayFourExpansion
open CanonicalRowCompletion CenteredMomentSupportedCorrelation CenteredMomentCompleteCommon
open CenteredMomentFixedRay
open CenteredMomentChildRows CenteredMomentSecondChildProfile
local notation "O" => ActualEisensteinCubic.O

def commonSecondColumns {ι : Type*} [Fintype ι] (s : OriginalData ι)
    (C : Ideal O) (hC : Supported C) : Finset (Ideal O) :=
  residualPool C hC.1 s.columns

def commonSecondBeta {ι : Type*} [Fintype ι] (s : OriginalData ι)
    (C L : Ideal O) (I : Ideal O) : ℂ :=
  if IsCoprime C I ∧ L ∣ I then s.beta (C*I) else 0

theorem commonSecond_source_norm_cap {ι : Type*} [Fintype ι]
    (s : OriginalData ι) (C L : Ideal O) (hC : Supported C) (H : ℝ)
    (hH : ∀ I ∈ s.columns, s.beta I ≠ 0 → (I.absNorm : ℝ) ≤ H) :
    ∀ I ∈ commonSecondColumns s C hC, commonSecondBeta s C L I ≠ 0 →
      (I.absNorm : ℝ) ≤ H/(C.absNorm : ℝ) := by
  intro I hI hb
  have hβ : s.beta (C*I) ≠ 0 := by
    intro hz
    simp only [commonSecondBeta, hz, ite_self] at hb
    exact hb rfl
  have hc : 0 < (C.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  apply (le_div_iff₀ hc).mpr
  have hh := hH (C*I) ((mem_residualPool C hC.1 s.columns I).mp hI) hβ
  simpa only [map_mul, Nat.cast_mul, mul_comm] using hh

theorem commonEnergy_eq_second_source {ι : Type*} [Fintype ι]
    (s : OriginalData ι) (C : Ideal O) (hC : Supported C) (τ : Character)
    (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    commonEnergy s C hC τ t L W K =
      sourceGaussEnergy (commonSecondColumns s C hC) (commonSecondBeta s C L)
        (heightCoeff τ t) W K := rfl

/-- This is the finite physical-block sum, with its literal common-height
phase. The definition includes every active common pair and partition. -/
def actualSecondBlocks (η : Character) (t : ℝ) (S : Finset (Ideal O))
    (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ H : ℝ) : ℂ :=
  ∑ p : ActiveLabel S β, heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)*
    ∑ U : Finset (CommonIndex p.val.1 p.val.2),
      ∑ n : SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
        physicalBlock η t (activeSource S β) β p.val.1 p.val.2
          (commonLabels_supported (activeSource S β) _ _ p.property).1
          (commonLabels_supported (activeSource S β) _ _ p.property).2 U
          (frequencyRadius Tsec Z ξ)
          (retainedRows (frequencyRadius Tsec Z ξ)
            (commonFrequencyGenerator p.val.1 p.val.2*
              nonunitFrequencyGenerator p.val.1 p.val.2 U)) W K (fun i => (n i : ℤ))

def actualSecondNormalizedBlocks (η : Character) (t : ℝ) (S : Finset (Ideal O))
    (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ H : ℝ) : ℂ :=
  ∑ p : ActiveLabel S β, heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)*
    ∑ U : Finset (CommonIndex p.val.1 p.val.2),
      ∑ n : SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
        ((outerScalar p.val.1 p.val.2 K (fun i => (n i : ℤ)) : ℝ) : ℂ)*
          (normalizer p.val.1 p.val.2 U : ℂ)*
          normalizedBlock η t (activeSource S β) β p.val.1 p.val.2
            (commonLabels_supported (activeSource S β) _ _ p.property).1
            (commonLabels_supported (activeSource S β) _ _ p.property).2 U
            (frequencyRadius Tsec Z ξ)
            (retainedRows (frequencyRadius Tsec Z ξ)
              (commonFrequencyGenerator p.val.1 p.val.2*
                nonunitFrequencyGenerator p.val.1 p.val.2 U)) W K (fun i => (n i : ℤ))

theorem actualSecondBlocks_eq_normalized (η : Character) (t : ℝ) (S : Finset (Ideal O))
    (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ H : ℝ) (hK : 0 < K) :
    actualSecondBlocks η t S β W K Tsec Z ξ H =
      actualSecondNormalizedBlocks η t S β W K Tsec Z ξ H := by
  unfold actualSecondBlocks actualSecondNormalizedBlocks
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro n hn
  exact physicalBlock_eq η t _ β _ _ _ _ U _ _
    (fun z hz => retainedRows_ne_zero _ _ z hz) W K hK (fun i => (n i : ℤ))

def secondBlockKernel (C D : Ideal O) (U : Finset (CommonIndex C D))
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4 → ℤ) (z : O) (I J : Ideal O) : ℂ :=
  wholeKernel W (fun _ => logAnnulus)
    (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
    (Real.log (secondEffectiveScale C D
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K/dyadicScale (n 0)))
    (Real.log (normValue z/dyadicScale (n 1)))
    (Real.log ((I.absNorm : ℝ)/dyadicScale (n 2)))
    (Real.log ((J.absNorm : ℝ)/dyadicScale (n 3)))

def secondBlockChildCoefficient (η : Character) (t : ℝ) (S : Finset (Ideal O))
    (β : Ideal O → ℂ) (C : Ideal O) (hC : Supported C) (A : O)
    (L : Ideal O) (χ : RayCharacter) (z : O) (I : sectorPool C hC.1 S) : ℂ :=
  divisorCoefficient L (sectorElement C hC.1 S)
    (movingCoefficient A (sectorElement C hC.1 S)
      (fun I => β (C*I)*heightCoeff η t I)) χ I * idealRowHom z I

/-- The fixed ray character and the genuine frequency A*z are retained
in the literal second child coefficient. Only the second projector is an
external ideal mask. -/
theorem secondBlockChildCoefficient_eq_ray_row (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C : Ideal O) (hC : Supported C)
    (A : O) (L : Ideal O) (χ : RayCharacter) (z : O) (I : sectorPool C hC.1 S) :
    secondBlockChildCoefficient η t S β C hC A L χ z I =
      (if L ∣ (I : Ideal O) then β (C*I) else 0) *
        heightCoeff (childCharacter η χ) t I * idealRowHom (A*z) I := by
  unfold secondBlockChildCoefficient divisorCoefficient movingCoefficient
  simp only [sectorElement_span]
  simp only [heightCoeff, child_ideal_primary η χ I (sectorPool_supported C hC.1 S I),
    idealRowHom_argument_mul, sectorElement]
  split_ifs <;> ring

def secondBlockRowPhase (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (R : ℝ) (z : O) : ℂ :=
  retainedScalar C D U R z * idealCorrelation C D hC hD
    ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z)

theorem secondBlockRowPhase_norm (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D) (U : Finset (CommonIndex C D))
    (R : ℝ) (z : O) : ‖secondBlockRowPhase C D hC hD U R z‖ ≤ 1 :=
  actual_retained_scalar_norm C D hC hD hCD U R z

/-- Exact second-projector and ray expansion. The right ray is inverted
and evaluated at the reflected row, exactly as in the source identity. -/
def actualSecondChildren (η : Character) (t : ℝ) (S : Finset (Ideal O))
    (β : Ideal O → ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (R : ℝ) (rows : Finset O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4 → ℤ) : ℂ :=
  let A := commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
  ∑ L ∈ divisorPool Finset.univ (fun J : sectorPool D hD.1 S => (J : Ideal O)),
    (UniqueFactorizationMonoid.moebius L : ℂ)*
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        pairCoeff (phaseTable (primaryGenerator C) (primaryGenerator D)) χ ξ *
          ∑ z ∈ rows, secondBlockRowPhase C D hC hD U R z *
            ∑ I : sectorPool C hC.1 S, ∑ J : sectorPool D hD.1 S,
              (secondBlockChildCoefficient η t S β C hC A L χ z I *
                star (secondBlockChildCoefficient η t S β D hD A L (ξ⁻¹) (-z) J)) *
                  secondBlockKernel C D U W K n z I J

set_option maxHeartbeats 600000 in
theorem normalizedBlock_eq_actual_children (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (hCD : primeSupport C = primeSupport D)
    (U : Finset (CommonIndex C D)) (R : ℝ) (rows : Finset O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4 → ℤ) :
    normalizedBlock η t S β C D hC hD U R rows W K n =
      actualSecondChildren η t S β C D hC hD U R rows W K n := by
  simpa only [normalizedBlock, actualSecondChildren, secondBlockChildCoefficient,
    secondBlockRowPhase, secondBlockKernel] using sector_correlation_children η t S β C D hC hD hCD
    (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)
    rows (retainedScalar C D U R) (secondBlockKernel C D U W K n)

theorem joint_normalizedBlock_eq_actual_children {α : Type*} (Λ : Finset α)
    (η : α → Character) (t : α → ℝ) (S : α → Finset (Ideal O))
    (β : α → Ideal O → ℂ) (C D : α → Ideal O)
    (hC : ∀ ℓ, Supported (C ℓ)) (hD : ∀ ℓ, Supported (D ℓ))
    (hCD : ∀ ℓ, primeSupport (C ℓ) = primeSupport (D ℓ))
    (U : ∀ ℓ, Finset (CommonIndex (C ℓ) (D ℓ)))
    (R : α → ℝ) (rows : α → Finset O) (W : 𝓢(ℝ,ℂ))
    (K : α → ℝ) (n : α → Fin 4 → ℤ) (weight : α → ℂ) :
    (∑ ℓ ∈ Λ, weight ℓ * normalizedBlock (η ℓ) (t ℓ) (S ℓ) (β ℓ)
      (C ℓ) (D ℓ) (hC ℓ) (hD ℓ) (U ℓ) (R ℓ) (rows ℓ) W (K ℓ) (n ℓ)) =
    ∑ ℓ ∈ Λ, weight ℓ * actualSecondChildren (η ℓ) (t ℓ) (S ℓ) (β ℓ)
      (C ℓ) (D ℓ) (hC ℓ) (hD ℓ) (U ℓ) (R ℓ) (rows ℓ) W (K ℓ) (n ℓ) := by
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  rw [normalizedBlock_eq_actual_children _ _ _ _ _ _ _ _ (hCD ℓ)]

def actualSecondProjectedBlocks (η : Character) (t : ℝ) (S : Finset (Ideal O))
    (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ H : ℝ) : ℂ :=
  ∑ p : ActiveLabel S β, heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)*
    ∑ U : Finset (CommonIndex p.val.1 p.val.2),
      ∑ n : SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
        ((outerScalar p.val.1 p.val.2 K (fun i => (n i : ℤ)) : ℝ) : ℂ)*
          (normalizer p.val.1 p.val.2 U : ℂ)*
          actualSecondChildren η t (activeSource S β) β p.val.1 p.val.2
            (commonLabels_supported (activeSource S β) _ _ p.property).1
            (commonLabels_supported (activeSource S β) _ _ p.property).2 U
            (frequencyRadius Tsec Z ξ)
            (retainedRows (frequencyRadius Tsec Z ξ)
              (commonFrequencyGenerator p.val.1 p.val.2*
                nonunitFrequencyGenerator p.val.1 p.val.2 U)) W K (fun i => (n i : ℤ))

set_option maxHeartbeats 600000 in
theorem actualSecondBlocks_eq_projected (η : Character) (t : ℝ) (S : Finset (Ideal O))
    (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ H : ℝ) (hK : 0 < K) :
    actualSecondBlocks η t S β W K Tsec Z ξ H =
      actualSecondProjectedBlocks η t S β W K Tsec Z ξ H := by
  rw [actualSecondBlocks_eq_normalized η t S β W K Tsec Z ξ H hK]
  unfold actualSecondNormalizedBlocks actualSecondProjectedBlocks
  apply Finset.sum_congr rfl
  intro p hp
  apply congrArg (fun q : ℂ => heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)*q)
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro n hn
  have hcd : primeSupport p.val.1 = primeSupport p.val.2 :=
    (commonLabels_data (supportedColumns (activeSource S β))
      (supportedColumns (activeSource S β)) p.val.1 p.val.2 p.property).2.2
  exact congrArg (fun q : ℂ =>
    (outerScalar p.val.1 p.val.2 K (fun i => (n i : ℤ)) : ℂ)*
      (normalizer p.val.1 p.val.2 U : ℂ)*q)
    (normalizedBlock_eq_actual_children η t (activeSource S β) β p.val.1 p.val.2
      (commonLabels_supported (activeSource S β) _ _ p.property).1
      (commonLabels_supported (activeSource S β) _ _ p.property).2 hcd U _ _ W K _)

theorem commonEnergy_second_blocks {ι : Type*} [Fintype ι]
    (s : OriginalData ι) (C : Ideal O) (hC : Supported C) (τ : Character)
    (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ H : ℝ) (hK : 0 < K)
    (hH : ∀ I ∈ commonSecondColumns s C hC,
      commonSecondBeta s C L I ≠ 0 → (I.absNorm : ℝ) ≤ H) :
    commonEnergy s C hC τ t L W K =
      ((K : ℂ)*paperRadialFourier W 0)*
        sourceSecondZero (commonSecondColumns s C hC) (commonSecondBeta s C L) τ t +
      actualSecondBlocks τ t (commonSecondColumns s C hC) (commonSecondBeta s C L)
        W K Tsec Z ξ H +
      secondDiscardedEnergy τ t (commonSecondColumns s C hC) (commonSecondBeta s C L)
        W K Tsec Z ξ := by
  rw [commonEnergy_eq_second_source, sourceGaussEnergy_localized τ t _ _ W K Tsec Z ξ hK]
  rw [original_secondRetainedEnergy_blocks τ t _ _ W K Tsec Z ξ H hK hH]
  rfl

/-- The smooth ball here is the actual enlarged amplifier majorant. The
same radius is then passed to the exact second Poisson identity. -/
theorem commonEnergy_enlarged_second_blocks {ι : Type*} [Fintype ι]
    (s : OriginalData ι) (C : Ideal O) (hC : Supported C) (τ : Character)
    (t : ℝ) (L : Ideal O) (Z A c d R₁ E₁ M a ω Tsec ξ H : ℝ)
    (hZ : 1 < Z) (hω : 0 ≤ ω)
    (hH : ∀ I ∈ s.columns, s.beta I ≠ 0 → (I.absNorm : ℝ) ≤ H) :
    (∀ h p : O, normValue h ≤ Z^(2*A-c-d+R₁+E₁-M) → normValue p ≤ Z^a →
      1 ≤ (ballProfile (‖eisEmbedding (p^6*h)‖^2 /
        Z^(2*A-c-d+R₁+E₁-M+max (d-c) 0+6*a+ω))).re) ∧
    commonEnergy s C hC τ t L ballProfile
      (Z^(2*A-c-d+R₁+E₁-M+max (d-c) 0+6*a+ω)) =
      ((Z^(2*A-c-d+R₁+E₁-M+max (d-c) 0+6*a+ω) : ℝ) : ℂ)*
        paperRadialFourier ballProfile 0 *
          sourceSecondZero (commonSecondColumns s C hC) (commonSecondBeta s C L) τ t +
      actualSecondNormalizedBlocks τ t (commonSecondColumns s C hC) (commonSecondBeta s C L)
        ballProfile (Z^(2*A-c-d+R₁+E₁-M+max (d-c) 0+6*a+ω)) Tsec Z ξ (H/(C.absNorm : ℝ)) +
      secondDiscardedEnergy τ t (commonSecondColumns s C hC) (commonSecondBeta s C L)
        ballProfile (Z^(2*A-c-d+R₁+E₁-M+max (d-c) 0+6*a+ω)) Tsec Z ξ := by
  refine ⟨?_, ?_⟩
  · intro h p hh hp
    exact actual_enlarged_amplified_ball Z (2*A-c-d+R₁+E₁-M) c d a ω hZ.le hω h p hh hp
  · rw [commonEnergy_second_blocks s C hC τ t L ballProfile _ Tsec Z ξ (H/(C.absNorm : ℝ))
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
      (commonSecond_source_norm_cap s C L hC H hH),
      actualSecondBlocks_eq_normalized _ _ _ _ _ _ _ _ _ _
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)]

/-- The first common indices and first projector remain in the direct sum
when the literal second Poisson identity is applied. -/
theorem joint_commonEnergy_second_blocks {α ι : Type*} [Fintype ι]
    (Λ : Finset α) (s : α → OriginalData ι) (C L : α → Ideal O)
    (hC : ∀ ℓ, Supported (C ℓ)) (τ : α → Character) (t : α → ℝ)
    (W : α → 𝓢(ℝ,ℂ)) (K Tsec Z ξ H : α → ℝ) (weight : α → ℂ)
    (hK : ∀ ℓ ∈ Λ, 0 < K ℓ)
    (hH : ∀ ℓ ∈ Λ, ∀ I ∈ commonSecondColumns (s ℓ) (C ℓ) (hC ℓ),
      commonSecondBeta (s ℓ) (C ℓ) (L ℓ) I ≠ 0 → (I.absNorm : ℝ) ≤ H ℓ) :
    (∑ ℓ ∈ Λ, weight ℓ * commonEnergy (s ℓ) (C ℓ) (hC ℓ) (τ ℓ) (t ℓ) (L ℓ) (W ℓ) (K ℓ)) =
      ∑ ℓ ∈ Λ, weight ℓ *
        (((K ℓ : ℂ)*paperRadialFourier (W ℓ) 0)*
          sourceSecondZero (commonSecondColumns (s ℓ) (C ℓ) (hC ℓ))
            (commonSecondBeta (s ℓ) (C ℓ) (L ℓ)) (τ ℓ) (t ℓ) +
        actualSecondBlocks (τ ℓ) (t ℓ) (commonSecondColumns (s ℓ) (C ℓ) (hC ℓ))
          (commonSecondBeta (s ℓ) (C ℓ) (L ℓ)) (W ℓ) (K ℓ) (Tsec ℓ) (Z ℓ) (ξ ℓ) (H ℓ) +
        secondDiscardedEnergy (τ ℓ) (t ℓ) (commonSecondColumns (s ℓ) (C ℓ) (hC ℓ))
          (commonSecondBeta (s ℓ) (C ℓ) (L ℓ)) (W ℓ) (K ℓ) (Tsec ℓ) (Z ℓ) (ξ ℓ)) := by
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  rw [commonEnergy_second_blocks (s ℓ) (C ℓ) (hC ℓ) (τ ℓ) (t ℓ) (L ℓ)
    (W ℓ) (K ℓ) (Tsec ℓ) (Z ℓ) (ξ ℓ) (H ℓ) (hK ℓ hℓ) (hH ℓ hℓ)]

def secondPrecountFactor (H P : ℝ) (C D : Ideal O)
    (U : Finset (CommonIndex C D)) (K : ℝ) (n : Fin 4 → ℤ) : ℝ :=
  (H*P)⁻¹ * (outerScalar C D K n*normalizer C D U*
    Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)))

theorem secondPrecountFactor_pos (H P : ℝ) (hH : 0 < H) (hP : 0 < P)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (K : ℝ) (hK : 0 < K) (n : Fin 4 → ℤ) :
    0 < secondPrecountFactor H P C D U K n := by
  have hc : 0 < (C.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd : 0 < (D.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hn := normalizer_pos C D hC U
  have hi := dyadicScale_pos (n 2)
  have hj := dyadicScale_pos (n 3)
  unfold secondPrecountFactor outerScalar
  positivity

/-- Normalizing the literal physical block extracts exactly the factor
used before the joint population estimate. -/
theorem actual_physicalBlock_precount (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (R : ℝ) (rows : Finset O)
    (hrows : ∀ z ∈ rows, z ≠ 0) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0 < K)
    (n : Fin 4 → ℤ) (H P : ℝ) :
    ‖physicalBlock η t S β C D hC hD U R rows W K n‖/(H*P) =
      secondPrecountFactor H P C D U K n *
        (‖normalizedBlock η t S β C D hC hD U R rows W K n‖/
          Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3))) := by
  have ho : 0 ≤ outerScalar C D K n := by unfold outerScalar; positivity
  have hn : 0 ≤ normalizer C D U := (normalizer_pos C D hC U).le
  have hs : Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)) ≠ 0 :=
    (Real.sqrt_pos.mpr (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))).ne'
  rw [physicalBlock_eq η t S β C D hC hD U R rows hrows W K hK n,
    norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ho,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn]
  unfold secondPrecountFactor
  field_simp

theorem actual_second_precount_log (H P Z : ℝ) (hH : 0 < H) (hP : 0 < P)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (K : ℝ) (hK : 0 < K) (n : Fin 4 → ℤ) :
    Real.logb Z (secondPrecountFactor H P C D U K n) =
      -Real.logb Z H + (Real.logb Z K-Real.logb Z H)-Real.logb Z P +
      (Real.logb Z (Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}) : ℝ)-
        Real.logb Z ((∏ Q ∈ U, Q.val).absNorm : ℝ)) +
      (Real.logb Z H-(Real.logb Z (C.absNorm : ℝ)+Real.logb Z (D.absNorm : ℝ))/2) := by
  have hf : 0 < outerScalar C D K n*normalizer C D U*
      Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)) := by
    simpa only [secondPrecountFactor, one_mul, inv_one] using
      secondPrecountFactor_pos 1 1 (by norm_num) (by norm_num) C D hC hD U K hK n
  unfold secondPrecountFactor
  rw [Real.logb_mul (inv_ne_zero (mul_pos hH hP).ne') hf.ne', Real.logb_inv,
    Real.logb_mul hH.ne' hP.ne', actual_prefactor_log C D hC hD U K Z hK n]
  ring

/-- Substitution of the actual enlarged radial scale gives precisely the
outside exponent in the joint high-bin ledger. -/
theorem enlarged_second_precount_log (Z A c d R₁ E₁ M a ω : ℝ) (hZ : 1 < Z)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (n : Fin 4 → ℤ) :
    Real.logb Z (secondPrecountFactor (Z^(A-c)) (Z^a) C D U
      (Z^(2*A-c-d+R₁+E₁-M+max (d-c) 0+6*a+ω)) n) =
      A-min c d+R₁+E₁-M+5*a+ω+
        Real.logb Z (Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}) : ℝ)-
        Real.logb Z ((∏ Q ∈ U, Q.val).absNorm : ℝ)-
        (Real.logb Z (C.absNorm : ℝ)+Real.logb Z (D.absNorm : ℝ))/2 := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  rw [actual_second_precount_log _ _ Z (Real.rpow_pos_of_pos hz _) (Real.rpow_pos_of_pos hz _)
    C D hC hD U _ (Real.rpow_pos_of_pos hz _) n]
  simp only [Real.logb_rpow hz hZ.ne']
  rcases le_total c d with hcd | hdc
  · rw [min_eq_left hcd, max_eq_left (sub_nonneg.mpr hcd)]
    ring
  · rw [min_eq_right hdc, max_eq_right (sub_nonpos.mpr hdc)]
    ring

theorem enlarged_second_precount_factor (Z A c d R₁ E₁ M a ω : ℝ) (hZ : 1 < Z)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (n : Fin 4 → ℤ) :
    secondPrecountFactor (Z^(A-c)) (Z^a) C D U
      (Z^(2*A-c-d+R₁+E₁-M+max (d-c) 0+6*a+ω)) n =
      Z^(A-min c d+R₁+E₁-M+5*a+ω+
        Real.logb Z (Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}) : ℝ)-
        Real.logb Z ((∏ Q ∈ U, Q.val).absNorm : ℝ)-
        (Real.logb Z (C.absNorm : ℝ)+Real.logb Z (D.absNorm : ℝ))/2) := by
  rw [← enlarged_second_precount_log Z A c d R₁ E₁ M a ω hZ C D hC hD U n]
  exact (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne'
    (secondPrecountFactor_pos _ _ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) C D hC hD U _
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) n)).symm

/-- The entire pre-count expression is an identity for the actual second
physical block, with the exact enlarged radius and exact projector/ray
children. It contains no count or pointwise-bound hypothesis. -/
theorem actual_enlarged_secondBlock_precount (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D) (U : Finset (CommonIndex C D))
    (R : ℝ) (rows : Finset O) (hrows : ∀ z ∈ rows, z ≠ 0)
    (W : 𝓢(ℝ,ℂ)) (n : Fin 4 → ℤ)
    (Z A c d R₁ E₁ M a ω : ℝ) (hZ : 1 < Z) :
    ‖physicalBlock η t S β C D hC hD U R rows W
      (Z^(2*A-c-d+R₁+E₁-M+max (d-c) 0+6*a+ω)) n‖/(Z^(A-c)*Z^a) =
      Z^(A-min c d+R₁+E₁-M+5*a+ω+
        Real.logb Z (Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}) : ℝ)-
        Real.logb Z ((∏ Q ∈ U, Q.val).absNorm : ℝ)-
        (Real.logb Z (C.absNorm : ℝ)+Real.logb Z (D.absNorm : ℝ))/2) *
        (‖actualSecondChildren η t S β C D hC hD U R rows W
          (Z^(2*A-c-d+R₁+E₁-M+max (d-c) 0+6*a+ω)) n‖/
          Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3))) := by
  rw [actual_physicalBlock_precount η t S β C D hC hD U R rows hrows W _
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) n,
    enlarged_second_precount_factor Z A c d R₁ E₁ M a ω hZ C D hC hD U n,
    normalizedBlock_eq_actual_children η t S β C D hC hD hCD]

#print axioms commonEnergy_second_blocks
#print axioms joint_commonEnergy_second_blocks
#print axioms actualSecondBlocks_eq_normalized
#print axioms normalizedBlock_eq_actual_children
#print axioms secondBlockChildCoefficient_eq_ray_row
#print axioms joint_normalizedBlock_eq_actual_children
#print axioms actualSecondBlocks_eq_projected
#print axioms commonEnergy_enlarged_second_blocks
#print axioms actual_physicalBlock_precount
#print axioms actual_second_precount_log
#print axioms enlarged_second_precount_factor
#print axioms actual_enlarged_secondBlock_precount
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointSecondBlock -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.MomentDetectorPlainMomentParameters ; sha256 f1c8b6c7a31d648d8cef660833b7fc85b9a4f4edf0087ddbe051e6fa321fd2e9 -/
section




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.Cycle25CenteredMomentDetectorPlainMomentParameters
open CenteredMomentDetectorPlainMomentParameters Cycle25ProbeFinalAssembly
open HeckeFamily HeckeDetectorRawFiber HeckeDetectorBatch ProbeHighRowFamily
open CenteredMomentDetectorDictionary
open CenteredMomentEnergyState CenteredMomentEnergyBands
open Cycle25CenteredMomentDetectorEnergyInitialState Cycle25CenteredMomentDetectorPlainMarkedState
open CenteredMomentDetectorEnergyInitialState CenteredMomentDetectorPlainMarkedState
open CenteredMomentDetectorPlainUnmarkedState Cycle25CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorPlainUnmarkedState CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O


def weighted_delta (D:Cycle25.Weighted.MomentData):ℝ := D.t/4
def weighted_stageError (D:Cycle25.Weighted.MomentData):ℝ := D.t/4
def weighted_kappaPlain (_D:Cycle25.Weighted.MomentData):ℝ := 3/4

theorem weighted_fixed_parameters (D:Cycle25.Weighted.MomentData):
    0< weighted_delta D ∧ weighted_delta D ≤ 1/4 ∧ 0< weighted_stageError D ∧
    weighted_delta D+weighted_stageError D ≤ D.t ∧ 3/4 ≤ weighted_kappaPlain D ∧ 0< weighted_kappaPlain D := by
  dsimp [weighted_delta,weighted_stageError,weighted_kappaPlain]
  constructor
  · exact div_pos D.t_pos (by norm_num)
  constructor
  · linarith [D.t_small]
  constructor
  · exact div_pos D.t_pos (by norm_num)
  constructor
  · linarith [D.t_pos]
  constructor <;> linarith

lemma weighted_source_base_gt_one (_D:Cycle25.Weighted.MomentData)(Z d:ℝ)
    (hZ:1< Z)(hd:(1/200:ℝ) ≤ d):1< Z^d :=
  Real.one_lt_rpow hZ (by linarith)

lemma weighted_witness_length_cap (D:Cycle25.Weighted.MomentData):
    1/2+75*D.ε ≤ (23/40:ℝ) := by linarith [D.epsilon_small]

variable {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label:Type*}
variable {U a tstar T heightAllowance:ℝ}{i:ℕ}

theorem weighted_actual_fiber_lengths (D:Cycle25.Weighted.MomentData)
    (F:Fiber M H Label (Fin D.N) U a D.ε tstar T heightAllowance i)(hU:1< U):
    0 ≤ F.m ∧ F.m ≤ 1/2+75*D.ε ∧ F.m ≤ 23/40 ∧
    1 ≤ U^F.m ∧ U^F.m ≤ U ∧ length U (U^F.m)=F.m := by
  have hm:=F.lengths hU
  have hcap:=hm.2.2.1.trans (weighted_witness_length_cap D)
  refine ⟨hm.2.2.2.2,hm.2.2.1,hcap,Real.one_le_rpow hU.le hm.2.2.2.2,?_,?_⟩
  · simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hU.le (show F.m ≤ 1 by linarith)
  · exact weighted_plain_length_eq F hU

lemma weighted_width_bands (D:Cycle25.Weighted.MomentData)(m:ℝ)(hm:m ≤ 23/40):
    1 ≤ 1+weighted_delta D ∧ 1+weighted_delta D ≤ 2 ∧
    1 ≤ max 1 (2*m)+weighted_delta D ∧ max 1 (2*m)+weighted_delta D ≤ 2 := by
  have hδ:0< weighted_delta D:=(weighted_fixed_parameters D).1
  have hd:weighted_delta D ≤ 1/4:=(weighted_fixed_parameters D).2.1
  have hmax:max 1 (2*m) ≤ 23/20:=max_le (by norm_num) (by linarith)
  have hlo:=le_max_left (1:ℝ) (2*m)
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem weighted_unmarked_state_admission (D:Cycle25.Weighted.MomentData)
    (F:Fiber M H Label (Fin D.N) U a D.ε tstar T heightAllowance i)
    (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ:ℝ)(hU:1< U)
    (hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)(hp:∀x,0 ≤ (Φ x).re)
    (hη:(η.modulus.absNorm:ℝ) ≤ U^(weighted_delta D)):
    let s:=state F η Q Φ bΦ (weighted_delta D) hU.le (weighted_fixed_parameters D).1.le hs hp hη;
    s.character=η ∧ s.fixedModulus=Q ∧ s.puncture=1 ∧
    s.radial.profile=Φ ∧ s.radial.scale=U ∧ s.radial.keep=weighted_initialKeep η Q ∧
    s.width=max 1 (2*F.m)+weighted_delta D ∧ 1 ≤ s.width ∧ s.width ≤ 2 ∧
    1 ≤ U^F.m ∧ U^F.m ≤ U ∧ 2*length U (U^F.m) ≤ s.width := by
  dsimp only
  have hf:=weighted_actual_fiber_lengths D F hU
  have hw:=weighted_width_bands D F.m hf.2.2.1
  have he:(state F η Q Φ bΦ (weighted_delta D) hU.le (weighted_fixed_parameters D).1.le hs hp hη).width=
      max 1 (2*F.m)+weighted_delta D:=padded_width _ _
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,he,?_,?_,hf.2.2.2.1,hf.2.2.2.2.1,?_⟩
  · rw [he];exact hw.2.2.1
  · rw [he];exact hw.2.2.2
  · rw [he,hf.2.2.2.2.2]
    exact (le_max_right 1 (2*F.m)).trans (le_add_of_nonneg_right (weighted_fixed_parameters D).1.le)

theorem weighted_source_label_fixed_allowance (D:Cycle25.Weighted.MomentData)
    (S:Cycle25ProbeFinalAssembly.WeightedSourceData D)(η:Character):
    ∀ᶠZ:ℝ in atTop,1< Z ∧
      ∀label:Sum Bool (RayQuotient.Characters S.modulus ⊤),∀d:ℝ,(1/200:ℝ) ≤ d→
      ((sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label).modulus.absNorm:ℝ)
         ≤ (Z^d)^(weighted_delta D) :=
  weighted_source_label_modulus_eventually S η (weighted_delta D) (weighted_fixed_parameters D).1

lemma weighted_final_exponent_budget (D:Cycle25.Weighted.MomentData)(base:ℝ):
    base+weighted_delta D+weighted_stageError D ≤ base+D.t := by
  linarith [(weighted_fixed_parameters D).2.2.2.1]

end SevenEighths.Cycle25CenteredMomentDetectorPlainMomentParameters

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.MomentDetectorPlainMomentParameters -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.WeightedSourceCount ; sha256 62bbec578447ef9d141553d2d1e53cfa77e19b1cf15f9cef46c046f31b7e4816 -/
section






/-! Source specialization of the original certified amplitude-class row count.
This stops before any physical numerator estimate. -/
noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace OAI.SevenEighths.Cycle25WeightedHighFinalAssembly
open Cycle25ProbeFinalAssembly Cycle25ProbeHighRowFamily Cycle25WeightedHighRowFamily
open ProbeFinalAssembly ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O

theorem weighted_source_amplitude_count {Δ : ℝ}
    (D : Cycle25.HighParameters.HighData Δ) (F : WeightedSourceData D.toMomentData)
    (counts : Cycle25ProbeHighRowFamily.CountParameters F.modulus ⊤ D.t) (τ : ℝ) (n : ℕ)
    (hτ : 0 < τ) (hτzero : τ < (1/200:ℝ)/2)
    (hτheight : 4*τ < (1/200:ℝ)*D.cost) (hτ2 : 2*τ ≤ D.t) :
    ∃C : ℝ,1 ≤ C ∧ ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d a C0 : ℝ,(1/200:ℝ) ≤ d → d ≤ 7/8 → 51/100 < a → a ≤ 7/8 → 1 ≤ C0 →
      ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ) ≤ rowNorm u ∧
        (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u ≤ Z^(d-D.t)) →
      ∀i : ℕ,i ≤ n →
      (∀u∈rows,detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        (3*(i+1:ℕ)*Z^τ) < a+2*D.e) →
      (∀u∈rows,a ≤ detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        ((3*i:ℕ)*Z^τ)) →
      ∀z : ℂ,z.re=17/50 → |z.im| ≤ Z^(2*τ) →
      weighted_SourceMomentBound F D.momentKappa counts η Z τ (C0*Z^D.t) (Z^(2*τ)) →
      let Q := physical F.modulus ⊤ (fun u : FreeRow=> u.val) (fun _ y=>(F.w y:ℂ))
        (fun _=>2) (fun j=> D.ell j/d) (fun _=> z) (Z^d)
      ∀bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t,
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun j=> D.ell j/d) Q bin
      let q := classMean Finset.univ ((2*a-1)/2) D.t (fun j=> D.ell j/d) bin
      rows'.Nonempty → 0 ≤ q ∧ q ≤ (2*a-1)/2 ∧
        (rows'.card:ℝ) ≤ C*C0*Z^(3*D.t)*
          (Z^d)^(Cycle25DetectorRowCount.rowCount (2*a-1) (q/(2*a-1)) D.momentKappa+(159*D.ε+9*D.t)) := by
  obtain ⟨K,hK,hcount⟩ := Cycle25ProbeFinalAssembly.balanced_source_count_from_raw_moments F.modulus ⊤ le_top F.S
    F.w F.smooth F.compact F.positive_support (fun y=>(F.bounded y).1) F.nonzero
    1 2 1 (by norm_num) (by norm_num) (by norm_num) F.support (fun y=>(F.bounded y).2)
    D.t D.t_pos (Sum Bool (RayQuotient.Characters F.modulus ⊤)) D.N n
    (1/200) (7/8) τ D.t (2*τ) D.t D.t
    (by norm_num) (by norm_num) hτ D.t_pos (by linarith) D.t_pos counts
  refine ⟨K+1,by linarith,?_⟩
  intro η
  have hbatches := Cycle25WeightedHighRowFamily.actual_source_amplitude_batches F.modulus ⊤ le_top F.S F.exclusions F.maximal η
    (1/200) (7/8) τ D.ε D.e D.κ D.cost D.t D.t D.t D.momentKappa n
    (by norm_num) (by norm_num) D.momentKappa_lo D.momentKappa_hi hτ hτzero hτheight
    D.epsilon_pos D.e_pos D.e_small D.kappa_pos D.kappa_small D.cost_pos.le
    D.t_pos D.t_pos.le D.t_pos (by nlinarith only [D.detector_budget])
  filter_upwards [hcount,hbatches,eventually_gt_atTop (1:ℝ)] with Z hc hb hZ
  intro d a C0 hd hd' ha ha' hC0 rows hrows i hi hnext hcurrent z hz hzim hmom
  dsimp only
  intro bin hne
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  have hdpos : 0 < d := by linarith
  let Q := physical F.modulus ⊤ (fun u : FreeRow=> u.val) (fun _ y=>(F.w y:ℂ))
    (fun _=>2) (fun j=> D.ell j/d) (fun _=> z) (Z^d)
  let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos
    (fun j=> D.ell j/d) Q bin
  let q := classMean Finset.univ ((2*a-1)/2) D.t (fun j=> D.ell j/d) bin
  have hsub : rows'⊆rows := Finset.filter_subset _ _
  have hband : rows⊆rowBand (Z^(1/100:ℝ)) (Z^(d-D.t)+1) := by
    intro u hu
    exact mem_rowBand.mpr ⟨(hrows u hu).1,(hrows u hu).2.1,by linarith [(hrows u hu).2.2.2]⟩
  obtain ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW,hUpper,hExternal,hMesh,hBin,hFam,hMean⟩ :=
    hb d hd hd' (Z^(d-D.t)+1) rows (hne.mono hsub) hband
      (fun u hu=>(hrows u hu).2.2.1) (fun u hu=>(hrows u hu).2.2.2)
      a i hi ha (by linarith) hnext hcurrent D.N D.ell (fun j=>(D.slots_bounds j).1)
      (fun j=>(D.slots_bounds j).2.2) (by rw [D.slots_sum]; linarith [Cycle25.ell_interval.1]) (fun _ y=>(F.w y:ℂ))
      (fun _=>2) (fun _=> z) bin hne
  have hBsub : B.rows⊆rows := hBr ▸ hsub
  have hBfam : ∀u∈B.rows,∀j,B.family u j=
      sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u) j := by
    intro u hu j
    exact hFam u (hBr ▸ hu) j
  have hraw := (hmom rows d a hd hd' ha (by linarith) hrows i z hz hzim)
    q B hBsub hBd hRev hSlots hWidths hW hUpper hExternal hMesh hBin hBfam
  have hcard := hc d hd hd' a D.ε D.momentKappa D.t C0 q i hi ha (by linarith) (by linarith)
    D.epsilon_pos.le D.epsilon_small D.momentKappa_lo D.momentKappa_hi D.t_pos (by linarith)
    B (by rw [hSlots];simp) hBin (hBr.symm ▸ hne) hMean hraw
  rw [hBr,hMesh] at hcard
  have hqb := classMean_bounds rows Finset.univ (Z^d) (2*a-1) D.t D.t_pos
    (fun j=> D.ell j/d) Q bin (by linarith)
    (fun j _=>(div_pos (D.slots_bounds j).1 hdpos).le)
    (by rw [←Finset.sum_div,D.slots_sum]; exact div_pos Cycle25.ell_pos hdpos) hne
  refine ⟨hqb.1,hqb.2,?_⟩
  have he : Cycle25DetectorRowCount.rowCount (2*a-1) (q/(2*a-1)) D.momentKappa+159*D.ε+D.t+D.t+7*D.t=Cycle25DetectorRowCount.rowCount (2*a-1) (q/(2*a-1)) D.momentKappa+(159*D.ε+9*D.t) := by ring
  rw [he] at hcard
  apply hcard.trans
  have hC0pos : 0 ≤ C0 := by linarith
  have hcp : 0 ≤ (Z^d)^(Cycle25DetectorRowCount.rowCount (2*a-1) (q/(2*a-1)) D.momentKappa+(159*D.ε+9*D.t)) := by positivity
  apply mul_le_mul_of_nonneg_right _ hcp
  apply mul_le_mul
  · nlinarith
  · apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith
  · positivity
  · positivity

end OAI.SevenEighths.Cycle25WeightedHighFinalAssembly
end
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.WeightedSourceCount -/
