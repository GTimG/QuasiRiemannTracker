/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.reserve_local_20261013.Bundles.B033
import Submissions.reserve_local_20261013.Bundles.B044
import Submissions.reserve_local_20261013.Bundles.B071
import Submissions.reserve_local_20261013.Bundles.B087
import Submissions.reserve_local_20261013.Bundles.B092
import Submissions.reserve_local_20261013.Bundles.B097
import Submissions.reserve_local_20261013.Bundles.B098
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowCommonBound
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ChildEnvelopeFitting
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.FirstLiveAdmission
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalBudget
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.MobiusHarmonicMass

/- BEGIN ORIGINAL MODULE Analytic.JointLowAbsorption ; sha256 345cda568221f7def920a7aa57b00241118b9f8b5b14c02fccb078a21165de68 -/
section




/-! Uniform absorption of the actual low source profile, finite-deletion
and bounded Fourier-height costs. The original two profiles stay fixed. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentCommonRadialPointwise CenteredMomentEligibleEnergy
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound
open CenteredMomentEnergyChildEnvelopeFitting CenteredMomentFirstAmplificationChoice
local notation "O" => HeckeFamily.O

def lowProfileConstant {ι : Type*} [Fintype ι] (M upper b₁ b₂ : ℝ) : ℝ :=
  2*(max 1 b₁*max 1 b₂)*(M^Fintype.card ι)^4*(max 1 upper)^Fintype.card ι

theorem low_profileCost_le_fixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (M upper b₁ b₂ : ℝ) (hM : 0 ≤ M)
    (hs : ∀ i, s.M i ≤ M) (hu : s.upper ≤ upper) (hb₁ : s.b₁ ≤ b₁) (hb₂ : s.b₂ ≤ b₂) :
    profileCost s ≤ lowProfileConstant (ι := ι) M upper b₁ b₂ := by
  have hp := input_profile_mass_le s M hM hs
  have hpn : 0 ≤ ∏ i,s.M i := Finset.prod_nonneg (fun i _ => zero_le_one.trans (s.M_ge_one i))
  calc
    _ = 2*(max 1 s.b₁*max 1 s.b₂)*(∏ i,s.M i)^4*(max 1 s.upper)^Fintype.card ι := by
      unfold profileCost Data.profileFactor
      change ((∏ i,s.M i)^2*(max 1 s.upper)^Fintype.card ι)*
        ((2*(max 1 s.b₁*max 1 s.b₂))*(∏ i,s.M i)^2) = _
      ring
    _ ≤ lowProfileConstant (ι := ι) M upper b₁ b₂ := by unfold lowProfileConstant; gcongr

lemma low_cube_height_power (Z ν vBound height : ℝ) (degree : ℕ)
    (hZ : 1 ≤ Z) (hν : 0 ≤ ν) (hv0 : 0 ≤ vBound) (hh0 : 0 ≤ height)
    (hv : vBound ≤ (1+4*Real.pi)*Z^ν) (hh : height ≤ Z^ν) :
    (1+vBound+height)^degree ≤ (3+4*Real.pi)^degree*Z^(ν*(degree : ℝ)) := by
  have hz : 1 ≤ Z^ν := Real.one_le_rpow hZ hν
  have hb : 1+vBound+height ≤ (3+4*Real.pi)*Z^ν := by nlinarith [Real.pi_pos]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1+vBound+height) hb degree
  rw [mul_pow] at hp
  have heq : (Z^ν)^degree = Z^(ν*(degree : ℝ)) := by
    rw [←Real.rpow_natCast (Z^ν),←Real.rpow_mul (zero_le_one.trans hZ)]
  rw [heq] at hp
  exact hp

def lowFixedCoefficient {ι : Type*} [Fintype ι] {a b : ℝ}
    (C M upper b₁ b₂ : ℝ) (p : Profiles a b) (S : Finset (ℕ × ℕ)) (degree : ℕ) : ℝ :=
  C*lowProfileConstant (ι := ι) M upper b₁ b₂*diagonalControl ballProfile*
    (p.control S)^2*(3+4*Real.pi)^degree

theorem low_fixed_coefficient_nonneg {ι : Type*} [Fintype ι] {a b : ℝ}
    (C M upper b₁ b₂ : ℝ) (p : Profiles a b) (S : Finset (ℕ × ℕ)) (degree : ℕ)
    (hC : 0 ≤ C) : 0 ≤ lowFixedCoefficient (ι := ι) C M upper b₁ b₂ p S degree := by
  unfold lowFixedCoefficient lowProfileConstant
  have hd := diagonalControl_nonneg ballProfile
  positivity

theorem low_actual_coefficient_absorbed {ι : Type*} [Fintype ι] [DecidableEq ι] {a b : ℝ}
    (s : Input ι) (p : Profiles a b) (S : Finset (ℕ × ℕ)) (degree : ℕ)
    (R Cideal : Ideal O) (hR : R ≠ 0) (hCi : Cideal ≠ 0)
    (Z Cbound M upper b₁ b₂ BR BC εmask ν vBound height : ℝ)
    (hZ : 1 ≤ Z) (hCb : 0 ≤ Cbound) (hM : 0 ≤ M) (he : 0 ≤ εmask) (hν : 0 ≤ ν)
    (hs : ∀ i,s.M i ≤ M) (hu : s.upper ≤ upper) (hb₁ : s.b₁ ≤ b₁) (hb₂ : s.b₂ ≤ b₂)
    (hRN : (R.absNorm : ℝ) ≤ Z^BR) (hCN : (Cideal.absNorm : ℝ) ≤ Z^BC)
    (hv0 : 0 ≤ vBound) (hh0 : 0 ≤ height)
    (hv : vBound ≤ (1+4*Real.pi)*Z^ν) (hh : height ≤ Z^ν) :
    Cbound*((R*Cideal).radical.absNorm : ℝ)^εmask*profileCost s*
      diagonalControl ballProfile*(p.control S)^2*(1+vBound+height)^degree ≤
      lowFixedCoefficient (ι := ι) Cbound M upper b₁ b₂ p S degree*
        Z^((BR+BC)*εmask+ν*(degree : ℝ)) := by
  have hr := radical_product_power R Cideal hR hCi Z BR BC εmask (zero_lt_one.trans_le hZ) he hRN hCN
  have hp := low_profileCost_le_fixed s M upper b₁ b₂ hM hs hu hb₁ hb₂
  have ht := low_cube_height_power Z ν vBound height degree hZ hν hv0 hh0 hv hh
  have hpc := profileCost_nonneg s
  have hdiag := diagonalControl_nonneg ballProfile
  have hpf : 0 ≤ lowProfileConstant (ι := ι) M upper b₁ b₂ := by unfold lowProfileConstant; positivity
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  calc
    _ ≤ Cbound*Z^((BR+BC)*εmask)*lowProfileConstant (ι := ι) M upper b₁ b₂*
      diagonalControl ballProfile*(p.control S)^2*((3+4*Real.pi)^degree*Z^(ν*(degree : ℝ))) := by gcongr
    _ = _ := by unfold lowFixedCoefficient; rw [Real.rpow_add (zero_lt_one.trans_le hZ)]; ring

#print axioms low_actual_coefficient_absorbed
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowAbsorption -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowHarmonic ; sha256 1976590c4a59e94c9cb4ef7129289fa2b61acd5b092c6ca176de4d8636667a63 -/
section



/-! Actual second common, partition, dyadic and projector harmonic mass.
The first common coefficient is retained literally throughout. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss CenteredMomentSecondBlockHarmonicMass
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCanonicalFirst CenteredMomentFirstAmplificationChoice
open CenteredMomentMobiusHarmonicMass CenteredMomentOriginalCommonHarmonic
open CenteredMomentFixedRay RayFourExpansion
local notation "O" => HeckeFamily.O

theorem actual_common_second_projector_harmonic_mass
    (B Bproj L Cr ε : ℝ) (hB : 0 ≤ B) (hBproj : 0 ≤ Bproj) (hL : 0 ≤ L)
    (hCr : 0 < Cr) (hε : 0 < ε) :
    ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (src : Input ι) (R seed C₁ L₁ : Ideal O) (hC₁ : Supported C₁),
      src.W₁ 0 = 0 → src.W₂ 0 = 0 → sourceRadius src/(C₁.absNorm : ℝ) ≤ Z^B →
      ∀ K Radius Hsource : ℝ, 0 < K → Radius ≤ Cr*Z^L → Hsource ≤ Z^B →
      let columns := commonSecondColumns (original src R seed) C₁ hC₁
      let β := commonSecondBeta (original src R seed) C₁ L₁
      ∀ Ds : ActiveBlocks columns β K Radius Hsource → Finset (Ideal O),
      (∀ q, ∀ D ∈ Ds q, (UniqueFactorizationMonoid.moebius D : ℂ) ≠ 0 →
        (D.absNorm : ℝ) ≤ Z^Bproj) →
      (∑ q : ActiveBlocks columns β K Radius Hsource, ∑ D ∈ Ds q,
        (‖(UniqueFactorizationMonoid.moebius D : ℂ)‖/(D.absNorm : ℝ))*
          pairWeight q.1.1.val.1 q.1.1.val.2) ≤ Cbound*Z^ε := by
  obtain ⟨Cb,hCb,hblocks⟩ := actual_block_harmonic_mass B L Cr (ε/2) hB hL hCr (by positivity)
  obtain ⟨Cd,hCd,hdivs⟩ := full_mass_subpower Bproj (ε/2) hBproj (by positivity)
  refine ⟨Cd*Cb,mul_pos hCd hCb,?_⟩
  filter_upwards [hblocks,hdivs] with Z hblocks hdivs
  refine ⟨hdivs.1,?_⟩
  intro ι instF instD src R seed C₁ L₁ hC₁ hz₁ hz₂ hsource K Radius Hsource hK hRadius hH columns β Ds hDs
  have hZ0 : 0 < Z := zero_lt_one.trans hdivs.1
  have hnorm : ∀ I ∈ columns, β I ≠ 0 → (I.absNorm : ℝ) ≤ Z^B := by
    intro I hI hβ
    exact (commonSecond_source_norm_cap (original src R seed) C₁ L₁ hC₁ (sourceRadius src)
      (fun J _ hJ => (original_column_norm src R seed J hz₁ hz₂ hJ).2) I hI hβ).trans hsource
  have hm := hblocks (1 : Ideal O) squarefree_one one_ne_zero columns β
    (fun I _ _ => one_dvd I) hnorm K Radius Hsource hK hRadius hH
  simp only [map_one,Nat.cast_one,div_one] at hm
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
    _ ≤ (Cd*Z^(ε/2))*(Cb*Z^(ε/2)) := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = (Cd*Cb)*(Z^(ε/2)*Z^(ε/2)) := by ring
    _ = (Cd*Cb)*Z^ε := by rw [←Real.rpow_add hZ0,add_halves]

/-- The finite ray projector contributes only its established absolute
mass; this operation leaves the second common harmonic weight intact. -/
lemma actual_second_ray_harmonic_factor (C D L : Ideal O) :
    (∑ χ : RayCharacter, ∑ ξ : RayCharacter,
      ‖pairCoeff (phaseTable (primaryGenerator C) (primaryGenerator D)) χ ξ‖ *
        ((‖(UniqueFactorizationMonoid.moebius L : ℂ)‖/(L.absNorm : ℝ))*pairWeight C D)) ≤
      256*((‖(UniqueFactorizationMonoid.moebius L : ℂ)‖/(L.absNorm : ℝ))*pairWeight C D) := by
  simp only [←Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (phaseTable_mass (primaryGenerator C) (primaryGenerator D))
    (mul_nonneg (div_nonneg (norm_nonneg _) (Nat.cast_nonneg _)) (pairWeight_nonneg _ _))

#print axioms actual_common_second_projector_harmonic_mass
#print axioms actual_second_ray_harmonic_factor
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowHarmonic -/

/- BEGIN ORIGINAL MODULE Analytic.JointSourceRowGeometry ; sha256 ae22c1e9dc0b58662f8cfc72d9ab104f4c130fd045440cbbf506ce74205bb546 -/
section




/-! Actual source row and missing-radical caps from retained frequency
support and one-sided source norm sectors. No row population bound is a premise. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI
noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.Local44.Analytic
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open CompletedGauss ConcretePrimeRowBridge CenteredMomentCanonicalFirst CenteredMomentActive
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalLedger
open CenteredMomentCompleteCommon CenteredMomentRankinRadical
open CenteredMomentSectorLocalization CenteredMomentSecondLiveBlock
open CenteredMomentFirstAmplificationChoice
open RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem swappedFirstSubset_principal (C D : Ideal O) (E : Finset (CommonIndex C D))
    (hE : E ∈ (principalSupport Finset.univ (leftExponent C D) (rightExponent C D)).powerset) :
    swappedFirstSubset C D E ∈
      (principalSupport Finset.univ (leftExponent D C) (rightExponent D C)).powerset := by
  apply Finset.mem_powerset.mpr
  intro P hP
  obtain ⟨Q,hQ,rfl⟩ := Finset.mem_map.mp hP
  have hq := (Finset.mem_filter.mp ((Finset.mem_powerset.mp hE) hQ)).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  change netExponent (rightExponent C D Q) (leftExponent C D Q) = 0
  unfold netExponent at *
  omega

/-- The source radius remains H/N(C₁), while sector endpoints need only
bound the common norm below, the numerator norms above, and K below. -/
theorem joint_row_geometry_sector (C₁ D₁ C₂ D₂ : Ideal O)
    (E : Finset (CommonIndex C₁ D₁)) (u : Oˣ)
    (U : Finset (CommonIndex C₂ D₂)) (h : O)
    (Z A c d R e M a ω L H εH εE ξ K : ℝ) (hZ : 1 < Z)
    (hH₀ : 0 ≤ H) (hH : H ≤ Z^(A+εH))
    (hC : Z^c ≤ (C₁.absNorm : ℝ))
    (hE : normValue (primeSubsetGenerator (fun P : CommonIndex C₁ D₁ => P.val) E) ≤ Z^(e+εE))
    (hF : normValue (leftEffectiveFactor C₁ D₁) ≤ Z^L)
    (hK : Z^(2*A-c-d+R+e-M+max (d-c) 0+6*a+ω) ≤ K)
    (hret : retainedWeight (frequencyRadius ((H/(C₁.absNorm : ℝ))^2/K) Z ξ)
      (normValue (commonFrequencyGenerator C₂ D₂*nonunitFrequencyGenerator C₂ D₂ U*h)) ≠ 0) :
    normValue (jointLeftRow C₁ D₁ C₂ D₂ E u U h) ≤
      4*Z^(M-R-max (c-d) 0+L-6*a-ω+2*εH+εE+ξ/2) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hcpow : 0 < Z^c := Real.rpow_pos_of_pos hz _
  have hkpow : 0 < Z^(2*A-c-d+R+e-M+max (d-c) 0+6*a+ω) := Real.rpow_pos_of_pos hz _
  have hk : 0 < K := hkpow.trans_le hK
  have hdiv : H/(C₁.absNorm : ℝ) ≤ Z^(A+εH)/Z^c :=
    (div_le_div_of_nonneg_left hH₀ hcpow hC).trans
      (div_le_div_of_nonneg_right hH hcpow.le)
  have hsq := pow_le_pow_left₀ (div_nonneg hH₀ (Nat.cast_nonneg _)) hdiv 2
  have hratio : (H/(C₁.absNorm : ℝ))^2/K ≤
      (Z^(A+εH)/Z^c)^2/Z^(2*A-c-d+R+e-M+max (d-c) 0+6*a+ω) :=
    (div_le_div_of_nonneg_right hsq hk.le).trans
      (div_le_div_of_nonneg_left (sq_nonneg _) hkpow hK)
  have hr := (retainedWeight_enclosure _ _ hret).2
  have he₀ : 0 ≤ normValue (primeSubsetGenerator (fun P : CommonIndex C₁ D₁ => P.val) E) := by
    unfold normValue; positivity
  have hf₀ : 0 ≤ normValue (leftEffectiveFactor C₁ D₁) := by unfold normValue; positivity
  have hw₀ : 0 ≤ normValue (commonFrequencyGenerator C₂ D₂*nonunitFrequencyGenerator C₂ D₂ U*h) := by
    unfold normValue; positivity
  rw [jointLeftRow_norm]
  calc
    _ ≤ Z^(e+εE)*Z^L*(4*frequencyRadius ((H/(C₁.absNorm : ℝ))^2/K) Z ξ) := by
      gcongr
    _ ≤ Z^(e+εE)*Z^L*(4*((Z^(A+εH)/Z^c)^2/
        Z^(2*A-c-d+R+e-M+max (d-c) 0+6*a+ω)*Z^(ξ/2))) := by
      unfold frequencyRadius
      gcongr
    _ = _ := by
      rw [←Real.rpow_sub hz,←Real.rpow_natCast (Z^(A+εH-c)) 2,
        ←Real.rpow_mul hz.le,←Real.rpow_sub hz]
      simp only [mul_assoc]
      rw [mul_left_comm (Z^L) 4,←mul_assoc,mul_comm (Z^(e+εE)) 4,
        mul_assoc,←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz]
      congr 2
      have hm : max (c-d) 0-max (d-c) 0 = c-d := by
        rcases le_total c d with hcd | hdc
        · rw [max_eq_right (sub_nonpos.mpr hcd),max_eq_left (sub_nonneg.mpr hcd)]; ring
        · rw [max_eq_left (sub_nonneg.mpr hdc),max_eq_right (sub_nonpos.mpr hdc)]; ring
      push_cast
      linarith

theorem joint_missing_geometry_sector (C₁ D₁ C₂ D₂ : Ideal O)
    (hC₁ : Supported C₁) (hCD₁ : primeSupport C₁ = primeSupport D₁)
    (E : Finset (CommonIndex C₁ D₁))
    (hE : E ∈ (principalSupport Finset.univ (leftExponent C₁ D₁) (rightExponent C₁ D₁)).powerset)
    (u : Oˣ) (U : Finset (CommonIndex C₂ D₂)) (h : O)
    (hw : jointLeftRow C₁ D₁ C₂ D₂ E u U h ≠ 0)
    (Z p R e R₀ : ℝ) (hZ : 1 < Z)
    (hR : Z^R ≤ normValue (activeConductor C₁ D₁))
    (he : Z^e ≤ normValue (primeSubsetGenerator (fun P : CommonIndex C₁ D₁ => P.val) E))
    (hp : ((commonRadical C₁ D₁).absNorm : ℝ) ≤ Z^p)
    (hR₀ : ((canceledIdeal C₁ D₁ 5).absNorm : ℝ) ≤ Z^R₀) :
    ((jointMissingRadical C₁ (jointLeftRow C₁ D₁ C₂ D₂ E u U h)).absNorm : ℝ) ≤
      Z^(p-R-e+R₀) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hb := joint_missing_radical_norm C₁ D₁ C₂ D₂ hC₁ hCD₁ E hE u U h hw
  rw [←joint_canceledIdeal_eq C₁ D₁ hC₁] at hb
  have hb' : ((jointMissingRadical C₁ (jointLeftRow C₁ D₁ C₂ D₂ E u U h)).absNorm : ℝ)*
      normValue (activeConductor C₁ D₁)*
      normValue (primeSubsetGenerator (fun P : CommonIndex C₁ D₁ => P.val) E) ≤
      ((commonRadical C₁ D₁).absNorm : ℝ)*(canceledIdeal C₁ D₁ 5).absNorm := by
    unfold normValue
    exact_mod_cast hb
  have hactive₀ : 0 ≤ normValue (activeConductor C₁ D₁) := by unfold normValue; positivity
  have hlo : ((jointMissingRadical C₁ (jointLeftRow C₁ D₁ C₂ D₂ E u U h)).absNorm : ℝ)*Z^R*Z^e ≤
      Z^p*Z^R₀ := by
    calc
      _ ≤ ((jointMissingRadical C₁ (jointLeftRow C₁ D₁ C₂ D₂ E u U h)).absNorm : ℝ)*
          normValue (activeConductor C₁ D₁)*
          normValue (primeSubsetGenerator (fun P : CommonIndex C₁ D₁ => P.val) E) := by
        gcongr
      _ ≤ _ := hb'.trans (mul_le_mul hp hR₀ (Nat.cast_nonneg _) (by positivity))
  calc
    _ ≤ (Z^p*Z^R₀)/(Z^R*Z^e) :=
      (le_div_iff₀ (mul_pos (Real.rpow_pos_of_pos hz _) (Real.rpow_pos_of_pos hz _))).mpr
        (by simpa only [mul_assoc] using hlo)
    _ = _ := by
      rw [←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_sub hz]
      congr 1
      ring

namespace ActualJointSourceRow
variable {Slot : Type*} [Fintype Slot] {s : OriginalData Slot} {side : Bool}

theorem label_principal (q : ActualJointSourceRow s side)
    (hE : q.E ∈ (principalSupport Finset.univ (leftExponent q.first.val.1 q.first.val.2)
      (rightExponent q.first.val.1 q.first.val.2)).powerset) :
    q.label.E ∈ (principalSupport Finset.univ (leftExponent q.label.C₁ q.label.D₁)
      (rightExponent q.label.C₁ q.label.D₁)).powerset := by
  cases side
  · exact swappedFirstSubset_principal _ _ _ hE
  · exact hE

theorem source_missing_geometry (q : ActualJointSourceRow s side)
    (η : Character) (ξ₁ ξ₂ : RayCharacter) (hz : q.z ≠ 0)
    (hE : q.E ∈ (principalSupport Finset.univ (leftExponent q.first.val.1 q.first.val.2)
      (rightExponent q.first.val.1 q.first.val.2)).powerset)
    (Z p R e R₀ : ℝ) (hZ : 1 < Z)
    (hR : Z^R ≤ normValue (activeConductor q.label.C₁ q.label.D₁))
    (he : Z^e ≤ normValue (primeSubsetGenerator (fun P : CommonIndex q.label.C₁ q.label.D₁ => P.val) q.label.E))
    (hp : ((commonRadical q.label.C₁ q.label.D₁).absNorm : ℝ) ≤ Z^p)
    (hR₀ : ((canceledIdeal q.label.C₁ q.label.D₁ 5).absNorm : ℝ) ≤ Z^R₀) :
    ((jointMissingRadical q.label.C₁ (q.reconstructed η ξ₁ ξ₂ hz).val).absNorm : ℝ) ≤
      Z^(p-R-e+R₀) := by
  rw [←q.label_row η ξ₁ ξ₂ hz]
  exact joint_missing_geometry_sector q.label.C₁ q.label.D₁ q.label.C₂ q.label.D₂
    q.label_supported.1 q.label_equal_support.1 q.label.E (q.label_principal hE)
    (q.unit η ξ₁ ξ₂) q.label.U q.label.h (q.label_row_nonzero η ξ₁ ξ₂ hz)
    Z p R e R₀ hZ hR he hp hR₀

theorem source_row_geometry (q : ActualJointSourceRow s side)
    (η : Character) (ξ₁ ξ₂ : RayCharacter) (hz : q.z ≠ 0)
    (Z A c d R e M a ω L H εH εE ξ K : ℝ) (hZ : 1 < Z)
    (hH₀ : 0 ≤ H) (hH : H ≤ Z^(A+εH))
    (hC : Z^c ≤ (q.label.C₁.absNorm : ℝ))
    (hE : normValue (primeSubsetGenerator
      (fun P : CommonIndex q.label.C₁ q.label.D₁ => P.val) q.label.E) ≤ Z^(e+εE))
    (hF : normValue (leftEffectiveFactor q.label.C₁ q.label.D₁) ≤ Z^L)
    (hK : Z^(2*A-c-d+R+e-M+max (d-c) 0+6*a+ω) ≤ K)
    (rows : Finset O)
    (hrows : q.z ∈ liveRows q.second.val.1 q.second.val.2 q.U
      (frequencyRadius ((H/(q.label.C₁.absNorm : ℝ))^2/K) Z ξ) rows) :
    normValue (q.reconstructed η ξ₁ ξ₂ hz).val ≤
      4*Z^(M-R-max (c-d) 0+L-6*a-ω+2*εH+εE+ξ/2) := by
  rw [←q.label_row η ξ₁ ξ₂ hz]
  apply joint_row_geometry_sector q.label.C₁ q.label.D₁ q.label.C₂ q.label.D₂
    q.label.E (q.unit η ξ₁ ξ₂) q.label.U q.label.h
    Z A c d R e M a ω L H εH εE ξ K hZ hH₀ hH hC hE hF hK
  have hh := liveRows_weight q.second.val.1 q.second.val.2 q.U
    (frequencyRadius ((H/(q.label.C₁.absNorm : ℝ))^2/K) Z ξ) rows q.z hrows
  cases side <;> exact hh

end ActualJointSourceRow

theorem eventually_source_row_geometry (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ {Slot : Type*} [Fintype Slot] (s : OriginalData Slot) (side : Bool)
        (q : ActualJointSourceRow s side) (η : Character) (ξ₁ ξ₂ : RayCharacter) (hz : q.z ≠ 0)
        (A c d R e M a ω L H εH εE ξ K W : ℝ),
      0 ≤ H → H ≤ Z^(A+εH) → Z^c ≤ (q.label.C₁.absNorm : ℝ) →
      normValue (primeSubsetGenerator
        (fun P : CommonIndex q.label.C₁ q.label.D₁ => P.val) q.label.E) ≤ Z^(e+εE) →
      normValue (leftEffectiveFactor q.label.C₁ q.label.D₁) ≤ Z^L →
      Z^(2*A-c-d+R+e-M+max (d-c) 0+6*a+ω) ≤ K →
      M-R-max (c-d) 0+L-6*a-ω+2*εH+εE+ξ/2+ε ≤ W →
      ∀ rows : Finset O, q.z ∈ liveRows q.second.val.1 q.second.val.2 q.U
        (frequencyRadius ((H/(q.label.C₁.absNorm : ℝ))^2/K) Z ξ) rows →
      ((Ideal.span {(q.reconstructed η ξ₁ ξ₂ hz).val}).absNorm : ℝ) ≤ Z^W := by
  filter_upwards [(tendsto_rpow_atTop hε).eventually (eventually_ge_atTop (4 : ℝ)),
    eventually_gt_atTop (1 : ℝ)] with Z hfour hZ
  refine ⟨hZ,?_⟩
  intro Slot inst s side q η ξ₁ ξ₂ hz A c d R e M a ω L H εH εE ξ K W
    hH₀ hH hC hE hF hK hW rows hrows
  have hr := q.source_row_geometry η ξ₁ ξ₂ hz Z A c d R e M a ω L H εH εE ξ K
    hZ hH₀ hH hC hE hF hK rows hrows
  calc
    _ ≤ 4*Z^(M-R-max (c-d) 0+L-6*a-ω+2*εH+εE+ξ/2) := hr
    _ ≤ Z^ε*Z^(M-R-max (c-d) 0+L-6*a-ω+2*εH+εE+ξ/2) := by gcongr
    _ = Z^(ε+(M-R-max (c-d) 0+L-6*a-ω+2*εH+εE+ξ/2)) :=
      (Real.rpow_add (zero_lt_one.trans hZ) _ _).symm
    _ ≤ Z^W := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)

#print axioms joint_row_geometry_sector
#print axioms joint_missing_geometry_sector
#print axioms ActualJointSourceRow.source_missing_geometry
#print axioms eventually_source_row_geometry
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointSourceRowGeometry -/

/- BEGIN ORIGINAL MODULE Global.Low.Detector.LowCommonBound ; sha256 c463b614f5e960ec92b09afcde9afe790b12fc3b6432bd4b1d6edaefa04db4d3 -/
section



/-! Adapted from OpenAI/math family003, pinned original module Detector.LowCommonBound.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace Submission20261012.Global
open OAI OAI.SevenEighths

noncomputable section
open scoped Classical ContDiff SchwartzMap
namespace LowProbe
open ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma low_window_log_support (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a)
    (hW : Function.support W⊆Set.Icc a b) (y : ℝ) (hy : W (Real.exp y)≠0) :
    |y|≤|Real.log a|+|Real.log b| := by
  have hs := hW hy
  have hlo := Real.log_le_log ha hs.1
  have hhi := Real.log_le_log (Real.exp_pos y) hs.2
  rw [Real.log_exp] at hlo hhi
  exact abs_le.mpr ⟨by linarith [neg_abs_le (Real.log a),abs_nonneg (Real.log b)],
    by linarith [le_abs_self (Real.log b),abs_nonneg (Real.log a)]⟩

theorem compensatedPhysicalProbe_low (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤ Submission20261012.Global.ell)
    (a b ε : ℝ) (ha : 0< a) (hε : 0<ε) (hε1 : ε<1)
    (W : Fin K→ℝ→ℂ) (hW : ∀i,Function.support (W i)⊆Set.Icc a b) (hWnorm : ∀i x,‖W i x‖≤1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hab1 : a1< b1) (hB0 : 0≤ B0) (hB1 : 0≤ B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤ B0) (hWB1 : ∀x,‖W1 x‖≤ B1) :
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in Filter.atTop,1< Z ∧
    ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=> Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤ b*Z^(ell i))→
      ‖compensatedPhysicalProbe η (calibrationForSet S hS) W0 W1
        (fun i=> canonicalSlotSupport (T i)) W (fun i=> Z^(ell i))
        (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z‖≤ C*Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+256*ε) := by
  obtain ⟨V,hV,hbudget,hidentity⟩ := compensatedPhysicalProbe_common_gaussian W
    (fun _=>|Real.log a|+|Real.log b|) (fun _=> by positivity)
    (fun i=> low_window_log_support (W i) a b ha (hW i))
  choose C hC he using fun A : Finset (Fin K)=> low_all_gaussian_dyads η S hS hbad ell hell hsum
    a b ε ha hε hε1 (V A) (hV A) W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hab1 hB0 hB1
    hW0 hW1 hW0s hW1s hWB0 hWB1
  let C0 := (∑A∈(Finset.univ : Finset (Fin K)).powerset,C A)+1
  have hC0 : 0< C0 := by
    have hn := Finset.sum_nonneg (fun A (_ : A∈(Finset.univ : Finset (Fin K)).powerset)=>(hC A).le)
    dsimp only [C0]
    linarith
  refine ⟨C0,hC0,?_⟩
  filter_upwards [Filter.eventually_all.mpr he] with Z hZ
  have hz1 : 1< Z := (hZ ∅).1
  have hz : 0< Z := lt_trans zero_lt_one hz1
  refine ⟨hz1,?_⟩
  intro T hT hout hdis hnorm
  have hslots : ∀i n,n∈canonicalSlotSupport (T i)→n≠0 := fun i=> canonicalSlotSupport_nonzero _ (hT i)
  rw [hidentity η (calibrationForSet S hS) W0 W1
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW0)
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1)
    _ hslots (fun i=> Z^(ell i)) (fun i=> by positivity)
    (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z (by positivity) (by positivity) hz]
  apply (norm_sum_le _ _).trans
  have hterm (A : Finset (Fin K)) :
      ‖∑'j : ℕ,lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=> canonicalSlotSupport (T i)) W
        (fun i=> Z^(ell i)) A (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) ((2:ℝ)^j)
        (Z*∏i∈Finset.univ\A,Z^(ell i)) (V A) (hV A)‖≤ C A*Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+256*ε) := by
    have hc : Z*(∏i∈Finset.univ\A,Z^(ell i))=Z^(1+lowSelectedLength ell A) := by
      rw [lowSelectedScale_product ell A Z hz,Real.rpow_add hz,Real.rpow_one]
    rw [hc]
    exact ((hZ A).2 T hT hout hdis hnorm A W hWnorm).2
  have hh := Finset.sum_le_sum (fun A (_ : A∈(Finset.univ : Finset (Fin K)).powerset)=> hterm A)
  apply hh.trans
  rw [←Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (by dsimp [C0];linarith) (Real.rpow_nonneg hz.le _)

theorem original_ray_compensatedPhysicalProbe_low (η : HeckeFamily.Character)
    (S : Finset Id) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hinj : Function.Injective ell)
    (hsum : ∑i,ell i≤ Submission20261012.Global.ell) (R : Set Id)
    (a b ε : ℝ) (ha : 0< a) (hab : a≤ b) (hε : 0<ε) (hε1 : ε<1)
    (W : Fin K→ℝ→ℂ) (hW : ∀i,Function.support (W i)⊆Set.Icc a b) (hWnorm : ∀i x,‖W i x‖≤1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hab1 : a1< b1) (hB0 : 0≤ B0) (hB1 : 0≤ B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤ B0) (hWB1 : ∀x,‖W1 x‖≤ B1) :
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in Filter.atTop,
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
        (fun i=> canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z^(ell i)))) W (fun i=> Z^(ell i))
        (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z‖≤ C*Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+256*ε) := by
  obtain ⟨C,hC,he⟩ := compensatedPhysicalProbe_low η S hmax hS.bad ell hell hsum
    a b ε ha hε hε1 W hW hWnorm W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hab1 hB0 hB1
    hW0 hW1 hW0s hW1s hWB0 hWB1
  refine ⟨C,hC,?_⟩
  filter_upwards [he,ProbeRaySlots.power_pools_eventually_disjoint R S (fun _=> a) (fun _=> b) ell
    (fun _=> ha) (fun _=> hab) hinj] with Z hZ hd
  have hz : 0< Z := lt_trans zero_lt_one hZ.1
  apply hZ.2 _ (fun i=> ProbeRaySlots.pool_supported R S hS a b (Z^(ell i)))
    (fun i P hP=>((ProbeRaySlots.mem_pool R S a b (Z^(ell i)) P).mp hP).2.2.2)
    (fun i j hij=> hd i j hij)
  intro i P hP
  have hh := ProbeRaySlots.pool_norm_bounds R S ha.le hab (Real.rpow_pos_of_pos hz _) P hP
  simpa only [mul_comm] using And.intro hh.1.le hh.2

end LowProbe
end

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Detector.LowCommonBound -/

/- BEGIN ORIGINAL MODULE Analytic.ActualFirstErrorSource ; sha256 e9094c4e99d8a66c00a54ba92eb2c12ca5b7cdd1a1d0c0dbf19d013943628b1c -/
section




/-! Actual extracted error estimates with Ready discharged by source caps.
Dead extracted sources vanish exactly. Every live extracted source receives
its Ready packet from the pinned source theorem before the genuine analytic
estimate is used. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
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
local instance actualFirstErrorSourceDecEq {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
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
local instance actualFirstErrorSourceFinite : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
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

open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstNonexceptionalFixedWeightSum
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentFirstSectors
open CenteredMomentFirstMixedRightTransport CenteredMomentSupportedCorrelation

namespace ExtractedErrorRun
variable {Slot : Type*} [Fintype Slot]

/-- The residual gates are exactly those furnished by the actual
amplification family and the first annular geometry. Conductor bounds and
first common norms are derived from the pinned source. -/
structure SourceAdmissible {s : Input Slot} {C : Ideal O} {P : Finset (Ideal O)}
    (x : ExtractedErrorRun s C P) (D R : Ideal O) (E : Finset (CommonIndex C D))
    (τ : Character) (Z K sigma delta reserve Dscale heightCap : ℝ) : Prop where
  height_le : |x.height| ≤ heightCap
  slot_coprime : ∀ B : actualAllocations s.pools C,
    frozenCoefficient B.val C R s.ν s.W s.P ≠ 0 →
    ∀ (prime : elementPool P) i, ∀ I ∈ (activeInput (child s C R B τ x.height)).slots i,
      IsCoprime (Ideal.span {prime.val}) I
  radical_cap : ∀ B : actualAllocations s.pools C,
    frozenCoefficient B.val C R s.ν s.W s.P ≠ 0 →
    ∀ prime i χ, (x.family B prime i χ).modulus.absNorm ≤
      CenteredMomentAmplificationRadicalFamily.radicalBound
        (CenteredMomentChildRows.childCharacter τ χ) fixedBadMask prime
        (CenteredMomentAmplificationActiveFactor.errorMovingExponent (errorIndex i))
  radius_inv : ∀ (prime : elementPool P) i,
    (errorCommonRadius Z (Real.logb Z (D.absNorm : ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun Q : CommonIndex C D => Q.val) E}) K (volume s)))
      (Real.logb Z (C.absNorm : ℝ)) sigma delta reserve prime (errorIndex i+1))⁻¹ ≤ Z^Dscale
end ExtractedErrorRun

theorem actual_first_extracted_error_source_sum
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
    (hbudget : CenteredMomentFirstSecondInputGates.exponent Avol Dscale Pmask qmoving εgeo ξ ≤ Bcap)
    (εalloc : ℝ) (hεalloc : 0 < εalloc)
    (hloss : ∀ j, CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j ≤ 1/10000)
    (hsaving : 0 ≤ saving)
    (Bfirst Lfirst Crfirst : ℝ) (hBfirst : 0 ≤ Bfirst) (hLfirst : 0 ≤ Lfirst)
    (hCrfirst : 0 < Crfirst) (hallocSmall : εalloc*Bfirst ≤ 1/10000)
    (qParent εconductor : ℝ) (hεconductor : 0 < εconductor)
    (hcostSource : CenteredMomentFirstSourceConductorCaps.rayCost ≤ cost)
    (hconductorBudget : qParent+2*Bfirst+sigma/3+εconductor ≤ qmoving):
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
    (src.η.modulus.absNorm : ℝ) ≤ Z^qParent →
    ∀ (R seedOuter seed : Ideal O), R ≠ 0 →
    Squarefree seedOuter → seedOuter ≠ 0 → Squarefree seed → seed ≠ 0 →
    (seed.absNorm : ℝ) ≤ Z^Bseed →
    src.W₁ 0=0 → src.W₂ 0=0 → volume src≤ Z^Avol → (R.absNorm : ℝ)≤ Z^Pmask →
    0 < sourceRadius src → sourceRadius src ≤ Z^Bfirst →
    ∀ profile : Profiles a b, profile.profile 0=src.W₁ → profile.profile 1=src.W₂ →
    src.X₁≤ Z^L → src.X₂≤ Z^L → src.Y₁≤ Z^L → src.Y₂≤ Z^L →
    ∀ (m A : O) (t₀ : ℝ) (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ)
      (K a₁ a₂ win delta reserve asource : ℝ),
    0 < K → 0 < a₁ → 0 < a₂ → 0 < asource →
    0 ≤ delta → 0 ≤ reserve → a0 ≤ asource →
    (∀ y, src.W₁ y ≠ 0 → a₁ ≤ y) → (∀ y, src.W₂ y ≠ 0 → a₂ ≤ y) →
    (∀ i y, V i y ≠ 0 → |y| ≤ win) →
    let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
    P.Nonempty →
    ∀ Mdecl Mwidth θclip : ℝ, 0 ≤ θclip →
    length Z src.X₁+length Z src.X₂+6*(3/4)*(∑i,w i)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mwidth →
    Mwidth-sigma/2≤ Mcap → Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤ CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀ Mgeom Mvolume heightCap : ℝ, 1 ≤ Mgeom → 0 ≤ heightCap →
    Z^(Mgeom/4)≤ src.X₁ → Z^(Mgeom/4)≤ src.X₂ → Z^(Mgeom/4)≤ src.Y₁ → Z^(Mgeom/4)≤ src.Y₂ →
    Mgeom≤ Real.logb Z K+Real.logb Z (src.η.modulus.absNorm : ℝ)+Real.logb Z fixedPresentationCost →
    Real.logb Z (volume src)≤(883/1000)*Mgeom → Real.logb Z (volume src)≤ Mvolume →
    Real.logb Z fixedPresentationCost≤1/1000 →
    Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm : ℝ))≤1/250 →
    (Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+(3/4)*mesh ≤ 1/10000 →
    delta+reserve ≤ 1/1000 → εsrc*Mvolume ≤ 1/1000 →
    ∀ radius : (p : Labels src R seedOuter) → Finset (CommonIndex p.val.1 p.val.2) → ℝ,
    (∀ p E, radius p E ≤ Crfirst*Z^Lfirst) →
    ∀ (ξ₁ ξ₂ : RayCharacter) (F : Families src R seedOuter ξ₁ ξ₂),
    ∀ left : (p : Labels src R seedOuter) → (E : Finset (CommonIndex p.val.1 p.val.2)) →
      Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
        (sourceRadius src/p.val.1.absNorm) (sourceRadius src/p.val.2.absNorm) →
      ExtractedErrorRun src p.val.1 P,
    ∀ right : (p : Labels src R seedOuter) → (E : Finset (CommonIndex p.val.1 p.val.2)) →
      Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
        (sourceRadius src/p.val.1.absNorm) (sourceRadius src/p.val.2.absNorm) →
      ExtractedErrorRun src p.val.2 P,
    (∀ (p : Labels src R seedOuter) (E : Finset (CommonIndex p.val.1 p.val.2)),
      E ∈ CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2 → ∀ n,
      (left p E n).SourceAdmissible p.val.2 R E (F p E).left Z K sigma delta reserve Dscale heightCap ∧
      (right p E n).SourceAdmissible p.val.1 R (swapSubset p.val.1 p.val.2 E) (F p E).right
        Z K sigma delta reserve Dscale heightCap) →
    (∑ p : Labels src R seedOuter,
      ∑ E ∈ CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2,
      ∑ n : Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
        (sourceRadius src/p.val.1.absNorm) (sourceRadius src/p.val.2.absNorm),
        allowanceWeight src R seedOuter m A t₀ W V K (radius p E) Z p E (F p E).left (F p E).right n *
          (Real.sqrt ((left p E n).normalizedValue N p.val.2 R seed E (F p E).left upper Z K sigma delta reserve)*
           Real.sqrt ((right p E n).normalizedValue N p.val.1 R seed
             (swapSubset p.val.1 p.val.2 E) (F p E).right upper Z K sigma delta reserve))) ≤
    Cbound*profile.control Uprofile^2*(1+heightCap+height)^Jheight*mass src^2*
      ((Real.exp win/((∏i,src.lo i)*a₁*a₂))*fixedPresentationCost*K*(src.η.modulus.absNorm : ℝ))*
      Z^(-3/10000 : ℝ)/((seedOuter.absNorm : ℝ)*(seed.absNorm : ℝ)) := by
  obtain ⟨Uprofile,Jheight,hactual⟩ := actual_first_allocated_extracted_error_sum (α := α) M H hH
    Wslot aslot bslot Mcap εremove lo hi εchild a b Mslot εmask hMslot hεmask haPlain haUpper hbPlain
    L hL ha hWs hW hbslot hMcap hεchild hε hbeta hbetaTop N lower upper a0 θsource
    hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
    hεsrc hδsrc hθsrc hBcap hξ Sbad hbad sigma cost hsigma hξsmall hcost hsigma_eq
    Avol Dscale Pmask qmoving εgeo hεgeo hbudget εalloc hεalloc hloss hsaving
    Bfirst Lfirst Crfirst hBfirst hLfirst hCrfirst hallocSmall
  refine ⟨Uprofile,Jheight,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hactualZ⟩ := hactual η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cbound,hCbound,?_⟩
  filter_upwards [hactualZ,eventually_fixed_pair_error_source_caps M H Sbad hbad εconductor hεconductor]
    with Z hZ hcaps
  refine ⟨hZ.1,?_⟩
  intro Aorig θ w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max hParent
    R seedOuter seed hR hseedOuter hseedOuter0 hseed hseed0 hseedcap
    hzero1 hzero2 hvolumeCap hmaskCap hH hHcap profile hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
    m A t₀ W V K a₁ a₂ win delta reserve asource hK ha₁ ha₂ hasource hdelta hreserve haSource
    hs₁ hs₂ hwin
  dsimp only
  intro hP Mdecl Mwidth θclip hθclip hcap hMdecl hMwidth hdrop hclip hsourceLower
    Mgeom Mvolume heightCap hgeom hheightCap hplainX₁ hplainX₂ hplainY₁ hplainY₂
    hwidth hvolGeom hvolCap hfixed hdef hpaid hfrequency hepsSmall radius hr ξ₁ ξ₂ F left right hruns
  apply hZ.2 Aorig θ w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max
    R seedOuter seed hR hseedOuter hseedOuter0 hseed hseed0 hseedcap
    hzero1 hzero2 hvolumeCap hmaskCap hH hHcap profile hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
    m A t₀ W V K a₁ a₂ win delta reserve asource hK ha₁ ha₂ hasource hdelta hreserve haSource
    hs₁ hs₂ hwin hP Mdecl Mwidth θclip hθclip hcap hMdecl hMwidth hdrop hclip hsourceLower
    Mgeom Mvolume heightCap hgeom hheightCap hplainX₁ hplainX₂ hplainY₁ hplainY₂
    hwidth hvolGeom hvolCap hfixed hdef hpaid hfrequency hepsSmall radius hr ξ₁ ξ₂ F left right
  intro p E hE n
  obtain ⟨hl,hr⟩ := hruns p E hE n
  have hp := commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset src.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient src R seedOuter)) _ _ p.property
  have hn := actual_first_label_norm_caps src R seedOuter hseedOuter hzero1 hzero2 Z Bfirst hHcap p
  have hcs := hcaps.2 src.η p.val.1 p.val.2 hp.1 E ξ₁ ξ₂ (F p E)
    qParent Bfirst sigma cost qmoving hParent hn.1 hcostSource hconductorBudget
  constructor
  · refine ⟨hl.height_le,hn.1,hl.slot_coprime,hl.radical_cap,?_,hl.radius_inv,?_⟩
    · intro B hB prime i χ
      exact (hcs (F p E).left ((left p E n).family B prime i χ) (Or.inl rfl) χ prime i
        (hl.radical_cap B hB prime i χ)).1
    · intro B hB prime i χ
      exact (hcs (F p E).left ((left p E n).family B prime i χ) (Or.inl rfl) χ prime i
        (hl.radical_cap B hB prime i χ)).2
  · refine ⟨hr.height_le,hn.2,hr.slot_coprime,hr.radical_cap,?_,hr.radius_inv,?_⟩
    · intro B hB prime i χ
      exact (hcs (F p E).right ((right p E n).family B prime i χ) (Or.inr rfl) χ prime i
        (hr.radical_cap B hB prime i χ)).1
    · intro B hB prime i χ
      exact (hcs (F p E).right ((right p E n).family B prime i χ) (Or.inr rfl) χ prime i
        (hr.radical_cap B hB prime i χ)).2

#print axioms actual_first_extracted_error_source_sum
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.ActualFirstErrorSource -/

/- BEGIN ORIGINAL MODULE Analytic.JointCoherentExceptionalPhysicalBase ; sha256 63810a7bcd8996b46c6b71070e0bd1091123a0ed5889822cc322539c42bfe354 -/
section




/-! Genuine coherent exceptional physical blocks, with the original volume
and the actual prime average kept through the second physical ledger. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CanonicalRowCompletion
open CenteredMomentCommonRadialData CenteredMomentCommonPairedSource CenteredMomentCommonSectorColumn
open CenteredMomentCommonLinearSource CenteredMomentCommonHeightEnvelope CenteredMomentReflectedSource
open CenteredMomentAmplificationChildInput CenteredMomentCanonicalFirst CenteredMomentFirstAmplificationChoice
open CenteredMomentActiveSource CenteredMomentSecondRetainedAggregate CenteredMomentSourceRow
open CenteredMomentSecondBlockAggregate CenteredMomentSecondSectorColumns
open CenteredMomentRowNorm CenteredMomentChildAssembly CenteredMomentHeckeColumnWindow
open CenteredMomentSecondScaled CenteredMomentSecondHeightFamily CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentFiniteProfileExceptionalCommon CenteredMomentFiniteProfileExceptional
open CenteredMomentCommonExceptionalCost CenteredMomentExceptionalAmplitudePair
open CenteredMomentFiniteProfileExceptionalPhysical CenteredMomentSectorLocalization
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentChildRows CenteredMomentForcing
open CenteredMomentFirstSectors
open CenteredMomentSecondPhysicalLedger CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondExceptionalKernel CenteredMomentMobiusRegroup CenteredMomentFixedRay
open RayFourExpansion UniqueFactorizationMonoid CompletedGauss
local notation "O" => HeckeFamily.O
local instance coherentExceptionalPhysicalBaseDecidableSum {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

lemma projectedSecondKernelSum_weighted_norm_le
    (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D) (U : Finset (CommonIndex C D))
    (R : ℝ) (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4 → ℤ)
    (E : ℝ) (hE : 0 ≤ E)
    (h : ∀ χ ξ : RayCharacter,
      (∑ L ∈ divisorPool Finset.univ (fun I : sectorPool D hD.1 S => (I : Ideal O)),
        ∑ z ∈ rows, ‖((1+SecondKernelLabel.kernelScale n : ℝ) : ℂ)*(moebius L : ℂ)*
          (projectedSecondKernelLabel η S β C D hC hD hCD U L χ ξ).kernelRow t z W K R n‖) ≤ E) :
    (1+SecondKernelLabel.kernelScale n)*
      ‖projectedSecondKernelSum η t S β C D hC hD hCD U R rows W K n‖ ≤ 256*E := by
  have hn : 0 ≤ 1+SecondKernelLabel.kernelScale n := by
    exact add_nonneg zero_le_one (div_nonneg
      (mul_nonneg (dyadicScale_pos _).le (dyadicScale_pos _).le)
      (mul_nonneg (dyadicScale_pos _).le (dyadicScale_pos _).le))
  let Ds := divisorPool Finset.univ (fun I : sectorPool D hD.1 S => (I : Ideal O))
  have he : ((1+SecondKernelLabel.kernelScale n : ℝ) : ℂ)*
      projectedSecondKernelSum η t S β C D hC hD hCD U R rows W K n =
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        pairCoeff (phaseTable (primaryGenerator C) (primaryGenerator D)) χ ξ*
          ∑ L ∈ Ds, ∑ z ∈ rows, ((1+SecondKernelLabel.kernelScale n : ℝ) : ℂ)*(moebius L : ℂ)*
            (projectedSecondKernelLabel η S β C D hC hD hCD U L χ ξ).kernelRow t z W K R n := by
    simp only [projectedSecondKernelSum,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro χ hχ
    rw [Finset.sum_comm]
    simp only [Ds,Finset.mul_sum,mul_assoc,mul_left_comm,mul_comm]
  have hnrm : ‖((1+SecondKernelLabel.kernelScale n : ℝ) : ℂ)*
      projectedSecondKernelSum η t S β C D hC hD hCD U R rows W K n‖ =
      (1+SecondKernelLabel.kernelScale n)*
        ‖projectedSecondKernelSum η t S β C D hC hD hCD U R rows W K n‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hn]
  rw [←hnrm,he]
  calc
    _ ≤ ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        ‖pairCoeff (phaseTable (primaryGenerator C) (primaryGenerator D)) χ ξ‖*E := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro χ hχ
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro ξ hξ
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      calc
        _ ≤ ∑ L ∈ Ds, ∑ z ∈ rows, ‖((1+SecondKernelLabel.kernelScale n : ℝ) : ℂ)*(moebius L : ℂ)*
            (projectedSecondKernelLabel η S β C D hC hD hCD U L χ ξ).kernelRow t z W K R n‖ := by
          apply (norm_sum_le _ _).trans
          exact Finset.sum_le_sum (fun L hL => norm_sum_le _ _)
        _ ≤ E := h χ ξ
    _ = (∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        ‖pairCoeff (phaseTable (primaryGenerator C) (primaryGenerator D)) χ ξ‖)*E := by
      simp only [Finset.sum_mul]
    _ ≤ 256*E := mul_le_mul_of_nonneg_right (phaseTable_mass _ _) hE

def coherentExceptionalProfile {ι : Type*} [Fintype ι] [DecidableEq ι] {wlo whi : ℝ}
    (Sprofile : Finset (ℕ×ℕ)) (src : Input ι) (profile : Profiles wlo whi)
    (J : ℕ) (Q : Ideal O) (K t : ℝ) : ℝ :=
  K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card)*(1+2*Real.pi)^(4*J)*
    profileMass Sprofile (withHeight src src.η t).toData (withHeight src src.η t).toData
      profile profile J*frozenProfile src^2/volume src.toData

lemma coherentExceptionalProfile_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {wlo whi : ℝ}
    (Sprofile : Finset (ℕ×ℕ)) (src : Input ι) (profile : Profiles wlo whi)
    (J : ℕ) (Q : Ideal O) (K t : ℝ) (hK : 0 ≤ K) :
    0 ≤ coherentExceptionalProfile Sprofile src profile J Q K t := by
  have hp := profileMass_nonneg Sprofile (withHeight src src.η t).toData
    (withHeight src src.η t).toData profile profile J
  have hv := (CenteredMomentExceptionalAmplitudePair.volume_pos src.toData).le
  unfold coherentExceptionalProfile
  positivity

def coherentExceptionalKernelBudget {ι : Type*} [Fintype ι] [DecidableEq ι] {wlo whi : ℝ}
    (Sprofile : Finset (ℕ×ℕ)) (src : Input ι) (profile : Profiles wlo whi)
    (J : ℕ) (Q C₁ C D : Ideal O) (U : Finset (CommonIndex C D))
    (K Z ε δ θ r t : ℝ) (n : Fin 4 → ℤ) : ℝ :=
  (volume src.toData/Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)))*
    (K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card)*
      Z^((Real.logb Z (dyadicScale (n 1))-4*Real.logb Z (forcingNorm C D U))/6+2*ε+δ-
        max (max (r-Real.logb Z ((C₁*C).absNorm : ℝ)) 0)
          (max (r-Real.logb Z ((C₁*D).absNorm : ℝ)) 0))*
      (((C₁*C).absNorm : ℝ)*(C₁*D).absNorm)^θ*
      ((1+2*Real.pi)^(4*J)*profileMass Sprofile (withHeight src src.η t).toData
        (withHeight src src.η t).toData profile profile J*frozenProfile src*frozenProfile src/
        (((C₁*C).absNorm : ℝ)*(C₁*D).absNorm)))

lemma coherentExceptionalKernelBudget_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {wlo whi : ℝ}
    (Sprofile : Finset (ℕ×ℕ)) (src : Input ι) (profile : Profiles wlo whi)
    (J : ℕ) (Q C₁ C D : Ideal O) (U : Finset (CommonIndex C D))
    (K Z ε δ θ r t : ℝ) (n : Fin 4 → ℤ) (hK : 0 ≤ K) (hZ : 0 < Z) :
    0 ≤ coherentExceptionalKernelBudget Sprofile src profile J Q C₁ C D U K Z ε δ θ r t n := by
  have hp := profileMass_nonneg Sprofile (withHeight src src.η t).toData
    (withHeight src src.η t).toData profile profile J
  have hv := (CenteredMomentExceptionalAmplitudePair.volume_pos src.toData).le
  have hf := frozenProfile_nonneg src
  unfold coherentExceptionalKernelBudget
  positivity

theorem coherent_exceptional_kernel_scalar {ι : Type*} [Fintype ι] [DecidableEq ι] {wlo whi : ℝ}
    (Sprofile : Finset (ℕ×ℕ)) (src : Input ι) (profile : Profiles wlo whi)
    (J : ℕ) (Q C₁ C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D))
    (K Z ε δ θ r t P Kphys : ℝ) (n : Fin 4 → ℤ) (hZ : 1 < Z) :
    secondPrecountFactor (volume src.toData) P C D U Kphys n*
      coherentExceptionalKernelBudget Sprofile src profile J Q C₁ C D U K Z ε δ θ r t n/
      (1+SecondKernelLabel.kernelScale n) =
    coherentExceptionalProfile Sprofile src profile J Q K t*
      Z^(2*ε+δ-max (max (r-Real.logb Z ((C₁*C).absNorm : ℝ)) 0)
        (max (r-Real.logb Z ((C₁*D).absNorm : ℝ)) 0))*
      (((C₁*C).absNorm : ℝ)*(C₁*D).absNorm)^θ*
      coherentExceptionalScalar (volume src.toData) P (C₁.absNorm : ℝ) C D U Kphys n := by
  have hv := CenteredMomentExceptionalAmplitudePair.volume_pos src.toData
  have hf : 0 < forcingNorm C D U := common_product_pos C D hC _
  unfold coherentExceptionalKernelBudget coherentExceptionalProfile coherentExceptionalScalar
  rw [show (Real.logb Z (dyadicScale (n 1))-4*Real.logb Z (forcingNorm C D U))/6+2*ε+δ-
      max (max (r-Real.logb Z ((C₁*C).absNorm : ℝ)) 0) (max (r-Real.logb Z ((C₁*D).absNorm : ℝ)) 0) =
    (Real.logb Z (dyadicScale (n 1))-4*Real.logb Z (forcingNorm C D U))/6+
      (2*ε+δ-max (max (r-Real.logb Z ((C₁*C).absNorm : ℝ)) 0)
        (max (r-Real.logb Z ((C₁*D).absNorm : ℝ)) 0)) by ring,
    count_power Z (dyadicScale (n 1)) (forcingNorm C D U) _ hZ (dyadicScale_pos _) hf]
  simp only [map_mul,Nat.cast_mul]
  field_simp
  <;> ring


#print axioms coherent_exceptional_kernel_scalar
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCoherentExceptionalPhysicalBase -/
