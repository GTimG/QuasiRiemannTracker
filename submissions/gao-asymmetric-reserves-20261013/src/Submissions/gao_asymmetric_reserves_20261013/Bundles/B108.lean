/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B101
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B104
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B105
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B107
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstMixedRightTransport

/- BEGIN ORIGINAL MODULE Analytic.JointActualErrorRuns ; sha256 76a57df5d4726d936c912263417038fdd14fd5ab8fc77542a98f0a5f9e7f9742 -/
section




/-! The selected amplifier family gives exactly the error run consumed
by the independent first-source estimates, in both orientations. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT ActualEisensteinCubic RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstScale
open CenteredMomentFirstMixedRightTransport CenteredMomentCanonicalFirst
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

namespace FirstJointLabel

theorem sideSubset_generator (q : FirstJointLabel ι) (left : Bool) :
    primeSubsetGenerator (fun Q : CommonIndex (q.sideCommon left) (q.sideCommon (!left)) => Q.val)
      (q.sideSubset left) = q.puncture := by
  cases left
  · exact swapSubset_generator q.C q.D q.E
  · rfl

theorem actual_amplifier_error_value
    (q : FirstJointLabel ι) (s : Input ι) (left : Bool)
    (P : Finset (Ideal O))
    (τ : (J : Finset ι) → Character → CenteredMomentPrimeElements.elementPool P →
      Fin 3 → RayCharacter → Character)
    (N : ℕ) (R seed : Ideal O) (t upper Z K sigma delta reserve : ℝ) :
    (actualAmplifierErrorRun s (q.sideCommon left) P τ (q.sideParent left) t).value
      N (q.sideCommon (!left)) R seed (q.sideSubset left) (q.sideParent left)
      upper Z K sigma delta reserve =
    allocatedExtractedErrors N s (q.sideCommon left) R seed (q.sideParent left) t upper Z
      (q.sideWidth (!left) Z)
      (nominalLog (q.sideCommon left) (q.sideCommon (!left))
        (Ideal.span {q.puncture}) K (volume s) Z)
      (q.sideWidth left Z) sigma delta reserve P
      (fun B => τ (liveIndices B.val) (q.sideParent left)) := by
  simp only [ExtractedErrorRun.value,actualAmplifierErrorRun,nominalLog,sideWidth,
    q.sideSubset_generator left]

end FirstJointLabel

#print axioms FirstJointLabel.actual_amplifier_error_value
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointActualErrorRuns -/

/- BEGIN ORIGINAL MODULE Analytic.JointCoherentExceptionalProfile ; sha256 1f705a7b5fa2d70068351ce8d50671c77d4a8c6b558217f8d03a708f23e8880c -/
section


/-! The coherent exceptional profile loses no source volume. Its remaining
height dependence is an explicit polynomial of fixed degree. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentFiniteProfileExceptionalCommon CenteredMomentFiniteProfileExceptional
open CenteredMomentExceptionalAmplitudePair CenteredMomentAllocatedDetectorAmplitude
open CenteredMomentCommonExceptionalCost UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {wlo whi : ℝ}

theorem coherentExceptionalProfile_exact
    (Sprofile : Finset (ℕ×ℕ)) (src : Input ι) (profile : Profiles wlo whi)
    (J : ℕ) (Q : Ideal O) (K t : ℝ) :
    coherentExceptionalProfile Sprofile src profile J Q K t =
      K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card)*(1+2*Real.pi)^(4*J)*
        profile.control Sprofile^2*(slotControl src.toData)^2*frozenProfile src^2*
          (1+|t|)^(2*J) := by
  have hv := CenteredMomentExceptionalAmplitudePair.volume_pos src.toData
  have hs := Real.sq_sqrt hv.le
  unfold coherentExceptionalProfile profileMass
  dsimp only [withHeight]
  change K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card)*(1+2*Real.pi)^(4*J)*
      (profile.control Sprofile*profile.control Sprofile*(1+‖t‖)^J*(1+‖t‖)^J*
        slotControl src.toData*slotControl src.toData*Real.sqrt (volume src.toData)*Real.sqrt (volume src.toData))*
          frozenProfile src^2/volume src.toData = _
  rw [Real.norm_eq_abs,show 2*J=J+J by omega,pow_add]
  field_simp [hv.ne']
  ring_nf
  rw [hs]
  ring

theorem coherentExceptionalProfile_height_factor
    (Sprofile : Finset (ℕ×ℕ)) (src : Input ι) (profile : Profiles wlo whi)
    (J : ℕ) (Q : Ideal O) (K t : ℝ) :
    coherentExceptionalProfile Sprofile src profile J Q K t =
      coherentExceptionalProfile Sprofile src profile J Q K 0*(1+|t|)^(2*J) := by
  rw [coherentExceptionalProfile_exact,coherentExceptionalProfile_exact]
  simp only [abs_zero,add_zero,one_pow,mul_one]

theorem coherentExceptionalProfile_height_power
    (Sprofile : Finset (ℕ×ℕ)) (src : Input ι) (profile : Profiles wlo whi)
    (J : ℕ) (Q : Ideal O) (K t Z ν Ct : ℝ)
    (hK : 0 ≤ K) (hZ : 1 ≤ Z) (hν : 0 ≤ ν) (hCt : 0 ≤ Ct) (ht : |t| ≤ Ct*Z^ν) :
    coherentExceptionalProfile Sprofile src profile J Q K t ≤
      coherentExceptionalProfile Sprofile src profile J Q K 0*(1+Ct)^(2*J)*Z^((2*J:ℝ)*ν) := by
  have hz := zero_lt_one.trans_le hZ
  have hone := Real.one_le_rpow hZ hν
  have hh : 1+|t| ≤ (1+Ct)*Z^ν := by nlinarith
  have hp := coherentExceptionalProfile_nonneg Sprofile src profile J Q K 0 hK
  rw [coherentExceptionalProfile_height_factor]
  calc
    _ ≤ coherentExceptionalProfile Sprofile src profile J Q K 0*((1+Ct)*Z^ν)^(2*J) := by gcongr
    _ = _ := by
      have he : (Z^ν)^(2*J) = Z^((2*J:ℝ)*ν) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
        congr 1
        push_cast
        ring
      rw [mul_pow,he]
      ring

#print axioms coherentExceptionalProfile_exact
#print axioms coherentExceptionalProfile_height_power
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCoherentExceptionalProfile -/

/- BEGIN ORIGINAL MODULE Analytic.JointCoherentExceptionalSum ; sha256 7c6e63ae238768fa50b0fd8b2631efbe0e202378010ff55fd0cc012631d20f6a -/
section


/-! The original coherent exceptional contribution over either literal
first source domain, with the sharp seeded common-sector measure. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondBlockAggregate
open CenteredMomentSecondEnergySplit CenteredMomentSecondExceptionalSourceFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentExceptionalAmplitudePair CenteredMomentSectorLocalization
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentFirstMixedAllowance CenteredMomentFirstPhysicalSource CenteredMomentFirstScale
open CenteredMomentCanonicalFirst CenteredMomentRankinRadical CenteredMomentSecondHeightFamily
open CenteredMomentAmplifiedRetainedRadius CompletedGauss
open RayFourExpansion ConcretePrimeRowBridge CanonicalRowCompletion
open CenteredMomentFiniteProfileExceptionalCommon CenteredMomentSecondExceptionalFamily
local notation "O" => HeckeFamily.O
local instance coherentExceptionalSumDecidableSum {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem actual_first_coherent_exceptional_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (wlo whi : ℝ) (hwlo : 0 < wlo) (hwhi : 0 ≤ whi) (lo hi : ι → ℝ)
    (ε δ θ B Bsource L Cr εmass Lfirst Crfirst εsum : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ) (hB : 0 ≤ B) (hBsource : 0 ≤ Bsource)
    (hL : 0 ≤ L) (hCr : 0 < Cr) (hεmass : 0 < εmass)
    (hLfirst : 0 ≤ Lfirst) (hCrfirst : 0 < Crfirst) (hεsum : 0 < εsum) (W : 𝓢(ℝ,ℂ)) :
    ∃ J : ℕ, ∃ Sprofile : Finset (ℕ×ℕ), (0,0) ∈ Sprofile ∧
    ∃ Cbound : ℝ, 0 ≤ Cbound ∧
    ∀ Q : Ideal O, Q ≠ 0 → Q ≠ ⊤ → Q ≤ Ideal.span {(72 : O)} →
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (src : Input ι) (profile : Profiles wlo whi),
    (∀ i, src.lo i = lo i) → (∀ i, src.hi i = hi i) → (∀ i, 1 ≤ src.P i) →
    src.W₁ = profile.profile 0 → src.W₂ = profile.profile 1 →
    0 < sourceRadius src → sourceRadius src ≤ Z^Bsource →
    ∀ (R seed : Ideal O), R ≠ 0 → Squarefree seed → seed ≠ 0 →
    ∀ Kfirst M A omega primeLoss T : ℝ, 0 < Kfirst → 1 ≤ M → 0 ≤ T →
    M ≤ Real.logb Z Kfirst+Real.logb Z (src.η.modulus.absNorm : ℝ)+Real.logb Z fixedPresentationCost →
    volume src.toData = Z^A → A ≤ (883/1000)*M →
    Z^(M/4) ≤ src.X₁ → Z^(M/4) ≤ src.X₂ → Z^(M/4) ≤ src.Y₁ → Z^(M/4) ≤ src.Y₂ →
    ∀ radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ,
      (∀ p E,radius p E ≤ Crfirst*Z^Lfirst) →
    let q := firstSourceOuterLabel src R seed Kfirst radius
    ∀ (labels : Finset (FirstSourceOuterIndex src R seed Kfirst radius)) (left : Bool) (p refwidth : ℝ),
      (∀ i ∈ labels, ((commonRadical i.1.val.1 i.1.val.2).absNorm : ℝ) ≤ Z^p) →
      (∀ i ∈ labels, -2*Real.logb Z (((q i).sideCommon left).absNorm : ℝ)+
        (q i).activeWidth Z+(q i).punctureWidth Z+
          allowance ((q i).sideCommon left) ((q i).sideCommon (!left)) Z ≤ refwidth) →
    let domain := firstSideSourceLabels labels q (fun _ => sourceRadius src) left
    let v := fun k : (i : FirstSourceOuterIndex src R seed Kfirst radius) × (q i).SourceIndex =>
      (q k.1).sourceChild k.2
    ∀ (χ₀ : ((i : FirstSourceOuterIndex src R seed Kfirst radius) × (q i).SourceIndex) → RayCharacter)
      (m : ((i : FirstSourceOuterIndex src R seed Kfirst radius) × (q i).SourceIndex) → O)
      (t Kphys Tsec ξ Hsource P : ((i : FirstSourceOuterIndex src R seed Kfirst radius) × (q i).SourceIndex) → ℝ),
      (∀ k ∈ domain, m k ≠ 0 ∧ goodLambda ∣ m k ∧ (2 : O) ∣ m k) →
      (∀ k ∈ domain, |t k| ≤ T ∧ 0 < Kphys k ∧ 0 < P k ∧ 1/P k ≤ Z^(-(3/500 : ℝ)+primeLoss)) →
      (∀ k ∈ domain, frequencyRadius (Tsec k) Z (ξ k) ≤ Cr*Z^L ∧ Hsource k ≤ Z^Bsource ∧
        (expandedFactor ((v k).sideCharacter left) : ℝ)*R.absNorm*(sourceRadius src)^2*
          (4*frequencyRadius (Tsec k) Z (ξ k)) ≤ Z^B) →
      (∀ k ∈ domain, Kphys k ≤ mainCommonRadius Z
        (Real.logb Z (((v k).sideCommon (!left)).absNorm : ℝ))
        (nominalLog ((v k).sideCommon left) ((v k).sideCommon (!left))
          (Ideal.span {primeSubsetGenerator
            (fun P : CommonIndex ((v k).sideCommon left) ((v k).sideCommon (!left)) => P.val)
            ((v k).sideSubset left)}) Kfirst (volume src.toData) Z)
        (Real.logb Z (((v k).sideCommon left).absNorm : ℝ)) (9/500) omega 0) →
      (∑ k ∈ domain,
        ‖partEnergy true ((v k).sideCharacter left) (χ₀ k) Q (m k) (t k)
          (commonSecondColumns (original src R seed) ((v k).sideCommon left) ((v k).sideCommon_supported left))
          (commonSecondBeta (original src R seed) ((v k).sideCommon left) k.2.1.val)
          W (Kphys k) (Tsec k) Z (ξ k) (Hsource k)‖/(volume src.toData*P k)) ≤
      Cbound*coherentExceptionalProfile Sprofile src profile J Q K T*
        (originalLowerProfile src wlo wlo)^(-2/3:ℝ)*
        ((src.η.modulus.absNorm : ℝ)*(Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72 : O)}).absNorm)*
        Z^(p+A+refwidth-93/1000+5*omega/6+primeLoss+2*ε+δ+2*Bsource*θ+εmass+εsum)/
          (seed.absNorm : ℝ) := by
  obtain ⟨J,Sprofile,hSprofile,Cenergy,hCenergy,henergy⟩ := actual_common_coherent_exceptional_normalized
    wlo whi hwlo hwhi lo hi ε δ θ B Bsource L Cr εmass hε hδ hθ hB hBsource hL hCr hεmass W
  obtain ⟨Csum,hCsum,hsum⟩ := actual_first_source_sector_harmonic_mass Bsource Lfirst Crfirst εsum
    hBsource hLfirst hCrfirst hεsum
  refine ⟨J,Sprofile,hSprofile,Cenergy*Csum,mul_nonneg hCenergy hCsum.le,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,henergy⟩ := henergy Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [henergy,hsum] with Z hZ hmass
  refine ⟨hZ.1,?_⟩
  intro src profile hlo hhi hP hW₁ hW₂ hsource₀ hsource R seed hR hs hs0
    Kfirst M A omega primeLoss T hKfirst hM hT hwidth hvolume hA hX₁ hX₂ hY₁ hY₂ radius hr
    q labels left p refwidth hrad hreference domain v χ₀ m t Kphys Tsec ξ Hsource P hm hKP hgeometry hKcap
  have hz := zero_lt_one.trans hZ.1
  have hv := CenteredMomentExceptionalAmplitudePair.volume_pos src.toData
  have ha := originalLowerProfile_pos src wlo wlo hwlo hwlo
  have hpT := coherentExceptionalProfile_nonneg Sprofile src profile J Q K T hK.le
  have hzero₁ : src.W₁ 0 = 0 := by
    by_contra hh
    exact (not_le_of_gt hwlo) (profile.support 0 (by simpa only [←hW₁,Function.mem_support] using hh)).1
  have hzero₂ : src.W₂ 0 = 0 := by
    by_contra hh
    exact (not_le_of_gt hwlo) (profile.support 1 (by simpa only [←hW₂,Function.mem_support] using hh)).1
  have hmass' := hmass.2 ι src R seed hs hs0 hzero₁ hzero₂ hsource₀ hsource Kfirst hKfirst radius hr labels p hrad
  have hmassSide : (∑ k ∈ domain,1/((k.2.1.val).absNorm : ℝ)) ≤ Csum*Z^(p+εsum)/(seed.absNorm : ℝ) := by
    cases left
    · exact hmass'.2
    · exact hmass'.1
  let F := Cenergy*coherentExceptionalProfile Sprofile src profile J Q K T*
    (originalLowerProfile src wlo wlo)^(-2/3:ℝ)*
    ((src.η.modulus.absNorm : ℝ)*(Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72 : O)}).absNorm)
  let loss := -93/1000+5*omega/6+primeLoss+2*ε+δ+2*Bsource*θ+εmass
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hpoint (k) (hk : k ∈ domain) :
      ‖partEnergy true ((v k).sideCharacter left) (χ₀ k) Q (m k) (t k)
        (commonSecondColumns (original src R seed) ((v k).sideCommon left) ((v k).sideCommon_supported left))
        (commonSecondBeta (original src R seed) ((v k).sideCommon left) k.2.1.val)
        W (Kphys k) (Tsec k) Z (ξ k) (Hsource k)‖/(volume src.toData*P k) ≤
      F*Z^(A+refwidth+loss)/(k.2.1.val.absNorm : ℝ) := by
    have hg : k.1 ∈ labels ∧ Squarefree k.2.1.val ∧ k.2.1.val ≠ 0 ∧ ((k.2.1.val).absNorm : ℝ) ≤ Z^Bsource := by
      cases left
      · exact firstRightSourceLabels_gates labels q _ Z Bsource hz.le (fun _ _ => hsource) k hk
      · exact firstLeftSourceLabels_gates labels q _ Z Bsource hz.le (fun _ _ => hsource) k hk
    have hseedPair := actual_common_gates src R seed hs hzero₁ hzero₂ _ _ k.1.1.property
    have hseed : seed ∣ (v k).sideCommon left := by
      cases left
      · exact hseedPair.2.2.2.2.1
      · exact hseedPair.2.2.2.1
    have hvlog : Real.logb Z (volume src.toData) ≤ (883/1000)*M := by
      rw [hvolume,Real.logb_rpow hz hZ.1.ne'];exact hA
    have hh := hZ.2 src profile hlo hhi hP hW₁ hW₂ hsource R seed
      ((v k).sideCommon left) k.2.1.val ((v k).sideCommon_supported left)
      hR hseed hg.2.1 hg.2.2.1 ((v k).sideCharacter left) (χ₀ k) (m k)
      (hm k hk).1 (hm k hk).2.1 (hm k hk).2.2
      (t k) (Kphys k) (Tsec k) (ξ k) (Hsource k) (P k) M Kfirst omega primeLoss
      (hKP k hk).2.1 (hKP k hk).2.2.1 (hgeometry k hk).1 (hgeometry k hk).2.1
      (hgeometry k hk).2.2 hX₁ hX₂ hY₁ hY₂
      (v k).parent ((v k).sideCommon (!left)) _ ((v k).sideCommon_supported (!left))
      ((v k).side_equal_support left) ((v k).sideSubset left) rfl ((v k).side_modulus left)
      hKfirst hM hwidth hvlog (hKP k hk).2.2.2 (hKcap k hk)
    have href : ((v k).sideCharacter left).modulus.absNorm*(volume src.toData/(((v k).sideCommon left).absNorm : ℝ)^2)*
        Z^(allowance ((v k).sideCommon left) ((v k).sideCommon (!left)) Z) ≤
        ((src.η.modulus.absNorm : ℝ)*(Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72 : O)}).absNorm)*
          Z^(A+refwidth) := by
      rw [hvolume,←(v k).sideReference_literal left Z A,
        (q k.1).sourceChild_sideReference k.2 left Z A hZ.1,
        (q k.1).side_reference_powers left Z A hZ.1]
      apply mul_le_mul_of_nonneg_left _ (q k.1).parentCost_pos.le
      exact Real.rpow_le_rpow_of_exponent_le hZ.1.le (by linarith [hreference k.1 hg.1])
    apply hh.trans
    have hprof := coherentExceptionalProfile_height_le Sprofile src profile J Q K (t k) T hK.le hT (hKP k hk).1
    calc
      _ ≤ Cenergy*coherentExceptionalProfile Sprofile src profile J Q K T*
          (originalLowerProfile src wlo wlo)^(-2/3:ℝ)*
          (((src.η.modulus.absNorm : ℝ)*(Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72 : O)}).absNorm)*
            Z^(A+refwidth))*Z^loss/(k.2.1.val.absNorm : ℝ) := by
        gcongr <;> positivity
      _ = _ := by dsimp only [F];rw [Real.rpow_add hz (A+refwidth) loss];ring
  apply (Finset.sum_le_sum hpoint).trans
  rw [show (∑ k ∈ domain,F*Z^(A+refwidth+loss)/(k.2.1.val.absNorm : ℝ)) =
      F*Z^(A+refwidth+loss)*(∑ k ∈ domain,1/(k.2.1.val.absNorm : ℝ)) by
      rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro k hk;ring]
  apply (mul_le_mul_of_nonneg_left hmassSide (by positivity)).trans_eq
  have he : Z^(A+refwidth+loss)*Z^(p+εsum) =
      Z^(p+A+refwidth-93/1000+5*omega/6+primeLoss+2*ε+δ+2*Bsource*θ+εmass+εsum) := by
    rw [←Real.rpow_add hz];congr 1;dsimp only [loss];ring
  dsimp only [F]
  calc
    _ = (Cenergy*Csum)*coherentExceptionalProfile Sprofile src profile J Q K T*
        (originalLowerProfile src wlo wlo)^(-2/3:ℝ)*
        ((src.η.modulus.absNorm : ℝ)*(Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72 : O)}).absNorm)*
        (Z^(A+refwidth+loss)*Z^(p+εsum))/(seed.absNorm : ℝ) := by ring
    _ = _ := by rw [he]

#print axioms actual_first_coherent_exceptional_sum
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCoherentExceptionalSum -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstBinJointSum ; sha256 ed590020eb5268c7af0ebff945502024ceb25ad65b71a77365a570e38750a4dc -/
section



/-! The literal common-bin contribution in the first coherent decomposition
is put in the exact joint-row/dyadic-fiber form of the high source theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentCanonicalFirst CenteredMomentSecondPhysicalBlock CenteredMomentSecondEnergySplit
open CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

namespace ActualFirstSecondSource
variable (src : Input ι) (R seed : Ideal O) (Kfirst : ℝ)
  (radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ)
  (side : Bool) (Z A M omega ξ : ℝ)

def mainScale (k : First src R seed Kfirst radius) :=
  firstLowMainScale (firstSourceOuterLabel src R seed Kfirst radius k.1) side Z A M omega

def mainRadius (k : First src R seed Kfirst radius) :=
  firstLowRadius (firstSourceOuterLabel src R seed Kfirst radius k.1) side
    (sourceRadius src) Z A M omega ξ

def mainHeight (k : First src R seed Kfirst radius) :=
  sourceRadius src/((firstSourceOuterLabel src R seed Kfirst radius k.1).sideCommon side).absNorm

variable (hs : Squarefree seed) (hz₁ : src.W₁ 0=0) (hz₂ : src.W₂ 0=0)

def binRows (bin : NonzeroElement → Option κ) (b : κ)
    (k : First src R seed Kfirst radius)
    (n : Blocks src R seed Kfirst radius side
      (mainScale src R seed Kfirst radius side Z A M omega)
      (mainRadius src R seed Kfirst radius side Z A M omega ξ)
      (mainHeight src R seed Kfirst radius side) k) : Finset O :=
  let x : Packet src R seed Kfirst radius side
      (mainScale src R seed Kfirst radius side Z A M omega)
      (mainRadius src R seed Kfirst radius side Z A M omega ξ)
      (mainHeight src R seed Kfirst radius side) := ⟨k,n,0⟩
  (sourceRows n.1.1.val.1 n.1.1.val.2 n.1.2 (mainRadius src R seed Kfirst radius side Z A M omega ξ k)).filter
    (fun z => ((row x).firstPresentation src.η k.2.2.1 k.2.2.2⁻¹).sourceBin
      (packetLabel hs hz₁ hz₂ x) bin z = some b)

theorem binRows_nonzero (bin : NonzeroElement → Option κ) (b : κ)
    (k : First src R seed Kfirst radius)
    (n : Blocks src R seed Kfirst radius side
      (mainScale src R seed Kfirst radius side Z A M omega)
      (mainRadius src R seed Kfirst radius side Z A M omega ξ)
      (mainHeight src R seed Kfirst radius side) k) (z : O)
    (hz : z∈binRows src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b k n) : z≠0 :=
  sourceRows_nonzero _ _ _ _ z (Finset.mem_filter.mp hz).1

theorem binBlock_eq (bin : NonzeroElement → Option κ) (b : κ)
    (k : First src R seed Kfirst radius) (t : ℝ) (W : 𝓢(ℝ,ℂ)) :
    firstLowBinBlock src R seed hs hz₁ hz₂ Kfirst radius k side Z A M omega ξ t W bin b =
      actualSecondRowBlocks (parent src R seed Kfirst radius side k) t
        (columns src R seed Kfirst radius side k) (beta src R seed Kfirst radius side k)
        W (mainScale src R seed Kfirst radius side Z A M omega k)
        (mainRadius src R seed Kfirst radius side Z A M omega ξ k)
        (mainHeight src R seed Kfirst radius side k)
        (binRows src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b k) := by
  cases side <;> rfl

theorem actual_first_bin_packet_majorant (hZ : 0< Z)
    (labels : Finset (FirstSourceOuterIndex src R seed Kfirst radius))
    (bin : NonzeroElement → Option κ) (b : κ) (P : ℝ) (hP : 0< P)
    (t : First src R seed Kfirst radius → ℝ) (W : 𝓢(ℝ,ℂ)) :
    (∑ k∈firstSideSourceLabels labels (firstSourceOuterLabel src R seed Kfirst radius)
      (fun _ => sourceRadius src) side,
      ‖firstLowBinBlock src R seed hs hz₁ hz₂ Kfirst radius k side
        Z A M omega ξ (t k) W bin b‖/(volume src.toData*P)) ≤
      ∑ x∈packets src R seed Kfirst radius side
        (mainScale src R seed Kfirst radius side Z A M omega)
        (mainRadius src R seed Kfirst radius side Z A M omega ξ)
        (mainHeight src R seed Kfirst radius side) labels
        (binRows src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b),
        packetValue hs hz₁ hz₂ (volume src.toData) P t W x := by
  simp only [binBlock_eq]
  have hV : 0< volume src.toData :=
    mul_pos (mul_pos src.X₁_pos src.X₂_pos) (Finset.prod_pos (fun j _ => src.P_pos j))
  apply first_domain_majorant hs hz₁ hz₂ _ P hV hP t W labels _
  · intro k hk
    exact Real.rpow_pos_of_pos hZ _
  · intro k hk n z hz
    exact binRows_nonzero src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b k n z hz

def binPackets (labels : Finset (FirstSourceOuterIndex src R seed Kfirst radius))
    (bin : NonzeroElement → Option κ) (b : κ) :=
  packets src R seed Kfirst radius side
    (mainScale src R seed Kfirst radius side Z A M omega)
    (mainRadius src R seed Kfirst radius side Z A M omega ξ)
    (mainHeight src R seed Kfirst radius side) labels
    (binRows src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b)

theorem binPackets_nonzero (labels : Finset (FirstSourceOuterIndex src R seed Kfirst radius))
    (bin : NonzeroElement → Option κ) (b : κ)
    (x : Packet src R seed Kfirst radius side
      (mainScale src R seed Kfirst radius side Z A M omega)
      (mainRadius src R seed Kfirst radius side Z A M omega ξ)
      (mainHeight src R seed Kfirst radius side))
    (hx : x∈binPackets src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ labels bin b) :
    (row x).z≠0 := by
  have hm := (Finset.mem_sigma.mp (Finset.mem_sigma.mp hx).2).2
  exact binRows_nonzero src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b x.1 x.2.1 x.2.2 hm

/-- The exact first-domain bin contribution, in the input form of
`actual_joint_high_source_geometry`. The indicator is the original physical
packet image, not an independent restriction on an enlarged source. -/
theorem actual_first_bin_joint_majorant (hZ : 0< Z)
    (labels : Finset (FirstSourceOuterIndex src R seed Kfirst radius))
    (bin : NonzeroElement → Option κ) (b : κ) (P : ℝ) (hP : 0< P)
    (t : First src R seed Kfirst radius → ℝ) (W : 𝓢(ℝ,ℂ))
    (fallback : First src R seed Kfirst radius) :
    let K := mainScale src R seed Kfirst radius side Z A M omega
    let Radius := mainRadius src R seed Kfirst radius side Z A M omega ξ
    let H := mainHeight src R seed Kfirst radius side
    let X := binPackets src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ labels bin b
    let hzero := binPackets_nonzero src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ labels bin b
    (∑ k∈firstSideSourceLabels labels (firstSourceOuterLabel src R seed Kfirst radius)
      (fun _ => sourceRadius src) side,
      ‖firstLowBinBlock src R seed hs hz₁ hz₂ Kfirst radius k side
        Z A M omega ξ (t k) W bin b‖/(volume src.toData*P)) ≤
      ∑ χ₁ : RayCharacter,∑ ξ₁ : RayCharacter,
      ∑ q∈rayRows fallback X hzero χ₁ ξ₁,
        ∑ n₁ : q.val.FirstDyadic Kfirst (radius q.val.first q.val.E) (sourceRadius src),
        ∑ n₂ : q.val.SecondDyadic (secondScale fallback K χ₁ ξ₁ q.val n₁)
          (secondScale fallback Radius χ₁ ξ₁ q.val n₁) (secondScale fallback H χ₁ ξ₁ q.val n₁),
        if (⟨q,n₁,n₂⟩ : FiberTarget fallback χ₁ ξ₁ K Radius H side)∈rayTarget fallback X hzero χ₁ ξ₁
        then fiberValue hs hz₁ hz₂ fallback χ₁ ξ₁ (volume src.toData) P t W ⟨q,n₁,n₂⟩ else 0 := by
  intro K Radius H X hzero
  apply (actual_first_bin_packet_majorant src R seed Kfirst radius side Z A M omega ξ
    hs hz₁ hz₂ hZ labels bin b P hP t W).trans_eq
  rw [show (∑ x∈packets src R seed Kfirst radius side K Radius H labels
      (binRows src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b),
      packetValue hs hz₁ hz₂ (volume src.toData) P t W x) =
      ∑ x∈X,packetValue hs hz₁ hz₂ (volume src.toData) P t W x by rfl]
  rw [sum_ray_partition hs hz₁ hz₂ X (volume src.toData) P t W]
  apply Finset.sum_congr rfl
  intro χ₁ hχ₁
  apply Finset.sum_congr rfl
  intro ξ₁ hξ₁
  exact sum_ray_fibers hs hz₁ hz₂ fallback X hzero χ₁ ξ₁ (volume src.toData) P t W

end ActualFirstSecondSource
#print axioms ActualFirstSecondSource.binBlock_eq
#print axioms ActualFirstSecondSource.actual_first_bin_packet_majorant
#print axioms ActualFirstSecondSource.actual_first_bin_joint_majorant
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstBinJointSum -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstMainScale ; sha256 99f6a1970d3c4dcaf6e487fd231fa3790d2b8d03fb19fbbf5b91c15de5c4473e -/
section




/-! The physical low/high split uses exactly the coherent amplifier's
radius, on either first side, with its actual small support loss. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSectorLocalization
open CenteredMomentFirstMixedRightTransport CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstAmplificationChoice
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace FirstJointLabel

theorem side_nominal_log_power (q : FirstJointLabel ι) (left : Bool) (Z A M : ℝ)
    (hZ : 1 < Z) :
    nominalLog (q.sideCommon left) (q.sideCommon (!left)) (Ideal.span {q.puncture})
      (Z^M) (Z^A) Z =
        2*A-q.sideWidth left Z-q.sideWidth (!left) Z+q.activeWidth Z+q.punctureWidth Z-M := by
  cases left
  · change nominalLog q.D q.C _ _ _ _ = _
    rw [nominalLog_swap,q.nominal_log_power Z A M hZ]
    dsimp only [sideWidth,sideCommon,Bool.not_false,Bool.false_eq_true,if_false,if_true]
    change _ = 2*A-q.rightWidth Z-q.leftWidth Z+q.activeWidth Z+q.punctureWidth Z-M
    ring
  · exact q.nominal_log_power Z A M hZ

theorem sideMainRadius_eq_firstLowMainScale (q : FirstJointLabel ι) (left : Bool)
    (Z A M delta reserve : ℝ) (hZ : 1 < Z) :
    q.sideMainRadius left Z (Z^M) (Z^A) (9/500) delta reserve =
      firstLowMainScale q left Z A M (delta+reserve) := by
  unfold sideMainRadius
  rw [q.side_nominal_log_power left Z A M hZ]
  unfold mainCommonRadius firstLowMainScale
  rw [q.activeWidth_normValue,q.punctureWidth_normValue]
  congr 1
  dsimp only [sideWidth]
  ring

theorem sideMainRadius_eq_firstLowMainScale_of_volume (q : FirstJointLabel ι) (left : Bool)
    (Z A M V delta reserve : ℝ) (hZ : 1 < Z) (hV : V = Z^A) :
    q.sideMainRadius left Z (Z^M) V (9/500) delta reserve =
      firstLowMainScale q left Z A M (delta+reserve) := by
  rw [hV]
  exact q.sideMainRadius_eq_firstLowMainScale left Z A M delta reserve hZ

end FirstJointLabel

theorem firstLowRadius_eq_second_frequency (q : FirstJointLabel ι) (left : Bool)
    (H Z A M omega ξ : ℝ) :
    firstLowRadius q left H Z A M omega ξ =
      frequencyRadius ((H/((q.sideCommon left).absNorm : ℝ))^2/
        firstLowMainScale q left Z A M omega) Z ξ := rfl

#print axioms FirstJointLabel.sideMainRadius_eq_firstLowMainScale
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstMainScale -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstSecondHighValue ; sha256 e943684d5cd9b0a68a3e60ed6baaad505afc01ea90d7b0fb6fe44e08cd3b2f6c -/
section


/-! Literal packet values equal the canonical source-row expressions in
the high theorem. No all-ideal row identity or natural-parent premise is
required from the caller. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open NonzeroJointSourceRow CenteredMomentCanonicalFirst
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace ActualFirstSecondSource
variable {src : Input ι} {R seed : Ideal O} {Kfirst : ℝ}
  {radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ}
  {side : Bool} {K Radius H : First src R seed Kfirst radius → ℝ}

theorem fiberValue_eq_high
    (hs : Squarefree seed) (hz₁ : src.W₁ 0=0) (hz₂ : src.W₂ 0=0)
    (fallback : First src R seed Kfirst radius)
    (rowDefault : NonzeroJointSourceRow (original src R seed) side)
    (χ ξ : RayCharacter) (V P : ℝ)
    (t : First src R seed Kfirst radius → ℝ) (W : 𝓢(ℝ,ℂ))
    (q : NonzeroJointSourceRow (original src R seed) side)
    (n : q.val.DyadicFiber Kfirst (radius q.val.first q.val.E) (sourceRadius src)
      (secondScale fallback K χ ξ q.val) (secondScale fallback Radius χ ξ q.val)
      (secondScale fallback H χ ξ q.val)) :
    let s := sourceKernel src R seed side hs hz₁ hz₂ rowDefault src.η χ ξ⁻¹ 1 1
    fiberValue hs hz₁ hz₂ fallback χ ξ V P t W ⟨q,n⟩ =
      ∑ χ₂ : RayCharacter,∑ ξ₂ : RayCharacter,∑ D∈(s q.label).physicalProjectors,
        ‖((s q.label).withRays χ₂ ξ₂).physicalRowTerm V P
          (t (firstAt fallback q.val χ ξ n.1)) q.val.z W
          (secondScale fallback K χ ξ q.val n.1)
          (secondScale fallback Radius χ ξ q.val n.1) (fun j => (n.2 j : ℤ)) D‖ := by
  dsimp only
  simp only [sourceKernel,recover_label]
  rfl

#print axioms fiberValue_eq_high
end ActualFirstSecondSource
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstSecondHighValue -/
