import Candidate.Cycle63.Physical.InitialMass.GeometrySources
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceSupport

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentFirstPhysicalSource
open CenteredMomentFirstPhysicalSourceSupport CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstReferenceSource CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstSourceReduction CenteredMomentSourceMass
open CenteredMomentSecondRetainedRows CenteredMomentLogDyadic CenteredMomentCanonicalFirst
open CenteredMomentExceptionalAmplitudePair CenteredMomentCompleteCommon
open CenteredMomentSectorLocalization ActualEisensteinCubic
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance scalarSupportDecidableSum : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- The norm-aligning phase kills zero physical blocks before applying
source support. Hence the scalar bound needs no support assertion about
unused columns in a padded input pool. -/
theorem actual_phase_scalar_volume (s : Input ι) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ) (hK : 0<K)
    (a₁ a₂ : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : ∀x,s.W₁ x≠0→a₁≤x) (hs₂ : ∀x,s.W₂ x≠0→a₂≤x)
    (q : FirstSourceCoordinate s R seed K Z ξ) :
    ‖normPhase (coordinateBlock s R seed W K Z ξ q)*
      (originalFirstBlock s R seed K Z ξ hK q).outside‖*volume s.toData≤
      (4/((∏i,s.lo i)*a₁*a₂))*K*
        Real.sqrt ((q.1.val.1.absNorm:ℝ)*q.1.val.2.absNorm)/
          (‖eisEmbedding (primeSubsetGenerator
            (fun P : CommonIndex q.1.val.1 q.1.val.2=>P.val) q.2.1.val)‖^2*
            ‖eisEmbedding (activeConductor q.1.val.1 q.1.val.2)‖) := by
  by_cases hn : coordinateBlock s R seed W K Z ξ q=0
  · simp only [hn,normPhase,norm_zero,Complex.ofReal_zero,zero_div,zero_mul]
    exact div_nonneg (mul_nonneg (mul_nonneg (div_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg (Finset.prod_nonneg (fun i _=>(s.lo_pos i).le)) ha₁.le) ha₂.le))
        hK.le) (Real.sqrt_nonneg _)) (mul_nonneg (sq_nonneg _) (norm_nonneg _))
  · have hh := original_scalar_volume s R seed a₁ a₂ ha₁ ha₂ hs₁ hs₂
      (CenteredMomentSecondHeightFamily.fixedBadMask*idealGenerator R) 1 s.t
      (finiteColumns (Fintype.piFinset s.pools)) q.1.val.1 q.1.val.2
      (originalFirstBlock s R seed K Z ξ hK q).hC
      (originalFirstBlock s R seed K Z ξ hK q).hD q.2.1.val
      (originalFirstBlock s R seed K Z ξ hK q).rows W (fun _=>logAnnulus)
      K (dyadicScale (q.2.2 0)) (dyadicScale (q.2.2 1))
      (dyadicScale (q.2.2 2)) (dyadicScale (q.2.2 3)) (Real.log 4)
      hK (dyadicScale_pos _) (dyadicScale_pos _)
      (fun _ _ h=>CenteredMomentSecondIdealBlockBound.logAnnulus_enclosure _ h) hn
    rw [Real.exp_log (by norm_num : (0:ℝ)<4)] at hh
    apply le_trans _ hh
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_left (norm_nonneg _)
        (normPhase_norm (coordinateBlock s R seed W K Z ξ q)))
      (CenteredMomentExceptionalAmplitudePair.volume_pos s.toData).le

/-- The same support bound in the geometry coordinates used by joint
Cauchy. The two common-ideal norm factors remain explicit. -/
theorem actual_phase_scalar_power (s : Input ι) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (M Z ξ : ℝ) (hZ : 1<Z)
    (a₁ a₂ : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : ∀x,s.W₁ x≠0→a₁≤x) (hs₂ : ∀x,s.W₂ x≠0→a₂≤x)
    (q : FirstSourceCoordinate s R seed (Z^M) Z ξ) :
    ‖normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)*
      (originalFirstBlock s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) q).outside‖≤
      (4/((∏i,s.lo i)*a₁*a₂))*Real.sqrt ((q.1.val.1.absNorm:ℝ)*q.1.val.2.absNorm)*
        Z^(outsideExponent M (Real.logb Z (volume s.toData))
          (geometryExponents s R seed (Z^M) Z ξ q)) := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hK : 0<Z^M := Real.rpow_pos_of_pos hz _
  have hV := CenteredMomentExceptionalAmplitudePair.volume_pos s.toData
  have hh := actual_phase_scalar_volume s R seed W (Z^M) Z ξ hK
    a₁ a₂ ha₁ ha₂ hs₁ hs₂ q
  have hC := (originalFirstBlock s R seed (Z^M) Z ξ hK q).hC
  let e := primeSubsetGenerator (fun P : CommonIndex q.1.val.1 q.1.val.2=>P.val) q.2.1.val
  let r := activeConductor q.1.val.1 q.1.val.2
  have he : 0<((Ideal.span {e}).absNorm:ℝ) :=
    CenteredMomentFirstScale.norm_pos _ (CenteredMomentFirstCanonicalFamily.subsetGenerator_supported
      q.1.val.1 q.1.val.2 hC q.2.1.val).1
  have hr : 0<((Ideal.span {r}).absNorm:ℝ) :=
    CenteredMomentFirstScale.active_norm_pos _ _
  have hp := outside_power (Z^M) (volume s.toData)
    ((Ideal.span {e}).absNorm:ℝ) ((Ideal.span {r}).absNorm:ℝ) Z hK hV he hr hZ
  rw [Real.logb_rpow hz hZ.ne'] at hp
  have hroot : Real.sqrt ((Ideal.span {r}).absNorm:ℝ)=‖eisEmbedding r‖ := by
    rw [←eisEmbedding_norm_sq_eq_absNorm_span,Real.sqrt_sq (norm_nonneg _)]
  rw [hroot,←eisEmbedding_norm_sq_eq_absNorm_span] at hp
  calc
    _ ≤ ((4/((∏i,s.lo i)*a₁*a₂))*Z^M*
        Real.sqrt ((q.1.val.1.absNorm:ℝ)*q.1.val.2.absNorm)/
        (‖eisEmbedding e‖^2*‖eisEmbedding r‖))/volume s.toData :=
      (le_div_iff₀ hV).mpr hh
    _ = (4/((∏i,s.lo i)*a₁*a₂))*
        Real.sqrt ((q.1.val.1.absNorm:ℝ)*q.1.val.2.absNorm)*
        (Z^M/(volume s.toData*‖eisEmbedding e‖^2*‖eisEmbedding r‖)) := by ring
    _ = _ := by
      rw [hp]
      congr 2
      dsimp [outsideExponent,geometryExponents,geometryNorms,geometryIdeals,e,r]
      rw [eisEmbedding_norm_sq_eq_absNorm_span]
      ring

lemma normalized_square_bound (Z o l n m C f : ℝ) (hZ : 0<Z)
    (hn : 0≤n) (hm : 0≤ m) (hf : 0≤f)
    (hbound : f≤C*Real.sqrt (n*m)*Z^o) :
    f^2/Z^(2*o+l)≤C^2*n*m/Z^l := by
  have hh := pow_le_pow_left₀ hf hbound 2
  simp only [mul_pow,Real.sq_sqrt (mul_nonneg hn hm)] at hh
  apply (div_le_div_of_nonneg_right hh (Real.rpow_nonneg hZ.le _)).trans_eq
  rw [Real.rpow_add hZ,←Real.rpow_mul_natCast hZ.le,
    show o*(2:ℕ)=2*o by norm_num;ring]
  field_simp

/-- The normalized left scalar pays the actual product of common-ideal
norms. Their later cancellation is retained in the joint source budget. -/
theorem actual_geometry_left_scalar_sq (s : Input ι) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (M Z ξ : ℝ) (hZ : 1<Z)
    (a₁ a₂ : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : ∀x,s.W₁ x≠0→a₁≤x) (hs₂ : ∀x,s.W₂ x≠0→a₂≤x)
    (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)) :
    ‖geometryColumnScalar false s R seed (Z^M) Z ξ M (Real.logb Z (volume s.toData))
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key
      (fun q=>normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)) j‖^2≤
      (4/((∏i,s.lo i)*a₁*a₂))^2*
        (j.1.val.1.val.1.absNorm:ℝ)*j.1.val.1.val.2.absNorm/
          Z^(leftExponent (Real.logb Z (volume s.toData))
            (geometryExponents s R seed (Z^M) Z ξ j.1.val)) := by
  have hh := actual_phase_scalar_power s R seed W M Z ξ hZ a₁ a₂ ha₁ ha₂ hs₁ hs₂ j.1.val
  have hb := normalized_square_bound Z
    (outsideExponent M (Real.logb Z (volume s.toData))
      (geometryExponents s R seed (Z^M) Z ξ j.1.val))
    (leftExponent (Real.logb Z (volume s.toData))
      (geometryExponents s R seed (Z^M) Z ξ j.1.val))
    (j.1.val.1.val.1.absNorm:ℝ) (j.1.val.1.val.2.absNorm:ℝ)
    (4/((∏i,s.lo i)*a₁*a₂)) _ (zero_lt_one.trans hZ)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (norm_nonneg _) hh
  simpa only [geometryColumnScalar,geometryFirstSource,Bool.false_eq_true,ite_false,norm_div,div_pow,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)] using hb

end
end OAI.SevenEighths.Cycle63InitialMass
