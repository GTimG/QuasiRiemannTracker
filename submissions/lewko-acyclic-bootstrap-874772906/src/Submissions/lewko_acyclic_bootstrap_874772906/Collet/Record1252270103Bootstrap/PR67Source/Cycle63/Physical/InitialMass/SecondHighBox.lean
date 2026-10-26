import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondHighCoordinates
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondCoarseSupport
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondEncodedGates
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentRankinRadical CenteredMomentCommonHarmonicMass
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSectorLocalization Cycle63Moment Cycle63HighGeometry Cycle63FinalCapacity
open CenteredMomentAmplificationChildSourceCaps

lemma ideal_log_box (I : Ideal O) (hI : I≠0) (Z B : ℝ) (hZ : 1<Z)
    (hcap : (I.absNorm:ℝ)≤Z^B) : 0≤Real.logb Z (I.absNorm:ℝ) ∧ Real.logb Z (I.absNorm:ℝ)≤B := by
  exact ⟨Real.logb_nonneg hZ (norm_ge_one I hI),
    (Real.logb_le_iff_le_rpow hZ (norm_pos I hI)).mpr hcap⟩

/-- Every inactive subset has norm at most the first common ideal. -/
lemma common_subset_log_box (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (Z B : ℝ) (hZ : 1<Z)
    (hcap : (C.absNorm:ℝ)≤Z^B) :
    0≤Real.logb Z ((∏P∈U,P.val).absNorm:ℝ) ∧
      Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)≤B := by
  have hpos := firstCommonSubsetNorm_pos C D hC U
  have hrad := firstCommonSubsetNorm_pos C D hC Finset.univ
  have hd : (∏P∈U,P.val)∣∏P : CommonIndex C D,P.val :=
    Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)
  have hn := Nat.le_of_dvd hrad (map_dvd Ideal.absNorm hd)
  have hh := commonRadical_norm_le C D hC.1 hD.1
  rw [first_common_radical_product] at hh
  have hnorm : ((∏P∈U,P.val).absNorm:ℝ)≤Z^B :=
    (Nat.cast_le.mpr hn).trans ((hh.trans (min_le_left _ _)).trans hcap)
  apply ideal_log_box _ _ Z B hZ hnorm
  exact Ideal.absNorm_eq_zero_iff.not.mp (Nat.ne_of_gt hpos)

/-- Coarse source-norm caps give a fixed box for all four high coordinates.
The box is independent of the source, allocations and row count. -/
theorem actual_high_coordinate_box (reflected left second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (heq₂ : primeSupport C₂=primeSupport D₂) (U : Finset (CommonIndex C₂ D₂))
    (Z M A a ξ reserve ε B : ℝ) (hZ : 1<Z) (hB : 0≤B)
    (hfirst : (l.1.1.absNorm:ℝ)≤Z^B ∧ (l.1.2.absNorm:ℝ)≤Z^B)
    (hsecond : (C₂.absNorm:ℝ)≤Z^B ∧ (D₂.absNorm:ℝ)≤Z^B)
    (hM : |M|≤B) (hA : |A|≤B) (ha : |a|≤B)
    (hω : |frequencyLoss Z 32 ξ+reserve|≤B)
    (hε : |ε|≤B) :
    ∀i,-(32*B)≤actualHighCoordinates reflected left second l C₂ D₂ U Z M A a ξ reserve ε i ∧
      actualHighCoordinates reflected left second l C₂ D₂ U Z M A a ξ reserve ε i≤32*B := by
  have hc₀ := ideal_log_box l.1.1 hC.1 Z B hZ hfirst.1
  have hd₀ := ideal_log_box l.1.2 hD.1 Z B hZ hfirst.2
  have hc : 0≤Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ) ∧
      Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)≤B := by
    cases reflected <;> assumption
  have hd : 0≤Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ) ∧
      Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)≤B := by
    cases reflected <;> assumption
  have hb₂ : 0≤Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ) ∧
      Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)≤B := by
    cases second
    · exact ideal_log_box C₂ hC₂.1 Z B hZ hsecond.1
    · exact ideal_log_box D₂ hD₂.1 Z B hZ hsecond.2
  have hE := common_subset_log_box l.1.1 l.1.2 hC hD l.2.val Z B hZ hfirst.1
  change 0≤Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ) ∧
    Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)≤B at hE
  have ht := common_subset_log_box C₂ D₂ hC₂ hD₂ U Z B hZ hsecond.1
  obtain ⟨hp,hEp,hR₀,hpc,hpd,hRp,hLc⟩ := actual_first_gates left l hC hD Z hZ
  have hr0 : 0≤Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    have hn : 0<(Ideal.span {activeConductor l.1.1 l.1.2}).absNorm := by
      exact_mod_cast active_norm_pos l.1.1 l.1.2
    exact_mod_cast hn
  have hl0 : 0≤Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ) :=
    Real.logb_nonneg hZ (normValue_ge_one _ (first_source_numerator_ne_zero left l hC))
  have hmissing := first_missing_norm_le left l hC hD
  have hm := ideal_log_box (firstSourceMissing left l)
    (Ideal.absNorm_eq_zero_iff.not.mp (Nat.ne_of_gt hmissing.1)) Z B hZ
    ((Nat.cast_le.mpr hmissing.2.1).trans hfirst.1)
  have hg0 : 0≤Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂)) :=
    Real.logb_nonneg hZ (normValue_ge_one _ (commonFrequencyGenerator_ne_zero C₂ D₂ hC₂))
  have hg := (Real.logb_le_iff_le_rpow hZ
    (normValue_pos _ (commonFrequencyGenerator_ne_zero C₂ D₂ hC₂))).mpr
      ((actual_common_norm_le C₂ D₂ hC₂ hD₂ heq₂).trans hsecond.1)
  have hcd : 0≤ max (Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)-
      Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)) 0 ∧
      max (Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)-
      Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)) 0≤B :=
    ⟨le_max_right _ _,max_le (by linarith [hc.2,hd.1]) hB⟩
  have hdc : 0≤ max (Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)-
      Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)) 0 ∧
      max (Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)-
      Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)) 0≤B :=
    ⟨le_max_right _ _,max_le (by linarith [hd.2,hc.1]) hB⟩
  rcases abs_le.mp hM with ⟨hMlo,hMhi⟩
  rcases abs_le.mp hA with ⟨hAlo,hAhi⟩
  rcases abs_le.mp ha with ⟨halo,hahi⟩
  rcases abs_le.mp hω with ⟨hωlo,hωhi⟩
  rcases abs_le.mp hε with ⟨hεlo,hεhi⟩
  intro i
  fin_cases i <;> dsimp [actualHighCoordinates] <;> constructor <;>
    linarith [hc.1,hc.2,hd.1,hd.2,hb₂.1,hb₂.2,hE.1,hE.2,ht.1,ht.2,hm.1,hm.2,hcd.1,hcd.2,hdc.1,hdc.2]

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
