/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.SecondRatioContraction
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.SecondDyadEnvelope
import Submissions.hailey_collet_1252270103.Cycle61.Physical.FinalCapacity.Geometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamily

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSectorLocalization CenteredMomentDyadicCount
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondBlockAggregate CenteredMomentSecondActiveDyadic
open CenteredMomentSecondBlockCount CenteredMomentSecondWholeKernel
open CenteredMomentSecondExceptionalFamily CenteredMomentFirstScale
open RayFourExpansion CenteredMomentSecondEnergySplit
local notation "O" => HeckeFamily.O
local instance secondRatioCapDecidable {ι : Type*} : DecidableEq ι := Classical.decEq _

/-- The actual canonical frequency factors have polynomial norm, without
counting their arithmetic labels or subsets. -/
lemma actual_second_frequency_norm_cap (C D : Ideal O)(hC : Supported C)(hD : Supported D)
    (hCD : primeSupport C=primeSupport D)(U : Finset (CommonIndex C D)) :
    1≤normValue (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) ∧
    normValue (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)≤(C.absNorm:ℝ)^2 := by
  have hne := mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC)
    (nonunitFrequencyGenerator_ne_zero C D hC U)
  refine ⟨normValue_ge_one _ hne,?_⟩
  have hd : Ideal.span {nonunitFrequencyGenerator C D U}∣C :=
    (dvd_mul_left (Ideal.span {nonunitFrequencyGenerator C D U}) (∏P∈U,P.val)).trans
      (selected_nonunit_dvd C D hC hD hCD U).1
  have hv : normValue (nonunitFrequencyGenerator C D U)≤(C.absNorm:ℝ) := by
    unfold normValue
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)) (map_dvd Ideal.absNorm hd)
  rw [normValue_mul,pow_two]
  exact mul_le_mul (Cycle61FinalCapacity.actual_common_norm_le C D hC hD hCD) hv
    (show 0≤normValue _ from Nat.cast_nonneg _) (Nat.cast_nonneg _)

abbrev SecondAbsoluteEnvelope (Z A D B L Cr : ℝ) :=
  ∀i : Fin 4,↥(indices (![Z^(-(D+2*B)),1,1,1] i)
    (![Z^(A+2*B),max 1 (4*Cr)*Z^L,Z^B,Z^B] i))

/-- Actual source-block membership supplies a common absolute interval,
even when K, the conductor and the frequency subset vary with every label. -/
lemma actual_second_dyads_absolute (Z A D₀ B L Cr : ℝ)(hZ : 1≤Z)
    (_hA : 0≤A)(_hD₀ : 0≤D₀)(hB : 0≤B)(hL : 0≤L)(_hCr : 0<Cr)
    (C D : Ideal O)(hC : Supported C)(hD : Supported D)(hCD : primeSupport C=primeSupport D)
    (U : Finset (CommonIndex C D))(K R H : ℝ)(hK : 0<K)
    (hKlo : Z^(-D₀)≤K)(hKhi : K≤Z^A)(hR : R≤Cr*Z^L)(hH : H≤Z^B)
    (hNC : (C.absNorm:ℝ)≤Z^B)(hND : (D.absNorm:ℝ)≤Z^B)
    (n : SourceBlocks C D U K R H)(i : Fin 4) :
    (n i:ℤ)∈indices (![Z^(-(D₀+2*B)),1,1,1] i)
      (![Z^(A+2*B),max 1 (4*Cr)*Z^L,Z^B,Z^B] i) := by
  have hz := zero_lt_one.trans_le hZ
  let G := commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
  have hG0 : G≠0 := mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC)
    (nonunitFrequencyGenerator_ne_zero C D hC U)
  have hG := actual_second_frequency_norm_cap C D hC hD hCD U
  have hNC1 := ideal_norm_ge_one C hC.1
  have hND1 := ideal_norm_ge_one D hD.1
  have hden : 0<(C.absNorm:ℝ)*(D.absNorm:ℝ) := by positivity
  have hprod : (C.absNorm:ℝ)*(D.absNorm:ℝ)≤Z^(2*B) := by
    apply (mul_le_mul hNC hND (Nat.cast_nonneg _) (by positivity)).trans_eq
    rw [←Real.rpow_add hz];congr 1;ring
  have helo : Z^(-(D₀+2*B))≤secondEffectiveScale C D G K := by
    have hh : Z^(-D₀)/Z^(2*B)≤K*normValue G/((C.absNorm:ℝ)*(D.absNorm:ℝ)) := by
      exact div_le_div₀ (mul_nonneg hK.le (show 0≤normValue G from Nat.cast_nonneg _)) (hKlo.trans (le_mul_of_one_le_right hK.le hG.1)) hden hprod
    rw [secondEffectiveScale,←normValue_eq_embedding]
    change _≤K*normValue G/((C.absNorm:ℝ)*(D.absNorm:ℝ))
    apply (le_of_eq ?_).trans hh
    rw [←Real.rpow_sub hz];congr 1;ring
  have hehi : secondEffectiveScale C D G K≤Z^(A+2*B) := by
    have hgpow : normValue G≤Z^(2*B) := by
      apply hG.2.trans
      calc (C.absNorm:ℝ)^2≤(Z^B)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hNC 2
           _=Z^(2*B) := by rw [←Real.rpow_natCast,←Real.rpow_mul hz.le];congr 1;ring
    rw [secondEffectiveScale,←normValue_eq_embedding]
    change K*normValue G/((C.absNorm:ℝ)*(D.absNorm:ℝ))≤_
    apply (div_le_self (mul_nonneg hK.le (show 0≤normValue _ from Nat.cast_nonneg _))
      (one_le_mul_of_one_le_of_one_le hNC1 hND1)).trans
    apply (mul_le_mul hKhi hgpow (show 0≤normValue _ from Nat.cast_nonneg _) (by positivity)).trans_eq
    rw [←Real.rpow_add hz]
  have hepos := secondEffectiveScale_pos C D hC.1 hD.1 G hG0 K hK
  have hupper (j : Fin 4) : sourceUpper C D G K R H j≤
      (![Z^(A+2*B),max 1 (4*Cr)*Z^L,Z^B,Z^B] j) := by
    fin_cases j
    · exact hehi
    · change max 1 (4*R/normValue G)≤max 1 (4*Cr)*Z^L
      apply max_le (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (Real.one_le_rpow hZ hL))
      apply (div_le_iff₀ (zero_lt_one.trans_le hG.1)).mpr
      calc 4*R≤(4*Cr)*Z^L := by linarith
           _≤max 1 (4*Cr)*Z^L := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
           _≤(max 1 (4*Cr)*Z^L)*normValue G := le_mul_of_one_le_right (by positivity) hG.1
    · change max 1 (H/(C.absNorm:ℝ))≤Z^B
      apply max_le (Real.one_le_rpow hZ hB)
      apply (div_le_iff₀ (zero_lt_one.trans_le hNC1)).mpr
      exact hH.trans (le_mul_of_one_le_right (by positivity) hNC1)
    · change max 1 (H/(D.absNorm:ℝ))≤Z^B
      apply max_le (Real.one_le_rpow hZ hB)
      apply (div_le_iff₀ (zero_lt_one.trans_le hND1)).mpr
      exact hH.trans (le_mul_of_one_le_right (by positivity) hND1)
  have hp := (mem_indices_iff_scale _ _
    (sourceLower_pos C D hC.1 hD.1 G hG0 K hK i)
    ((sourceLower_pos C D hC.1 hD.1 G hG0 K hK i).trans_le (sourceLower_le_upper C D G K R H i))
    (n i)).mp (n i).property
  have hloVec : ∀j : Fin 4,0<(![Z^(-(D₀+2*B)),1,1,1] j) := by
    intro j;fin_cases j
    · change 0<Z^(-(D₀+2*B));positivity
    all_goals change (0:ℝ)<1;norm_num
  have hhiVec : ∀j : Fin 4,0<(![Z^(A+2*B),max 1 (4*Cr)*Z^L,Z^B,Z^B] j) := by
    intro j;fin_cases j
    · change 0<Z^(A+2*B);positivity
    · change 0<max 1 (4*Cr)*Z^L;positivity
    all_goals change 0<Z^B;positivity
  apply (mem_indices_iff_scale _ _ (hloVec i) (hhiVec i) _).mpr
  constructor
  · apply le_trans ?_ hp.1
    fin_cases i
    · exact helo
    all_goals exact le_rfl
  · exact hp.2.trans (mul_le_mul_of_nonneg_left (hupper i) (by norm_num))

/-- One finite absolute box counts all ratio bins, without counting any
moving ideal, allocation, source or partition label. -/
theorem second_absolute_envelope_subpower (A D B L Cr ε : ℝ)
    (hA : 0≤A)(hD : 0≤D)(hB : 0≤B)(hL : 0≤L)(_hCr : 0<Cr)(hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
      (Fintype.card (SecondAbsoluteEnvelope Z A D B L Cr):ℝ)≤C*Z^ε := by
  obtain ⟨C,hC,hcount⟩ := four_indices_subpower (max 1 (4*Cr)) (A+D+4*B+L) ε
    (le_max_left _ _) (by positivity) hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount,eventually_ge_atTop (1:ℝ)] with Z hc hZ
  have hz := zero_lt_one.trans_le hZ
  apply hc ![Z^(-(D+2*B)),1,1,1] ![Z^(A+2*B),max 1 (4*Cr)*Z^L,Z^B,Z^B]
  · intro i;fin_cases i
    · change 0<Z^(-(D+2*B));positivity
    all_goals change (0:ℝ)<1;norm_num
  · intro i;fin_cases i
    · exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
    · exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) (Real.one_le_rpow hZ hL)
    · exact Real.one_le_rpow hZ hB
    · exact Real.one_le_rpow hZ hB
  · intro i;fin_cases i
    · change Z^(A+2*B)/Z^(-(D+2*B))≤max 1 (4*Cr)*Z^(A+D+4*B+L)
      rw [←Real.rpow_sub hz]
      apply (Real.rpow_le_rpow_of_exponent_le hZ (show A+2*B- -(D+2*B)≤A+D+4*B+L by linarith)).trans
      exact le_mul_of_one_le_left (by positivity) (le_max_left _ _)
    · change (max 1 (4*Cr)*Z^L)/1≤max 1 (4*Cr)*Z^(A+D+4*B+L)
      rw [div_one]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (le_max_of_le_left (by norm_num))
    · change Z^B/1≤max 1 (4*Cr)*Z^(A+D+4*B+L)
      rw [div_one]
      exact (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)).trans
        (le_mul_of_one_le_left (by positivity) (le_max_left _ _))
    · change Z^B/1≤max 1 (4*Cr)*Z^(A+D+4*B+L)
      rw [div_one]
      exact (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)).trans
        (le_mul_of_one_le_left (by positivity) (le_max_left _ _))

/-- Uniform image count across every varying source-block label. The only
membership input is the literal SourceBlocks construction, not a ratio or
cardinality estimate. Constants precede the moving family and its size. -/
theorem actual_second_ratio_bins_subpower (A D₀ B L Cr ε : ℝ)
    (hA : 0≤A)(hD₀ : 0≤D₀)(hB : 0≤B)(hL : 0≤L)(hCr : 0<Cr)(hε : 0<ε) :
    ∃C₀ : ℝ,0<C₀ ∧ ∀ᶠZ : ℝ in atTop,
    ∀{Label : Type*}[Fintype Label](block : Label→SecondBlockSource)
      (C D : Label→Ideal O),(∀l,Supported (C l)) → (∀l,Supported (D l)) →
      (∀l,primeSupport (C l)=primeSupport (D l)) →
    ∀(U : (l : Label)→Finset (CommonIndex (C l) (D l)))(K R H : Label→ℝ),
      (∀l,0<K l) → (∀l,Z^(-D₀)≤K l) → (∀l,K l≤Z^A) →
      (∀l,R l≤Cr*Z^L) → (∀l,H l≤Z^B) →
      (∀l,((C l).absNorm:ℝ)≤Z^B) → (∀l,((D l).absNorm:ℝ)≤Z^B) →
    ∀n : (l : Label)→SourceBlocks (C l) (D l) (U l) (K l) (R l) (H l),
      (∀l i,(block l).dyad i=(n l i:ℤ)) →
      ((secondRatioBins block).card:ℝ)≤C₀*Z^ε := by
  obtain ⟨C₀,hC₀,hcount⟩ := second_absolute_envelope_subpower A D₀ B L Cr ε hA hD₀ hB hL hCr hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hcount,eventually_ge_atTop (1:ℝ)] with Z hc hZ
  intro Label _ block C D hC hD hCD U K R H hK hKlo hKhi hR hH hNC hND n hdyad
  let index : SecondAbsoluteEnvelope Z A D₀ B L Cr→ℤ := fun m=>
    (m 0).val+(m 1).val-(m 2).val-(m 3).val
  have hsub : secondRatioBins block⊆Finset.univ.image index := by
    intro r hr
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hr
    let m : SecondAbsoluteEnvelope Z A D₀ B L Cr := fun i=>
      ⟨(n l i:ℤ),actual_second_dyads_absolute Z A D₀ B L Cr hZ hA hD₀ hB hL hCr
        (C l) (D l) (hC l) (hD l) (hCD l) (U l) (K l) (R l) (H l)
        (hK l) (hKlo l) (hKhi l) (hR l) (hH l) (hNC l) (hND l) (n l) i⟩
    apply Finset.mem_image.mpr
    refine ⟨m,Finset.mem_univ _,?_⟩
    simp only [index,m,secondRatioIndex,hdyad]
  have hh : (secondRatioBins block).card≤Fintype.card (SecondAbsoluteEnvelope Z A D₀ B L Cr) :=
    (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by rw [Finset.card_univ]))
  exact (show ((secondRatioBins block).card:ℝ)≤Fintype.card (SecondAbsoluteEnvelope Z A D₀ B L Cr)
    by exact_mod_cast hh).trans hc

/-- Native actual-datum instantiation for a heterogeneous family of retained
blocks. Conductor caps follow from the original polynomial support, and
SourceBlocks itself supplies every dyadic-membership condition. -/
theorem actual_second_datum_ratio_bins_subpower {α : Type*}[Fintype α][DecidableEq α]
    (A D₀ B L Cr ε : ℝ)(hA : 0≤A)(hD₀ : 0≤D₀)(hB : 0≤B)(hL : 0≤L)
    (hCr : 0<Cr)(hε : 0<ε) :
    ∃C₀ : ℝ,0<C₀ ∧ ∀ᶠZ : ℝ in atTop,
    ∀{Label : Type*}[Fintype Label](slots : Label→Finset α)(s : (l : Label)→Input (slots l))
      (R seed : Label→Ideal O)(hseed : ∀l,Squarefree (seed l))
      (hz₁ : ∀l,(s l).W₁ 0=0)(hz₂ : ∀l,(s l).W₂ 0=0)
      (K Tsec : Label→ℝ)(ξ : ℝ)(hK : ∀l,0<K l),
      (∀l,Z^(-D₀)≤K l) → (∀l,K l≤Z^A) →
      (∀l,frequencyRadius (Tsec l) Z ξ≤Cr*Z^L) → (∀l,sourceRadius (s l)≤Z^B) →
    ∀q : (l : Label)→ActualSecondBlockIndex (s l) (R l) (seed l) (K l) (Tsec l) Z ξ,
      ((secondRatioBins (fun l=>(actualSecondBlockDatum (slots l) (s l) (R l) (seed l)
        (hseed l) (hz₁ l) (hz₂ l) (K l) (Tsec l) Z ξ (hK l) (q l)).block)).card:ℝ)≤C₀*Z^ε := by
  obtain ⟨C₀,hC₀,hcount⟩ := actual_second_ratio_bins_subpower A D₀ B L Cr ε hA hD₀ hB hL hCr hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hcount] with Z hc
  intro Label _ slots s R seed hseed hz₁ hz₂ K Tsec ξ hK hKlo hKhi hR hsource q
  let datum := fun l=>actualSecondBlockDatum (slots l) (s l) (R l) (seed l)
    (hseed l) (hz₁ l) (hz₂ l) (K l) (Tsec l) Z ξ (hK l) (q l)
  have hnorm (l : Label) : ((datum l).C.absNorm:ℝ)≤Z^B ∧ ((datum l).D.absNorm:ℝ)≤Z^B := by
    have hh := actual_common_gates (s l) (R l) (seed l) (hseed l) (hz₁ l) (hz₂ l)
      (q l).1.val.val.1 (q l).1.val.val.2 (q l).1.val.property
    exact ⟨hh.2.2.2.2.2.1.trans (hsource l),hh.2.2.2.2.2.2.trans (hsource l)⟩
  exact hc (fun l=>(datum l).block) (fun l=>(datum l).C) (fun l=>(datum l).D)
    (fun l=>(datum l).hC) (fun l=>(datum l).hD) (fun l=>(datum l).sameSupport)
    (fun l=>(datum l).inactive) K (fun l=>frequencyRadius (Tsec l) Z ξ)
    (fun l=>sourceRadius (s l)) hK hKlo hKhi hR hsource (fun l=>(hnorm l).1) (fun l=>(hnorm l).2)
    (fun l=>(q l).2.2) (fun _ _=>rfl)

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_frequency_norm_cap
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_dyads_absolute
#print axioms OAI.SevenEighths.Cycle61InitialMass.second_absolute_envelope_subpower

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_ratio_bins_subpower

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_datum_ratio_bins_subpower
