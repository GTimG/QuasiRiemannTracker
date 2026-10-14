/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B115
import Candidate.Bundles.B117
import Candidate.Bundles.B153
import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamily

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondRatioContraction; sha256 a4210eedcec029b150fdec0ff6b25816b5da4b681a3a0cef30258c2b93498d89 -/
section
                                                         

set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open CenteredMomentSectorLocalization

def secondRatioIndex (s : SecondBlockSource) : ℤ :=
  s.dyad 0+s.dyad 1-s.dyad 2-s.dyad 3

lemma actual_second_ratio_index (s : SecondBlockSource) :
    s.ratio=dyadicScale (secondRatioIndex s) := by
  simp only [SecondBlockSource.ratio,secondRatioIndex,dyadicScale,
    zpow_sub₀ (by norm_num : (2:ℝ)≠0),zpow_add₀ (by norm_num : (2:ℝ)≠0)]
  ring

def secondRatioBins {Label : Type*}[Fintype Label] (s : Label→ SecondBlockSource) : Finset ℤ :=
  Finset.univ.image (fun l=>secondRatioIndex (s l))

abbrev SecondRatioFiber {Label : Type*} (s : Label→ SecondBlockSource)(r : ℤ) :=
  {l : Label // secondRatioIndex (s l)=r}

/-- Group the original weighted sum without taking absolute values of
individual first or second labels. -/
theorem actual_second_ratio_sum {Label : Type*}[Fintype Label]
    (s : Label→ SecondBlockSource)(w : Label→ℂ)(W : 𝓢(ℝ,ℂ)) :
    (∑l,w l*(s l).value W)=∑r∈secondRatioBins s,
      ∑l : SecondRatioFiber s r,w l.val*(s l.val).value W := by
  classical
  rw [←Finset.sum_fiberwise_of_maps_to
    (fun l (hl : l∈(Finset.univ : Finset Label))=>
      Finset.mem_image_of_mem (fun l=>secondRatioIndex (s l)) hl)]
  apply Finset.sum_congr rfl
  intro r hr
  exact (Finset.sum_subtype (Finset.univ.filter (fun l=>secondRatioIndex (s l)=r))
    (fun l=>by simp) (fun l=>w l*(s l).value W))

/-- Apply the whole-kernel contraction to exact ratio fibers. Original
weights remain inside the joint balanced energy on every fiber. -/
theorem actual_second_ratio_contraction (W : 𝓢(ℝ,ℂ))(A J : ℕ) :
    ∃C : ℝ,0≤ C ∧ ∀{Label : Type*}[Fintype Label]
      (s : Label→ SecondBlockSource)(w : Label→ℂ)(E : ℤ→ℝ),
      (∀r∈secondRatioBins s,0≤ E r) →
      (∀r∈secondRatioBins s,∀t : ℝ,
        let src:=fun l : SecondRatioFiber s r=>s l.val
        let weight:=fun l : SecondRatioFiber s r=>w l.val
        secondBalancedEnergyPair src (secondEffectiveWeight src weight W)
          (secondGeometricBalance src (secondEffectiveWeight src weight W)) t≤ E r*(1+‖t‖)^J) →
      ‖∑l,w l*(s l).value W‖≤ C*∑r∈secondRatioBins s,E r/(1+dyadicScale r)^A := by
  classical
  obtain ⟨C,hC,hbound⟩:=actual_second_effective_contraction W A J
  refine ⟨C,hC,?_⟩
  intro Label _ s w E hE he
  rw [actual_second_ratio_sum]
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  have hd : 0< dyadicScale r := by unfold dyadicScale; positivity
  have hh:=hbound (fun l : SecondRatioFiber s r=>s l.val)
    (fun l : SecondRatioFiber s r=>w l.val) (dyadicScale r) hd
    (fun l=>by rw [actual_second_ratio_index,l.property]) (E r) (hE r hr) (he r hr)
  have hpos : 0<(1+dyadicScale r)^A := by positivity
  rw [←mul_div_assoc]
  apply (le_div_iff₀ hpos).mpr
  calc
    _=(1+dyadicScale r)^A*‖∑l : SecondRatioFiber s r,w l.val*(s l.val).value W‖ := mul_comm _ _
    _≤ C*E r := hh

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_ratio_index
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_ratio_sum
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_ratio_contraction

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondRatioContraction -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondRatioCap; sha256 d72f205fa20d9b811d6670b2216b4a201c6185428281f0895bb232be1743400c -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                          
                                                      
                                              
                                                                  

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
    1≤ normValue (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) ∧
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
    (show 0≤ normValue _ from Nat.cast_nonneg _) (Nat.cast_nonneg _)

abbrev SecondAbsoluteEnvelope (Z A D B L Cr : ℝ) :=
  ∀i : Fin 4,↥(indices (![Z^(-(D+2*B)),1,1,1] i)
    (![Z^(A+2*B),max 1 (4*Cr)*Z^L,Z^B,Z^B] i))

/-- Actual source-block membership supplies a common absolute interval,
even when K, the conductor and the frequency subset vary with every label. -/
lemma actual_second_dyads_absolute (Z A D₀ B L Cr : ℝ)(hZ : 1≤ Z)
    (_hA : 0≤ A)(_hD₀ : 0≤ D₀)(hB : 0≤ B)(hL : 0≤ L)(_hCr : 0< Cr)
    (C D : Ideal O)(hC : Supported C)(hD : Supported D)(hCD : primeSupport C=primeSupport D)
    (U : Finset (CommonIndex C D))(K R H : ℝ)(hK : 0< K)
    (hKlo : Z^(-D₀)≤ K)(hKhi : K≤ Z^A)(hR : R≤ Cr*Z^L)(hH : H≤ Z^B)
    (hNC : (C.absNorm:ℝ)≤ Z^B)(hND : (D.absNorm:ℝ)≤ Z^B)
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
  have hprod : (C.absNorm:ℝ)*(D.absNorm:ℝ)≤ Z^(2*B) := by
    apply (mul_le_mul hNC hND (Nat.cast_nonneg _) (by positivity)).trans_eq
    rw [←Real.rpow_add hz];congr 1;ring
  have helo : Z^(-(D₀+2*B))≤ secondEffectiveScale C D G K := by
    have hh : Z^(-D₀)/Z^(2*B)≤ K*normValue G/((C.absNorm:ℝ)*(D.absNorm:ℝ)) := by
      exact div_le_div₀ (mul_nonneg hK.le (show 0≤ normValue G from Nat.cast_nonneg _)) (hKlo.trans (le_mul_of_one_le_right hK.le hG.1)) hden hprod
    rw [secondEffectiveScale,←normValue_eq_embedding]
    change _≤ K*normValue G/((C.absNorm:ℝ)*(D.absNorm:ℝ))
    apply (le_of_eq ?_).trans hh
    rw [←Real.rpow_sub hz];congr 1;ring
  have hehi : secondEffectiveScale C D G K≤ Z^(A+2*B) := by
    have hgpow : normValue G≤ Z^(2*B) := by
      apply hG.2.trans
      calc (C.absNorm:ℝ)^2≤(Z^B)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hNC 2
           _=Z^(2*B) := by rw [←Real.rpow_natCast,←Real.rpow_mul hz.le];congr 1;ring
    rw [secondEffectiveScale,←normValue_eq_embedding]
    change K*normValue G/((C.absNorm:ℝ)*(D.absNorm:ℝ))≤ _
    apply (div_le_self (mul_nonneg hK.le (show 0≤ normValue _ from Nat.cast_nonneg _))
      (one_le_mul_of_one_le_of_one_le hNC1 hND1)).trans
    apply (mul_le_mul hKhi hgpow (show 0≤ normValue _ from Nat.cast_nonneg _) (by positivity)).trans_eq
    rw [←Real.rpow_add hz]
  have hepos := secondEffectiveScale_pos C D hC.1 hD.1 G hG0 K hK
  have hupper (j : Fin 4) : sourceUpper C D G K R H j≤
      (![Z^(A+2*B),max 1 (4*Cr)*Z^L,Z^B,Z^B] j) := by
    fin_cases j
    · exact hehi
    · change max 1 (4*R/normValue G)≤ max 1 (4*Cr)*Z^L
      apply max_le (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (Real.one_le_rpow hZ hL))
      apply (div_le_iff₀ (zero_lt_one.trans_le hG.1)).mpr
      calc 4*R≤(4*Cr)*Z^L := by linarith
           _≤ max 1 (4*Cr)*Z^L := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
           _≤(max 1 (4*Cr)*Z^L)*normValue G := le_mul_of_one_le_right (by positivity) hG.1
    · change max 1 (H/(C.absNorm:ℝ))≤ Z^B
      apply max_le (Real.one_le_rpow hZ hB)
      apply (div_le_iff₀ (zero_lt_one.trans_le hNC1)).mpr
      exact hH.trans (le_mul_of_one_le_right (by positivity) hNC1)
    · change max 1 (H/(D.absNorm:ℝ))≤ Z^B
      apply max_le (Real.one_le_rpow hZ hB)
      apply (div_le_iff₀ (zero_lt_one.trans_le hND1)).mpr
      exact hH.trans (le_mul_of_one_le_right (by positivity) hND1)
  have hp := (mem_indices_iff_scale _ _
    (sourceLower_pos C D hC.1 hD.1 G hG0 K hK i)
    ((sourceLower_pos C D hC.1 hD.1 G hG0 K hK i).trans_le (sourceLower_le_upper C D G K R H i))
    (n i)).mp (n i).property
  have hloVec : ∀j : Fin 4,0<(![Z^(-(D₀+2*B)),1,1,1] j) := by
    intro j;fin_cases j
    · change 0< Z^(-(D₀+2*B));positivity
    all_goals change (0:ℝ)<1;norm_num
  have hhiVec : ∀j : Fin 4,0<(![Z^(A+2*B),max 1 (4*Cr)*Z^L,Z^B,Z^B] j) := by
    intro j;fin_cases j
    · change 0< Z^(A+2*B);positivity
    · change 0< max 1 (4*Cr)*Z^L;positivity
    all_goals change 0< Z^B;positivity
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
    (hA : 0≤ A)(hD : 0≤ D)(hB : 0≤ B)(hL : 0≤ L)(_hCr : 0< Cr)(hε : 0<ε) :
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,
      (Fintype.card (SecondAbsoluteEnvelope Z A D B L Cr):ℝ)≤ C*Z^ε := by
  obtain ⟨C,hC,hcount⟩ := four_indices_subpower (max 1 (4*Cr)) (A+D+4*B+L) ε
    (le_max_left _ _) (by positivity) hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount,eventually_ge_atTop (1:ℝ)] with Z hc hZ
  have hz := zero_lt_one.trans_le hZ
  apply hc ![Z^(-(D+2*B)),1,1,1] ![Z^(A+2*B),max 1 (4*Cr)*Z^L,Z^B,Z^B]
  · intro i;fin_cases i
    · change 0< Z^(-(D+2*B));positivity
    all_goals change (0:ℝ)<1;norm_num
  · intro i;fin_cases i
    · exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
    · exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) (Real.one_le_rpow hZ hL)
    · exact Real.one_le_rpow hZ hB
    · exact Real.one_le_rpow hZ hB
  · intro i;fin_cases i
    · change Z^(A+2*B)/Z^(-(D+2*B))≤ max 1 (4*Cr)*Z^(A+D+4*B+L)
      rw [←Real.rpow_sub hz]
      apply (Real.rpow_le_rpow_of_exponent_le hZ (show A+2*B- -(D+2*B)≤ A+D+4*B+L by linarith)).trans
      exact le_mul_of_one_le_left (by positivity) (le_max_left _ _)
    · change (max 1 (4*Cr)*Z^L)/1≤ max 1 (4*Cr)*Z^(A+D+4*B+L)
      rw [div_one]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (le_max_of_le_left (by norm_num))
    · change Z^B/1≤ max 1 (4*Cr)*Z^(A+D+4*B+L)
      rw [div_one]
      exact (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)).trans
        (le_mul_of_one_le_left (by positivity) (le_max_left _ _))
    · change Z^B/1≤ max 1 (4*Cr)*Z^(A+D+4*B+L)
      rw [div_one]
      exact (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)).trans
        (le_mul_of_one_le_left (by positivity) (le_max_left _ _))

/-- Uniform image count across every varying source-block label. The only
membership input is the literal SourceBlocks construction, not a ratio or
cardinality estimate. Constants precede the moving family and its size. -/
theorem actual_second_ratio_bins_subpower (A D₀ B L Cr ε : ℝ)
    (hA : 0≤ A)(hD₀ : 0≤ D₀)(hB : 0≤ B)(hL : 0≤ L)(hCr : 0< Cr)(hε : 0<ε) :
    ∃C₀ : ℝ,0< C₀ ∧ ∀ᶠZ : ℝ in atTop,
    ∀{Label : Type*}[Fintype Label](block : Label→ SecondBlockSource)
      (C D : Label→ Ideal O),(∀l,Supported (C l)) → (∀l,Supported (D l)) →
      (∀l,primeSupport (C l)=primeSupport (D l)) →
    ∀(U : (l : Label)→ Finset (CommonIndex (C l) (D l)))(K R H : Label→ℝ),
      (∀l,0< K l) → (∀l,Z^(-D₀)≤ K l) → (∀l,K l≤ Z^A) →
      (∀l,R l≤ Cr*Z^L) → (∀l,H l≤ Z^B) →
      (∀l,((C l).absNorm:ℝ)≤ Z^B) → (∀l,((D l).absNorm:ℝ)≤ Z^B) →
    ∀n : (l : Label)→ SourceBlocks (C l) (D l) (U l) (K l) (R l) (H l),
      (∀l i,(block l).dyad i=(n l i:ℤ)) →
      ((secondRatioBins block).card:ℝ)≤ C₀*Z^ε := by
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
  have hh : (secondRatioBins block).card≤ Fintype.card (SecondAbsoluteEnvelope Z A D₀ B L Cr) :=
    (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by rw [Finset.card_univ]))
  exact (show ((secondRatioBins block).card:ℝ)≤ Fintype.card (SecondAbsoluteEnvelope Z A D₀ B L Cr)
    by exact_mod_cast hh).trans hc

/-- Native actual-datum instantiation for a heterogeneous family of retained
blocks. Conductor caps follow from the original polynomial support, and
SourceBlocks itself supplies every dyadic-membership condition. -/
theorem actual_second_datum_ratio_bins_subpower {α : Type*}[Fintype α][DecidableEq α]
    (A D₀ B L Cr ε : ℝ)(hA : 0≤ A)(hD₀ : 0≤ D₀)(hB : 0≤ B)(hL : 0≤ L)
    (hCr : 0< Cr)(hε : 0<ε) :
    ∃C₀ : ℝ,0< C₀ ∧ ∀ᶠZ : ℝ in atTop,
    ∀{Label : Type*}[Fintype Label](slots : Label→ Finset α)(s : (l : Label)→ Input (slots l))
      (R seed : Label→ Ideal O)(hseed : ∀l,Squarefree (seed l))
      (hz₁ : ∀l,(s l).W₁ 0=0)(hz₂ : ∀l,(s l).W₂ 0=0)
      (K Tsec : Label→ℝ)(ξ : ℝ)(hK : ∀l,0< K l),
      (∀l,Z^(-D₀)≤ K l) → (∀l,K l≤ Z^A) →
      (∀l,frequencyRadius (Tsec l) Z ξ≤ Cr*Z^L) → (∀l,sourceRadius (s l)≤ Z^B) →
    ∀q : (l : Label)→ ActualSecondBlockIndex (s l) (R l) (seed l) (K l) (Tsec l) Z ξ,
      ((secondRatioBins (fun l=>(actualSecondBlockDatum (slots l) (s l) (R l) (seed l)
        (hseed l) (hz₁ l) (hz₂ l) (K l) (Tsec l) Z ξ (hK l) (q l)).block)).card:ℝ)≤ C₀*Z^ε := by
  obtain ⟨C₀,hC₀,hcount⟩ := actual_second_ratio_bins_subpower A D₀ B L Cr ε hA hD₀ hB hL hCr hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hcount] with Z hc
  intro Label _ slots s R seed hseed hz₁ hz₂ K Tsec ξ hK hKlo hKhi hR hsource q
  let datum := fun l=>actualSecondBlockDatum (slots l) (s l) (R l) (seed l)
    (hseed l) (hz₁ l) (hz₂ l) (K l) (Tsec l) Z ξ (hK l) (q l)
  have hnorm (l : Label) : ((datum l).C.absNorm:ℝ)≤ Z^B ∧ ((datum l).D.absNorm:ℝ)≤ Z^B := by
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

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondRatioCap -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondRetainedContraction; sha256 021e39272ca41de82b947ddcc944a5fe1d57ab5708d47448568a632f319d1143 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                           
                                                  

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization
open CenteredMomentSourceLiveColumn CenteredMomentCommonPairedSource
open CenteredMomentAmplificationChildInput CenteredMomentExceptionalAmplitudePair
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondEnergySplit
open CenteredMomentLogDyadic CenteredMomentOriginalCommonHarmonic CenteredMomentSecondLocalization
open CenteredMomentSecondBlockAggregate
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondLiveBlock
open CenteredMomentActiveSource CenteredMomentFirstSectors CenteredMomentSourceRow
open Cycle61Moment RayFourExpansion CenteredMomentCommonHeightEnvelope
open CenteredMomentSourceMass CenteredMomentSecondActivePhysicalDictionary
local notation "O" => HeckeFamily.O
local instance secondRestrictedSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Change only the physical row set. The original input, character family,
Fourier scale and dyadic block coordinates remain literal. -/
def ordinarySecondDatum (d : SecondInputDatum α) (χ : RayCharacter) (Q : Ideal O) (m : O) :
    SecondInputDatum α :=
  {d with
    rows:=partRows false d.input.η χ Q m d.C d.D d.inactive d.radius
    rows_ne:=fun z hz=>sourceRows_nonzero d.C d.D d.inactive d.radius z
      (Finset.mem_filter.mp hz).1}

@[simp] theorem ordinary_second_dyad (d : SecondInputDatum α)
    (χ : RayCharacter)(Q : Ideal O)(m : O)(i : Fin 4) :
    (ordinarySecondDatum d χ Q m).block.dyad i=d.block.dyad i := rfl

@[simp] theorem ordinary_second_ratio (d : SecondInputDatum α)
    (χ : RayCharacter)(Q : Ideal O)(m : O) :
    secondRatioIndex (ordinarySecondDatum d χ Q m).block=secondRatioIndex d.block := rfl

/-- The two full positive normalized sums, on the rows of the supplied
restricted datums. Residual ideals and all source labels stay in the sum. -/
def secondNormalizedSum {Label : Type*}[Fintype Label]
    (reflected : Bool)(d : Label→ SecondInputDatum α)(w : Label→ℂ)(t u : ℝ) : ℝ :=
  ∑r∈secondLiveRows (fun l=>(d l).block),
    ∑L∈secondResidualIdeals (fun l=>(d l).block) r,
      (‖w r.1‖*(d r.1).block.outside*volume (d r.1).input.toData)*
        (if reflected then
          ‖normalizedColumn (withHeight (d r.1).input ((d r.1).τ r.2.2.1⁻¹)
            ((d r.1).input.t+2*Real.pi*(u-(-t))))
            (d r.1).D (d r.1).hD (d r.1).R (d r.1).seed L (-r.2.2.2.val)‖^2
         else
          ‖normalizedColumn (withHeight (d r.1).input ((d r.1).τ r.2.1)
            ((d r.1).input.t+2*Real.pi*(u-t)))
            (d r.1).C (d r.1).hC (d r.1).R (d r.1).seed L r.2.2.2.val‖^2)

lemma normalized_balance_sqrt (E H T : ℝ)(hE : 0≤ E)(hH : 0< H)(hT : 0≤ T) :
    Real.sqrt (E*H*T)*Real.sqrt (E/H*T)=E*T := by
  rw [←Real.sqrt_mul (mul_nonneg (mul_nonneg hE hH.le) hT)]
  have heq : E*H*T*(E/H*T)=(E*T)^2 := by field_simp
  rw [heq,Real.sqrt_sq_eq_abs,abs_of_nonneg (mul_nonneg hE hT)]

/-- Literal full positive normalized sums on every exact ratio fiber. -/
def SecondNormalizedBound {Label : Type*}[Fintype Label]
    (W : 𝓢(ℝ,ℂ))(degree windowDegree : ℕ)
    (d : Label→ SecondInputDatum α)(w : Label→ℂ)(E H : ℤ→ℝ) : Prop :=
  ∀r∈secondRatioBins (fun l=>(d l).block),∀(reflected : Bool)(t u : ℝ),
        let datum:=fun l : SecondRatioFiber (fun l=>(d l).block) r=>d l.val;
        let src:=fun l : SecondRatioFiber (fun l=>(d l).block) r=>(datum l).block;
        let weight:=fun l : SecondRatioFiber (fun l=>(d l).block) r=>w l.val;
        secondNormalizedSum reflected datum (secondEffectiveWeight src weight W) t u≤
          ((if reflected then E r/H r else E r*H r)*(1+‖t‖)^degree)*
            (1+‖u‖)^(2*windowDegree)

/-- Joint restricted physical block contraction from literal positive sums
on each exact ratio fiber. Constants precede the moving datum family. -/
theorem restricted_second_ratio_from_normalized (W : 𝓢(ℝ,ℂ))(A degree windowDegree : ℕ)
    (hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus) :
    ∃C : ℝ,0≤ C ∧ ∀{Label : Type*}[Fintype Label]
    (d : Label→ SecondInputDatum α)(w : Label→ℂ)(E H : ℤ→ℝ),
      (∀r∈secondRatioBins (fun l=>(d l).block),0≤ E r) →
      (∀r∈secondRatioBins (fun l=>(d l).block),0< H r) →
      SecondNormalizedBound W degree windowDegree d w E H →
      ‖∑l,w l*(d l).block.value W‖≤
        C*∑r∈secondRatioBins (fun l=>(d l).block),E r/(1+dyadicScale r)^A := by
  obtain ⟨C,hC,hcon⟩:=actual_second_ratio_contraction W A degree
  let IL:=|∫u : ℝ,(1+‖u‖)^windowDegree*‖columnDensity logAnnulus hc hs u‖|
  let IR:=|∫u : ℝ,(1+‖u‖)^windowDegree*‖columnDensity (fun x=>star (logAnnulus x))
    (CenteredMomentConjugateWindow.conjugate_compact logAnnulus hc)
    (CenteredMomentConjugateWindow.conjugate_smooth logAnnulus hs) u‖|
  refine ⟨C*IL*IR,by dsimp [IL,IR];positivity,?_⟩
  intro Label _ d w E H hE hH hnorm
  have hh:=hcon (fun l=>(d l).block) w (fun r=>E r*IL*IR)
    (fun r hr=>by have he:=hE r hr; dsimp [IL,IR];positivity) ?_
  · apply hh.trans_eq
    simp_rw [show ∀ r : ℤ, E r*IL*IR/(1+dyadicScale r)^A =
      E r/(1+dyadicScale r)^A*IL*IR by intro r; ring]
    rw [←Finset.sum_mul,←Finset.sum_mul]
    ring
  · intro r hr t
    let datum:=fun l : SecondRatioFiber (fun l=>(d l).block) r=>d l.val
    let src:=fun l : SecondRatioFiber (fun l=>(d l).block) r=>(datum l).block
    let weight:=fun l : SecondRatioFiber (fun l=>(d l).block) r=>w l.val
    let ew:=secondEffectiveWeight src weight W
    have hleft:=hnorm r hr false t
    have hright:=hnorm r hr true t
    have hEt : 0≤ E r*H r*(1+‖t‖)^degree := by have he:=hE r hr; have hh:=hH r hr; positivity
    have hEr : 0≤ E r/H r*(1+‖t‖)^degree := by have he:=hE r hr; have hh:=hH r hr; positivity
    have hb:=actual_balanced_energy_from_normalized datum ew t windowDegree
      (E r*H r*(1+‖t‖)^degree) (E r/H r*(1+‖t‖)^degree) hEt hEr hc hs
      (fun u=>by simpa only [secondNormalizedSum,Bool.false_eq_true,ite_false] using hleft u)
      (fun u=>by simpa only [secondNormalizedSum,ite_true] using hright u)
    rw [normalized_balance_sqrt (E r) (H r) ((1+‖t‖)^degree) (hE r hr) (hH r hr)
      (by positivity)] at hb
    exact hb.trans_eq (by dsimp [IL,IR];ring)

/-- Ordinary restriction leaves the exact ratio image unchanged. -/
@[simp] theorem ordinary_second_ratio_bins {Label : Type*}[Fintype Label]
    (d : Label→ SecondInputDatum α)(χ : Label→ RayCharacter)
    (Q : Label→ Ideal O)(m : Label→ O) :
    secondRatioBins (fun l=>(ordinarySecondDatum (d l) (χ l) (Q l) (m l)).block)=
      secondRatioBins (fun l=>(d l).block) := rfl

/-- Literal ordinary part of the original retained energy, preserving the
single weighted block sum. No restricted block is required to be nonzero. -/
theorem actual_original_ordinary_assembly (slots : Finset α) (s : Input slots)
    (R seed : Ideal O) (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (χ : RayCharacter)(Q : Ideal O)(m : O)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0< K) :
    partEnergy false s.η χ Q m s.t (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s R seed) W K Tsec Z ξ (sourceRadius s)=
      ∑q : ActualSecondBlockIndex s R seed K Tsec Z ξ,
        actualSecondBlockWeight s R seed K Tsec Z ξ q*
          (ordinarySecondDatum
            (actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK q)
            χ Q m).block.value W := by
  unfold partEnergy
  rw [Fintype.sum_sigma]
  conv_lhs => rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Fintype.sum_sigma,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only [actualSecondBlockWeight,ordinarySecondDatum,actualSecondBlockDatum,
    actualSecondInputDatum,SecondInputDatum.block,originalSecondBlock,SecondBlockSource.value]
  apply congrArg (fun x : ℂ=>heightCoeff s.η s.t p.val.val.1*
    star (heightCoeff s.η s.t p.val.val.2)*x)
  exact (physicalBlock_active s.η s.t _ _ _ _ _ _ U _ _ W K _).symm

/-- Heterogeneous ordinary parts remain one joint physical block sum. -/
theorem actual_joint_ordinary_assembly {Label : Type*} [Fintype Label]
    (slots : Label→ Finset α) (s : (l : Label)→ Input (slots l))
    (R seed : Label→ Ideal O) (hseed : ∀l,Squarefree (seed l))
    (hz₁ : ∀l,(s l).W₁ 0=0) (hz₂ : ∀l,(s l).W₂ 0=0)
    (χ : Label→ RayCharacter)(Q : Label→ Ideal O)(m : Label→ O)
    (W : 𝓢(ℝ,ℂ)) (K Tsec : Label→ℝ) (Z ξ : ℝ) (hK : ∀l,0< K l)
    (weight : Label→ℂ) :
    (∑l,weight l*partEnergy false (s l).η (χ l) (Q l) (m l) (s l).t
      (finiteColumns (Fintype.piFinset (s l).pools)) (coefficient (s l) (R l) (seed l))
        W (K l) (Tsec l) Z ξ (sourceRadius (s l)))=
      ∑q : (l : Label) × ActualSecondBlockIndex (s l) (R l) (seed l) (K l) (Tsec l) Z ξ,
        (weight q.1*actualSecondBlockWeight (s q.1) (R q.1) (seed q.1) (K q.1) (Tsec q.1) Z ξ q.2)*
          (ordinarySecondDatum
            (actualSecondBlockDatum (slots q.1) (s q.1) (R q.1) (seed q.1)
              (hseed q.1) (hz₁ q.1) (hz₂ q.1) (K q.1) (Tsec q.1) Z ξ (hK q.1) q.2)
            (χ q.1) (Q q.1) (m q.1)).block.value W := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro l hl
  rw [actual_original_ordinary_assembly (slots l) (s l) (R l) (seed l)
    (hseed l) (hz₁ l) (hz₂ l) (χ l) (Q l) (m l) W (K l) (Tsec l) Z ξ (hK l),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  exact (mul_assoc _ _ _).symm

/-- Actual source-block ratio cardinality survives ordinary restriction;
conductor caps are still discharged by the original polynomial support. -/
theorem actual_ordinary_ratio_bins_subpower
    (A D₀ B L Cr ε : ℝ)(hA : 0≤ A)(hD₀ : 0≤ D₀)(hB : 0≤ B)(hL : 0≤ L)
    (hCr : 0< Cr)(hε : 0<ε) :
    ∃C₀ : ℝ,0< C₀ ∧ ∀ᶠZ : ℝ in atTop,
    ∀{Label : Type*}[Fintype Label](slots : Label→ Finset α)(s : (l : Label)→ Input (slots l))
      (R seed : Label→ Ideal O)(hseed : ∀l,Squarefree (seed l))
      (hz₁ : ∀l,(s l).W₁ 0=0)(hz₂ : ∀l,(s l).W₂ 0=0)
      (K Tsec : Label→ℝ)(ξ : ℝ)(hK : ∀l,0< K l),
      (∀l,Z^(-D₀)≤ K l) → (∀l,K l≤ Z^A) →
      (∀l,frequencyRadius (Tsec l) Z ξ≤ Cr*Z^L) → (∀l,sourceRadius (s l)≤ Z^B) →
    ∀(q : (l : Label)→ ActualSecondBlockIndex (s l) (R l) (seed l) (K l) (Tsec l) Z ξ)
      (χ : Label→ RayCharacter)(Q : Label→ Ideal O)(m : Label→ O),
      ((secondRatioBins (fun l=>(ordinarySecondDatum
        (actualSecondBlockDatum (slots l) (s l) (R l) (seed l)
          (hseed l) (hz₁ l) (hz₂ l) (K l) (Tsec l) Z ξ (hK l) (q l))
        (χ l) (Q l) (m l)).block)).card:ℝ)≤ C₀*Z^ε := by
  obtain ⟨C₀,hC₀,hcount⟩:=actual_second_datum_ratio_bins_subpower (α:=α)
    A D₀ B L Cr ε hA hD₀ hB hL hCr hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hcount] with Z hcount
  intro Label _ slots s R seed hseed hz₁ hz₂ K Tsec ξ hK hKlo hKhi hR hsource q χ Q m
  simpa only [ordinary_second_ratio_bins] using
    hcount slots s R seed hseed hz₁ hz₂ K Tsec ξ hK hKlo hKhi hR hsource q

/-- A genuine absolute dyadic envelope pays only the ratio-image overhead,
not the number of arithmetic source labels. Rows may already be restricted. -/
theorem actual_restricted_second_subpower (W : 𝓢(ℝ,ℂ))
    (decay degree windowDegree : ℕ)
    (hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (A D₀ B L Cr ε : ℝ)(hA : 0≤ A)(hD₀ : 0≤ D₀)(hB : 0≤ B)(hL : 0≤ L)
    (hCr : 0< Cr)(hε : 0<ε) :
    ∃C : ℝ,0≤ C ∧ ∀ᶠZ : ℝ in atTop,
    ∀{Label : Type*}[Fintype Label](d : Label→ SecondInputDatum α)
      (w : Label→ℂ)(sourceCap : Label→ℝ)(H : ℤ→ℝ)(E₀ : ℝ),0≤ E₀ →
      (∀l,Z^(-D₀)≤(d l).K) → (∀l,(d l).K≤ Z^A) →
      (∀l,(d l).radius≤ Cr*Z^L) → (∀l,sourceCap l≤ Z^B) →
      (∀l,((d l).C.absNorm:ℝ)≤ Z^B) → (∀l,((d l).D.absNorm:ℝ)≤ Z^B) →
    ∀n : (l : Label)→ SourceBlocks (d l).C (d l).D (d l).inactive
        (d l).K (d l).radius (sourceCap l),
      (∀l i,(d l).dyad i=(n l i:ℤ)) →
      (∀r∈secondRatioBins (fun l=>(d l).block),0< H r) →
      SecondNormalizedBound W degree windowDegree d w (fun _=>E₀) H →
      ‖∑l,w l*(d l).block.value W‖≤ C*E₀*Z^ε := by
  obtain ⟨C₁,hC₁,hcon⟩:=restricted_second_ratio_from_normalized (α:=α) W decay degree windowDegree hc hs
  obtain ⟨C₀,hC₀,hcount⟩:=actual_second_ratio_bins_subpower A D₀ B L Cr ε hA hD₀ hB hL hCr hε
  refine ⟨C₁*C₀,mul_nonneg hC₁ hC₀.le,?_⟩
  filter_upwards [hcount] with Z hcount
  intro Label _ d w sourceCap H E₀ hE hKlo hKhi hR hsource hNC hND n hdyad hH hnorm
  have hcard:=hcount (fun l=>(d l).block) (fun l=>(d l).C) (fun l=>(d l).D)
    (fun l=>(d l).hC) (fun l=>(d l).hD) (fun l=>(d l).sameSupport)
    (fun l=>(d l).inactive) (fun l=>(d l).K) (fun l=>(d l).radius) sourceCap
    (fun l=>(d l).K_pos) hKlo hKhi hR hsource hNC hND n hdyad
  have hh:=hcon d w (fun _=>E₀) H (fun _ _=>hE) hH hnorm
  have hsum : (∑r∈secondRatioBins (fun l=>(d l).block),E₀/(1+dyadicScale r)^decay)≤
      ((secondRatioBins (fun l=>(d l).block)).card:ℝ)*E₀ := by
    calc
      _ ≤ ∑r∈secondRatioBins (fun l=>(d l).block),E₀ := by
        apply Finset.sum_le_sum
        intro r hr
        exact div_le_self hE (one_le_pow₀ (by linarith [dyadicScale_pos r]))
      _ = _ := by simp
  have ht:=(hh.trans (mul_le_mul_of_nonneg_left hsum hC₁)).trans
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hE) hC₁)
  exact ht.trans_eq (by ring)

/-- Direct whole ordinary-energy bound from the actual normalized ratio
fibers. All fixed Mellin constants precede sources, allocations and heights. -/
theorem actual_joint_ordinary_from_normalized (W : 𝓢(ℝ,ℂ))
    (decay degree windowDegree : ℕ)
    (hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus) :
    ∃C : ℝ,0≤ C ∧ ∀{Label : Type*}[Fintype Label]
    (slots : Label→ Finset α) (s : (l : Label)→ Input (slots l))
    (R seed : Label→ Ideal O) (hseed : ∀l,Squarefree (seed l))
    (hz₁ : ∀l,(s l).W₁ 0=0) (hz₂ : ∀l,(s l).W₂ 0=0)
    (χ : Label→ RayCharacter)(Q : Label→ Ideal O)(m : Label→ O)
    (K Tsec : Label→ℝ) (Z ξ : ℝ) (hK : ∀l,0< K l)(weight : Label→ℂ),
      let datum := fun q : (l : Label) × ActualSecondBlockIndex (s l) (R l) (seed l)
        (K l) (Tsec l) Z ξ=>ordinarySecondDatum
          (actualSecondBlockDatum (slots q.1) (s q.1) (R q.1) (seed q.1)
            (hseed q.1) (hz₁ q.1) (hz₂ q.1) (K q.1) (Tsec q.1) Z ξ (hK q.1) q.2)
          (χ q.1) (Q q.1) (m q.1);
      let jointWeight := fun q : (l : Label) × ActualSecondBlockIndex (s l) (R l) (seed l)
        (K l) (Tsec l) Z ξ=>weight q.1*
          actualSecondBlockWeight (s q.1) (R q.1) (seed q.1) (K q.1) (Tsec q.1) Z ξ q.2;
      ∀E H : ℤ→ℝ,
      (∀r∈secondRatioBins (fun q=>(datum q).block),0≤ E r) →
      (∀r∈secondRatioBins (fun q=>(datum q).block),0< H r) →
      SecondNormalizedBound W degree windowDegree datum jointWeight E H →
      ‖∑l,weight l*partEnergy false (s l).η (χ l) (Q l) (m l) (s l).t
        (finiteColumns (Fintype.piFinset (s l).pools)) (coefficient (s l) (R l) (seed l))
        W (K l) (Tsec l) Z ξ (sourceRadius (s l))‖≤
          C*∑r∈secondRatioBins (fun q=>(datum q).block),E r/(1+dyadicScale r)^decay := by
  obtain ⟨C,hC,hcon⟩:=restricted_second_ratio_from_normalized (α:=α) W decay degree windowDegree hc hs
  refine ⟨C,hC,?_⟩
  intro Label _ slots s R seed hseed hz₁ hz₂ χ Q m K Tsec Z ξ hK weight
  dsimp only
  intro E H hE hH hnorm
  rw [actual_joint_ordinary_assembly slots s R seed hseed hz₁ hz₂ χ Q m W K Tsec Z ξ hK weight]
  exact hcon _ _ E H hE hH hnorm

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.ordinary_second_ratio
#print axioms OAI.SevenEighths.Cycle61InitialMass.restricted_second_ratio_from_normalized

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_joint_ordinary_assembly

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_restricted_second_subpower

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_joint_ordinary_from_normalized

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_ordinary_ratio_bins_subpower

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondRetainedContraction -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondLabelDisintegration; sha256 287bd179c68ab314dc69746ae54959170427ca39fe3427497c95c1fa96aaa50c -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                             
                                                   

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss Cycle61Moment
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondLiveBlock
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondLedger
open CenteredMomentFirstDiscardedEnergy CenteredMomentActive
open CenteredMomentSecondBlockAggregate CenteredMomentSecondPhysicalBlock
open CenteredMomentSectorLocalization CenteredMomentSecondDyadicPartition
open CenteredMomentDyadicCount CenteredMomentActiveSource CenteredMomentFirstSectors
open CenteredMomentSecondRetainedAggregate
local notation "O" => HeckeFamily.O
local instance secondLabelSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- The exact raw arithmetic label, before vanishing partitions are removed. -/
abbrev SecondArithmeticLabel := (CD : Ideal O×Ideal O)×Finset (CommonIndex CD.1 CD.2)

def actualSecondArithmeticLabel {ι : Type*}[Fintype ι](s : Input ι)
    (R seed : Ideal O)(K Tsec Z ξ : ℝ)
    (q : ActualSecondBlockIndex s R seed K Tsec Z ξ) : SecondArithmeticLabel :=
  ⟨q.1.val.val,q.2.1⟩

def actualSecondDyad {ι : Type*}[Fintype ι](s : Input ι)
    (R seed : Ideal O)(K Tsec Z ξ : ℝ)
    (q : ActualSecondBlockIndex s R seed K Tsec Z ξ) : Fin 4→ℤ := fun i=>(q.2.2 i:ℤ)

/-- All four dyads, together with the literal ideal pair and partition,
recover the actual retained block index without further multiplicity. -/
theorem actual_second_label_dyad_injective {ι : Type*}[Fintype ι](s : Input ι)
    (R seed : Ideal O)(K Tsec Z ξ : ℝ) :
    Function.Injective (fun q : ActualSecondBlockIndex s R seed K Tsec Z ξ=>
      (actualSecondArithmeticLabel s R seed K Tsec Z ξ q,actualSecondDyad s R seed K Tsec Z ξ q)) := by
  intro q v h
  apply actual_second_block_code_injective s R seed K Tsec Z ξ
  exact congrArg (fun x : SecondArithmeticLabel×(Fin 4→ℤ)=>
    (⟨x.1.1,x.1.2,x.2⟩ : SecondBlockCode)) h

/-- A literal canonical unit partition belongs to the genuine principal
inactive subset family used by the arithmetic scalar payments. -/
lemma canonical_partition_inactive (C D : Ideal O)(U : Finset (CommonIndex C D))(z : O)
    (h : canonicalPartition C D U z) : U∈inactiveSubsets C D := by
  rw [inactiveSubsets,Finset.mem_powerset]
  intro i hi
  rw [←h] at hi
  have he := (Finset.mem_filter.mp hi).2.1
  apply Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
  dsimp only [netExponent]
  omega

/-- Nonzero original physical blocks have valid arithmetic partitions.
This uses the original physical sum, independently of any ordinary filter. -/
theorem second_block_nonzero_inactive (d : SecondBlockSource)(W : 𝓢(ℝ,ℂ))
    (hn : d.value W≠0) : d.inactive∈inactiveSubsets d.C d.D := by
  by_contra hU
  apply hn
  unfold SecondBlockSource.value physicalBlock
  apply Finset.sum_eq_zero
  intro z hz
  simp only [show ¬canonicalPartition d.C d.D d.inactive _ from
    fun h=>hU (canonical_partition_inactive d.C d.D d.inactive _ h),ite_false]

def actualSecondSupportedLabel {ι : Type*}[Fintype ι](s : Input ι)
    (R seed : Ideal O)(K Tsec Z ξ : ℝ)
    (q : ActualSecondBlockIndex s R seed K Tsec Z ξ)
    (hU : q.2.1∈inactiveSubsets q.1.val.val.1 q.1.val.val.2) : FirstSourceLabel :=
  ⟨q.1.val.val,⟨q.2.1,hU⟩⟩

/-- An original-nonzero selected block subset has genuine supported labels.
The nonzero evidence refers to the unrestricted datum. -/
theorem actual_second_original_nonzero_supported {α : Type*}[Fintype α][DecidableEq α]
    (slots : Finset α)(s : Input slots)(R seed : Ideal O)(hseed : Squarefree seed)
    (hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)(K Tsec Z ξ : ℝ)(hK : 0< K)
    (W : 𝓢(ℝ,ℂ))(rows : Finset (ActualSecondBlockIndex s R seed K Tsec Z ξ))
    (hn : ∀q∈rows,(actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK q).block.value W≠0) :
    ∀q∈rows,q.2.1∈inactiveSubsets q.1.val.val.1 q.1.val.val.2 := by
  intro q hq
  have hh := second_block_nonzero_inactive
    (actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK q).block W (hn q hq)
  simpa only [actualSecondBlockDatum,actualSecondInputDatum,SecondInputDatum.block,originalSecondBlock] using hh

/-- Full supported arithmetic labels of the original live ideal pairs. -/
def actualSecondLabels {ι : Type*}[Fintype ι](s : Input ι)(R seed : Ideal O) :
    Finset FirstSourceLabel :=
  Finset.univ.image (fun q : (p : liveLabels s.η (finiteColumns (Fintype.piFinset s.pools))
    (coefficient s R seed))×↥(inactiveSubsets p.val.val.1 p.val.val.2)=>
      (⟨q.1.val.val,q.2⟩ : FirstSourceLabel))

lemma actual_second_supported_label_mem {ι : Type*}[Fintype ι](s : Input ι)
    (R seed : Ideal O)(K Tsec Z ξ : ℝ)
    (q : ActualSecondBlockIndex s R seed K Tsec Z ξ)
    (hU : q.2.1∈inactiveSubsets q.1.val.val.1 q.1.val.val.2) :
    actualSecondSupportedLabel s R seed K Tsec Z ξ q hU∈actualSecondLabels s R seed := by
  exact Finset.mem_image.mpr ⟨⟨q.1,⟨q.2.1,hU⟩⟩,Finset.mem_univ _,rfl⟩

/-- Arithmetic gates of every full supported label follow from the actual
source coefficients, including both seed divisibilities. -/
theorem actual_second_labels_gates {ι : Type*}[Fintype ι](s : Input ι)
    (R seed : Ideal O)(hseed : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (l : FirstSourceLabel)(hl : l∈actualSecondLabels s R seed) :
    Supported l.1.1 ∧ Supported l.1.2 ∧ primeSupport l.1.1=primeSupport l.1.2 ∧
    seed∣l.1.1 ∧ seed∣l.1.2 ∧
    (l.1.1.absNorm:ℝ)≤ sourceRadius s ∧ (l.1.2.absNorm:ℝ)≤ sourceRadius s := by
  obtain ⟨q,_,rfl⟩:=Finset.mem_image.mp hl
  have hg:=actual_common_gates s R seed hseed hz₁ hz₂ _ _ q.1.val.property
  have hs:=commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
    (coefficient s R seed)) _ _ q.1.val.property
  exact ⟨hs.1,hs.2,hg.2.2.1,hg.2.2.2.1,hg.2.2.2.2.1,hg.2.2.2.2.2⟩

/-- Exact subset image identity before enlargement to the full arithmetic
label set. Original block filters and ratio-fiber filters remain in `rows`. -/
theorem actual_second_label_dyad_image_sum {ι : Type*}[Fintype ι](s : Input ι)
    (R seed : Ideal O)(K Tsec Z ξ : ℝ)
    (rows : Finset (ActualSecondBlockIndex s R seed K Tsec Z ξ))
    (hU : ∀q∈rows,q.2.1∈inactiveSubsets q.1.val.val.1 q.1.val.val.2)
    (cost : FirstSourceLabel→(Fin 4→ℤ)→ℝ) :
    let code:=fun q : rows=>(actualSecondSupportedLabel s R seed K Tsec Z ξ q.val
      (hU q.val q.property),actualSecondDyad s R seed K Tsec Z ξ q.val);
    (∑q : rows,cost (code q).1 (code q).2)=∑x∈Finset.univ.image code,cost x.1 x.2 := by
  dsimp only
  rw [Finset.sum_image]
  intro q _ v _ h
  apply Subtype.ext
  apply actual_second_label_dyad_injective s R seed K Tsec Z ξ
  exact congrArg (fun x : FirstSourceLabel×(Fin 4→ℤ)=>
    ((⟨x.1.1,x.1.2.val⟩ : SecondArithmeticLabel),x.2)) h

/-- Exact positive-sum disintegration, retaining all four dyads. The cost
may contain the complete residual-projector and common-allocation sums. -/
theorem actual_second_positive_disintegration {ι : Type*}[Fintype ι](s : Input ι)
    (R seed : Ideal O)(K Tsec Z ξ : ℝ)
    (rows : Finset (ActualSecondBlockIndex s R seed K Tsec Z ξ))
    (hU : ∀q∈rows,q.2.1∈inactiveSubsets q.1.val.val.1 q.1.val.val.2)
    (box : Finset (Fin 4→ℤ))
    (hbox : ∀q∈rows,actualSecondDyad s R seed K Tsec Z ξ q∈box)
    (cost : FirstSourceLabel→(Fin 4→ℤ)→ℝ)
    (hcost : ∀l∈actualSecondLabels s R seed,∀n∈box,0≤ cost l n) :
    (∑q : rows,cost (actualSecondSupportedLabel s R seed K Tsec Z ξ q.val (hU q.val q.property))
      (actualSecondDyad s R seed K Tsec Z ξ q.val))≤
      ∑n∈box,∑l∈actualSecondLabels s R seed,cost l n := by
  let code := fun q : rows=>(actualSecondSupportedLabel s R seed K Tsec Z ξ q.val
    (hU q.val q.property),actualSecondDyad s R seed K Tsec Z ξ q.val)
  have hinj : Function.Injective code := by
    intro q v h
    apply Subtype.ext
    apply actual_second_label_dyad_injective s R seed K Tsec Z ξ
    exact congrArg (fun x : FirstSourceLabel×(Fin 4→ℤ)=>
      ((⟨x.1.1,x.1.2.val⟩ : SecondArithmeticLabel),x.2)) h
  have hsub : Finset.univ.image code⊆actualSecondLabels s R seed×ˢbox := by
    intro x hx
    obtain ⟨q,_,rfl⟩:=Finset.mem_image.mp hx
    exact Finset.mem_product.mpr ⟨actual_second_supported_label_mem s R seed K Tsec Z ξ
      q.val (hU q.val q.property),hbox q.val q.property⟩
  calc
    _=∑x∈Finset.univ.image code,cost x.1 x.2 := by
      rw [Finset.sum_image (fun _ _ _ _ h=>hinj h)]
    _≤∑x∈actualSecondLabels s R seed×ˢbox,cost x.1 x.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro x hx _
      exact hcost x.1 (Finset.mem_product.mp hx).1 x.2 (Finset.mem_product.mp hx).2
    _=_ := by rw [Finset.sum_product,Finset.sum_comm]

/-- The finite common absolute box retains every coordinate. -/
def secondAbsoluteBox (Z A D B L Cr : ℝ) : Finset (Fin 4→ℤ) :=
  Fintype.piFinset (fun i=>indices (![Z^(-(D+2*B)),1,1,1] i)
    (![Z^(A+2*B),max 1 (4*Cr)*Z^L,Z^B,Z^B] i))

lemma second_absolute_box_card (Z A D B L Cr : ℝ) :
    (secondAbsoluteBox Z A D B L Cr).card=Fintype.card (SecondAbsoluteEnvelope Z A D B L Cr) := by
  simp only [secondAbsoluteBox,Fintype.card_piFinset,SecondAbsoluteEnvelope,Fintype.card_pi,
    Fintype.card_coe]

/-- A subset of actual supported blocks pays the complete four-coordinate
box once. This applies verbatim to nonzero-block and exact ratio subsets. -/
theorem actual_second_positive_subpower {α : Type*}[Fintype α][DecidableEq α]
    (A D₀ B L Cr ε : ℝ)(hA : 0≤ A)(hD₀ : 0≤ D₀)(hB : 0≤ B)(hL : 0≤ L)
    (hCr : 0< Cr)(hε : 0<ε) :
    ∃C₀ : ℝ,0< C₀ ∧ ∀ᶠZ : ℝ in atTop,1≤ Z ∧
    ∀(slots : Finset α)(s : Input slots)(R seed : Ideal O)(_hseed : Squarefree seed)
      (_hz₁ : s.W₁ 0=0)(_hz₂ : s.W₂ 0=0)(K Tsec ξ : ℝ)(_hK : 0< K),
      Z^(-D₀)≤ K → K≤ Z^A → frequencyRadius Tsec Z ξ≤ Cr*Z^L → sourceRadius s≤ Z^B →
    ∀(rows : Finset (ActualSecondBlockIndex s R seed K Tsec Z ξ))
      (hU : ∀q∈rows,q.2.1∈inactiveSubsets q.1.val.val.1 q.1.val.val.2)
      (cost : FirstSourceLabel→ℝ),
      (∀l∈actualSecondLabels s R seed,0≤ cost l) →
      (∑q : rows,cost (actualSecondSupportedLabel s R seed K Tsec Z ξ q.val (hU q.val q.property)))≤
        C₀*Z^ε*(∑l∈actualSecondLabels s R seed,cost l) := by
  obtain ⟨C₀,hC₀,hcount⟩:=second_absolute_envelope_subpower A D₀ B L Cr ε hA hD₀ hB hL hCr hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hcount,eventually_ge_atTop (1:ℝ)] with Z hcount hZ
  refine ⟨hZ,?_⟩
  intro slots s R seed _hseed _hz₁ _hz₂ K Tsec ξ _hK hKlo hKhi hR hsource rows hU cost hcost
  let box:=secondAbsoluteBox Z A D₀ B L Cr
  have hbox (q : ActualSecondBlockIndex s R seed K Tsec Z ξ) :
      actualSecondDyad s R seed K Tsec Z ξ q∈box := by
    have hg:=actual_common_gates s R seed _hseed _hz₁ _hz₂ _ _ q.1.val.property
    have hs:=commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s R seed)) _ _ q.1.val.property
    apply Fintype.mem_piFinset.mpr
    intro i
    exact actual_second_dyads_absolute Z A D₀ B L Cr hZ hA hD₀ hB hL hCr
      _ _ hs.1 hs.2 hg.2.2.1 q.2.1 K (frequencyRadius Tsec Z ξ) (sourceRadius s)
      _hK hKlo hKhi hR hsource (hg.2.2.2.2.2.1.trans hsource)
      (hg.2.2.2.2.2.2.trans hsource) q.2.2 i
  have hh:=actual_second_positive_disintegration s R seed K Tsec Z ξ rows hU box
    (fun q _=>hbox q) (fun l _=>cost l) (fun l hl _ _=>hcost l hl)
  have hnonneg : 0≤∑l∈actualSecondLabels s R seed,cost l := Finset.sum_nonneg hcost
  have hcard : (box.card:ℝ)≤ C₀*Z^ε := by
    rw [show box.card=Fintype.card (SecondAbsoluteEnvelope Z A D₀ B L Cr) from
      second_absolute_box_card Z A D₀ B L Cr]
    exact hcount
  have heq : (∑_n∈box,∑l∈actualSecondLabels s R seed,cost l)=
      (box.card:ℝ)*(∑l∈actualSecondLabels s R seed,cost l) := by simp
  rw [heq] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right hcard hnonneg)

/-- Heterogeneous source identities and projector keys remain injective
when the exact second arithmetic label and all four dyads are retained. -/
theorem actual_second_joint_label_dyad_injective {α Label : Type*}
    [Fintype α][DecidableEq α]
    (slots : Label→ Finset α)(s : (l : Label)→ Input (slots l))
    (R seed : Label→ Ideal O)(K Tsec : Label→ℝ)(Z ξ : ℝ)
    (first : Label→ FirstSourceLabel)
    (hfirst : Function.Injective (fun l=>(first l,seed l))) :
    Function.Injective (fun q : (l : Label)×ActualSecondBlockIndex (s l) (R l) (seed l)
      (K l) (Tsec l) Z ξ=>
      (first q.1,seed q.1,actualSecondArithmeticLabel (s q.1) (R q.1) (seed q.1)
        (K q.1) (Tsec q.1) Z ξ q.2,
        actualSecondDyad (s q.1) (R q.1) (seed q.1) (K q.1) (Tsec q.1) Z ξ q.2)) := by
  intro q v h
  apply actual_second_joint_block_code_injective slots s R seed K Tsec Z ξ first hfirst
  exact congrArg (fun x : FirstSourceLabel×Ideal O×SecondArithmeticLabel×(Fin 4→ℤ)=>
    (x.1,x.2.1,(⟨x.2.2.1.1,x.2.2.1.2,x.2.2.2⟩ : SecondBlockCode))) h

/-- A heterogeneous selected block subset reindexes into its full supported
second labels and the same absolute dyadic box. First source identities are
retained; no ordinary block norm or arithmetic label cardinality is paid. -/
theorem actual_second_joint_positive_disintegration {α Label : Type*}
    [Fintype α][DecidableEq α][Fintype Label]
    (slots : Label→ Finset α)(s : (l : Label)→ Input (slots l))
    (R seed : Label→ Ideal O)(K Tsec : Label→ℝ)(Z ξ : ℝ)
    (rows : Finset ((l : Label)×ActualSecondBlockIndex (s l) (R l) (seed l)
      (K l) (Tsec l) Z ξ))
    (hU : ∀q∈rows,q.2.2.1∈inactiveSubsets q.2.1.val.val.1 q.2.1.val.val.2)
    (box : Finset (Fin 4→ℤ))
    (hbox : ∀q∈rows,actualSecondDyad (s q.1) (R q.1) (seed q.1)
      (K q.1) (Tsec q.1) Z ξ q.2∈box)
    (cost : Label→ FirstSourceLabel→(Fin 4→ℤ)→ℝ)
    (hcost : ∀l,∀v∈actualSecondLabels (s l) (R l) (seed l),∀n∈box,0≤ cost l v n) :
    (∑q : rows,cost q.val.1
      (actualSecondSupportedLabel (s q.val.1) (R q.val.1) (seed q.val.1)
        (K q.val.1) (Tsec q.val.1) Z ξ q.val.2 (hU q.val q.property))
      (actualSecondDyad (s q.val.1) (R q.val.1) (seed q.val.1)
        (K q.val.1) (Tsec q.val.1) Z ξ q.val.2))≤
      ∑n∈box,∑l,∑v∈actualSecondLabels (s l) (R l) (seed l),cost l v n := by
  let code := fun q : rows=>
    ((⟨q.val.1,actualSecondSupportedLabel (s q.val.1) (R q.val.1) (seed q.val.1)
      (K q.val.1) (Tsec q.val.1) Z ξ q.val.2 (hU q.val q.property)⟩ :
      (l : Label)×FirstSourceLabel),
      actualSecondDyad (s q.val.1) (R q.val.1) (seed q.val.1)
        (K q.val.1) (Tsec q.val.1) Z ξ q.val.2)
  have hinj : Function.Injective code := by
    rintro ⟨⟨l,q⟩,hq⟩ ⟨⟨m,v⟩,hv⟩ h
    have hl : l=m := congrArg (fun x=>x.1.1) h
    cases hl
    have hqv : q=v := actual_second_label_dyad_injective (s l) (R l) (seed l) (K l) (Tsec l) Z ξ
      (congrArg (fun x : ((l : Label)×FirstSourceLabel)×(Fin 4→ℤ)=>
        ((⟨x.1.2.1,x.1.2.2.val⟩ : SecondArithmeticLabel),x.2)) h)
    cases hqv
    rfl
  let labels := Finset.univ.sigma (fun l=>actualSecondLabels (s l) (R l) (seed l))
  have hsub : Finset.univ.image code⊆labels×ˢbox := by
    intro x hx
    obtain ⟨q,_,rfl⟩:=Finset.mem_image.mp hx
    exact Finset.mem_product.mpr ⟨Finset.mem_sigma.mpr ⟨Finset.mem_univ _,
      actual_second_supported_label_mem _ _ _ _ _ _ _ q.val.2 (hU q.val q.property)⟩,
      hbox q.val q.property⟩
  calc
    _=∑x∈Finset.univ.image code,cost x.1.1 x.1.2 x.2 := by
      rw [Finset.sum_image (fun _ _ _ _ h=>hinj h)]
    _≤∑x∈labels×ˢbox,cost x.1.1 x.1.2 x.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro x hx _
      obtain ⟨hl,hn⟩:=Finset.mem_product.mp hx
      exact hcost x.1.1 x.1.2 (Finset.mem_sigma.mp hl).2 x.2 hn
    _=_ := by
      rw [Finset.sum_product,Finset.sum_comm]
      simp only [labels,Finset.sum_sigma]

/-- The heterogeneous selected scalar family pays only the common absolute
four-dyad cardinality. The remaining sum is exactly the finite supported
arithmetic-label payment, including its first projector identity. -/
theorem actual_second_joint_positive_subpower {α : Type*}[Fintype α][DecidableEq α]
    (A D₀ B L Cr ε : ℝ)(hA : 0≤ A)(hD₀ : 0≤ D₀)(hB : 0≤ B)(hL : 0≤ L)
    (hCr : 0< Cr)(hε : 0<ε) :
    ∃C₀ : ℝ,0< C₀ ∧ ∀ᶠZ : ℝ in atTop,1≤ Z ∧
    ∀{Label : Type*}[Fintype Label]
      (slots : Label→ Finset α)(s : (l : Label)→ Input (slots l))
      (R seed : Label→ Ideal O)(_hseed : ∀l,Squarefree (seed l))
      (_hz₁ : ∀l,(s l).W₁ 0=0)(_hz₂ : ∀l,(s l).W₂ 0=0)
      (K Tsec : Label→ℝ)(ξ : ℝ)(_hK : ∀l,0< K l),
      (∀l,Z^(-D₀)≤ K l) → (∀l,K l≤ Z^A) →
      (∀l,frequencyRadius (Tsec l) Z ξ≤ Cr*Z^L) → (∀l,sourceRadius (s l)≤ Z^B) →
    ∀(rows : Finset ((l : Label)×ActualSecondBlockIndex (s l) (R l) (seed l)
      (K l) (Tsec l) Z ξ))
      (hU : ∀q∈rows,q.2.2.1∈inactiveSubsets q.2.1.val.val.1 q.2.1.val.val.2)
      (cost : Label→ FirstSourceLabel→ℝ),
      (∀l,∀v∈actualSecondLabels (s l) (R l) (seed l),0≤ cost l v) →
      (∑q : rows,cost q.val.1
        (actualSecondSupportedLabel (s q.val.1) (R q.val.1) (seed q.val.1)
          (K q.val.1) (Tsec q.val.1) Z ξ q.val.2 (hU q.val q.property)))≤
        C₀*Z^ε*(∑l,∑v∈actualSecondLabels (s l) (R l) (seed l),cost l v) := by
  obtain ⟨C₀,hC₀,hcount⟩:=second_absolute_envelope_subpower A D₀ B L Cr ε hA hD₀ hB hL hCr hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hcount,eventually_ge_atTop (1:ℝ)] with Z hcount hZ
  refine ⟨hZ,?_⟩
  intro Label _ slots s R seed _hseed _hz₁ _hz₂ K Tsec ξ _hK hKlo hKhi hR hsource rows hU cost hcost
  let box:=secondAbsoluteBox Z A D₀ B L Cr
  have hbox (q : (l : Label)×ActualSecondBlockIndex (s l) (R l) (seed l)
      (K l) (Tsec l) Z ξ) :
      actualSecondDyad (s q.1) (R q.1) (seed q.1) (K q.1) (Tsec q.1) Z ξ q.2∈box := by
    have hg:=actual_common_gates (s q.1) (R q.1) (seed q.1) (_hseed q.1) (_hz₁ q.1) (_hz₂ q.1)
      _ _ q.2.1.val.property
    have hs:=commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset (s q.1).pools))
      (coefficient (s q.1) (R q.1) (seed q.1))) _ _ q.2.1.val.property
    apply Fintype.mem_piFinset.mpr
    intro i
    exact actual_second_dyads_absolute Z A D₀ B L Cr hZ hA hD₀ hB hL hCr
      _ _ hs.1 hs.2 hg.2.2.1 q.2.2.1 (K q.1) (frequencyRadius (Tsec q.1) Z ξ) (sourceRadius (s q.1))
      (_hK q.1) (hKlo q.1) (hKhi q.1) (hR q.1) (hsource q.1)
      (hg.2.2.2.2.2.1.trans (hsource q.1)) (hg.2.2.2.2.2.2.trans (hsource q.1)) q.2.2.2 i
  have hh:=actual_second_joint_positive_disintegration slots s R seed K Tsec Z ξ rows hU box
    (fun q _=>hbox q) (fun l v _=>cost l v) (fun l v hv _ _=>hcost l v hv)
  have hn : 0≤∑l,∑v∈actualSecondLabels (s l) (R l) (seed l),cost l v := by
    apply Finset.sum_nonneg
    intro l _
    exact Finset.sum_nonneg (hcost l)
  have hcard : (box.card:ℝ)≤ C₀*Z^ε := by
    rw [show box.card=Fintype.card (SecondAbsoluteEnvelope Z A D₀ B L Cr) from
      second_absolute_box_card Z A D₀ B L Cr]
    exact hcount
  have heq : (∑_n∈box,∑l,∑v∈actualSecondLabels (s l) (R l) (seed l),cost l v)=
      (box.card:ℝ)*(∑l,∑v∈actualSecondLabels (s l) (R l) (seed l),cost l v) := by simp
  rw [heq] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right hcard hn)

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_label_dyad_injective
#print axioms OAI.SevenEighths.Cycle61InitialMass.second_block_nonzero_inactive
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_positive_disintegration

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_positive_subpower

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_labels_gates
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_joint_label_dyad_injective
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_joint_positive_disintegration

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_original_nonzero_supported

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_joint_positive_subpower

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_label_dyad_image_sum

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondLabelDisintegration -/
