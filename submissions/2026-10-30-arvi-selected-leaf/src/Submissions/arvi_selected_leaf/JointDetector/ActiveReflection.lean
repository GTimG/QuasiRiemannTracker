/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.arvi_selected_leaf.JointDetector.UniformReflection

/-! Remove only genuinely empty input source sectors BEFORE taking reflected
maxima. This keeps the auxiliary source cap independent of contraction depth. -/
namespace Qrh.JointDetector
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic
open CanonicalRowCompletion CanonicalQuadraticSieve ConcreteTraceCRT CompletedGauss
open ConcretePrimeRowBridge IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

def activeInputKeys (L : ℝ) : Finset (Oˣ × ℕ × ℕ) :=
  (BadFrequencySectors.boundedKeys L).filter fun k => inputSectorScale k ≤ L

theorem selectedNorm_empty_sources (rows : Finset O) : selectedNorm rows ∅ = 0 := by
  apply le_antisymm _ (sq_nonneg _)
  apply selectedNorm_le_of_energy _ _ 0 le_rfl
  intro a
  simp [selectedDualEnergy]

theorem inputSectorSources_empty (S : Finset (Ideal O)) (L : ℝ)
    (hS : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ L) (k : Oˣ × ℕ × ℕ)
    (hk : ¬inputSectorScale k ≤ L) : selectedFrequencySources (inputFrequencies S) k = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro I hI
  have hn := inputSectorSources_norm_le S L hS k I hI
  have hs := selectedFrequencySources_supported (inputFrequencies S) k I hI
  have hone : (1 : ℝ) ≤ Ideal.absNorm I := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hs.1 (Ideal.absNorm_eq_zero_iff.mp h))
  have hh := (le_div_iff₀ (inputSectorScale_pos k)).mp (hone.trans hn)
  exact hk (by simpa only [one_mul] using hh)

theorem selectedNorm_active_input_sectors (rows : Finset O) (S : Finset (Ideal O)) (L : ℝ)
    (hS : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ L) :
    selectedNorm rows S ≤ ∑ k ∈ activeInputKeys L,
      selectedNorm rows (selectedFrequencySources (inputFrequencies S) k) := by
  apply (selectedNorm_input_sectors rows S L hS).trans_eq
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro k hk hnot
  have hn : ¬inputSectorScale k ≤ L := by
    intro h
    exact hnot (Finset.mem_filter.mpr ⟨hk,h⟩)
  rw [inputSectorSources_empty S L hS k hn,selectedNorm_empty_sources]

def activeReflectionValues (F : Finset (Ideal O)) (L B H : ℝ) : Finset ℝ :=
  insert 0 ((activeInputKeys L).biUnion fun k =>
    (gcdPool (fun I : F => I.val)).biUnion fun D =>
      (idealDivisors (commonMaskIdeal D)).image fun e =>
        simpleModeProfile (selectedQuotientRows F D) (L/inputSectorScale k)
          (B/(Ideal.absNorm D : ℝ)) H (idealGenerator e))

def activeReflectionProfile (F : Finset (Ideal O)) (L B H : ℝ) : ℝ :=
  (activeReflectionValues F L B H).sup' (Finset.insert_nonempty _ _) (fun x => x)

theorem activeReflectionProfile_nonneg (F : Finset (Ideal O)) (L B H : ℝ) :
    0 ≤ activeReflectionProfile F L B H := by
  unfold activeReflectionProfile activeReflectionValues
  exact Finset.le_sup' (fun x : ℝ => x) (Finset.mem_insert_self _ _)

theorem simpleModeProfile_le_active (F : Finset (Ideal O)) (L B H : ℝ)
    (k : Oˣ × ℕ × ℕ) (hk : k ∈ activeInputKeys L)
    (D : Ideal O) (hD : D ∈ gcdPool (fun I : F => I.val))
    (e : Ideal O) (he : e ∈ idealDivisors (commonMaskIdeal D)) :
    simpleModeProfile (selectedQuotientRows F D) (L/inputSectorScale k)
      (B/(Ideal.absNorm D : ℝ)) H (idealGenerator e) ≤ activeReflectionProfile F L B H := by
  unfold activeReflectionProfile
  apply Finset.le_sup' (fun x : ℝ => x)
  exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨k,hk,
    Finset.mem_biUnion.mpr ⟨D,hD,Finset.mem_image.mpr ⟨e,he,rfl⟩⟩⟩)

theorem activeReflectionProfile_le_of_modes (F : Finset (Ideal O)) (L B H K : ℝ)
    (hK : 0 ≤ K)
    (hbound : ∀ k ∈ activeInputKeys L,
      ∀ D ∈ gcdPool (fun I : F => I.val), ∀ e ∈ idealDivisors (commonMaskIdeal D),
      L/reflectedSourceRatio e k + (L*(Ideal.absNorm D : ℝ)/(B*reflectedSourceRatio e k)) *
        selectedNorm (selectedQuotientRows F D) (selectedFrequencyPool
          (reflectionFrequencies (reflectedFrequencyCutoff L B H D e k))
          (reflectedFrequencyCutoff L B H D e k)) ≤ K) :
    activeReflectionProfile F L B H ≤ K := by
  apply Finset.sup'_le
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact hK
  · obtain ⟨k,hk,hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨D,hD,hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hx
    rw [simpleModeProfile_eq_reflected]
    exact hbound k hk D hD e he

/-- Active input sectors give the crucial source cap. It is quadratic in
the ORIGINAL row radius, independent of the old source-length exponent. -/
theorem active_reflected_cutoff_le (L B H : ℝ) (hL : 0 < L) (hH : 0 ≤ H)
    (D : Ideal O) (hD : Admissible D) (e : Ideal O)
    (he : e ∈ idealDivisors (commonMaskIdeal D))
    (k : Oˣ × ℕ × ℕ) (hk : k ∈ activeInputKeys L) :
    reflectedFrequencyCutoff L B H D e k ≤
      4*(Ideal.absNorm reflectionBadIdeal : ℝ)*B^2*H/(Ideal.absNorm D : ℝ) := by
  have hdpos : 0 < (Ideal.absNorm D : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun h => hD.1 (Ideal.absNorm_eq_zero_iff.mp h))
  have hR : reflectedSourceRatio e k ≤ (Ideal.absNorm reflectionBadIdeal : ℝ)*(Ideal.absNorm D : ℝ)*L := by
    exact mul_le_mul (maskDivisor_norm_le D hD e he).2 (Finset.mem_filter.mp hk).2
      (inputSectorScale_pos k).le (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  calc
    _ ≤ 4*B^2*((Ideal.absNorm reflectionBadIdeal : ℝ)*(Ideal.absNorm D : ℝ)*L)/
        (L*(Ideal.absNorm D : ℝ)^2)*H := by
      unfold reflectedFrequencyCutoff
      gcongr
    _ = _ := by field_simp

/-- Uniform all-source reflection with only potentially occupied input
sectors. All other hypotheses are original ranges and arithmetic conditions. -/
theorem squarefree_active_uniform_reflection (P loss : ℝ) (hP : 0 ≤ P) (hloss : 0 < loss) :
    ∃ C Z₀ s : ℝ, 0 < C ∧ 0 < s ∧ s ≤ 1 ∧ s ≤ loss/3 ∧
      ∀ (Z L B : ℝ) (F S : Finset (Ideal O)),
      Z₀ ≤ Z → 1 ≤ L → L ≤ Z^P → 1 ≤ B → B ≤ Z^P →
      (∀ I ∈ F, Admissible I) →
      (∀ I ∈ F, ∀ J ∈ F, primaryGenerator I-primaryGenerator J ∈
        (Ideal.span {(36 : O)} : Ideal O)) →
      (∀ I ∈ F, (Ideal.absNorm I : ℝ) ∈ Set.Icc B (2*B)) →
      (∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ L) →
      selectedNorm (F.image primaryGenerator) S ≤ C*Z^loss*activeReflectionProfile F L B (Z^s) := by
  let Q := uniformReflectionScale P
  have hQ : 0 ≤ Q := by dsimp [Q,uniformReflectionScale]; positivity
  let η := loss/3
  have hη : 0 < η := by dsimp [η]; positivity
  let ε := η/(2*(Q+1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεid : ε*(2*(Q+1)) = η := by dsimp [ε]; field_simp
  have hεbudget : Q*ε ≤ η/2 := by nlinarith
  let s := min 1 η
  have hs : 0 < s := lt_min zero_lt_one hη
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsη : s ≤ η := min_le_right _ _
  obtain ⟨A,hAge⟩ := exists_nat_ge (8*Q/s)
  have hA : 8*Q ≤ s*(A : ℝ) := by simpa only [mul_comm] using (div_le_iff₀ hs).mp hAge
  obtain ⟨Cn,Ct,hCn,hCt,hreflection⟩ := squarefree_supported_reflection A
  obtain ⟨Cm,hCm,hmode⟩ := modeBudget_uniform QuadraticInitialBound.sieveCutoff Q η ε Cn Ct
    hQ hη hε hεbudget hCn hCt
  obtain ⟨Co,hCo,houter⟩ := sharedDivisorCost_uniform Q η ε hη hε (by nlinarith)
  obtain ⟨Ci,hCi,hinput⟩ := badSector_small_power P η hP hη
  let C := (1/6 : ℝ)*Co*Ci*Cm
  let Z₀ := max 4 (32*(Ideal.absNorm reflectionBadIdeal : ℝ))
  refine ⟨C,Z₀,s,by dsimp [C]; positivity,hs,hs1,hsη,?_⟩
  intro Z L B F S hZ₀ hL hLU hB hBU hF hmod hN hS
  have hZ : 4 ≤ Z := (le_max_left _ _).trans hZ₀
  have hbad : 32*(Ideal.absNorm reflectionBadIdeal : ℝ) ≤ Z := (le_max_right _ _).trans hZ₀
  have hz : 0 < Z := by linarith
  have hz1 : 1 ≤ Z := by linarith
  have hL0 : 0 < L := by linarith
  have hB0 : 0 < B := by linarith
  have h2BU : 2*B ≤ Z^Q := by
    calc
      _ ≤ Z*(Z^P) := mul_le_mul (by linarith : (2 : ℝ) ≤ Z) hBU hB0.le hz.le
      _ = Z^(P+1) := by rw [Real.rpow_add hz,Real.rpow_one]; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz1 (by dsimp [Q,uniformReflectionScale]; linarith)
  have hout := houter Z (2*B) hz1 (by positivity) h2BU
  have hin := hinput Z L hz1 hL0 hLU
  have hprofile0 := activeReflectionProfile_nonneg F L B (Z^s)
  have hSD0 : 0 ≤ sharedDivisorCost reflectionBadIdeal (2*B) ε hε := by
    unfold sharedDivisorCost
    exact mul_nonneg
      (mul_nonneg (idealDivisorConstant_pos ε hε).le (Real.rpow_nonneg (by positivity) ε))
      (mul_nonneg (idealDivisorConstant_pos ε hε).le
        (Real.rpow_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg _)) ε))
  have hsector (k : Oˣ × ℕ × ℕ) (hk : k ∈ activeInputKeys L) :
      selectedNorm (F.image primaryGenerator) (selectedFrequencySources (inputFrequencies S) k) ≤
        (1/6 : ℝ)*sharedDivisorCost reflectionBadIdeal (2*B) ε hε*
          (Cm*Z^η*activeReflectionProfile F L B (Z^s)) := by
    have hbudget : reflectionBudget F (L/inputSectorScale k) B (Z^s) Cn Ct ε hε A ≤
        Cm*Z^η*activeReflectionProfile F L B (Z^s) := by
      apply reflectionBudget_le_of_modes F _ B (Z^s) Cn Ct ε _ hε A (by positivity)
      intro D hD e he
      obtain ⟨hb,hl,hd,hbU,h2bU,hEl,hEu,hTu⟩ := reflection_polynomial_ranges F hF Z P L B s
        hZ hP hbad hL hLU hB hBU hs1 (fun I hI => (hN I hI).2) D hD e he k (Finset.mem_filter.mp hk).1
      have hDn := (selectedGcd_spec F hF (2*B) (fun I hI => (hN I hI).2) D hD).1.1
      have hm := hmode (selectedQuotientRows F D) Z (L/inputSectorScale k)
        (B/(Ideal.absNorm D : ℝ)) s (idealGenerator e) A (by linarith) hl hb hd
        hbU h2bU hEl hEu hTu (quotientRows_card_le F hF D hDn B hB0.le hN) hA
      exact hm.trans (mul_le_mul_of_nonneg_left (simpleModeProfile_le_active F L B (Z^s) k hk D hD e he)
        (by positivity))
    exact (hreflection F hF hmod (selectedFrequencySources (inputFrequencies S) k)
      (L/inputSectorScale k) B (Z^s) ε hε (div_pos hL0 (inputSectorScale_pos k)) hB0
      (Real.rpow_nonneg hz.le _) hN (selectedFrequencySources_supported (inputFrequencies S) k)
      (inputSectorSources_norm_le S L hS k)).trans (mul_le_mul_of_nonneg_left hbudget (by positivity))
  have hcard' : ((activeInputKeys L).card : ℝ) ≤ ((BadFrequencySectors.boundedKeys L).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset (fun k => inputSectorScale k ≤ L) (BadFrequencySectors.boundedKeys L))
  have hcard : ((activeInputKeys L).card : ℝ) ≤ Ci*Z^η := hcard'.trans hin
  calc
    _ ≤ ∑ k ∈ activeInputKeys L, selectedNorm (F.image primaryGenerator)
        (selectedFrequencySources (inputFrequencies S) k) := selectedNorm_active_input_sectors _ S L hS
    _ ≤ ∑ k ∈ activeInputKeys L, (1/6 : ℝ)*sharedDivisorCost reflectionBadIdeal (2*B) ε hε*
        (Cm*Z^η*activeReflectionProfile F L B (Z^s)) := Finset.sum_le_sum fun k hk => hsector k hk
    _ = (1/6 : ℝ)*sharedDivisorCost reflectionBadIdeal (2*B) ε hε *
        ((activeInputKeys L).card : ℝ)*(Cm*Z^η*activeReflectionProfile F L B (Z^s)) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ (1/6 : ℝ)*(Co*Z^η)*(Ci*Z^η)*(Cm*Z^η*activeReflectionProfile F L B (Z^s)) := by gcongr
    _ = C*(Z^η*Z^η*Z^η)*activeReflectionProfile F L B (Z^s) := by dsimp [C]; ring
    _ = _ := by rw [← Real.rpow_add hz, ← Real.rpow_add hz]; congr 2; dsimp [η]; ring

end
end Qrh.JointDetector

#print axioms Qrh.JointDetector.squarefree_active_uniform_reflection
#print axioms Qrh.JointDetector.active_reflected_cutoff_le
