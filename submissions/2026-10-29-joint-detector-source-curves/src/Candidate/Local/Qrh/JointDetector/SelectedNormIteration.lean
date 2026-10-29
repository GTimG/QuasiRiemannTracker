/- Copyright (c) 2026 Joseph Bebel. All rights reserved. -/
import Candidate.Local.Qrh.JointDetector.SelectedContraction
import Candidate.Local.Qrh.JointDetector.SlotWordProducer
import Candidate.Local.Qrh.JointDetector.UniformSlotAmplification

/-! The selected norm iteration uses literal slot data, all ordinary source
ideals, and their actual inherited quotient descriptors. The mesh is an
explicit early parameter; slot count and coefficient constants are late. -/
namespace Qrh.JointDetector
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic
open CanonicalRowCompletion CanonicalQuadraticSieve ConcreteTraceCRT CompletedGauss
open ConcretePrimeRowBridge IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

structure SelectedSquarefreeFamily {N : ℕ} (d : SelectedSlotData N)
    (Z mesh Cslot wmin δ B : ℝ) (F : Finset (Ideal O)) : Prop where
  bounded : d.Bounded Z mesh Cslot
  selected : d.Selects Z (F.image primaryGenerator)
  slope : d.HasSlope δ
  width : wmin ≤ ∑ i, d.width i
  admissible : ∀ I ∈ F, Admissible I
  ray : ∀ I ∈ F, ∀ J ∈ F, primaryGenerator I-primaryGenerator J ∈ (Ideal.span {(36 : O)} : Ideal O)
  rowNorm : ∀ I ∈ F, (Ideal.absNorm I : ℝ) ∈ Set.Icc B (2*B)

theorem SelectedSquarefreeFamily.quotient {N : ℕ} {d : SelectedSlotData N}
    {Z mesh Cslot wmin δ B : ℝ} {F : Finset (Ideal O)}
    (h : SelectedSquarefreeFamily d Z mesh Cslot wmin δ B F)
    (D : Ideal O) (hD : D ≠ 0) :
    SelectedSquarefreeFamily (d.quotient (primaryGenerator D)) Z mesh Cslot wmin δ
      (B/(Ideal.absNorm D : ℝ)) (descendantIdealFamily F D) := by
  refine ⟨SelectedSlotData.quotient_bounded h.bounded _,?_,
    SelectedSlotData.quotient_hasSlope h.slope _,h.width,
    descendantIdealFamily_admissible F h.admissible D,?_,?_⟩
  · rw [descendantIdealFamily_primary_rows F h.admissible D]
    exact selectedSlotData_quotient_selects d F D Z h.selected
  · intro I hI J hJ
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hI
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hJ
    rw [primaryGenerator_span z (selectedQuotientRows_spec F h.admissible D ⟨z,hz⟩).1
        (selectedQuotientRows_spec F h.admissible D ⟨z,hz⟩).2.1,
      primaryGenerator_span w (selectedQuotientRows_spec F h.admissible D ⟨w,hw⟩).1
        (selectedQuotientRows_spec F h.admissible D ⟨w,hw⟩).2.1]
    exact selectedQuotientRows_mod36 F h.admissible D h.ray ⟨z,hz⟩ ⟨w,hw⟩
  · intro I hI
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hI
    exact selectedQuotientRows_norm F h.admissible D hD B h.rowNorm ⟨z,hz⟩

def SquarefreeLongNormBound (N : ℕ) (Z A P mesh Cslot wmin δ c K : ℝ) : Prop :=
  ∀ (d : SelectedSlotData N) (F S : Finset (Ideal O)) (B L : ℝ),
    SelectedSquarefreeFamily d Z mesh Cslot wmin δ B F →
    1 ≤ B → B ≤ Z^A → B ≤ L → L ≤ Z^P →
    (∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ L) →
    selectedNorm (F.image primaryGenerator) S ≤ K*(L+B^c*L^(1-δ))

def SquarefreeAllNormBound (N : ℕ) (Z A P mesh Cslot wmin δ q K : ℝ) : Prop :=
  ∀ (d : SelectedSlotData N) (F S : Finset (Ideal O)) (B L : ℝ),
    SelectedSquarefreeFamily d Z mesh Cslot wmin δ B F →
    1 ≤ B → B ≤ Z^A → 1 ≤ L → L ≤ Z^P →
    (∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ L) →
    selectedNorm (F.image primaryGenerator) S ≤ K*(L+B^q*L^δ)

theorem initial_long_envelope_le (L B δ : ℝ) (hB : 0 < B) (hBL : B ≤ L) (hδ : δ ≤ 1) :
    L+B^2 ≤ L+B^(1+δ)*L^(1-δ) := by
  have hp := Real.rpow_le_rpow hB.le hBL (show 0 ≤ 1-δ by linarith)
  have hh := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hB.le (1+δ))
  have he : B^(1+δ)*B^(1-δ) = B^2 := by
    rw [← Real.rpow_add hB]
    convert Real.rpow_natCast B 2 using 1 <;> norm_num <;> ring
  rw [he] at hh
  exact add_le_add le_rfl hh

/-- Initial family bound, uniform in all literal slot data and their common
masks. The initial analytic estimate needs no selection hypothesis. -/
theorem squarefree_family_initial_long (A P loss : ℝ) (hAP : A ≤ P) (hP : 0 ≤ P) (hloss : 0 < loss) :
    ∃ C Z₀ : ℝ, 0 < C ∧ ∀ (N : ℕ) (Z mesh Cslot wmin δ : ℝ),
      Z₀ ≤ Z → δ ≤ 1 →
      SquarefreeLongNormBound N Z A P mesh Cslot wmin δ (1+δ) (C*Z^loss) := by
  obtain ⟨C,Z₀,hC,hbound⟩ := squarefree_selected_initial_bound P loss hP hloss
  refine ⟨C,max Z₀ 1,hC,?_⟩
  intro N Z mesh Cslot wmin δ hZ hδ d F S B L hf hB hBA hBL hLP hS
  have hz1 : 1 ≤ Z := (le_max_right _ _).trans hZ
  have hbP := hBA.trans (Real.rpow_le_rpow_of_exponent_le hz1 hAP)
  have hh := hbound Z L B F S ((le_max_left _ _).trans hZ) (hB.trans hBL) hLP hB hbP
    hf.admissible hf.ray hf.rowNorm hS
  exact hh.trans (mul_le_mul_of_nonneg_left (initial_long_envelope_le L B δ (by linarith) hBL hδ) (by positivity))

/-- The active reflected source length stays in ONE auxiliary polynomial
range throughout the iteration, independent of the old source-length cap. -/
theorem active_reflected_source_cap (Z A P L B s : ℝ) (D e : Ideal O) (k : Oˣ × ℕ × ℕ)
    (hZ : 1 ≤ Z) (hbad : 4*(Ideal.absNorm reflectionBadIdeal : ℝ) ≤ Z)
    (hL : 0 < L) (hBU : B ≤ Z^A) (hB : 0 ≤ B) (hs : s ≤ A)
    (hP : 3*A+1 ≤ P) (hD : Admissible D)
    (he : e ∈ idealDivisors (commonMaskIdeal D)) (hk : k ∈ activeInputKeys L) :
    reflectedFrequencyCutoff L B (Z^s) D e k ≤ Z^P := by
  have hz : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hDN : (1 : ℝ) ≤ Ideal.absNorm D := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hD.1 (Ideal.absNorm_eq_zero_iff.mp h))
  calc
    _ ≤ 4*(Ideal.absNorm reflectionBadIdeal : ℝ)*B^2*Z^s/(Ideal.absNorm D : ℝ) :=
      active_reflected_cutoff_le L B (Z^s) hL (Real.rpow_nonneg hz.le _) D hD e he k hk
    _ ≤ 4*(Ideal.absNorm reflectionBadIdeal : ℝ)*B^2*Z^s := div_le_self (by positivity) hDN
    _ ≤ Z*(Z^A)^2*Z^A := by
      apply mul_le_mul _ (Real.rpow_le_rpow_of_exponent_le hZ hs) (Real.rpow_nonneg hz.le _) (by positivity)
      exact mul_le_mul hbad (pow_le_pow_left₀ hB hBU 2) (sq_nonneg B) hz.le
    _ = Z^(3*A+1) := by
      rw [← Real.rpow_mul_natCast hz.le]
      conv_lhs => arg 1; arg 1; rw [← Real.rpow_one Z]
      rw [← Real.rpow_add hz, ← Real.rpow_add hz]
      congr 1
      norm_num
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ hP


theorem supportedSources_empty_below_one (S : Finset (Ideal O)) (Y : ℝ) (hY : Y < 1)
    (hS : ∀ I ∈ S, Supported I) (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Y) : S = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro I hI
  have hone : (1 : ℝ) ≤ Ideal.absNorm I := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => (hS I hI).1 (Ideal.absNorm_eq_zero_iff.mp h))
  linarith [hN I hI]

/-- A whole family reflection step. The previous all-source family bound
is applied only to inherited literal descriptors, and every reflected
source remains in the same fixed cap `P≥3A+1`. Tiny rows/sources are counted
directly. No reflection, selection-inheritance or tail premise is assumed. -/
theorem squarefree_family_all_to_long (A P loss : ℝ)
    (hA : 0 < A) (hP : 3*A+1 ≤ P) (hloss : 0 < loss) :
    ∃ C Z₀ : ℝ, 0 < C ∧ ∀ (N : ℕ) (Z mesh Cslot wmin δ q K : ℝ),
      Z₀ ≤ Z → 1/2 ≤ δ → δ ≤ 1 → 0 ≤ q → 32768 ≤ K →
      SquarefreeAllNormBound N Z A P mesh Cslot wmin δ q K →
      SquarefreeLongNormBound N Z A P mesh Cslot wmin δ (q+2*δ-1) (C*K*Z^loss) := by
  let η := min (loss/2) A
  have hη : 0 < η := lt_min (by positivity) hA
  have hηloss : η ≤ loss/2 := min_le_left _ _
  have hηA : η ≤ A := min_le_right _ _
  obtain ⟨C,Z₀,s,hC,hs,hs1,hsη,hreflection⟩ := squarefree_active_uniform_reflection P η (by linarith) hη
  refine ⟨5*C,max Z₀ (max 1 (4*(Ideal.absNorm reflectionBadIdeal : ℝ))),by positivity,?_⟩
  intro N Z mesh Cslot wmin δ q K hZ hδ hδ1 hq hK hall
  intro d F S B L hf hB hBU hBL hLP hS
  have hz1 : 1 ≤ Z := (le_max_left _ _).trans ((le_max_right _ _).trans hZ)
  have hbad : 4*(Ideal.absNorm reflectionBadIdeal : ℝ) ≤ Z :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hZ)
  have hz : 0 < Z := lt_of_lt_of_le zero_lt_one hz1
  have hL : 1 ≤ L := hB.trans hBL
  have hL0 : 0 < L := by linarith
  have hB0 : 0 < B := by linarith
  have hK0 : 0 < K := by linarith
  have hBA : B ≤ Z^P := hBU.trans (Real.rpow_le_rpow_of_exponent_le hz1 (by linarith))
  have hsA : s ≤ A := by linarith
  have hdesc : ∀ k ∈ activeInputKeys L,
      ∀ D ∈ gcdPool (fun I : F => I.val), ∀ e ∈ idealDivisors (commonMaskIdeal D),
      let Y := reflectedFrequencyCutoff L B (Z^s) D e k
      selectedNorm (selectedQuotientRows F D) (selectedFrequencyPool (reflectionFrequencies Y) Y) ≤
        K*(Y+(B/(Ideal.absNorm D : ℝ))^q*Y^δ) := by
    intro k hk D hD e he
    dsimp only
    let Y := reflectedFrequencyCutoff L B (Z^s) D e k
    let b := B/(Ideal.absNorm D : ℝ)
    let T := selectedFrequencyPool (reflectionFrequencies Y) Y
    have hd := selectedGcd_spec F hf.admissible (2*B) (fun I hI => (hf.rowNorm I hI).2) D hD
    have hDN : (1 : ℝ) ≤ Ideal.absNorm D := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hd.1.1 (Ideal.absNorm_eq_zero_iff.mp h))
    have hDN0 : 0 < (Ideal.absNorm D : ℝ) := by linarith
    have hb : 0 < b := div_pos hB0 hDN0
    have hR : 0 < reflectedSourceRatio e k := by
      have hr := (reflectedSourceRatio_range F hf.admissible L B hL
        (fun I hI => (hf.rowNorm I hI).2) D hD e he k (Finset.mem_filter.mp hk).1).1
      linarith
    have hY : 0 ≤ Y := by dsimp [Y,reflectedFrequencyCutoff]; positivity
    have hpool := reflectedFrequencyPool_spec L B (Z^s) D e k hY
    change selectedNorm (selectedQuotientRows F D) T ≤ K*(Y+b^q*Y^δ)
    by_cases hy1 : 1 ≤ Y
    · by_cases hb1 : 1 ≤ b
      · have hchild := hf.quotient D hd.1.1
        have hbU : b ≤ Z^A := (div_le_self hB0.le hDN).trans hBU
        have hYU : Y ≤ Z^P := active_reflected_source_cap Z A P L B s D e k hz1 hbad hL0 hBU hB0.le hsA hP hd.1 he hk
        have hh := hall (d.quotient (primaryGenerator D)) (descendantIdealFamily F D) T b Y
          hchild hb1 hbU hy1 hYU (fun I hI => (hpool I hI).2)
        rwa [descendantIdealFamily_primary_rows F hf.admissible D] at hh
      · have ht := quotient_selectedNorm_trivial F hf.admissible D hd.1.1 B Y hB0.le hY hf.rowNorm T
          (fun I hI => (hpool I hI).1) (fun I hI => (hpool I hI).2)
        have hlinear : 32768*b*Y ≤ K*Y := by
          apply mul_le_mul_of_nonneg_right _ hY
          calc
            32768*b ≤ 32768 := by linarith
            _ ≤ K := hK
        apply (ht.trans hlinear).trans
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hb.le _) (Real.rpow_nonneg hY _))) hK0.le
    · have ht : T = ∅ := supportedSources_empty_below_one T Y (lt_of_not_ge hy1)
        (fun I hI => (hpool I hI).1) (fun I hI => (hpool I hI).2)
      rw [ht,selectedNorm_empty_sources]
      positivity
  have hprofile := activeReflectionProfile_improve F hf.admissible L B (Z^s) K q δ hL hB0 hBL
    (Real.one_le_rpow hz1 hs.le) (by linarith) hq hδ hδ1 (fun I hI => (hf.rowNorm I hI).2) hdesc
  calc
    _ ≤ C*Z^η*activeReflectionProfile F L B (Z^s) :=
      hreflection Z L B F S ((le_max_left _ _).trans hZ) hL hLP hB hBA hf.admissible hf.ray hf.rowNorm hS
    _ ≤ C*Z^η*(5*K*Z^s*(L+B^(q+2*δ-1)*L^(1-δ))) := mul_le_mul_of_nonneg_left hprofile (by positivity)
    _ = (5*C)*K*Z^(η+s)*(L+B^(q+2*δ-1)*L^(1-δ)) := by rw [Real.rpow_add hz]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hz1 (by linarith)) (by positivity)


theorem row_crossing_range (Z A B c δ : ℝ) (hZ : 1 ≤ Z) (hA : 0 ≤ A)
    (hB : 1 ≤ B) (hBU : B ≤ Z^A) (hδ : 0 < δ) (hc : δ ≤ c) (hc3 : c ≤ 3*δ) :
    B ≤ B^(c/δ) ∧ B^(c/δ) ≤ Z^(3*A) := by
  have hz : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hb : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hc1 : 1 ≤ c/δ := (le_div_iff₀ hδ).mpr (by linarith)
  have hcU : c/δ ≤ 3 := (div_le_iff₀ hδ).mpr (by linarith)
  refine ⟨?_,?_⟩
  · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hB hc1
  · calc
      _ ≤ (Z^A)^(c/δ) := Real.rpow_le_rpow hb.le hBU (by linarith)
      _ = Z^(A*(c/δ)) := (Real.rpow_mul hz.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)

theorem crossing_log_target (Z A L B c δ : ℝ) (hZ : 1 < Z) (hA : 0 ≤ A)
    (hL : 1 ≤ L) (hB : 1 ≤ B) (hBU : B ≤ Z^A) (hδ : 0 < δ)
    (hc : δ ≤ c) (hc3 : c ≤ 3*δ) (hcross : L ≤ B^(c/δ)) :
    ∃ target : ℝ, 0 ≤ target ∧ target ≤ 3*A ∧ L*Z^target = B^(c/δ) := by
  have hz : 0 < Z := by linarith
  have hL0 : 0 < L := by linarith
  have hB0 : 0 < B := by linarith
  have hratio : 0 < B^(c/δ)/L := div_pos (Real.rpow_pos_of_pos hB0 _) hL0
  have hratio1 : 1 ≤ B^(c/δ)/L := (le_div_iff₀ hL0).mpr (by simpa using hcross)
  have hrU : B^(c/δ)/L ≤ Z^(3*A) :=
    (div_le_self (Real.rpow_nonneg hB0.le _) hL).trans (row_crossing_range Z A B c δ hZ.le hA hB hBU hδ hc hc3).2
  have hlog : 0 < Real.log Z := Real.log_pos hZ
  let target := Real.log (B^(c/δ)/L)/Real.log Z
  have ht : 0 ≤ target := div_nonneg (Real.log_nonneg hratio1) hlog.le
  have htU : target ≤ 3*A := by
    apply (div_le_iff₀ hlog).mpr
    have hh := Real.log_le_log hratio hrU
    simpa only [Real.log_rpow hz] using hh
  have hpow : Z^target = B^(c/δ)/L := by
    rw [Real.rpow_def_of_pos hz]
    dsimp [target]
    have he : Real.log Z*(Real.log (B^(c/δ)/L)/Real.log Z) = Real.log (B^(c/δ)/L) := by field_simp
    rw [he,Real.exp_log hratio]
  refine ⟨target,ht,htU,?_⟩
  rw [hpow]
  field_simp

/-- The actual literal slot word converts a long-source family envelope to
an all-source envelope. The mesh is chosen BEFORE `N`, and every merged
source remains below the fixed cap `P≥3A+1`. -/
theorem squarefree_family_long_to_all (A P loss : ℝ)
    (hA : 0 < A) (hP : 3*A+1 ≤ P) (hloss : 0 < loss) :
    ∃ mesh₀ : ℝ, 0 < mesh₀ ∧ ∀ (N : ℕ) (Cslot wmin : ℝ),
      0 ≤ Cslot → 0 < wmin → ∃ C Z₀ : ℝ, 0 < C ∧
      ∀ (Z mesh δ c K : ℝ), Z₀ ≤ Z → 0 ≤ mesh → mesh ≤ mesh₀ →
      1/2 ≤ δ → δ ≤ 1 → δ ≤ c → c ≤ 3*δ → 1 ≤ K →
      SquarefreeLongNormBound N Z A P mesh Cslot wmin δ c K →
      SquarefreeAllNormBound N Z A P mesh Cslot wmin δ (Contraction.ratio δ*c) (C*K*Z^loss) := by
  let ε := min (loss/8) (1/4)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hεloss : ε ≤ loss/8 := min_le_left _ _
  have hε1 : ε ≤ 1/4 := min_le_right _ _
  refine ⟨ε,hε,?_⟩
  intro N Cslot wmin hCslot hwmin
  obtain ⟨Ca,Z₀,hCa,hamp⟩ := uniform_slot_crossing P (3*A) ε (by linarith) (by positivity) hε N Cslot wmin hCslot hwmin
  let C := 2*(Ca+1)
  have hC : 0 < C := by dsimp [C]; positivity
  have hC2 : 2 ≤ C := by dsimp [C]; linarith
  refine ⟨C,max Z₀ 2,hC,?_⟩
  intro Z mesh δ c K hZ hm hmU hδ hδ1 hc hc3 hK hlong
  intro d F S B L hf hB hBU hL hLP hS
  have hz2 : 2 ≤ Z := (le_max_right _ _).trans hZ
  have hz1 : 1 ≤ Z := by linarith
  have hz : 0 < Z := by linarith
  have hB0 : 0 < B := by linarith
  have hL0 : 0 < L := by linarith
  have hK0 : 0 < K := by linarith
  have hd : 0 < δ := by linarith
  have hcrossrange := row_crossing_range Z A B c δ hz1 hA.le hB hBU hd hc hc3
  have hZloss : 1 ≤ Z^loss := Real.one_le_rpow hz1 hloss.le
  have hother : 0 ≤ B^(Contraction.ratio δ*c)*L^δ := by positivity
  by_cases hlarge : B^(c/δ) ≤ L
  · have hbound := hlong d F S B L hf hB hBU (hcrossrange.1.trans hlarge) hLP hS
    calc
      _ ≤ K*(L+B^c*L^(1-δ)) := hbound
      _ ≤ K*(2*L) := mul_le_mul_of_nonneg_left (long_envelope_above_crossing B L c δ hB0 hL0 hd hlarge) hK0.le
      _ ≤ (C*K*Z^loss)*L := by
        have hh : 2 ≤ C*Z^loss := hC2.trans (le_mul_of_one_le_right hC.le hZloss)
        have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh hK0.le) hL0.le
        nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hother) (by positivity)
  · obtain ⟨target,ht,htU,heq⟩ := crossing_log_target Z A L B c δ (by linarith) hA.le hL hB hBU hd hc hc3 (le_of_not_ge hlarge)
    obtain ⟨Y,merged,hYlo,hYhi,hmerged,hamplified⟩ := hamp Z L mesh δ target d (F.image primaryGenerator) S
      ((le_max_left _ _).trans hZ) hL hLP hm (by linarith) (by linarith) hδ1 ht htU hf.bounded hf.selected hf.slope hf.width hS
    have hYcross : B^(c/δ) ≤ Y := by rwa [heq] at hYlo
    have hY0 : 0 < Y := (Real.rpow_pos_of_pos hB0 _).trans_le hYcross
    have hYupper : Y ≤ Z^(mesh+ε)*B^(c/δ) := by
      apply hYhi.trans_eq
      rw [show target+mesh+ε = target+(mesh+ε) by ring,Real.rpow_add hz target (mesh+ε),← mul_assoc,heq]
      ring
    have hYP : Y ≤ Z^P := by
      calc
        _ ≤ Z^(mesh+ε)*Z^(3*A) := hYupper.trans (mul_le_mul_of_nonneg_left hcrossrange.2 (Real.rpow_nonneg hz.le _))
        _ = Z^(mesh+ε+3*A) := (Real.rpow_add hz _ _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz1 (by linarith)
    have htarget := hlong d F merged B Y hf hB hBU (hcrossrange.1.trans hYcross) hYP hmerged
    have hden : 0 < (Y/L)^δ := Real.rpow_pos_of_pos (div_pos hY0 hL0) _
    have hscalar := amplified_long_envelope_le Z L B Y c δ (mesh+ε) hz1 hL0 hB0 hY0 hd hδ1 (by positivity) hYcross hYupper
    calc
      _ ≤ Ca*Z^ε*selectedNorm (F.image primaryGenerator) merged/(Y/L)^δ := hamplified
      _ ≤ Ca*Z^ε*(K*(Y+B^c*Y^(1-δ)))/(Y/L)^δ :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htarget (by positivity)) hden.le
      _ = Ca*K*Z^ε*((Y+B^c*Y^(1-δ))/(Y/L)^δ) := by ring
      _ ≤ Ca*K*Z^ε*(2*Z^(mesh+ε)*B^(Contraction.ratio δ*c)*L^δ) :=
        mul_le_mul_of_nonneg_left hscalar (by positivity)
      _ = (2*Ca)*K*Z^(ε+(mesh+ε))*(B^(Contraction.ratio δ*c)*L^δ) := by rw [Real.rpow_add hz ε (mesh+ε)]; ring
      _ ≤ C*K*Z^loss*(B^(Contraction.ratio δ*c)*L^δ) := by
        apply mul_le_mul_of_nonneg_right _ hother
        apply mul_le_mul (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith : 2*Ca ≤ C) hK0.le)
          (Real.rpow_le_rpow_of_exponent_le hz1 (by linarith)) (Real.rpow_nonneg hz.le _) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hL0.le) (by positivity)


theorem SquarefreeLongNormBound.mono {N : ℕ} {Z A P mesh Cslot wmin δ c K K' : ℝ}
    (h : SquarefreeLongNormBound N Z A P mesh Cslot wmin δ c K) (hKK : K ≤ K') :
    SquarefreeLongNormBound N Z A P mesh Cslot wmin δ c K' := by
  intro d F S B L hf hB hBU hBL hLP hS
  apply (h d F S B L hf hB hBU hBL hLP hS).trans
  exact mul_le_mul_of_nonneg_right hKK (by have hL := hB.trans hBL; positivity)

theorem SquarefreeAllNormBound.mono {N : ℕ} {Z A P mesh Cslot wmin δ q K K' : ℝ}
    (h : SquarefreeAllNormBound N Z A P mesh Cslot wmin δ q K) (hKK : K ≤ K') :
    SquarefreeAllNormBound N Z A P mesh Cslot wmin δ q K' := by
  intro d F S B L hf hB hBU hL hLP hS
  apply (h d F S B L hf hB hBU hL hLP hS).trans
  exact mul_le_mul_of_nonneg_right hKK (by positivity)

/-- Every finite contraction stage is an actual selected norm bound. The
mesh is fixed before the slot count and all common coefficient data. The
same stage works for every slope in the entire interval `(1/2,1]`. -/
theorem squarefree_family_iterated_long (A P : ℝ) (hA : 0 < A) (hP : 3*A+1 ≤ P)
    (n : ℕ) (loss : ℝ) (hloss : 0 < loss) :
    ∃ mesh₀ : ℝ, 0 < mesh₀ ∧ ∀ (N : ℕ) (Cslot wmin : ℝ),
      0 ≤ Cslot → 0 < wmin → ∃ C Z₀ : ℝ, 32768 ≤ C ∧
      ∀ (Z mesh δ : ℝ), Z₀ ≤ Z → 0 ≤ mesh → mesh ≤ mesh₀ → 1/2 < δ → δ ≤ 1 →
      SquarefreeLongNormBound N Z A P mesh Cslot wmin δ (Contraction.exponent δ n) (C*Z^loss) := by
  induction n generalizing loss with
  | zero =>
    obtain ⟨C,Z₀,hC,hinitial⟩ := squarefree_family_initial_long A P loss (by linarith) (by linarith) hloss
    refine ⟨1,by norm_num,?_⟩
    intro N Cslot wmin hCslot hwmin
    refine ⟨max 32768 C,max Z₀ 1,le_max_left _ _,?_⟩
    intro Z mesh δ hZ hm hmU hδ hδ1
    have hh := hinitial N Z mesh Cslot wmin δ ((le_max_left _ _).trans hZ) hδ1
    change SquarefreeLongNormBound N Z A P mesh Cslot wmin δ (1+δ) _
    exact hh.mono (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by linarith [((le_max_right Z₀ 1).trans hZ)]) _))
  | succ n ih =>
    let ε := loss/3
    have hε : 0 < ε := by dsimp [ε]; positivity
    obtain ⟨mp,hmp,hprevious⟩ := ih ε hε
    obtain ⟨ma,hma,hamplification⟩ := squarefree_family_long_to_all A P ε hA hP hε
    obtain ⟨Cr,Zr,hCr,hreflection⟩ := squarefree_family_all_to_long A P ε hA hP hε
    refine ⟨min mp ma,lt_min hmp hma,?_⟩
    intro N Cslot wmin hCslot hwmin
    obtain ⟨Cp,Zp,hCp,hprevious⟩ := hprevious N Cslot wmin hCslot hwmin
    obtain ⟨Ca,Za,hCa,hamplification⟩ := hamplification N Cslot wmin hCslot hwmin
    let Cm := max 32768 (Ca*Cp)
    let C := max 32768 (Cr*Cm)
    let Z₀ := max 1 (max Zp (max Za Zr))
    refine ⟨C,Z₀,le_max_left _ _,?_⟩
    intro Z mesh δ hZ hm hmU hδ hδ1
    have hz1 : 1 ≤ Z := (le_max_left _ _).trans hZ
    have hz : 0 < Z := lt_of_lt_of_le zero_lt_one hz1
    have hZp : Zp ≤ Z := (le_max_left _ _).trans ((le_max_right _ _).trans hZ)
    have hZa : Za ≤ Z := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hZ))
    have hZr : Zr ≤ Z := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hZ))
    have hCp0 : 0 < Cp := by linarith
    have hCm : 32768 ≤ Cm := le_max_left _ _
    have hCm0 : 0 < Cm := by linarith
    have hp := hprevious Z mesh δ hZp hm (hmU.trans (min_le_left _ _)) hδ hδ1
    have hc := contraction_exponent_range δ n hδ hδ1
    have hKp : 32768 ≤ Cp*Z^ε := hCp.trans (le_mul_of_one_le_right hCp0.le (Real.one_le_rpow hz1 hε.le))
    have ha := hamplification Z mesh δ (Contraction.exponent δ n) (Cp*Z^ε)
      hZa hm (hmU.trans (min_le_right _ _)) hδ.le hδ1 hc.1
      ((div_le_iff₀ (show 0 < δ by linarith)).mp hc.2.2) (by linarith) hp
    have hcostA : Ca*(Cp*Z^ε)*Z^ε ≤ Cm*Z^(2*ε) := by
      calc
        _ = (Ca*Cp)*Z^(ε+ε) := by rw [Real.rpow_add hz]; ring
        _ ≤ Cm*Z^(ε+ε) := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hz.le _)
        _ = _ := by congr 1; congr 1; ring
    have ha' := ha.mono hcostA
    have hKm : 32768 ≤ Cm*Z^(2*ε) := hCm.trans
      (le_mul_of_one_le_right hCm0.le (Real.one_le_rpow hz1 (by positivity)))
    have hq : 0 ≤ Contraction.ratio δ*Contraction.exponent δ n :=
      mul_nonneg (Contraction.ratio_nonneg (by linarith) hδ1) ((by linarith : 0 ≤ δ).trans hc.1)
    have hr := hreflection N Z mesh Cslot wmin δ (Contraction.ratio δ*Contraction.exponent δ n)
      (Cm*Z^(2*ε)) hZr hδ.le hδ1 hq hKm ha'
    have hexp : Contraction.ratio δ*Contraction.exponent δ n+2*δ-1 = Contraction.exponent δ (n+1) := by
      rw [Contraction.exponent]
      ring
    rw [hexp] at hr
    apply hr.mono
    calc
      _ = (Cr*Cm)*Z^(2*ε+ε) := by rw [Real.rpow_add hz]; ring
      _ ≤ C*Z^(2*ε+ε) := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hz.le _)
      _ = _ := by congr 1; congr 1; dsimp [ε]; ring


/-- CLOSED squarefree selected all-source norm. For any fixed polynomial
row/source ranges and slope interval above one half, choose the mesh before
the number of slots. Every later bounded common coefficient array, including
growing gcd/root masks, is uniform in the resulting constant. Ordinary source
ideals, the unit, natural zeros and arbitrary dual vectors are all retained.
This is the full sextic squarefree operator; it is not a natural-row claim for
powers2,3,4. -/
theorem squarefree_selected_norm (A P gap loss : ℝ)
    (hA : 0 < A) (hP : 3*A+1 ≤ P) (hgap : 0 < gap) (hgaphalf : gap < 1/2)
    (hloss : 0 < loss) :
    ∃ mesh₀ : ℝ, 0 < mesh₀ ∧ ∀ (N : ℕ) (Cslot wmin : ℝ),
      0 ≤ Cslot → 0 < wmin → ∃ C Z₀ : ℝ, 0 < C ∧
      ∀ (Z mesh δ : ℝ), Z₀ ≤ Z → 0 ≤ mesh → mesh ≤ mesh₀ →
      1/2+gap ≤ δ → δ ≤ 3/4 →
      SquarefreeAllNormBound N Z A P mesh Cslot wmin δ (1-δ) (C*Z^loss) := by
  let ε := loss/4
  have hε : 0 < ε := by dsimp [ε]; positivity
  let reserve := loss/(4*(A+1))
  have hreserve : 0 < reserve := by dsimp [reserve]; positivity
  have hresid : reserve*(4*(A+1)) = loss := by dsimp [reserve]; field_simp
  have hresbudget : A*reserve ≤ ε := by dsimp [ε]; nlinarith
  obtain ⟨n,hn⟩ := Contraction.uniform_depth hgap hgaphalf hreserve
  obtain ⟨mp,hmp,hprevious⟩ := squarefree_family_iterated_long A P hA hP n ε hε
  obtain ⟨ma,hma,hamplification⟩ := squarefree_family_long_to_all A P ε hA hP hε
  refine ⟨min mp ma,lt_min hmp hma,?_⟩
  intro N Cslot wmin hCslot hwmin
  obtain ⟨Cp,Zp,hCp,hprevious⟩ := hprevious N Cslot wmin hCslot hwmin
  obtain ⟨Ca,Za,hCa,hamplification⟩ := hamplification N Cslot wmin hCslot hwmin
  have hCp0 : 0 < Cp := by linarith
  refine ⟨Ca*Cp,max 1 (max Zp Za),mul_pos hCa hCp0,?_⟩
  intro Z mesh δ hZ hm hmU hδ hδhi
  have hz1 : 1 ≤ Z := (le_max_left _ _).trans hZ
  have hz : 0 < Z := lt_of_lt_of_le zero_lt_one hz1
  have hZp : Zp ≤ Z := (le_max_left _ _).trans ((le_max_right _ _).trans hZ)
  have hZa : Za ≤ Z := (le_max_right _ _).trans ((le_max_right _ _).trans hZ)
  have hdhalf : 1/2 < δ := by linarith
  have hd : 0 < δ := by linarith
  have hd1 : δ ≤ 1 := by linarith
  have hc := contraction_exponent_range δ n hdhalf hd1
  have hprevious := hprevious Z mesh δ hZp hm (hmU.trans (min_le_left _ _)) hdhalf hd1
  have hKp : 1 ≤ Cp*Z^ε := (by linarith : 1 ≤ Cp).trans
    (le_mul_of_one_le_right hCp0.le (Real.one_le_rpow hz1 hε.le))
  have hall := hamplification Z mesh δ (Contraction.exponent δ n) (Cp*Z^ε)
    hZa hm (hmU.trans (min_le_right _ _)) hdhalf.le hd1 hc.1
    ((div_le_iff₀ hd).mp hc.2.2) hKp hprevious
  have hρ0 := Contraction.ratio_nonneg hd hd1
  have hρ1 := (Contraction.ratio_lt_one hdhalf).le
  have hρδ : Contraction.ratio δ*δ = 1-δ := div_mul_cancel₀ _ hd.ne'
  have hq : Contraction.ratio δ*Contraction.exponent δ n ≤ 1-δ+reserve := by
    calc
      _ = (1-δ)+Contraction.ratio δ*(Contraction.exponent δ n-δ) := by rw [← hρδ]; ring
      _ ≤ (1-δ)+1*reserve := add_le_add le_rfl
        (mul_le_mul hρ1 (by linarith [hn δ hδ hδhi]) (sub_nonneg.mpr hc.1) zero_le_one)
      _ = _ := by ring
  intro d F S B L hf hB hBU hL hLP hS
  have hB0 : 0 < B := by linarith
  have hL0 : 0 < L := by linarith
  have hBr : B^reserve ≤ Z^ε := by
    calc
      _ ≤ (Z^A)^reserve := Real.rpow_le_rpow hB0.le hBU hreserve.le
      _ = Z^(A*reserve) := (Real.rpow_mul hz.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz1 hresbudget
  have hBq : B^(Contraction.ratio δ*Contraction.exponent δ n) ≤ Z^ε*B^(1-δ) := by
    calc
      _ ≤ B^(1-δ+reserve) := Real.rpow_le_rpow_of_exponent_le hB hq
      _ = B^(1-δ)*B^reserve := Real.rpow_add hB0 _ _
      _ ≤ B^(1-δ)*Z^ε := mul_le_mul_of_nonneg_left hBr (Real.rpow_nonneg hB0.le _)
      _ = _ := by ring
  have hEnvelope : L+B^(Contraction.ratio δ*Contraction.exponent δ n)*L^δ ≤
      Z^ε*(L+B^(1-δ)*L^δ) := by
    have hlinear : L ≤ Z^ε*L := le_mul_of_one_le_left hL0.le (Real.one_le_rpow hz1 hε.le)
    have hpower := mul_le_mul_of_nonneg_right hBq (Real.rpow_nonneg hL0.le δ)
    nlinarith
  calc
    _ ≤ (Ca*(Cp*Z^ε)*Z^ε)*(L+B^(Contraction.ratio δ*Contraction.exponent δ n)*L^δ) :=
      hall d F S B L hf hB hBU hL hLP hS
    _ ≤ (Ca*(Cp*Z^ε)*Z^ε)*(Z^ε*(L+B^(1-δ)*L^δ)) :=
      mul_le_mul_of_nonneg_left hEnvelope (by positivity)
    _ = (Ca*Cp)*Z^(ε+ε+ε)*(L+B^(1-δ)*L^δ) := by
      rw [Real.rpow_add hz (ε+ε) ε,Real.rpow_add hz ε ε]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hz1 (by dsimp [ε]; linarith)) (mul_pos hCa hCp0).le

end
end Qrh.JointDetector

#print axioms Qrh.JointDetector.squarefree_family_all_to_long
#print axioms Qrh.JointDetector.squarefree_family_long_to_all
#print axioms Qrh.JointDetector.squarefree_family_iterated_long
#print axioms Qrh.JointDetector.squarefree_selected_norm
