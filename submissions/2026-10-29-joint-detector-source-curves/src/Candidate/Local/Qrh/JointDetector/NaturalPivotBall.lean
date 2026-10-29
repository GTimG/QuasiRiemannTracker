/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.NaturalSelectedNorm
import Candidate.Local.Qrh.JointDetector.SlotHistogram
import Candidate.Local.Qrh.JointDetector.NaturalScalarBudget

/-! The selected squarefree norm on a ball, rather than one annulus.
All actual nonrectangular fibres and ordinary source ideals are retained.
Dyadic partitioning costs a logarithm, absorbed with a fixed small power
before the later finite slot count is supplied. -/
namespace Qrh.JointDetector.NaturalPivotBall
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredExceptionalCount IdealMobiusDivisorSum CompletedGauss
local notation "O" => ActualEisensteinCubic.O

def normBin (B : ℝ) (z : O) : Fin (columnDyadicLength B+1) :=
  ⟨min (Nat.log 2 (Ideal.absNorm (Ideal.span {z}))) (columnDyadicLength B),
    Nat.lt_succ_of_le (min_le_right _ _)⟩

theorem log_norm_le_length (B : ℝ) (I : Ideal O)
    (hI : (Ideal.absNorm I:ℝ) ≤ B) :
    Nat.log 2 (Ideal.absNorm I) ≤ columnDyadicLength B := by
  have hceil : Ideal.absNorm I ≤ Nat.ceil B := by
    exact_mod_cast hI.trans (Nat.le_ceil B)
  have hpow : Nat.ceil B ≤ 2^columnDyadicLength B := by
    apply Nat.ceil_le.mpr
    exact_mod_cast columnDyadicLength_cover B
  have hlog := Nat.log_mono_right (b:=2) (hceil.trans hpow)
  simpa only [Nat.log_pow (by decide : 1 < 2)] using hlog

theorem normBin_generator (B : ℝ) (I : Ideal O) (hI : Admissible I)
    (hIB : (Ideal.absNorm I:ℝ) ≤ B) :
    (normBin B (primaryGenerator I)).val=Nat.log 2 (Ideal.absNorm I) := by
  simp only [normBin,(primaryGenerator_spec I (primaryGenerator_admissible I hI)).1]
  exact min_eq_left (log_norm_le_length B I hIB)

theorem finite_ball_norm {N : ℕ} (Z A P mesh Cslot wmin δ K : ℝ)
    (hbound : SquarefreeAllNormBound N Z A P mesh Cslot wmin δ (1-δ) K)
    (hK : 0 ≤ K) (hδ : δ ≤ 1)
    (d : SelectedSlotData N) (F S : Finset (Ideal O)) (B L : ℝ)
    (hb : d.Bounded Z mesh Cslot) (hs : d.Selects Z (F.image primaryGenerator))
    (hslope : d.HasSlope δ) (hw : wmin ≤ ∑ i, d.width i)
    (hF : ∀ I ∈ F, Admissible I)
    (hray : ∀ I ∈ F, ∀ J ∈ F,
      primaryGenerator I-primaryGenerator J ∈ (Ideal.span {(36:O)} : Ideal O))
    (hnorm : ∀ I ∈ F, (Ideal.absNorm I:ℝ) ≤ B)
    (hB : 1 ≤ B) (hBA : B ≤ Z^A) (hL : 1 ≤ L) (hLP : L ≤ Z^P)
    (hS : ∀ I ∈ S, (Ideal.absNorm I:ℝ) ≤ L) :
    selectedNorm (F.image primaryGenerator) S ≤
      (columnDyadicLength B+1:ℝ)*K*(L+B^(1-δ)*L^δ) := by
  have hL0 : 0 < L := by linarith
  have hB0 : 0 < B := by linarith
  have hnorms (k : Fin (columnDyadicLength B+1)) :
      selectedNorm ((F.filter fun I => Nat.log 2 (Ideal.absNorm I)=k.val).image primaryGenerator) S ≤
        K*(L+B^(1-δ)*L^δ) := by
    let Fk := F.filter fun I => Nat.log 2 (Ideal.absNorm I)=k.val
    change selectedNorm (Fk.image primaryGenerator) S ≤ _
    by_cases hempty : Fk=∅
    · simp only [hempty,Finset.image_empty,SlotHistogram.selectedNorm_empty_rows]
      positivity
    · obtain ⟨I,hI⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      have hknorm (J : Ideal O) (hJ : J ∈ Fk) :
          (Ideal.absNorm J:ℝ) ∈ Set.Icc ((2:ℝ)^k.val) (2*(2:ℝ)^k.val) := by
        have hj := Finset.mem_filter.mp hJ
        have hpos : 0 < Ideal.absNorm J := by exact_mod_cast norm_pos (hF J hj.1).1
        have hlo := Nat.pow_log_le_self 2 (Nat.ne_of_gt hpos)
        have hhi := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (Ideal.absNorm J)
        rw [hj.2] at hlo hhi
        constructor
        · exact_mod_cast hlo
        · have hh : (Ideal.absNorm J:ℝ) < (2:ℝ)^(k.val+1) := by exact_mod_cast hhi
          simpa only [pow_succ,mul_comm] using hh.le
      have hDB : (2:ℝ)^k.val ≤ B := (hknorm I hI).1.trans (hnorm I (Finset.mem_filter.mp hI).1)
      have hD : 1 ≤ (2:ℝ)^k.val := one_le_pow₀ (by norm_num)
      have hsf : SelectedSquarefreeFamily d Z mesh Cslot wmin δ ((2:ℝ)^k.val) Fk := by
        refine ⟨hb,?_,hslope,hw,?_,?_,hknorm⟩
        · intro z hz i
          exact hs z (Finset.image_subset_image (Finset.filter_subset _ _) hz) i
        · intro J hJ; exact hF J (Finset.mem_filter.mp hJ).1
        · intro J hJ Q hQ
          exact hray J (Finset.mem_filter.mp hJ).1 Q (Finset.mem_filter.mp hQ).1
      have hh := hbound d Fk S ((2:ℝ)^k.val) L hsf hD (hDB.trans hBA) hL hLP hS
      have hp := Real.rpow_le_rpow (by positivity : 0 ≤ (2:ℝ)^k.val) hDB
        (sub_nonneg.mpr hδ)
      exact hh.trans (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ L^δ))) hK)
  have hpartition := SlotHistogram.selectedNorm_rows_partition_le
    (F.image primaryGenerator) S (normBin B) (K*(L+B^(1-δ)*L^δ)) (by positivity)
  have hh := hpartition (fun k => by
    apply (selectedNorm_mono_rows (sources:=S) ?_).trans (hnorms k)
    intro z hz
    obtain ⟨hz,hbin⟩ := Finset.mem_filter.mp hz
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hz
    apply Finset.mem_image.mpr
    refine ⟨I,Finset.mem_filter.mpr ⟨hI,?_⟩,rfl⟩
    have hval := congrArg Fin.val hbin
    rw [normBin_generator B I (hF I hI) (hnorm I hI)] at hval
    exact hval)
  simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one,mul_assoc] using hh

/-- A residual pivot radius below one contains no nonzero ideal. -/
theorem selectedNorm_small_ball (F S : Finset (Ideal O)) (B : ℝ)
    (hF : ∀ I ∈ F, Admissible I) (hB : B < 1)
    (hnorm : ∀ I ∈ F, (Ideal.absNorm I:ℝ) ≤ B) :
    selectedNorm (F.image primaryGenerator) S=0 := by
  have hempty : F=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro I hI
    have hpos : 0 < Ideal.absNorm I := by exact_mod_cast norm_pos (hF I hI).1
    have hone : (1:ℝ) ≤ (Ideal.absNorm I:ℝ) := by exact_mod_cast hpos
    exact (not_lt_of_ge (hone.trans (hnorm I hI))) hB
  rw [hempty,Finset.image_empty,SlotHistogram.selectedNorm_empty_rows]

/-- Uniform selected squarefree ball norm. The original early-mesh order is
unchanged, and no source ideal is removed. -/
theorem squarefree_ball_selected_norm (A P gap loss : ℝ)
    (hA : 0 < A) (hP : 3*A+1 ≤ P) (hgap : 0 < gap) (hgaphalf : gap < 1/2)
    (hloss : 0 < loss) :
    ∃ mesh₀ : ℝ, 0 < mesh₀ ∧ ∀ (N : ℕ) (Cslot wmin : ℝ),
      0 ≤ Cslot → 0 < wmin → ∃ C Z₀ : ℝ, 0 < C ∧
      ∀ (Z mesh δ : ℝ), Z₀ ≤ Z → 0 ≤ mesh → mesh ≤ mesh₀ →
      1/2+gap ≤ δ → δ ≤ 3/4 →
      ∀ (d : SelectedSlotData N) (F S : Finset (Ideal O)) (B L : ℝ),
      d.Bounded Z mesh Cslot → d.Selects Z (F.image primaryGenerator) → d.HasSlope δ →
      wmin ≤ ∑ i, d.width i → (∀ I ∈ F, Admissible I) →
      (∀ I ∈ F, ∀ J ∈ F,
        primaryGenerator I-primaryGenerator J ∈ (Ideal.span {(36:O)} : Ideal O)) →
      (∀ I ∈ F, (Ideal.absNorm I:ℝ) ≤ B) →
      1 ≤ B → B ≤ Z^A → 1 ≤ L → L ≤ Z^P →
      (∀ I ∈ S, (Ideal.absNorm I:ℝ) ≤ L) →
      selectedNorm (F.image primaryGenerator) S ≤ C*Z^loss*(L+B^(1-δ)*L^δ) := by
  obtain ⟨mesh₀,hm,hbound⟩ := squarefree_selected_norm A P gap (loss/2)
    hA hP hgap hgaphalf (by positivity)
  refine ⟨mesh₀,hm,?_⟩
  intro N Cslot wmin hCslot hwmin
  obtain ⟨C,Z₀,hC,hbound⟩ := hbound N Cslot wmin hCslot hwmin
  let D : ℝ := 2+A/((loss/2)*Real.log 2)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D*C,max 1 Z₀,mul_pos hD hC,?_⟩
  intro Z mesh δ hZ hm0 hmm hδlo hδhi d F S B L hb hs hslope hw hF hray hnorm hB hBA hL hLP hS
  have hZ1 : 1 ≤ Z := (le_max_left _ _).trans hZ
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ1
  have hbound := hbound Z mesh δ ((le_max_right _ _).trans hZ) hm0 hmm hδlo hδhi
  have hh := finite_ball_norm Z A P mesh Cslot wmin δ (C*Z^(loss/2)) hbound
    (by positivity) (by linarith) d F S B L hb hs hslope hw hF hray hnorm hB hBA hL hLP hS
  have hmcard : (columnDyadicLength B+1:ℝ) ≤ D*Z^(loss/2) := by
    have hlog : columnDyadicLength B ≤ columnDyadicLength (Z^A) := by
      unfold columnDyadicLength
      apply Nat.ceil_mono
      apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num)).le
      exact Real.log_le_log (by linarith) hBA
    have hcard : (columnDyadicLength B+1:ℝ) ≤ (columnDyadicLength (Z^A)+1:ℝ) := by
      exact_mod_cast Nat.add_le_add_right hlog 1
    exact hcard.trans
      (NaturalScalarBudget.dyadic_shell_card_le Z A (loss/2) hZ1 hA (by positivity))
  calc
    _ ≤ (columnDyadicLength B+1:ℝ)*(C*Z^(loss/2))*(L+B^(1-δ)*L^δ) := hh
    _ ≤ (D*Z^(loss/2))*(C*Z^(loss/2))*(L+B^(1-δ)*L^δ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmcard (by positivity)) (by positivity)
    _ = D*C*Z^loss*(L+B^(1-δ)*L^δ) := by
      have hpow : Z^(loss/2)*Z^(loss/2)=Z^loss := by
        rw [← Real.rpow_add hZ0]
        congr 1
        ring
      calc
        _ = D*C*(Z^(loss/2)*Z^(loss/2))*(L+B^(1-δ)*L^δ) := by ring
        _ = _ := by rw [hpow]

end
end Qrh.JointDetector.NaturalPivotBall

#print axioms Qrh.JointDetector.NaturalPivotBall.squarefree_ball_selected_norm
