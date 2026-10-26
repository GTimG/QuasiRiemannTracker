import Candidate.Target830.Parameters

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Target830.Source
noncomputable section

/-- A fixed, actually refined width partition, independent of moving
sources and of the ambient slot cardinality. -/
def widthCellIndex (s : ℝ) : ℤ :=
  max 0 (min 600000 (Int.ceil ((s-widthLower)/sourceWidthMesh)))

def widthCellUpper (s : ℝ) : ℝ :=
  widthLower+sourceWidthMesh*(widthCellIndex s:ℝ)

theorem widthCellIndex_bounds (s : ℝ) :
    0 ≤ widthCellIndex s ∧ widthCellIndex s ≤ 600000 := by
  unfold widthCellIndex
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem widthCellUpper_bounds {s : ℝ} (hs : s ∈ Set.Icc widthLower widthUpper) :
    widthCellUpper s ∈ Set.Icc widthLower widthUpper ∧
      s ≤ widthCellUpper s ∧ widthCellUpper s-s ≤ sourceWidthMesh := by
  have hm : (0:ℝ)<sourceWidthMesh := by norm_num [sourceWidthMesh]
  have hlo : 0 ≤ (s-widthLower)/sourceWidthMesh := div_nonneg (by linarith [hs.1]) hm.le
  have hhi : (s-widthLower)/sourceWidthMesh ≤ (600000:ℤ) := by
    apply (div_le_iff₀ hm).mpr
    norm_num [sourceWidthMesh,widthLower,widthUpper] at *
    linarith [hs.2]
  have hc0 : 0 ≤ Int.ceil ((s-widthLower)/sourceWidthMesh) := Int.ceil_nonneg hlo
  have hc1 : Int.ceil ((s-widthLower)/sourceWidthMesh) ≤ 600000 := Int.ceil_le.mpr hhi
  have he : widthCellIndex s=Int.ceil ((s-widthLower)/sourceWidthMesh) := by
    unfold widthCellIndex
    rw [min_eq_right hc1,max_eq_right hc0]
  have hb := Int.le_ceil ((s-widthLower)/sourceWidthMesh)
  have ht := Int.ceil_lt_add_one ((s-widthLower)/sourceWidthMesh)
  have hp := mul_le_mul_of_nonneg_left hb hm.le
  have hq := mul_lt_mul_of_pos_left ht hm
  have ci0 : (0:ℝ) ≤ (widthCellIndex s:ℝ) := by exact_mod_cast (widthCellIndex_bounds s).1
  have ci1 : (widthCellIndex s:ℝ) ≤ 600000 := by exact_mod_cast (widthCellIndex_bounds s).2
  have hlo' := mul_nonneg hm.le ci0
  have hhi' := mul_le_mul_of_nonneg_left ci1 hm.le
  rw [←he] at hp hq
  rw [mul_div_cancel₀ _ hm.ne'] at hp
  rw [mul_add,mul_div_cancel₀ _ hm.ne'] at hq
  unfold widthCellUpper
  norm_num [sourceWidthMesh,widthLower,widthUpper] at *
  constructor
  · constructor <;> linarith
  · constructor <;> linarith

def amplifierMinimum : ℝ := 185436487/36000000000

theorem low_payment_identity (P : SourcePlane) (b : ℝ) :
    P.amp b-P.q/(6*kappa0)*(P.gap b+6*P.amp b)=lowReserve := by
  cases P <;>
    norm_num [SourcePlane.amp,SourcePlane.gap,SourcePlane.q,SourcePlane.B,
      SourcePlane.lambda,kappa0,lowReserve] <;> ring

theorem source_guards (P : SourcePlane) {b : ℝ}
    (hb : b ∈ Set.Icc widthLower widthUpper) :
    0<P.gap b ∧ 0<amplifierMinimum ∧ amplifierMinimum≤P.amp b ∧
    P.amp b≤1/75 ∧ P.total b+9*P.amp b<1 ∧
    P.total b+4*P.amp b<49/50 ∧ P.total b+(9/2)*P.amp b<49/50 ∧
    0<P.supplied b ∧ P.supplied b≤1/25 ∧
    2*P.supplied b<P.frequency b ∧ P.frequency b<1 := by
  rcases hb with ⟨hlo,hhi⟩
  cases P <;>
    norm_num [SourcePlane.amp,SourcePlane.gap,SourcePlane.q,SourcePlane.B,
      SourcePlane.lambda,SourcePlane.total,SourcePlane.supplied,SourcePlane.frequency,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,
      frequencyAllowance,amplifierMinimum,widthLower,widthUpper] at *
  all_goals
    repeat' constructor
    all_goals linarith

theorem error_reserves (P : SourcePlane) {b : ℝ}
    (hb : b ∈ Set.Icc widthLower widthUpper) :
    errorReserve<P.amp b/4-P.gap b/6 ∧
    errorReserve<13*P.amp b/4-P.gap b/6 ∧
    errorReserve<4*P.amp b-P.gap b/6 := by
  rcases hb with ⟨hlo,hhi⟩
  cases P <;>
    norm_num [SourcePlane.amp,SourcePlane.gap,SourcePlane.q,SourcePlane.B,
      SourcePlane.lambda,kappa0,lowReserve,errorReserve,widthLower,widthUpper] at *
  all_goals
    repeat' constructor
    all_goals linarith

end
end OAI.SevenEighths.Target830.Source
#print axioms OAI.SevenEighths.Target830.Source.widthCellUpper_bounds
#print axioms OAI.SevenEighths.Target830.Source.low_payment_identity
#print axioms OAI.SevenEighths.Target830.Source.source_guards
#print axioms OAI.SevenEighths.Target830.Source.error_reserves
