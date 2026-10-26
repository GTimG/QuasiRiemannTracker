/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact full volume and separate corners after two common and one forced allocation. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedHighCoordinatesScalar
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedForcedGeometryCaps
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedHighCoordinates
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAddedZeroUniform CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildSourceCaps
local notation "O"=>HeckeFamily.O
variable {ι:Type*} [Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _
variable (s:Input ι) (C₁ R:Ideal O) (B₁:actualAllocations s.pools C₁) (τ₁:Character) (t₁:ℝ)
    (C₂:Ideal O) (B₂:actualAllocations (child s C₁ R B₁ τ₁ t₁).pools C₂) (τ₂:Character) (t₂:ℝ)
    (C₃:Ideal O) (B₃:actualAllocations (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂).pools C₃)
    (τ₃:Character) (t₃:ℝ)

/-- No marked-slot factor is dropped: the numerator is the full original
X1*X2*product P, and the three denominators are the actual raw reductions. -/
theorem three_volume_exact :
    volume (child (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂) C₃ ((R*C₁)*C₂) B₃ τ₃ t₃)=
      (s.X₁*s.X₂*∏i,s.P i)/
        (rawReduction B₁.val s.P*
          rawReduction B₂.val (child s C₁ R B₁ τ₁ t₁).P*
          rawReduction B₃.val (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂).P) := by
  rw [common_volume,common_volume,common_volume,div_div,div_div]
  simp only [volume,mul_assoc]

/-- Exact uniform annular constant for three nonzero frozen allocations.
The last allocation may be the selected complete forced part. -/
theorem three_volume_bound (N:ℕ) (b:ℝ) (hb:1≤b) (hN:Fintype.card ι≤N) (hu:s.upper≤b)
    (hf₁:frozenCoefficient B₁.val C₁ R s.ν s.W s.P≠0)
    (hf₂:frozenCoefficient B₂.val C₂ (R*C₁)
      (child s C₁ R B₁ τ₁ t₁).ν (child s C₁ R B₁ τ₁ t₁).W (child s C₁ R B₁ τ₁ t₁).P≠0)
    (hf₃:frozenCoefficient B₃.val C₃ ((R*C₁)*C₂)
      (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂).ν
      (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂).W
      (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂).P≠0) :
    volume (child (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂) C₃ ((R*C₁)*C₂) B₃ τ₃ t₃)≤
      b^(3*N)*volume s/((C₁.absNorm:ℝ)*(C₂.absNorm:ℝ)*(C₃.absNorm:ℝ)) := by
  let s₁:=child s C₁ R B₁ τ₁ t₁
  let s₂:=child s₁ C₂ (R*C₁) B₂ τ₂ t₂
  have hN₁:Fintype.card (liveIndices B₁.val)≤N:=(live_card_le B₁.val).trans hN
  have hN₂:Fintype.card (liveIndices B₂.val)≤N:=(live_card_le B₂.val).trans hN₁
  have h₁:=common_volume_le N b hb s hN hu C₁ R B₁ τ₁ t₁ hf₁
  have h₂:=common_volume_le N b hb s₁ hN₁ hu C₂ (R*C₁) B₂ τ₂ t₂ hf₂
  have h₃:=common_volume_le N b hb s₂ hN₂ hu C₃ ((R*C₁)*C₂) B₃ τ₃ t₃ hf₃
  have hn:(0:ℝ)≤b^N:=pow_nonneg (zero_le_one.trans hb) _
  have h₂':volume s₂≤b^N*(b^N*volume s/(C₁.absNorm:ℝ))/(C₂.absNorm:ℝ):=
    h₂.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h₁ hn) (Nat.cast_nonneg _))
  apply (h₃.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h₂' hn) (Nat.cast_nonneg _))).trans_eq
  have hp:b^(3*N)=b^N*b^N*b^N:=by rw [Nat.mul_comm 3 N,pow_mul];ring
  rw [hp]
  field_simp

/-- The annular constant contributes explicitly to the raw-volume log
coordinate. It is not inserted into the outside-scalar x0 estimate. -/
theorem three_log_volume_bound (N:ℕ) (b Z:ℝ) (hb:1≤b) (hZ:1<Z)
    (hN:Fintype.card ι≤N) (hu:s.upper≤b)
    (hf₁:frozenCoefficient B₁.val C₁ R s.ν s.W s.P≠0)
    (hf₂:frozenCoefficient B₂.val C₂ (R*C₁)
      (child s C₁ R B₁ τ₁ t₁).ν (child s C₁ R B₁ τ₁ t₁).W (child s C₁ R B₁ τ₁ t₁).P≠0)
    (hf₃:frozenCoefficient B₃.val C₃ ((R*C₁)*C₂)
      (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂).ν
      (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂).W
      (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂).P≠0) :
    Real.logb Z (volume (child (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂)
      C₃ ((R*C₁)*C₂) B₃ τ₃ t₃))≤
      Real.logb Z (volume s)-Real.logb Z (C₁.absNorm:ℝ)-Real.logb Z (C₂.absNorm:ℝ)-
        Real.logb Z (C₃.absNorm:ℝ)+3*(N:ℝ)*Real.logb Z b := by
  have hv:=three_volume_bound s C₁ R B₁ τ₁ t₁ C₂ B₂ τ₂ t₂ C₃ B₃ τ₃ t₃ N b hb hN hu hf₁ hf₂ hf₃
  have h₁:(0:ℝ)<C₁.absNorm:=zero_lt_one.trans_le (norm_ge_one _ (allocation_ne s C₁ B₁))
  have h₂:(0:ℝ)<C₂.absNorm:=zero_lt_one.trans_le (norm_ge_one _ (allocation_ne (child s C₁ R B₁ τ₁ t₁) C₂ B₂))
  have h₃:(0:ℝ)<C₃.absNorm:=zero_lt_one.trans_le (norm_ge_one _
    (allocation_ne (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂) C₃ B₃))
  have hbp:0<b:=zero_lt_one.trans_le hb
  have hlog:=Real.logb_le_logb_of_le hZ (volume_pos _) hv
  rw [Real.logb_div (mul_ne_zero (pow_ne_zero _ hbp.ne') (volume_pos s).ne')
      (mul_ne_zero (mul_ne_zero h₁.ne' h₂.ne') h₃.ne'),
    Real.logb_mul (pow_ne_zero _ hbp.ne') (volume_pos s).ne',Real.logb_pow,
    Real.logb_mul (mul_ne_zero h₁.ne' h₂.ne') h₃.ne',Real.logb_mul h₁.ne' h₂.ne'] at hlog
  push_cast at hlog
  linarith

/-- The original polynomial volume cap gives the third physical log
coordinate with all three common norms and the exact annular allowance. -/
theorem three_log_volume_cap (N:ℕ) (b Z A:ℝ) (hb:1≤b) (hZ:1<Z)
    (hN:Fintype.card ι≤N) (hu:s.upper≤b) (hV:volume s≤Z^A)
    (hf₁:frozenCoefficient B₁.val C₁ R s.ν s.W s.P≠0)
    (hf₂:frozenCoefficient B₂.val C₂ (R*C₁)
      (child s C₁ R B₁ τ₁ t₁).ν (child s C₁ R B₁ τ₁ t₁).W (child s C₁ R B₁ τ₁ t₁).P≠0)
    (hf₃:frozenCoefficient B₃.val C₃ ((R*C₁)*C₂)
      (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂).ν
      (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂).W
      (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂).P≠0) :
    Real.logb Z (volume (child (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂)
      C₃ ((R*C₁)*C₂) B₃ τ₃ t₃))≤
      A-Real.logb Z (C₁.absNorm:ℝ)-Real.logb Z (C₂.absNorm:ℝ)-
        Real.logb Z (C₃.absNorm:ℝ)+3*(N:ℝ)*Real.logb Z b := by
  have hh:=three_log_volume_bound s C₁ R B₁ τ₁ t₁ C₂ B₂ τ₂ t₂ C₃ B₃ τ₃ t₃ N b Z hb hZ hN hu hf₁ hf₂ hf₃
  have hv:=Real.logb_le_logb_of_le hZ (volume_pos s) hV
  rw [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hv
  linarith

/-- Four original corners remain separate throughout all three allocations,
both as raw bounds and as logarithmic widths. -/
theorem three_raw_and_log_corners (Z:ℝ) (hZ:1<Z) :
    let s₃:=child (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂) C₃ ((R*C₁)*C₂) B₃ τ₃ t₃
    s₃.X₁≤s.X₁ ∧ s₃.X₂≤s.X₂ ∧ s₃.Y₁≤s.Y₁ ∧ s₃.Y₂≤s.Y₂ ∧
    Real.logb Z s₃.X₁≤Real.logb Z s.X₁ ∧ Real.logb Z s₃.X₂≤Real.logb Z s.X₂ ∧
    Real.logb Z s₃.Y₁≤Real.logb Z s.Y₁ ∧ Real.logb Z s₃.Y₂≤Real.logb Z s.Y₂ := by
  intro s₃
  obtain ⟨h₁,h₂,h₃,h₄⟩:=SelectedForcedGeometry.third_child_raw_caps
    s C₁ R B₁ τ₁ t₁ C₂ B₂ τ₂ t₂ C₃ B₃ τ₃ t₃ s.X₁ s.X₂ s.Y₁ s.Y₂ le_rfl le_rfl le_rfl le_rfl
  exact ⟨h₁,h₂,h₃,h₄,Real.logb_le_logb_of_le hZ s₃.X₁_pos h₁,
    Real.logb_le_logb_of_le hZ s₃.X₂_pos h₂,Real.logb_le_logb_of_le hZ s₃.Y₁_pos h₃,
    Real.logb_le_logb_of_le hZ s₃.Y₂_pos h₄⟩

end
end QRH.Record1252270103Source.Admission.SelectedHighCoordinates
#print axioms QRH.Record1252270103Source.Admission.SelectedHighCoordinates.three_volume_exact
#print axioms QRH.Record1252270103Source.Admission.SelectedHighCoordinates.three_volume_bound
#print axioms QRH.Record1252270103Source.Admission.SelectedHighCoordinates.three_log_volume_bound
#print axioms QRH.Record1252270103Source.Admission.SelectedHighCoordinates.three_log_volume_cap
#print axioms QRH.Record1252270103Source.Admission.SelectedHighCoordinates.three_raw_and_log_corners
#print axioms QRH.Record1252270103Source.Admission.SelectedForcedGeometry.third_child_full_slots_image
