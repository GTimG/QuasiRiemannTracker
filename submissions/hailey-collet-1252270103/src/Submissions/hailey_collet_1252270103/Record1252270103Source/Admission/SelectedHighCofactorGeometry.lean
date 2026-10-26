/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual raw-pair capacity for the third selected child, from the full volume
and original-slot conservation. All common factors and raw corners are retained. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedHighCoordinatesVolume
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedHighSlotsLedger
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedHighCofactorGeometry
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn Record12518109Natural.MarkedPlain SelectedHighSlots
open CenteredMomentAmplificationChildSourceCaps
local notation "O" => HeckeFamily.O
variable {ι : Type} [Fintype ι]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
variable (s : Input ι) (C₁ R : Ideal O) (B₁ : actualAllocations s.pools C₁)
    (τ₁ : Character) (t₁ : ℝ) (C₂ : Ideal O)
    (B₂ : actualAllocations (child s C₁ R B₁ τ₁ t₁).pools C₂)
    (τ₂ : Character) (t₂ : ℝ) (C₃ : Ideal O)
    (B₃ : actualAllocations (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂).pools C₃)
    (τ₃ : Character) (t₃ : ℝ)

/-- The full final original-slot width is exactly the marked part of the
literal third child's logarithmic volume. -/
theorem third_log_volume_pair (Z : ℝ) (hZ : 1<Z) (w : ι→ℝ) (hscale : ∀i,s.P i=Z^(w i)) :
    let schild:=child (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂)
      C₃ ((R*C₁)*C₂) B₃ τ₃ t₃
    Real.logb Z (volume schild)=Real.logb Z (schild.X₁*schild.X₂)+
      ∑i∈finalImage B₁.val B₂.val B₃.val,w i := by
  intro schild
  have hp : (∏i,schild.P i)=Z^(∑i∈finalImage B₁.val B₂.val B₃.val,w i) := by
    rw [third_child_slot_product s C₁ R B₁ τ₁ t₁ C₂ B₂ τ₂ t₂ C₃ B₃ τ₃ t₃]
    simp_rw [hscale]
    rw [←Real.rpow_sum_of_pos (zero_lt_one.trans hZ)]
  change Real.logb Z (schild.X₁*schild.X₂*(∏i,schild.P i))=_
  rw [hp,Real.logb_mul (mul_pos schild.X₁_pos schild.X₂_pos).ne'
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).ne',
    Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']

variable (hf₁ : frozenCoefficient B₁.val C₁ R s.ν s.W s.P≠0)
    (hf₂ : frozenCoefficient B₂.val C₂ (R*C₁)
      (child s C₁ R B₁ τ₁ t₁).ν (child s C₁ R B₁ τ₁ t₁).W (child s C₁ R B₁ τ₁ t₁).P≠0)
    (hf₃ : frozenCoefficient B₃.val C₃ ((R*C₁)*C₂)
      (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂).ν
      (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂).W
      (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂).P≠0)
include hf₁ hf₂ hf₃

/-- The actual cofactor raw-pair gate, with all three common norms and the
full annular volume loss. No target capacity or energy bound is assumed. -/
theorem actual_raw_pair_capacity (N : ℕ) (upper Z A wmin : ℝ)
    (hN : Fintype.card ι≤N) (hupper : 1≤upper) (hsupper : s.upper≤upper)
    (hZ : 1<Z) (hV : volume s≤Z^A) (w : ι→ℝ)
    (hscale : ∀i,s.P i=Z^(w i)) (hw : ∀i,0≤w i)
    (T : Finset ι) (hT : T⊆finalImage B₁.val B₂.val B₃.val) :
    let schild:=child (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂)
      C₃ ((R*C₁)*C₂) B₃ τ₃ t₃
    let full:=finalImage B₁.val B₂.val B₃.val
    let live:=∑i∈largeSlots full w wmin,w i
    let small:=∑i∈largeSlots T w wmin,w i
    let x₃:=A-Real.logb Z (C₁.absNorm:ℝ)-Real.logb Z (C₂.absNorm:ℝ)-
      Real.logb Z (C₃.absNorm:ℝ)-live+small+3*(N:ℝ)*Real.logb Z upper
    schild.X₁*schild.X₂≤Z^(x₃-∑i∈T,w i) := by
  intro schild full live small x₃
  have hv:=SelectedHighCoordinates.three_log_volume_cap s C₁ R B₁ τ₁ t₁ C₂ B₂ τ₂ t₂ C₃ B₃
    τ₃ t₃ N upper Z A hupper hZ hN hsupper hV hf₁ hf₂ hf₃
  have he:=third_log_volume_pair s C₁ R B₁ τ₁ t₁ C₂ B₂ τ₂ t₂ C₃ B₃ τ₃ t₃ Z hZ w hscale
  have hc:=subset_width_conservation full T w wmin hT hw
  have hl : Real.logb Z (schild.X₁*schild.X₂)≤x₃-∑i∈T,w i := by
    dsimp only [x₃,live,small,full] at *
    linarith only [hv,he,hc]
  calc
    schild.X₁*schild.X₂=Z^(Real.logb Z (schild.X₁*schild.X₂)) :=
      (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (mul_pos schild.X₁_pos schild.X₂_pos)).symm
    _≤Z^(x₃-∑i∈T,w i) := Real.rpow_le_rpow_of_exponent_le hZ.le hl

/-- All geometric gates used by the annular cofactor caller, on the literal
third child and arbitrary collision subset. The canonical lower endpoint is one. -/
theorem actual_canonical_cofactor_geometry (N : ℕ) (upper Z A wmin b δ allowance : ℝ)
    (hN : Fintype.card ι≤N) (hupper : 1≤upper) (hsupper : s.upper≤upper)
    (hslower : 1≤s.lower) (hZ : 1<Z) (hV : volume s≤Z^A)
    (hmin : 0≤wmin) (w : ι→ℝ) (hscale : ∀i,s.P i=Z^(w i)) (hw : ∀i,0≤w i)
    (htotal : b-δ≤∑i,w i) (hwidth : (∑i,w i)≤b)
    (hloss : δ+(N:ℝ)*wmin≤2*allowance)
    (T : Finset ι) (hT : T⊆finalImage B₁.val B₂.val B₃.val) :
    let schild:=child (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂)
      C₃ ((R*C₁)*C₂) B₃ τ₃ t₃
    let full:=finalImage B₁.val B₂.val B₃.val
    let live:=∑i∈largeSlots full w wmin,w i
    let small:=∑i∈largeSlots T w wmin,w i
    let forced:=Real.logb Z (C₃.absNorm:ℝ)
    let x₃:=A-Real.logb Z (C₁.absNorm:ℝ)-Real.logb Z (C₂.absNorm:ℝ)-
      forced-live+small+3*(N:ℝ)*Real.logb Z upper
    0≤forced ∧ 0≤small ∧ small≤live ∧ live≤b ∧
    b-2*allowance≤live+Real.logb Z (C₁.absNorm:ℝ)+Real.logb Z (C₂.absNorm:ℝ)+forced ∧
    (∑i∈T,w i)+(live-small)≤∑i∈full,w i ∧
    schild.X₁*schild.X₂≤Z^(x₃-∑i∈T,w i) ∧
    schild.X₁≤s.X₁ ∧ schild.X₂≤s.X₂ ∧ schild.Y₁≤s.Y₁ ∧ schild.Y₂≤s.Y₂ ∧
    (∏i,schild.P i)=∏i∈full,s.P i := by
  intro schild full live small forced x₃
  obtain ⟨hl₀,hl₁,hl₂,hsub⟩:=canonical_selected_slot_ledger s C₁ R B₁ τ₁ t₁ C₂ B₂ τ₂ t₂ C₃ B₃
    hf₁ hf₂ hf₃ N Z wmin b δ allowance hN hslower hZ hmin w hscale hw htotal hwidth hloss
  obtain ⟨hs₀,hs₁,hcons⟩:=hsub T hT
  obtain ⟨hX₁,hX₂,hY₁,hY₂⟩:=SelectedForcedGeometry.third_child_raw_caps s C₁ R B₁ τ₁ t₁
    C₂ B₂ τ₂ t₂ C₃ B₃ τ₃ t₃ s.X₁ s.X₂ s.Y₁ s.Y₂ le_rfl le_rfl le_rfl le_rfl
  have hf : 0≤forced := Real.logb_nonneg hZ
    (norm_ge_one C₃ (allocation_ne (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂) C₃ B₃))
  exact ⟨hf,hs₀,hs₁,hl₁,hl₂,hcons,
    actual_raw_pair_capacity s C₁ R B₁ τ₁ t₁ C₂ B₂ τ₂ t₂ C₃ B₃ τ₃ t₃ hf₁ hf₂ hf₃
      N upper Z A wmin hN hupper hsupper hZ hV w hscale hw T hT,
    hX₁,hX₂,hY₁,hY₂,third_child_slot_product s C₁ R B₁ τ₁ t₁ C₂ B₂ τ₂ t₂ C₃ B₃ τ₃ t₃⟩

end
end QRH.Record1252270103Source.Admission.SelectedHighCofactorGeometry
#print axioms QRH.Record1252270103Source.Admission.SelectedHighCofactorGeometry.third_log_volume_pair
#print axioms QRH.Record1252270103Source.Admission.SelectedHighCofactorGeometry.actual_raw_pair_capacity
#print axioms QRH.Record1252270103Source.Admission.SelectedHighCofactorGeometry.actual_canonical_cofactor_geometry
