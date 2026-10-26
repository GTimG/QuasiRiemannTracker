/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Only zero tuple summands are erased; the corrected column coefficient is equal. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.CoupledFirstBounds
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceSecondZeroEnergy
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.SecondRemainder
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceInputTailUniform CenteredMomentSourceZeroEnergy CenteredMomentExceptionalAmplitudePair
local notation "O"=>ActualEisensteinCubic.O
local instance supportedTupleDecidable {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _
variable {ι : Type*} [Fintype ι]

def liveModifier (s : Input ι) (modifier : Tuple ι→ℂ) (R seed : Ideal O) (v : Tuple ι) : ℂ :=
  if High.CoupledFirst.tupleCoefficient s modifier R seed v=0 then 0 else modifier v

theorem live_tuple_eq (s : Input ι) (modifier : Tuple ι→ℂ) (R seed : Ideal O) :
    High.CoupledFirst.tupleCoefficient s (liveModifier s modifier R seed) R seed=
      High.CoupledFirst.tupleCoefficient s modifier R seed := by
  funext v
  by_cases h : High.CoupledFirst.tupleCoefficient s modifier R seed v=0
  · have hl : liveModifier s modifier R seed v=0 := ite_eq_left h
    dsimp only [High.CoupledFirst.tupleCoefficient]
    rw [hl,zero_mul]
    exact h.symm
  · have hl : liveModifier s modifier R seed v=modifier v := ite_eq_right h
    dsimp only [High.CoupledFirst.tupleCoefficient]
    rw [hl]

theorem live_coefficient_eq (s : Input ι) (modifier : Tuple ι→ℂ) (R seed : Ideal O) :
    High.CoupledFirst.coefficient s (liveModifier s modifier R seed) R seed=
      High.CoupledFirst.coefficient s modifier R seed := by
  unfold High.CoupledFirst.coefficient
  rw [live_tuple_eq]

theorem live_modifier_bound (s : Input ι) (modifier : Tuple ι→ℂ) (R seed : Ideal O)
    (factor : ℝ) (hf : 0≤factor)
    (hmod : ∀v∈Fintype.piFinset s.pools,
      High.CoupledFirst.tupleCoefficient s modifier R seed v≠0→‖modifier v‖≤factor) :
    ∀v∈Fintype.piFinset s.pools,‖liveModifier s modifier R seed v‖≤factor := by
  intro v hv
  dsimp [liveModifier]
  split_ifs with h
  · simpa using hf
  · exact hmod v hv h

theorem tuple_norm_cap (s : Input ι) (modifier : Tuple ι→ℂ) (R seed : Ideal O)
    (factor : ℝ) (hf : 0≤factor) (W₁ W₂ : 𝓢(ℝ,ℂ))
    (he₁ : s.W₁=W₁) (he₂ : s.W₂=W₂)
    (hmod : ∀v∈Fintype.piFinset s.pools,
      High.CoupledFirst.tupleCoefficient s modifier R seed v≠0→‖modifier v‖≤factor) :
    ∀v∈Fintype.piFinset s.pools,
      ‖High.CoupledFirst.tupleCoefficient s modifier R seed v‖≤2*(factor*plainControl s W₁ W₂) := by
  intro v hv
  by_cases hz : High.CoupledFirst.tupleCoefficient s modifier R seed v=0
  · rw [hz,norm_zero]
    exact mul_nonneg (by norm_num) (mul_nonneg hf (plainControl_nonneg s W₁ W₂))
  have hb:=profileCoefficient_norm_le R s.ν s.ν_bound s.W s.P s.M W₁ W₂
    (SchwartzMap.seminorm ℝ 0 0 W₁) (SchwartzMap.seminorm ℝ 0 0 W₂)
    (fun i=>zero_le_one.trans (s.M_ge_one i)) (apply_nonneg _ _) (apply_nonneg _ _)
    s.W_bound (SchwartzMap.norm_le_seminorm ℝ W₁) (SchwartzMap.norm_le_seminorm ℝ W₂)
    s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed v
  have hb' : ‖profileCoefficient R s.ν s.W s.P W₁ W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed v‖≤
      2*plainControl s W₁ W₂ := hb.trans_eq (by dsimp [plainControl];ring)
  dsimp only [High.CoupledFirst.tupleCoefficient]
  rw [he₁,he₂,norm_mul]
  exact (mul_le_mul (hmod v hv hz) hb' (norm_nonneg _) hf).trans_eq (by ring)

theorem tuple_radius (s : Input ι) (modifier : Tuple ι→ℂ) (R seed : Ideal O)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (v : Tuple ι)
    (hv : High.CoupledFirst.tupleCoefficient s modifier R seed v≠0) :
    finiteTupleProduct v≠0 ∧ (Ideal.absNorm (finiteTupleProduct v):ℝ)≤sourceRadius s := by
  have hn:=High.CoupledFirst.tuple_nonzero s modifier R seed v hv
  have hz (i : ι) : s.W i 0=0 := by
    by_contra h
    exact (not_le_of_gt (s.lo_pos i)) (s.support i h).1
  have hh:=profileCoefficient_product_bound R s.ν s.W s.P s.hi s.W₁ s.W₂ s.b₁ s.b₂
    s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed s.P_pos s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos
    one_ne_zero one_ne_zero rfl s.same_product hz hz₁ hz₂
    (fun i x hx=>(s.support i hx).2) (fun x hx=>s.support₁ hx) (fun x hx=>s.support₂ hx) v hn
  simpa only [CenteredMomentOriginalCommonHarmonic.sourceRadius,map_one,Nat.cast_one,mul_one,div_one] using hh

theorem supported_input_mass (hi : ι→ℝ) (whi : ℝ) (hhi : ∀i,0≤hi i) (hwhi : 0≤whi)
    (s : Input ι) (modifier : Tuple ι→ℂ) (factor : ℝ) (hf : 0≤factor)
    (R seed : Ideal O)
    (hmod : ∀v∈Fintype.piFinset s.pools,
      High.CoupledFirst.tupleCoefficient s modifier R seed v≠0→‖modifier v‖≤factor)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (wlo : ℝ) (hwlo : 0<wlo)
    (he₁ : s.W₁=W₁) (he₂ : s.W₂=W₂)
    (hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi)
    (hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi) (hshi : ∀i,s.hi i≤hi i) :
    (∑I∈finiteColumns (Fintype.piFinset s.pools),‖High.CoupledFirst.coefficient s modifier R seed I‖)≤
      (2*128^(Fintype.card ι+2)*(∏i,hi i)*whi^2)*(factor*plainControl s W₁ W₂)*volume s.toData := by
  have h:=High.CoupledFirst.input_mass hi whi hhi hwhi s (liveModifier s modifier R seed)
    factor hf (live_modifier_bound s modifier R seed factor hf hmod) W₁ W₂ wlo hwlo
    he₁ he₂ hs₁ hs₂ hshi R seed
  rwa [live_coefficient_eq] at h
end
end QRH.Record1252270103Source.SecondRemainder
#print axioms QRH.Record1252270103Source.SecondRemainder.live_coefficient_eq
#print axioms QRH.Record1252270103Source.SecondRemainder.tuple_norm_cap
#print axioms QRH.Record1252270103Source.SecondRemainder.tuple_radius
#print axioms QRH.Record1252270103Source.SecondRemainder.supported_input_mass
