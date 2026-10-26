/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowAggregate
import Candidate.Cycle63.Physical.InitialMass.GeometryLowSidePayment
import Candidate.Cycle63.Physical.InitialMass.GeometrySecondCaps
import Candidate.Cycle63.Physical.InitialMass.GeometryCoarseSidePayment
import Candidate.Cycle63.Physical.InitialMass.GeometryShiftedHeight
import Candidate.Cycle63.Physical.InitialMass.GeometryMainCoarseFamily

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentCanonicalFirst
open CenteredMomentSectorLocalization CenteredMomentSourceRow
open CenteredMomentWholeDivisorShell CenteredMomentLogDyadic
open CenteredMomentCommonProfile Cycle63Moment
open CenteredMomentAmplificationChildSourceCaps CenteredMomentRankinRadical
open CenteredMomentSecondPhysicalBlock CenteredMomentChildRows RayFourExpansion
open CenteredMomentSecondCanonical CenteredMomentCommonHeightEnvelope
open CenteredMomentNaturalRowSource CenteredMomentCommonPairedSource
open CenteredMomentSecondInputCapacitySource CenteredMomentSecondCanonicalScalar
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance mainLowNormalizedPaymentSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _

omit [DecidableEq α] in
/-- All scalar first-label gates come from the literal original source.
The residual projector is kept as a separate key and the selected first
allocation remains attached to that key. -/
theorem actual_main_low_first_source_gates {Label : Type*}
    (reflected : Bool) (s : Input α) (R seed : Ideal O) (K Z ξ B : ℝ) (hK : 0<K)
    (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤Z^B) (bin : ℤ×(Fin 5→ℤ))
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed K Z ξ hK bin) :
    ∀l,
      let first:=geometryFirstLabel s R seed K Z ξ hK bin (firstIndex l).1.val
      Supported first.1.1 ∧ Supported first.1.2 ∧
      primeSupport first.1.1=primeSupport first.1.2 ∧
      seed∣first.1.1 ∧ seed∣first.1.2 ∧
      (first.1.1.absNorm:ℝ)≤Z^B ∧ (first.1.2.absNorm:ℝ)≤Z^B ∧
      Squarefree (firstIndex l).1.val.2.1.val := by
  intro l first
  let src:=geometryFirstSource s R seed K Z ξ hK bin (firstIndex l).1.val.1
  have hg:=actual_common_gates s R seed hs hz₁ hz₂
    (firstIndex l).1.val.1.val.1.val.1 (firstIndex l).1.val.1.val.1.val.2
    (firstIndex l).1.val.1.val.1.property
  exact ⟨src.hC,src.hD,src.sameSupport,hg.2.2.2.1,hg.2.2.2.2.1,
    (actual_geometry_norm_caps s R seed K Z ξ B hs hz₁ hz₂ hsource
      (firstIndex l).1.val.1.val 0).2,
    (actual_geometry_norm_caps s R seed K Z ξ B hs hz₁ hz₂ hsource
      (firstIndex l).1.val.1.val 1).2,
    actual_first_live_squarefree _ _ _ (firstIndex l).1.property⟩

/-- Restriction to a shared first shell preserves the exact selected
allocation, arithmetic-label/projector injection and original support gates. -/
theorem actual_main_low_first_shell_restriction {Label : Type*} [Fintype Label]
    (reflected : Bool) (s : Input α) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed K Z ξ hK bin)
    (hinj : Function.Injective (fun l=>(geometryFirstLabel s R seed K Z ξ hK bin
      (firstIndex l).1.val,(firstIndex l).1.val.2.1.val)))
    (hf : ∀l,frozenCoefficient (firstIndex l).2.val
      (geometryColumnIdeal reflected s R seed K Z ξ hK bin (firstIndex l).1.val)
      R s.ν s.W s.P≠0) (n : ℤ) :
    Function.Injective (fun l : SelectedFirstShell (fun l=>(firstIndex l).1.val) n=>
      (geometryFirstLabel s R seed K Z ξ hK bin (firstIndex l.val).1.val,
        (firstIndex l.val).1.val.2.1.val)) ∧
    (∀l : SelectedFirstShell (fun l=>(firstIndex l).1.val) n,
      frozenCoefficient (firstIndex l.val).2.val
        (geometryColumnIdeal reflected s R seed K Z ξ hK bin (firstIndex l.val).1.val)
        R s.ν s.W s.P≠0) ∧
    (∀l : SelectedFirstShell (fun l=>(firstIndex l).1.val) n,
      dyadicScale n≤((firstIndex l.val).1.val.2.1.val.absNorm:ℝ) ∧
      ((firstIndex l.val).1.val.2.1.val.absNorm:ℝ)<2*dyadicScale n) :=
  actual_geometry_selected_first_shell_restriction reflected s R seed K Z ξ hK bin
    (fun l=>(firstIndex l).1) (fun l=>(firstIndex l).2) hinj hf n

/-- An occupied common FIRST shell supplies a real first-source witness.
It bounds the radical endpoint and supplies the exact scalar cancellation
ledger for the entire restricted selected family, including empty rows. -/
theorem actual_main_low_first_shell_scalar_gates {Label : Type*} [Fintype Label]
    (reflected : Bool) (s : Input α) (R seed : Ideal O) (K Z ξ B A : ℝ) (hK : 0<K)
    (hZ : 2≤Z) (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤Z^B) (bin : ℤ×(Fin 5→ℤ))
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed K Z ξ hK bin)
    (n : ℤ) (hn : n∈selectedShells (selectedFirstProjectors (fun l=>(firstIndex l).1.val))) :
    let w:=Real.logb Z 2
    let c : Fin 5:=if reflected then 1 else 0
    let p:=((bin.2 2:ℝ)+1)*w
    let exponent:=A-(bin.2 c:ℝ)*w+((bin.2 3:ℝ)+1)*w+((bin.2 4:ℝ)+1)*w
    let sideLower:=(bin.2 2:ℝ)*w+A-((bin.2 c:ℝ)+1)*w+
      (bin.2 3:ℝ)*w+(bin.2 4:ℝ)*w
    p≤B+1 ∧ p+exponent-sideLower=4*w ∧
    ∀l : SelectedFirstShell (fun l=>(firstIndex l).1.val) n,
      let first:=geometryFirstLabel s R seed K Z ξ hK bin (firstIndex l.val).1.val
      ((commonRadical first.1.1 first.1.2).absNorm:ℝ)≤Z^p ∧
      lowGeometryExponent reflected Z A first≤exponent ∧
      sideLower≤geometryHighSide reflected A
        (geometryExponents s R seed K Z ξ (firstIndex l.val).1.val.1.val) := by
  intro w c p exponent sideLower
  obtain ⟨D,hD⟩ := (shell_nonempty_iff _ n).mpr hn
  have hmem:=(shell_member_data _ n D hD).1
  rw [selected_first_projectors_eq_image] at hmem
  obtain ⟨j,_,_⟩:=Finset.mem_image.mp hmem
  have hp:=actual_geometry_low_bin_radical_exponent_cap s R seed K Z ξ B hZ
    hs hz₁ hz₂ hsource bin (firstIndex j).1.val.1
  have hZ1 : 1<Z := by linarith
  have hg:=actual_geometry_low_bin_scalar_gates s R seed K Z ξ B A hK hZ1
    hs hz₁ hz₂ hsource bin reflected
  exact ⟨hp,hg.1,fun l=>hg.2 (firstIndex l.val).1.val⟩

end

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentCanonicalFirst
open CenteredMomentSectorLocalization CenteredMomentSourceRow
open CenteredMomentWholeDivisorShell CenteredMomentLogDyadic
open CenteredMomentCommonProfile Cycle63Moment
open CenteredMomentAmplificationChildSourceCaps CenteredMomentRankinRadical
open CenteredMomentSecondPhysicalBlock CenteredMomentChildRows RayFourExpansion
open CenteredMomentSecondCanonical CenteredMomentCommonHeightEnvelope
open CenteredMomentNaturalRowSource CenteredMomentCommonPairedSource
open CenteredMomentSecondInputCapacitySource CenteredMomentSecondCanonicalScalar
local notation "O" => HeckeFamily.O
local instance mainLowSpliceSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 20000

/-- A lower bound for the moving target suffices for a fixed height degree. -/
theorem geometry_uniform_shifted_height_splice (coarse targetMin τ : ℝ)
    (hτ : 0<τ) (smallDegree : ℕ) :
    ∃degree : ℕ,∀Z target v height t u E Cs Cc control : ℝ,
      1≤Z → targetMin≤target → 0≤height → 0≤Cs → 0≤Cc → 0≤ control →
      (2*(1+|v|+height+2*Real.pi*(|t|+|u|))≤Z^τ →
        E≤Cs*control*Z^target*(2*(1+|v|+height+2*Real.pi*(|t|+|u|)))^smallDegree) →
      E≤Cc*control*Z^coarse →
      E≤(2+4*Real.pi)^degree*(Cs+Cc)*control*Z^target*
        (1+|v|+height)^degree*(1+|t|)^degree*(1+|u|)^degree := by
  obtain ⟨n,hn⟩ := geometry_large_height_absorption coarse targetMin τ hτ
  refine ⟨max n smallDegree,?_⟩
  intro Z target v height t u E Cs Cc control hZ htarget hh hCs hCc hc hs hb
  let H := 2*(1+|v|+height+2*Real.pi*(|t|+|u|))
  have hH : 1≤H := by
    dsimp [H]
    have hp : 0≤2*Real.pi*(|t|+|u|) := by positivity
    linarith [abs_nonneg v]
  have hraw : E≤(Cs+Cc)*control*Z^target*H^(max n smallDegree) := by
    by_cases h : H≤Z^τ
    · apply (hs h).trans
      apply mul_le_mul
      · gcongr; linarith
      · exact pow_le_pow_right₀ hH (le_max_right _ _)
      · positivity
      · positivity
    · have hscale := hn Z H hZ (le_of_lt (lt_of_not_ge h))
      have hz := Real.rpow_le_rpow_of_exponent_le hZ htarget
      calc
        E≤Cc*control*Z^coarse := hb
        _≤Cc*control*(Z^targetMin*H^n) := mul_le_mul_of_nonneg_left hscale (mul_nonneg hCc hc)
        _≤Cc*control*(Z^target*H^(max n smallDegree)) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCc hc)
          exact mul_le_mul hz (pow_le_pow_right₀ hH (le_max_left _ _)) (by positivity) (by positivity)
        _≤(Cs+Cc)*control*Z^target*H^(max n smallDegree) := by
          rw [←mul_assoc]
          gcongr
          linarith
  apply hraw.trans
  have hp := pow_le_pow_left₀ (by positivity : 0≤H)
    (geometry_shifted_height_product v height t u hh) (max n smallDegree)
  have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0≤(Cs+Cc)*control*Z^target)
  simpa only [mul_pow,mul_assoc,mul_left_comm,mul_comm] using hm

end
end OAI.SevenEighths.Cycle63InitialMass
