/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MainParameters
import Candidate.Uneven.MainLowPaidMain
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowNormalizedPayment
import Candidate.Uneven.MainLowPaidMain
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Uneven.MainPhysicalRowsPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowAggregate
import Candidate.Cycle63.Physical.InitialMass.GeometryLowSidePayment
import Candidate.Cycle63.Physical.InitialMass.GeometrySecondCaps
import Candidate.Cycle63.Physical.InitialMass.GeometryCoarseSidePayment
import Candidate.Cycle63.Physical.InitialMass.GeometryShiftedHeight
import Candidate.Cycle63.Physical.InitialMass.GeometryMainCoarseFamily

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.MainPhysical
open OAI OAI.SevenEighths
open OAI.SevenEighths.MainLow
open OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open Sil.Uneven.MainSource
open OAI OAI.SevenEighths
open OAI.SevenEighths.Cycle63InitialMass
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
theorem actual_main_low_first_source_gates (P : Plane) {Label : Type*}
    (reflected : Bool) (s : Input α) (R seed : Ideal O) (K Z ξ B : ℝ) (hK : 0 < K)
    (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s ≤ Z^B) (bin : ℤ×(Fin 5→ℤ))
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed K Z ξ hK bin) :
    ∀l,
      let first:=geometryFirstLabel s R seed K Z ξ hK bin (firstIndex l).1.val
      Supported first.1.1 ∧ Supported first.1.2 ∧
      primeSupport first.1.1=primeSupport first.1.2 ∧
      seed∣first.1.1 ∧ seed∣first.1.2 ∧
      (first.1.1.absNorm:ℝ) ≤ Z^B ∧ (first.1.2.absNorm:ℝ) ≤ Z^B ∧
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

omit [DecidableEq α] in

/-- Restriction to a shared first shell preserves the exact selected
allocation, arithmetic-label/projector injection and original support gates. -/
theorem actual_main_low_first_shell_restriction (P : Plane) {Label : Type*} [Fintype Label]
    (reflected : Bool) (s : Input α) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0 < K)
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
      dyadicScale n ≤ ((firstIndex l.val).1.val.2.1.val.absNorm:ℝ) ∧
      ((firstIndex l.val).1.val.2.1.val.absNorm:ℝ) < 2*dyadicScale n) :=
  actual_geometry_selected_first_shell_restriction reflected s R seed K Z ξ hK bin
    (fun l=>(firstIndex l).1) (fun l=>(firstIndex l).2) hinj hf n


/-- An occupied common FIRST shell supplies a real first-source witness.
It bounds the radical endpoint and supplies the exact scalar cancellation
ledger for the entire restricted selected family, including empty rows. -/
theorem actual_main_low_first_shell_scalar_gates (P : Plane) {Label : Type*} [Fintype Label]
    (reflected : Bool) (s : Input α) (R seed : Ideal O) (K Z ξ B A : ℝ) (hK : 0 < K)
    (hZ : 2 ≤ Z) (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s ≤ Z^B) (bin : ℤ×(Fin 5→ℤ))
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed K Z ξ hK bin)
    (n : ℤ) (hn : n∈selectedShells (selectedFirstProjectors (fun l=>(firstIndex l).1.val))) :
    let w:=Real.logb Z 2
    let c : Fin 5:=if reflected then 1 else 0
    let p:=((bin.2 2:ℝ)+1)*w
    let exponent:=A-(bin.2 c:ℝ)*w+((bin.2 3:ℝ)+1)*w+((bin.2 4:ℝ)+1)*w
    let sideLower:=(bin.2 2:ℝ)*w+A-((bin.2 c:ℝ)+1)*w+
      (bin.2 3:ℝ)*w+(bin.2 4:ℝ)*w
    p ≤ B+1 ∧ p+exponent-sideLower=4*w ∧
    ∀l : SelectedFirstShell (fun l=>(firstIndex l).1.val) n,
      let first:=geometryFirstLabel s R seed K Z ξ hK bin (firstIndex l.val).1.val
      ((commonRadical first.1.1 first.1.2).absNorm:ℝ) ≤ Z^p ∧
      lowGeometryExponent reflected Z A first ≤ exponent ∧
      sideLower ≤ geometryHighSide reflected A
        (geometryExponents s R seed K Z ξ (firstIndex l.val).1.val.1.val) := by
  intro w c p exponent sideLower
  obtain ⟨D,hD⟩ := (shell_nonempty_iff _ n).mpr hn
  have hmem:=(shell_member_data _ n D hD).1
  rw [selected_first_projectors_eq_image] at hmem
  obtain ⟨j,_,_⟩:=Finset.mem_image.mp hmem
  have hp:=actual_geometry_low_bin_radical_exponent_cap s R seed K Z ξ B hZ
    hs hz₁ hz₂ hsource bin (firstIndex j).1.val.1
  have hZ1 : 1 < Z := by linarith
  have hg:=actual_geometry_low_bin_scalar_gates s R seed K Z ξ B A hK hZ1
    hs hz₁ hz₂ hsource bin reflected
  exact ⟨hp,hg.1,fun l=>hg.2 (firstIndex l.val).1.val⟩

/-- The existing saved-label/projector dictionary specialized to the
literal selected first family. Its inverse retains the actual allocator. -/
abbrev MainLowSavedFirstPair {Label : Type*} [Fintype Label]
    (reflected : Bool) (s : Input α) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0 < K)
    (bin : ℤ×(Fin 5→ℤ))
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed K Z ξ hK bin) :=
  SelectedLowFirstPair
    (fun j=>geometryFirstLabel s R seed K Z ξ hK bin (firstIndex j).1.val)
    (fun j=>(firstIndex j).1.val.2.1.val)

def mainLowSavedFirstOriginal (P : Plane) {Label : Type*} [Fintype Label]
    (reflected : Bool) (s : Input α) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0 < K)
    (bin : ℤ×(Fin 5→ℤ))
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed K Z ξ hK bin)
    (hinj : Function.Injective (fun j=>(geometryFirstLabel s R seed K Z ξ hK bin
      (firstIndex j).1.val,(firstIndex j).1.val.2.1.val)))
    (pair : MainLowSavedFirstPair reflected s R seed K Z ξ hK bin firstIndex) : Label :=
  (selectedLowFirstPairEquiv
    (fun j=>geometryFirstLabel s R seed K Z ξ hK bin (firstIndex j).1.val)
    (fun j=>(firstIndex j).1.val.2.1.val) hinj).symm pair

omit [DecidableEq α] in

omit [DecidableEq α] in

omit [DecidableEq α] in

end

noncomputable section
open Sil.Uneven.MainSource
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
set_option maxHeartbeats 200000


/-- A lower bound for the moving target suffices for a fixed height degree. -/
theorem geometry_uniform_shifted_height_splice (P : Plane) (coarse targetMin τ : ℝ)
    (hτ : 0 < τ) (smallDegree : ℕ) :
    ∃degree : ℕ,∀Z target v height t u E Cs Cc control : ℝ,
      1 ≤ Z → targetMin ≤ target → 0 ≤ height → 0 ≤ Cs → 0 ≤ Cc → 0 ≤ control →
      (2*(1+|v|+height+2*Real.pi*(|t|+|u|)) ≤ Z^τ →
        E ≤ Cs*control*Z^target*(2*(1+|v|+height+2*Real.pi*(|t|+|u|)))^smallDegree) →
      E ≤ Cc*control*Z^coarse →
      E ≤ (2+4*Real.pi)^degree*(Cs+Cc)*control*Z^target*
        (1+|v|+height)^degree*(1+|t|)^degree*(1+|u|)^degree := by
  obtain ⟨n,hn⟩ := geometry_large_height_absorption coarse targetMin τ hτ
  refine ⟨max n smallDegree,?_⟩
  intro Z target v height t u E Cs Cc control hZ htarget hh hCs hCc hc hs hb
  let H := 2*(1+|v|+height+2*Real.pi*(|t|+|u|))
  have hH : 1 ≤ H := by
    dsimp [H]
    have hp : 0 ≤ 2*Real.pi*(|t|+|u|) := by positivity
    linarith [abs_nonneg v]
  have hraw : E ≤ (Cs+Cc)*control*Z^target*H^(max n smallDegree) := by
    by_cases h : H ≤ Z^τ
    · apply (hs h).trans
      apply mul_le_mul
      · gcongr; linarith
      · exact pow_le_pow_right₀ hH (le_max_right _ _)
      · positivity
      · positivity
    · have hscale := hn Z H hZ (le_of_lt (lt_of_not_ge h))
      have hz := Real.rpow_le_rpow_of_exponent_le hZ htarget
      calc
        E ≤ Cc*control*Z^coarse := hb
        _ ≤ Cc*control*(Z^targetMin*H^n) := mul_le_mul_of_nonneg_left hscale (mul_nonneg hCc hc)
        _ ≤ Cc*control*(Z^target*H^(max n smallDegree)) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCc hc)
          exact mul_le_mul hz (pow_le_pow_right₀ hH (le_max_left _ _)) (by positivity) (by positivity)
        _ ≤ (Cs+Cc)*control*Z^target*H^(max n smallDegree) := by
          rw [←mul_assoc]
          gcongr
          linarith
  apply hraw.trans
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ H)
    (geometry_shifted_height_product v height t u hh) (max n smallDegree)
  have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ (Cs+Cc)*control*Z^target)
  simpa only [mul_pow,mul_assoc,mul_left_comm,mul_comm] using hm



/-- Literal complete selected-family costs, with only the pending bounded-height
low estimate explicit. The moving target is kept at its exact value. -/
def MainLowAllHeightSpec (P : Plane) {α : Type}[Fintype α][DecidableEq α]
    (N degree smallDegree : ℕ) (B Cs b bs window plainCap lo ap εmass ξ U targetMin τ Csmall K Z : ℝ) : Prop :=
∀target : ℝ,targetMin ≤ target → ∀hZ : 1 < Z,
      ∀{Label : Type}[Fintype Label]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)(Dfirst a reserve t : ℝ)(hK : 0 < Z^Dfirst),
      Squarefree seed → Endpoints b bs bs s →
      lo ≤ s.lower → sourceRadius s ≤ Z^B → |Real.logb Z (volume s)| ≤ B → |Dfirst| ≤ B →
      |a| ≤ B → |frequencyLoss Z 32 ξ+reserve| ≤ B → (∀j,s.M j ≤ Cs) →
      (∀j,CenteredMomentSlotRatios.logWindow (s.lo j) (s.hi j) ≤ window) →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j ≤ Z^plainCap) →
      (∀j,s.P j ≤ Z^plainCap) →
      (∀i I,I∈s.pools i→(I.absNorm:ℝ) ≤ Z^U) →
      (∀x,s.W₁ x≠0→ap ≤ x) → (∀x,s.W₂ x≠0→ap ≤ x) →
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),0 ≤ a → 0 ≤ reserve →
      ∀(bin : ℤ×(Fin 5→ℤ))
        (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^Dfirst) Z ξ hK bin),
      Function.Injective (fun l=>(geometryFirstLabel s R seed (Z^Dfirst) Z ξ hK bin (firstIndex l).1.val,
        (firstIndex l).1.val.2.1.val)) →
      (∀l,frozenCoefficient (firstIndex l).2.val
        (geometryColumnIdeal reflected s R seed (Z^Dfirst) Z ξ hK bin (firstIndex l).1.val) R s.ν s.W s.P≠0) →
      let Index := (l : Label)×GeometryLowSecondIndex reflected s R seed Z Dfirst a ξ reserve b t N hZ bin (firstIndex l)
      let datum := fun q : Index=>geometryLowSecondDatum reflected s R seed Z Dfirst a ξ reserve b t N hZ bin
        (firstIndex q.1) hs₁ hs₂ q.2
      ∀(rows : Finset (secondLiveRows (fun q=>(datum q).block)))(second : Bool)(W : 𝓢(ℝ,ℂ))
        (height : rows→ℝ)(Ds : rows→Finset (Ideal O))(control B₁ B₂ v externalHeight t₀ u : ℝ),
      0 ≤ externalHeight → 0 ≤ control → 0 ≤ B₁ → 0 ≤ B₂ →
      (∀x,‖s.W₁ x‖ ≤ B₁) → (∀x,‖s.W₂ x‖ ≤ B₂) → (B₁*B₂)^2 ≤ control →
      (∀r : rows,∀L∈Ds r,L∈(datum r.val.val.1).block.divisors ∧ Squarefree L) →
      let cost := fun r : rows=>geometryFirstHighMass reflected s R seed W Dfirst Z ξ εmass hK bin
        (firstIndex r.val.val.1.1).1.val *
        ((datum r.val.val.1).K/volume (geometryLowFirstChild reflected s R seed (Z^Dfirst) Z ξ hK bin t
          (firstIndex r.val.val.1.1)))*
        normalizer (datum r.val.val.1).C (datum r.val.val.1).D (datum r.val.val.1).inactive/lowerFactor N lo ap*
        highNormalizedRowCost second datum r.val (height r) (Ds r)
      (2*(1+|v|+externalHeight+2*Real.pi*(|t₀|+|u|)) ≤ Z^τ →
        (∑r : rows,cost r) ≤ Csmall*control*
          geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*Z^target*
          (2*(1+|v|+externalHeight+2*Real.pi*(|t₀|+|u|)))^smallDegree) →
      (∑r : rows,cost r) ≤ K*control*
        geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*Z^target*
        (1+|v|+externalHeight)^degree*(1+|t₀|)^degree*(1+|u|)^degree


end
end OAI.SevenEighths.MainPhysical


