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

omit [DecidableEq α] in
/-- The full selected first family is split by ONE global projector union.
No second row or zero-bin selector is involved in this disintegration. -/
theorem actual_main_low_first_shell_sum {Label : Type*} [Fintype Label]
    (reflected : Bool) (s : Input α) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed K Z ξ hK bin)
    (cost : Label→ℝ) :
    (∑l,cost l)=
      ∑n∈selectedShells (selectedFirstProjectors (fun l=>(firstIndex l).1.val)),
        ∑l : SelectedFirstShell (fun l=>(firstIndex l).1.val) n,cost l.val := by
  exact selected_first_shell_sum (fun l=>(firstIndex l).1.val)
    (fun l=>actual_first_live_squarefree _ _ _ (firstIndex l).1.property) cost

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

/-- Constants for the shared first shell and the selected first-child
source cap are saved before all source labels, allocations and shifts. -/
theorem eventual_actual_main_low_first_bindings (N : ℕ) (U εshell b bs loss : ℝ)
    (hU : 0≤U) (hεshell : 0<εshell) (hb : 1≤b) (hbs : 1≤bs) (hloss : 0<loss) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀{ι : Type}{Label : Type*}[Fintype ι][DecidableEq ι][Fintype Label]
        (reflected : Bool)(s : Input ι)(R seed : Ideal O)(K ξ Bvolume t : ℝ)(hK : 0<K),
      Fintype.card ι≤N → Endpoints b bs bs s → volume s≤Z^Bvolume →
      (∀j I,I∈s.pools j→(I.absNorm:ℝ)≤Z^U) →
      ∀(bin : ℤ×(Fin 5→ℤ))
        (firstIndex : Label→GeometryLowFirstIndex reflected s R seed K Z ξ hK bin),
      (∀l,frozenCoefficient (firstIndex l).2.val
        (geometryColumnIdeal reflected s R seed K Z ξ hK bin (firstIndex l).1.val)
        R s.ν s.W s.P≠0) →
      ((selectedShells (selectedFirstProjectors (fun l=>(firstIndex l).1.val))).card:ℝ)≤C*Z^εshell ∧
      (∀n∈selectedShells (selectedFirstProjectors (fun l=>(firstIndex l).1.val)),
        1≤dyadicScale n ∧ dyadicScale n≤Z^(((N:ℝ)+2)*U)) ∧
      (∀l,sourceRadius (geometryLowFirstChild reflected s R seed K Z ξ hK bin t
        (firstIndex l))≤Z^(Bvolume+loss)) := by
  obtain ⟨C,hC,hcount⟩:=eventual_actual_geometry_selected_first_shell_subpower N U εshell hU hεshell
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount,eventual_geometry_child_source_cap N b bs loss hb hbs hloss]
    with Z hshell hchild
  refine ⟨hshell.1,?_⟩
  intro ι Label _ _ _ reflected s R seed K ξ Bvolume t hK hn hend hvol hpool bin firstIndex hf
  refine ⟨hshell.2 s hn hpool R seed K ξ hK bin (fun l=>(firstIndex l).1.val),?_,?_⟩
  · intro n hn'
    exact actual_geometry_selected_first_shell_scale s N R seed K Z ξ U hK
      hn hshell.1.le hU hpool bin (fun l=>(firstIndex l).1.val) n hn'
  · intro l
    exact hchild.2 s Bvolume hn hend hvol
      (geometryColumnIdeal reflected s R seed K Z ξ hK bin (firstIndex l).1.val)
      R (firstIndex l).2
      (geometryColumnCharacter reflected s R seed K Z ξ hK bin (firstIndex l).1.val) t (hf l)

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

/-- The existing saved-label/projector dictionary specialized to the
literal selected first family. Its inverse retains the actual allocator. -/
abbrev MainLowSavedFirstPair {Label : Type*} [Fintype Label]
    (reflected : Bool) (s : Input α) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed K Z ξ hK bin) :=
  SelectedLowFirstPair
    (fun j=>geometryFirstLabel s R seed K Z ξ hK bin (firstIndex j).1.val)
    (fun j=>(firstIndex j).1.val.2.1.val)

def mainLowSavedFirstOriginal {Label : Type*} [Fintype Label]
    (reflected : Bool) (s : Input α) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed K Z ξ hK bin)
    (hinj : Function.Injective (fun j=>(geometryFirstLabel s R seed K Z ξ hK bin
      (firstIndex j).1.val,(firstIndex j).1.val.2.1.val)))
    (pair : MainLowSavedFirstPair reflected s R seed K Z ξ hK bin firstIndex) : Label :=
  (selectedLowFirstPairEquiv
    (fun j=>geometryFirstLabel s R seed K Z ξ hK bin (firstIndex j).1.val)
    (fun j=>(firstIndex j).1.val.2.1.val) hinj).symm pair

omit [DecidableEq α] in
theorem actual_main_low_saved_first_original_fields {Label : Type*} [Fintype Label]
    (reflected : Bool) (s : Input α) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed K Z ξ hK bin)
    (hinj : Function.Injective (fun j=>(geometryFirstLabel s R seed K Z ξ hK bin
      (firstIndex j).1.val,(firstIndex j).1.val.2.1.val)))
    (pair : MainLowSavedFirstPair reflected s R seed K Z ξ hK bin firstIndex) :
    let j:=mainLowSavedFirstOriginal reflected s R seed K Z ξ hK bin firstIndex hinj pair
    geometryFirstLabel s R seed K Z ξ hK bin (firstIndex j).1.val=pair.1.val ∧
      (firstIndex j).1.val.2.1.val=pair.2.val :=
  selected_low_pair_inverse_fields _ _ hinj pair

omit [DecidableEq α] in
/-- The recovered allocation has the original frozen coefficient support.
Its choice precedes every second label and the complete frequency sum. -/
theorem actual_main_low_saved_first_allocation {Label : Type*} [Fintype Label]
    (reflected : Bool) (s : Input α) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed K Z ξ hK bin)
    (hinj : Function.Injective (fun j=>(geometryFirstLabel s R seed K Z ξ hK bin
      (firstIndex j).1.val,(firstIndex j).1.val.2.1.val)))
    (hf : ∀j,frozenCoefficient (firstIndex j).2.val
      (geometryColumnIdeal reflected s R seed K Z ξ hK bin (firstIndex j).1.val)
      R s.ν s.W s.P≠0)
    (pair : MainLowSavedFirstPair reflected s R seed K Z ξ hK bin firstIndex) :
    let j:=mainLowSavedFirstOriginal reflected s R seed K Z ξ hK bin firstIndex hinj pair
    frozenCoefficient (firstIndex j).2.val
      (geometryColumnIdeal reflected s R seed K Z ξ hK bin (firstIndex j).1.val)
      R s.ν s.W s.P≠0 := hf _

omit [DecidableEq α] in
/-- Reindex complete second-label costs using the existing occupied-pair
bijection. This keeps the selected first allocation and every child label,
and charges no first-label cardinality. -/
theorem actual_main_low_saved_first_cost_reindex {Label : Type*} [Fintype Label]
    (reflected : Bool) (s : Input α) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed K Z ξ hK bin)
    (hinj : Function.Injective (fun j=>(geometryFirstLabel s R seed K Z ξ hK bin
      (firstIndex j).1.val,(firstIndex j).1.val.2.1.val)))
    (children : Label→Finset FirstSourceLabel) (cost : Label→FirstSourceLabel→ℝ) :
    let first:=fun j=>geometryFirstLabel s R seed K Z ξ hK bin (firstIndex j).1.val
    let projector:=fun j=>(firstIndex j).1.val.2.1.val
    (∑j,∑v∈children j,cost j v)=
      ∑l : selectedLowFirstLabels first,
        ∑D : selectedLowFirstProjectors first projector l.val,
          ∑v∈children (mainLowSavedFirstOriginal reflected s R seed K Z ξ hK bin firstIndex
            hinj ⟨l,D⟩),
            cost (mainLowSavedFirstOriginal reflected s R seed K Z ξ hK bin firstIndex hinj ⟨l,D⟩) v :=
  selected_low_first_cost_reindex _ _ hinj children cost

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
      1≤Z → targetMin≤target → 0≤height → 0≤Cs → 0≤Cc → 0≤control →
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

private lemma low_coarse_cost_association (m k n l q : ℝ) :
    m*k*n/l*q=m*(k*n/l)*q := by ring

private lemma low_side_control_association (C P control X H E : ℝ)
    (h : E≤C*control*P*X*H) : E≤C*(control*P)*X*H := by
  convert h using 1; ring

/-- Literal complete selected-family costs, with only the pending bounded-height
low estimate explicit. The moving target is kept at its exact value. -/
def MainLowAllHeightSpec {α : Type}[Fintype α][DecidableEq α]
    (N degree smallDegree : ℕ) (B Cs b bs window plainCap lo ap εmass ξ U targetMin τ Csmall K Z : ℝ) : Prop :=
∀target : ℝ,targetMin≤target → ∀hZ : 1<Z,
      ∀{Label : Type}[Fintype Label]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)(Dfirst a reserve t : ℝ)(hK : 0<Z^Dfirst),
      Squarefree seed → Endpoints b bs bs s →
      lo≤s.lower → sourceRadius s≤Z^B → |Real.logb Z (volume s)|≤B → |Dfirst|≤B →
      |a|≤B → |frequencyLoss Z 32 ξ+reserve|≤B → (∀j,s.M j≤Cs) →
      (∀j,CenteredMomentSlotRatios.logWindow (s.lo j) (s.hi j)≤window) →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j≤Z^plainCap) →
      (∀j,s.P j≤Z^plainCap) →
      (∀i I,I∈s.pools i→(I.absNorm:ℝ)≤Z^U) →
      (∀x,s.W₁ x≠0→ap≤x) → (∀x,s.W₂ x≠0→ap≤x) →
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),0≤a → 0≤reserve →
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
      0≤externalHeight → 0≤control → 0≤B₁ → 0≤B₂ →
      (∀x,‖s.W₁ x‖≤B₁) → (∀x,‖s.W₂ x‖≤B₂) → (B₁*B₂)^2≤control →
      (∀r : rows,∀L∈Ds r,L∈(datum r.val.val.1).block.divisors ∧ Squarefree L) →
      let cost := fun r : rows=>geometryFirstHighMass reflected s R seed W Dfirst Z ξ εmass hK bin
        (firstIndex r.val.val.1.1).1.val *
        ((datum r.val.val.1).K/volume (geometryLowFirstChild reflected s R seed (Z^Dfirst) Z ξ hK bin t
          (firstIndex r.val.val.1.1)))*
        normalizer (datum r.val.val.1).C (datum r.val.val.1).D (datum r.val.val.1).inactive/lowerFactor N lo ap*
        highNormalizedRowCost second datum r.val (height r) (Ds r)
      (2*(1+|v|+externalHeight+2*Real.pi*(|t₀|+|u|))≤Z^τ →
        (∑r : rows,cost r)≤Csmall*control*
          geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*Z^target*
          (2*(1+|v|+externalHeight+2*Real.pi*(|t₀|+|u|)))^smallDegree) →
      (∑r : rows,cost r)≤K*control*
        geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*Z^target*
        (1+|v|+externalHeight)^degree*(1+|t₀|)^degree*(1+|u|)^degree

/-- Join a bounded-height low estimate to the genuine all-projector coarse
source theorem. Constants precede moving sources, rows, and both shifts.
The physical outer factor is derived from an occupied original first column;
empty row families vanish. Both Mellin polynomial powers remain separate. -/
theorem actual_main_low_all_height_splice {α : Type}[Fintype α][DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (N : ℕ)(hα : Fintype.card α≤N)
    (targetMin τ : ℝ)(hτ : 0<τ)(smallDegree : ℕ)(Csmall : ℝ)(hsmallC : 0<Csmall)
    (B loss ε pad Cs b bs window plainCap lo ap εvolume εmass ξ U : ℝ)
    (hB : 0≤B)(hloss : 0<loss)(hε : 0<ε)(hpad : 0<pad)
    (hCs : 1≤Cs)(hb : 1≤b)(hbs : 1≤bs)(hwindow : 0≤window)(hcap : 0≤plainCap)
    (hlo : 0<lo)(hap : 0<ap)(hev : 0<εvolume)(hem : 0≤εmass)
    (hξ : 0≤ξ)(hξε : ξ≤loss)(hU : 0≤U) :
    ∃degree : ℕ,∃K : ℝ,0<K ∧ ∀ᶠ Z : ℝ in atTop,
      MainLowAllHeightSpec (α:=α) N degree smallDegree B Cs b bs window plainCap lo ap εmass ξ U targetMin τ Csmall K Z := by
  let coarse := B+(39*(B+loss)+(B+loss)*εmass+(B+loss)*ε+εvolume)+
    8*(B+loss)+3*loss+((N:ℝ)+2)*plainCap+2*pad+3*(((N:ℝ)+2)*U)*ε
  let Cside := geometrySupportConstant N lo ap ap
  have hside : 0<Cside := geometrySupportConstant_pos N lo ap ap hlo hap hap
  obtain ⟨Kc,hKc,hcoarse⟩ := actual_geometry_main_all_projector_coarse_family
    η₀ u₀ F₀ R₀ hu₀ N hα B loss ε pad Cs b bs window plainCap lo ap εvolume εmass ξ U
    hB hloss hε hpad hCs hb hbs hwindow hcap hlo hap hev hem hξ hξε hU
  obtain ⟨degree,hext⟩ := geometry_uniform_shifted_height_splice (coarse+B) targetMin τ hτ smallDegree
  have hfinal : 0<(2+4*Real.pi)^degree*(Csmall+Kc*(1+Cside⁻¹^2)) := by positivity
  refine ⟨degree,(2+4*Real.pi)^degree*(Csmall+Kc*(1+Cside⁻¹^2)),hfinal,?_⟩
  filter_upwards [hcoarse] with Z hc
  unfold MainLowAllHeightSpec
  intro target htarget hZ Label _ reflected s R seed Dfirst a reserve t hKfirst hseed he hlow hsource hA hMbox habox hω
    hM hwin hscales hP hpool hsap₁ hsap₂ hs₁ hs₂ ha hreserve bin firstIndex hinj halloc Index datum
    rows second W height Ds control B₁ B₂ v externalHeight t₀ u hh hcontrol hB₁ hB₂ hW₁ hW₂ hcontrolB hDs cost hsmall
  classical
  have hphysical : 0≤geometryHighFactor reflected Cside bin :=
    (geometry_high_factor_pos reflected Cside bin hside).le
  by_cases hr : rows.Nonempty
  · obtain ⟨r,hr⟩ := hr
    let l : Label := r.val.1.1
    have hunit := actual_geometry_coarse_side_unit reflected Cside hside s R seed
      (Z^Dfirst) Z ξ B hZ.le hB hseed hs₁ hs₂ hsource bin (firstIndex l).1.val.1
    have hraw := hc hZ reflected s R seed Dfirst a reserve t hKfirst hseed he hlow hsource hA hMbox habox hω
      hM hwin hscales hP hpool hsap₁ hsap₂ hs₁ hs₂ ha hreserve bin (fun l=>(firstIndex l).1) hinj (fun l=>(firstIndex l).2) halloc
      rows second W height Ds control B₁ B₂ hcontrol hB₁ hB₂ hW₁ hW₂ hcontrolB hDs
    have hraw' : (∑r : rows,cost r)≤Kc*control*Z^coarse := by
      convert hraw using 1
      apply Finset.sum_congr rfl
      intro r _
      exact low_coarse_cost_association _ _ _ _ _
    have hpaid := geometry_coarse_side_bound reflected Cside Z B coarse (∑r : rows,cost r)
      Kc control bin (zero_lt_one.trans hZ) hKc.le hcontrol hunit hraw'
    have hs : 2*(1+|v|+externalHeight+2*Real.pi*(|t₀|+|u|))≤Z^τ →
        (∑r : rows,cost r)≤Csmall*(control*geometryHighFactor reflected Cside bin)*Z^target*
          (2*(1+|v|+externalHeight+2*Real.pi*(|t₀|+|u|)))^smallDegree := by
      intro h
      exact low_side_control_association _ _ _ _ _ _ (hsmall h)
    have hb : (∑r : rows,cost r)≤(Kc*(1+Cside⁻¹^2))*
        (control*geometryHighFactor reflected Cside bin)*Z^(coarse+B) := by
      convert hpaid using 1; ring
    have hout := hext Z target v externalHeight t₀ u (∑r : rows,cost r) Csmall
      (Kc*(1+Cside⁻¹^2)) (control*geometryHighFactor reflected Cside bin)
      hZ.le htarget hh hsmallC.le (by positivity) (mul_nonneg hcontrol hphysical) hs hb
    convert hout using 1; ring
  · have hzero : (∑r : rows,cost r)=0 := by
      apply Finset.sum_eq_zero
      intro r _
      exact False.elim (hr ⟨r.val,r.property⟩)
    rw [hzero]
    have hz := Real.rpow_nonneg (zero_lt_one.trans hZ).le target
    have hv := pow_nonneg (add_nonneg (add_nonneg zero_le_one (abs_nonneg v)) hh) degree
    have ht := pow_nonneg (add_nonneg zero_le_one (abs_nonneg t₀)) degree
    have hu := pow_nonneg (add_nonneg zero_le_one (abs_nonneg u)) degree
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg hfinal.le hcontrol) hphysical) hz) hv) ht) hu

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_main_low_first_source_gates
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_main_low_first_shell_sum
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_main_low_first_shell_restriction
#print axioms OAI.SevenEighths.Cycle63InitialMass.eventual_actual_main_low_first_bindings
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_main_low_saved_first_cost_reindex
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_main_low_saved_first_original_fields
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_main_low_saved_first_allocation
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_main_low_first_shell_scalar_gates

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_main_low_all_height_splice

#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_uniform_shifted_height_splice
