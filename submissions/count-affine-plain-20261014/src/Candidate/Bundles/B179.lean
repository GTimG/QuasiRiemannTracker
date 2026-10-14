/- Cycle61 successor parameter adaptation by Zhongpai Gao, with AI assistance. Nominal θ=4374299/5000000, q=67/100; exact reserves and actual source consumers are changed by scoped ownership maps. Original notices/provenance remain intact. Full source replay and independent verification are pending. -/
/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B109
import Candidate.Bundles.B117
import Candidate.Bundles.B125
import Candidate.Bundles.B135
import Candidate.Bundles.B165
import Candidate.Bundles.B166
import Candidate.Bundles.B167
import Candidate.Bundles.B171
import Candidate.Bundles.B176
import Candidate.Bundles.B178
import OAI.NumberTheory.DirichletL.Moments.FirstChildProfileControl

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainLowNormalizedPayment; sha256 08628d88ecd6c38fa74340f3058f64f2a11ef32fb99dafbfbe228fc8cc29d8de -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                          
                                                            
                                                          
                                                      
                                                             
                                                         
                                                            

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentCanonicalFirst
open CenteredMomentSectorLocalization CenteredMomentSourceRow
open CenteredMomentWholeDivisorShell CenteredMomentLogDyadic
open CenteredMomentCommonProfile Cycle61Moment
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
    (reflected : Bool) (s : Input α) (R seed : Ideal O) (K Z ξ B : ℝ) (hK : 0< K)
    (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤ Z^B) (bin : ℤ×(Fin 5→ℤ))
    (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed K Z ξ hK bin) :
    ∀l,
      let first:=geometryFirstLabel s R seed K Z ξ hK bin (firstIndex l).1.val
      Supported first.1.1 ∧ Supported first.1.2 ∧
      primeSupport first.1.1=primeSupport first.1.2 ∧
      seed∣first.1.1 ∧ seed∣first.1.2 ∧
      (first.1.1.absNorm:ℝ)≤ Z^B ∧ (first.1.2.absNorm:ℝ)≤ Z^B ∧
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
    (reflected : Bool) (s : Input α) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0< K)
    (bin : ℤ×(Fin 5→ℤ))
    (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed K Z ξ hK bin)
    (cost : Label→ℝ) :
    (∑l,cost l)=
      ∑n∈selectedShells (selectedFirstProjectors (fun l=>(firstIndex l).1.val)),
        ∑l : SelectedFirstShell (fun l=>(firstIndex l).1.val) n,cost l.val := by
  exact selected_first_shell_sum (fun l=>(firstIndex l).1.val)
    (fun l=>actual_first_live_squarefree _ _ _ (firstIndex l).1.property) cost

/-- Restriction to a shared first shell preserves the exact selected
allocation, arithmetic-label/projector injection and original support gates. -/
theorem actual_main_low_first_shell_restriction {Label : Type*} [Fintype Label]
    (reflected : Bool) (s : Input α) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0< K)
    (bin : ℤ×(Fin 5→ℤ))
    (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed K Z ξ hK bin)
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
    (hU : 0≤ U) (hεshell : 0<εshell) (hb : 1≤ b) (hbs : 1≤ bs) (hloss : 0< loss) :
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
      ∀{ι : Type}{Label : Type*}[Fintype ι][DecidableEq ι][Fintype Label]
        (reflected : Bool)(s : Input ι)(R seed : Ideal O)(K ξ Bvolume t : ℝ)(hK : 0< K),
      Fintype.card ι≤ N → Endpoints b bs bs s → volume s≤ Z^Bvolume →
      (∀j I,I∈s.pools j→(I.absNorm:ℝ)≤ Z^U) →
      ∀(bin : ℤ×(Fin 5→ℤ))
        (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed K Z ξ hK bin),
      (∀l,frozenCoefficient (firstIndex l).2.val
        (geometryColumnIdeal reflected s R seed K Z ξ hK bin (firstIndex l).1.val)
        R s.ν s.W s.P≠0) →
      ((selectedShells (selectedFirstProjectors (fun l=>(firstIndex l).1.val))).card:ℝ)≤ C*Z^εshell ∧
      (∀n∈selectedShells (selectedFirstProjectors (fun l=>(firstIndex l).1.val)),
        1≤ dyadicScale n ∧ dyadicScale n≤ Z^(((N:ℝ)+2)*U)) ∧
      (∀l,sourceRadius (geometryLowFirstChild reflected s R seed K Z ξ hK bin t
        (firstIndex l))≤ Z^(Bvolume+loss)) := by
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
    (reflected : Bool) (s : Input α) (R seed : Ideal O) (K Z ξ B A : ℝ) (hK : 0< K)
    (hZ : 2≤ Z) (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤ Z^B) (bin : ℤ×(Fin 5→ℤ))
    (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed K Z ξ hK bin)
    (n : ℤ) (hn : n∈selectedShells (selectedFirstProjectors (fun l=>(firstIndex l).1.val))) :
    let w:=Real.logb Z 2
    let c : Fin 5:=if reflected then 1 else 0
    let p:=((bin.2 2:ℝ)+1)*w
    let exponent:=A-(bin.2 c:ℝ)*w+((bin.2 3:ℝ)+1)*w+((bin.2 4:ℝ)+1)*w
    let sideLower:=(bin.2 2:ℝ)*w+A-((bin.2 c:ℝ)+1)*w+
      (bin.2 3:ℝ)*w+(bin.2 4:ℝ)*w
    p≤ B+1 ∧ p+exponent-sideLower=4*w ∧
    ∀l : SelectedFirstShell (fun l=>(firstIndex l).1.val) n,
      let first:=geometryFirstLabel s R seed K Z ξ hK bin (firstIndex l.val).1.val
      ((commonRadical first.1.1 first.1.2).absNorm:ℝ)≤ Z^p ∧
      lowGeometryExponent reflected Z A first≤ exponent ∧
      sideLower≤ geometryHighSide reflected A
        (geometryExponents s R seed K Z ξ (firstIndex l.val).1.val.1.val) := by
  intro w c p exponent sideLower
  obtain ⟨D,hD⟩ := (shell_nonempty_iff _ n).mpr hn
  have hmem:=(shell_member_data _ n D hD).1
  rw [selected_first_projectors_eq_image] at hmem
  obtain ⟨j,_,_⟩:=Finset.mem_image.mp hmem
  have hp:=actual_geometry_low_bin_radical_exponent_cap s R seed K Z ξ B hZ
    hs hz₁ hz₂ hsource bin (firstIndex j).1.val.1
  have hZ1 : 1< Z := by linarith
  have hg:=actual_geometry_low_bin_scalar_gates s R seed K Z ξ B A hK hZ1
    hs hz₁ hz₂ hsource bin reflected
  exact ⟨hp,hg.1,fun l=>hg.2 (firstIndex l.val).1.val⟩

/-- The existing saved-label/projector dictionary specialized to the
literal selected first family. Its inverse retains the actual allocator. -/
abbrev MainLowSavedFirstPair {Label : Type*} [Fintype Label]
    (reflected : Bool) (s : Input α) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0< K)
    (bin : ℤ×(Fin 5→ℤ))
    (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed K Z ξ hK bin) :=
  SelectedLowFirstPair
    (fun j=>geometryFirstLabel s R seed K Z ξ hK bin (firstIndex j).1.val)
    (fun j=>(firstIndex j).1.val.2.1.val)

def mainLowSavedFirstOriginal {Label : Type*} [Fintype Label]
    (reflected : Bool) (s : Input α) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0< K)
    (bin : ℤ×(Fin 5→ℤ))
    (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed K Z ξ hK bin)
    (hinj : Function.Injective (fun j=>(geometryFirstLabel s R seed K Z ξ hK bin
      (firstIndex j).1.val,(firstIndex j).1.val.2.1.val)))
    (pair : MainLowSavedFirstPair reflected s R seed K Z ξ hK bin firstIndex) : Label :=
  (selectedLowFirstPairEquiv
    (fun j=>geometryFirstLabel s R seed K Z ξ hK bin (firstIndex j).1.val)
    (fun j=>(firstIndex j).1.val.2.1.val) hinj).symm pair

omit [DecidableEq α] in
theorem actual_main_low_saved_first_original_fields {Label : Type*} [Fintype Label]
    (reflected : Bool) (s : Input α) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0< K)
    (bin : ℤ×(Fin 5→ℤ))
    (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed K Z ξ hK bin)
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
    (reflected : Bool) (s : Input α) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0< K)
    (bin : ℤ×(Fin 5→ℤ))
    (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed K Z ξ hK bin)
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
    (reflected : Bool) (s : Input α) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0< K)
    (bin : ℤ×(Fin 5→ℤ))
    (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed K Z ξ hK bin)
    (hinj : Function.Injective (fun j=>(geometryFirstLabel s R seed K Z ξ hK bin
      (firstIndex j).1.val,(firstIndex j).1.val.2.1.val)))
    (children : Label→ Finset FirstSourceLabel) (cost : Label→ FirstSourceLabel→ℝ) :
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
open CenteredMomentCommonProfile Cycle61Moment
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
      1≤ Z → targetMin≤ target → 0≤ height → 0≤ Cs → 0≤ Cc → 0≤ control →
      (2*(1+|v|+height+2*Real.pi*(|t|+|u|))≤ Z^τ →
        E≤ Cs*control*Z^target*(2*(1+|v|+height+2*Real.pi*(|t|+|u|)))^smallDegree) →
      E≤ Cc*control*Z^coarse →
      E≤(2+4*Real.pi)^degree*(Cs+Cc)*control*Z^target*
        (1+|v|+height)^degree*(1+|t|)^degree*(1+|u|)^degree := by
  obtain ⟨n,hn⟩ := geometry_large_height_absorption coarse targetMin τ hτ
  refine ⟨max n smallDegree,?_⟩
  intro Z target v height t u E Cs Cc control hZ htarget hh hCs hCc hc hs hb
  let H := 2*(1+|v|+height+2*Real.pi*(|t|+|u|))
  have hH : 1≤ H := by
    dsimp [H]
    have hp : 0≤2*Real.pi*(|t|+|u|) := by positivity
    linarith [abs_nonneg v]
  have hraw : E≤(Cs+Cc)*control*Z^target*H^(max n smallDegree) := by
    by_cases h : H≤ Z^τ
    · apply (hs h).trans
      apply mul_le_mul
      · gcongr; linarith
      · exact pow_le_pow_right₀ hH (le_max_right _ _)
      · positivity
      · positivity
    · have hscale := hn Z H hZ (le_of_lt (lt_of_not_ge h))
      have hz := Real.rpow_le_rpow_of_exponent_le hZ htarget
      calc
        E≤ Cc*control*Z^coarse := hb
        _≤ Cc*control*(Z^targetMin*H^n) := mul_le_mul_of_nonneg_left hscale (mul_nonneg hCc hc)
        _≤ Cc*control*(Z^target*H^(max n smallDegree)) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCc hc)
          exact mul_le_mul hz (pow_le_pow_right₀ hH (le_max_left _ _)) (by positivity) (by positivity)
        _≤(Cs+Cc)*control*Z^target*H^(max n smallDegree) := by
          rw [←mul_assoc]
          gcongr
          linarith
  apply hraw.trans
  have hp := pow_le_pow_left₀ (by positivity : 0≤ H)
    (geometry_shifted_height_product v height t u hh) (max n smallDegree)
  have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0≤(Cs+Cc)*control*Z^target)
  simpa only [mul_pow,mul_assoc,mul_left_comm,mul_comm] using hm

private lemma low_coarse_cost_association (m k n l q : ℝ) :
    m*k*n/l*q=m*(k*n/l)*q := by ring

private lemma low_side_control_association (C P control X H E : ℝ)
    (h : E≤ C*control*P*X*H) : E≤ C*(control*P)*X*H := by
  convert h using 1; ring

/-- Literal complete selected-family costs, with only the pending bounded-height
low estimate explicit. The moving target is kept at its exact value. -/
def MainLowAllHeightSpec {α : Type}[Fintype α][DecidableEq α]
    (N degree smallDegree : ℕ) (B Cs b bs window plainCap lo ap εmass ξ U targetMin τ Csmall K Z : ℝ) : Prop :=
∀target : ℝ,targetMin≤ target → ∀hZ : 1< Z,
      ∀{Label : Type}[Fintype Label]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)(Dfirst a reserve t : ℝ)(hK : 0< Z^Dfirst),
      Squarefree seed → Endpoints b bs bs s →
      lo≤ s.lower → sourceRadius s≤ Z^B → |Real.logb Z (volume s)|≤ B → |Dfirst|≤ B →
      |a|≤ B → |frequencyLoss Z 32 ξ+reserve|≤ B → (∀j,s.M j≤ Cs) →
      (∀j,CenteredMomentSlotRatios.logWindow (s.lo j) (s.hi j)≤ window) →
      (∀second j,Cycle61.Physical.sourcePlainScales s.toData.toSource second j≤ Z^plainCap) →
      (∀j,s.P j≤ Z^plainCap) →
      (∀i I,I∈s.pools i→(I.absNorm:ℝ)≤ Z^U) →
      (∀x,s.W₁ x≠0→ ap≤ x) → (∀x,s.W₂ x≠0→ ap≤ x) →
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),0≤ a → 0≤ reserve →
      ∀(bin : ℤ×(Fin 5→ℤ))
        (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed (Z^Dfirst) Z ξ hK bin),
      Function.Injective (fun l=>(geometryFirstLabel s R seed (Z^Dfirst) Z ξ hK bin (firstIndex l).1.val,
        (firstIndex l).1.val.2.1.val)) →
      (∀l,frozenCoefficient (firstIndex l).2.val
        (geometryColumnIdeal reflected s R seed (Z^Dfirst) Z ξ hK bin (firstIndex l).1.val) R s.ν s.W s.P≠0) →
      let Index := (l : Label)×GeometryLowSecondIndex reflected s R seed Z Dfirst a ξ reserve b t N hZ bin (firstIndex l)
      let datum := fun q : Index=>geometryLowSecondDatum reflected s R seed Z Dfirst a ξ reserve b t N hZ bin
        (firstIndex q.1) hs₁ hs₂ q.2
      ∀(rows : Finset (secondLiveRows (fun q=>(datum q).block)))(second : Bool)(W : 𝓢(ℝ,ℂ))
        (height : rows→ℝ)(Ds : rows→ Finset (Ideal O))(control B₁ B₂ v externalHeight t₀ u : ℝ),
      0≤ externalHeight → 0≤ control → 0≤ B₁ → 0≤ B₂ →
      (∀x,‖s.W₁ x‖≤ B₁) → (∀x,‖s.W₂ x‖≤ B₂) → (B₁*B₂)^2≤ control →
      (∀r : rows,∀L∈Ds r,L∈(datum r.val.val.1).block.divisors ∧ Squarefree L) →
      let cost := fun r : rows=>geometryFirstHighMass reflected s R seed W Dfirst Z ξ εmass hK bin
        (firstIndex r.val.val.1.1).1.val *
        ((datum r.val.val.1).K/volume (geometryLowFirstChild reflected s R seed (Z^Dfirst) Z ξ hK bin t
          (firstIndex r.val.val.1.1)))*
        normalizer (datum r.val.val.1).C (datum r.val.val.1).D (datum r.val.val.1).inactive/lowerFactor N lo ap*
        highNormalizedRowCost second datum r.val (height r) (Ds r)
      (2*(1+|v|+externalHeight+2*Real.pi*(|t₀|+|u|))≤ Z^τ →
        (∑r : rows,cost r)≤ Csmall*control*
          geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*Z^target*
          (2*(1+|v|+externalHeight+2*Real.pi*(|t₀|+|u|)))^smallDegree) →
      (∑r : rows,cost r)≤ K*control*
        geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*Z^target*
        (1+|v|+externalHeight)^degree*(1+|t₀|)^degree*(1+|u|)^degree

set_option maxHeartbeats 40000 in
/-- Join a bounded-height low estimate to the genuine all-projector coarse
source theorem. Constants precede moving sources, rows, and both shifts.
The physical outer factor is derived from an occupied original first column;
empty row families vanish. Both Mellin polynomial powers remain separate. -/
theorem actual_main_low_all_height_splice {α : Type}[Fintype α][DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (N : ℕ)(hα : Fintype.card α≤ N)
    (targetMin τ : ℝ)(hτ : 0<τ)(smallDegree : ℕ)(Csmall : ℝ)(hsmallC : 0< Csmall)
    (B loss ε pad Cs b bs window plainCap lo ap εvolume εmass ξ U : ℝ)
    (hB : 0≤ B)(hloss : 0< loss)(hε : 0<ε)(hpad : 0< pad)
    (hCs : 1≤ Cs)(hb : 1≤ b)(hbs : 1≤ bs)(hwindow : 0≤ window)(hcap : 0≤ plainCap)
    (hlo : 0< lo)(hap : 0< ap)(hev : 0<εvolume)(hem : 0≤εmass)
    (hξ : 0≤ξ)(hξε : ξ≤ loss)(hU : 0≤ U) :
    ∃degree : ℕ,∃K : ℝ,0< K ∧ ∀ᶠ Z : ℝ in atTop,
      MainLowAllHeightSpec (α:=α) N degree smallDegree B Cs b bs window plainCap lo ap εmass ξ U targetMin τ Csmall K Z := by
  let coarse := B+(39*(B+loss)+(B+loss)*εmass+(B+loss)*ε+εvolume)+
    8*(B+loss)+3*loss+((N:ℝ)+2)*plainCap+2*pad+3*(((N:ℝ)+2)*U)*ε
  let Cside := geometrySupportConstant N lo ap ap
  have hside : 0< Cside := geometrySupportConstant_pos N lo ap ap hlo hap hap
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
  have hphysical : 0≤ geometryHighFactor reflected Cside bin :=
    (geometry_high_factor_pos reflected Cside bin hside).le
  by_cases hr : rows.Nonempty
  · obtain ⟨r,hr⟩ := hr
    let l : Label := r.val.1.1
    have hunit := actual_geometry_coarse_side_unit reflected Cside hside s R seed
      (Z^Dfirst) Z ξ B hZ.le hB hseed hs₁ hs₂ hsource bin (firstIndex l).1.val.1
    have hraw := hc hZ reflected s R seed Dfirst a reserve t hKfirst hseed he hlow hsource hA hMbox habox hω
      hM hwin hscales hP hpool hsap₁ hsap₂ hs₁ hs₂ ha hreserve bin (fun l=>(firstIndex l).1) hinj (fun l=>(firstIndex l).2) halloc
      rows second W height Ds control B₁ B₂ hcontrol hB₁ hB₂ hW₁ hW₂ hcontrolB hDs
    have hraw' : (∑r : rows,cost r)≤ Kc*control*Z^coarse := by
      convert hraw using 1
      apply Finset.sum_congr rfl
      intro r _
      exact low_coarse_cost_association _ _ _ _ _
    have hpaid := geometry_coarse_side_bound reflected Cside Z B coarse (∑r : rows,cost r)
      Kc control bin (zero_lt_one.trans hZ) hKc.le hcontrol hunit hraw'
    have hs : 2*(1+|v|+externalHeight+2*Real.pi*(|t₀|+|u|))≤ Z^τ →
        (∑r : rows,cost r)≤ Csmall*(control*geometryHighFactor reflected Cside bin)*Z^target*
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
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_low_first_source_gates
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_low_first_shell_sum
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_low_first_shell_restriction
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_main_low_first_bindings
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_low_saved_first_cost_reindex
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_low_saved_first_original_fields
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_low_saved_first_allocation
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_low_first_shell_scalar_gates

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_low_all_height_splice

#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_uniform_shifted_height_splice

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainLowNormalizedPayment -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondLowSourceCaps; sha256 a12b4d86b1085af7e04982a2d4fc09fb5b6fa36d32e8351241eef45cd143521f -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                        
                                            

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily Cycle61Moment.LowBranch
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentSlotRatios
open CenteredMomentCommonProfile CenteredMomentCommonHeightEnvelope
open CenteredMomentAmplificationChildInput CenteredMomentEligibleEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open CenteredMomentDivisorRectangle CenteredMomentDivisorRaw
local notation "O" => HeckeFamily.O

/-- Taking a residual plain divisor and clipping at one cannot exceed
the corresponding original plain scale clipped at one. -/
theorem final_plain_le_original_max {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Data ι) (second : Bool) (D : Ideal O)
    (alloc : Allocation D (Finset.univ : Finset (ι⊕Fin 2))) (j : Fin 2) :
    finalPlain s second D alloc j≤ max 1 (Cycle61.Physical.sourcePlainScales s.toSource second j) := by
  have hn : (1:ℝ)≤(Ideal.absNorm (selectedPlain D alloc j):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ alloc (Sum.inr j)))
  have hx := source_plain_positive s second j
  change max 1 (Cycle61.Physical.sourcePlainScales s.toSource second j/
    (Ideal.absNorm (selectedPlain D alloc j):ℝ))≤ _
  exact max_le_max_left 1 (div_le_self hx.le hn)

/-- Both common allocations and the residual projector only shrink plain
scales. This cap holds simultaneously for every supported allocation. -/
theorem actual_two_common_final_plain_cap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (bound : ℝ) (hbound : 1≤ bound)
    (hplain : ∀side j,Cycle61.Physical.sourcePlainScales s.toData.toSource side j≤ bound)
    (C₁ R₁ : Ideal O) (B₁ : actualAllocations s.pools C₁) (χ₁ : Character) (t₁ : ℝ)
    (C₂ R₂ : Ideal O) (B₂ : actualAllocations (child s C₁ R₁ B₁ χ₁ t₁).pools C₂)
    (χ₂ : Character) (t₂ : ℝ)
    (D : Ideal O)
    (alloc : Allocation D (Finset.univ : Finset ((liveIndices B₂.val)⊕Fin 2)))
    (side : Bool) (j : Fin 2) :
    finalPlain (commonData (withHeight (child s C₁ R₁ B₁ χ₁ t₁) χ₂ t₂) C₂ R₂ B₂)
      side D alloc j≤ bound := by
  apply (final_plain_le_original_max _ side D alloc j).trans
  apply max_le hbound
  have hsecond := actual_child_plain_scale_le
    (withHeight (child s C₁ R₁ B₁ χ₁ t₁) χ₂ t₂) C₂ R₂ B₂ χ₂ t₂ side j
  have hfirst := actual_child_plain_scale_le s C₁ R₁ B₁ χ₁ t₁ side j
  exact hsecond.trans (hfirst.trans (hplain side j))

/-- The two universal input gates of the low column theorem follow from
fixed original window and plain-scale bounds, uniformly in both allocations. -/
theorem eventual_two_common_low_source_caps (N : ℕ) (window bs pad L : ℝ)
    (hwindow : 0≤ window) (hbs : 1≤ bs) (hpad : 0< pad) (hL : 0≤ L) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧
      ∀{ι : Type}[Fintype ι][DecidableEq ι](s : Input ι),
      Fintype.card ι≤ N → (∀i,logWindow (s.lo i) (s.hi i)≤ window) →
      s.b₁≤ bs → s.b₂≤ bs →
      (∀side j,Cycle61.Physical.sourcePlainScales s.toData.toSource side j≤ Z^L) →
      ∀(C₁ R₁ : Ideal O)(B₁ : actualAllocations s.pools C₁)(χ₁ : Character)(t₁ : ℝ)
        (C₂ R₂ : Ideal O)(B₂ : actualAllocations (child s C₁ R₁ B₁ χ₁ t₁).pools C₂)
        (χ₂ : Character)(t₂ : ℝ),
      let src := commonData (withHeight (child s C₁ R₁ B₁ χ₁ t₁) χ₂ t₂) C₂ R₂ B₂
      src.toSource.allowance Z≤ pad ∧
        ∀(D : Ideal O)(alloc : Allocation D (Finset.univ : Finset ((liveIndices B₂.val)⊕Fin 2)))
          (side : Bool)(j : Fin 2),finalPlain src side D alloc j≤ Z^L := by
  filter_upwards [eventual_two_common_allowance N window bs pad hwindow hbs hpad] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι _ _ s hcard hw hb₁ hb₂ hplain C₁ R₁ B₁ χ₁ t₁ C₂ R₂ B₂ χ₂ t₂ src
  have ha := hz.2 s hcard hw hb₁ hb₂ C₁ R₁ B₁ χ₁ t₁ C₂ R₂ B₂ χ₂ t₂
  have hc : 0≤ Cycle61.Physical.plainClipAllowance Z ![src.b₁,src.b₂] := by
    unfold Cycle61.Physical.plainClipAllowance
    exact Finset.sum_nonneg (fun j _=>Real.logb_nonneg hz.1 (le_max_left _ _))
  refine ⟨by linarith,?_⟩
  intro D alloc side j
  exact actual_two_common_final_plain_cap s (Z^L) (Real.one_le_rpow hz.1.le hL) hplain
    C₁ R₁ B₁ χ₁ t₁ C₂ R₂ B₂ χ₂ t₂ D alloc side j

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.final_plain_le_original_max
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_two_common_final_plain_cap

#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_two_common_low_source_caps

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondLowSourceCaps -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainLowFull; sha256 578bc1c97b3cbcdc68a7517e6bbef48475b5f0da43f8ec340c079e737d7b19a7 -/
section
                                                           
                                                       
                                                         
                                                       
                                                                   

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentSourceLiveColumn
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceMass CenteredMomentRankinRadical CenteredMomentFirstDiscardedEnergy
open CenteredMomentLogDyadic CenteredMomentWholeDivisorShell CenteredMomentSlotRatios
open CenteredMomentCommonPairedSource
open CenteredMomentFirstChildProfileControl
open Cycle61FinalNatural Cycle61Moment.LowBranch
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentCanonicalFirst
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentEligibleEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale
open CenteredMomentCommonLinearNormalization CenteredMomentSourceLiveColumn
open Cycle61Moment
open Cycle61FinalLow
open Cycle61Moment.LowBranch Cycle61FinalNatural Cycle61FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle61FinalProfiles

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal HeckeFamily.O) [NeZero M]
variable (H : Subgroup (HeckeFamily.O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

local notation "O" => HeckeFamily.O
local instance geometryMainLowFullDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

private theorem shared_squarefree_shells {Label : Type*} [Fintype Label]
    (Ds : Label→ Finset (Ideal O)) :
    selectedShells (sharedProjectors (fun l=>(Ds l).filter Squarefree))=
      selectedShells (sharedProjectors Ds) := by
  have hlive : live (sharedProjectors (fun l=>(Ds l).filter Squarefree))=
      live (sharedProjectors Ds) := by
    ext D
    simp only [mem_live,sharedProjectors,Finset.mem_biUnion,Finset.mem_univ,true_and,
      Finset.mem_filter]
    constructor
    · rintro ⟨⟨l,hl,_⟩,hm⟩
      exact ⟨⟨l,hl⟩,hm⟩
    · rintro ⟨⟨l,hl⟩,hm⟩
      exact ⟨⟨l,hl,squarefree_of_moebius_ne_zero D hm⟩,hm⟩
  exact congrArg (fun S=>S.image normKey) hlive

private theorem low_shared_shell_contraction {Label : Type*} [Fintype Label]
    (Ds : Label→ Finset (Ideal O))(hs : ∀l D,D∈Ds l→ Squarefree D)
    (cost : Label→ Ideal O→ℝ)(hc : ∀l D,0≤ cost l D)
    (factor εshell : ℝ)
    (hbound : ∀n∈selectedShells (sharedProjectors Ds),
      (∑l,∑D∈shell (sharedProjectors Ds) n,cost l D)≤
        factor*(2*dyadicScale n)^(3*εshell)) :
    (∑l,∑D∈Ds l,cost l D)≤ factor*
      (∑n∈selectedShells (sharedProjectors Ds),(2*dyadicScale n)^(3*εshell)) := by
  apply (shared_projector_shell_sum_le Ds hs cost hc).trans
  calc
    _≤∑n∈selectedShells (sharedProjectors Ds),factor*(2*dyadicScale n)^(3*εshell) :=
      Finset.sum_le_sum hbound
    _=_ := (Finset.mul_sum _ _ _).symm


theorem actual_geometry_low_second_source_caps
    (reflected : Bool)(s : Input α)(R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ)(N : ℕ)(hZ : 1< Z)(bin : ℤ×(Fin 5→ℤ))
    (j : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)
    (n : GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin j)
    (Ncap : ℕ)(hN : Fintype.card α≤ Ncap)(Y : ℝ)
    (hpool : ∀i I,I∈s.pools i→(I.absNorm:ℝ)≤ Y) :
    let datum:=geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin j hw₁ hw₂ n
    Fintype.card datum.slots≤ Ncap ∧
      (∀i I,I∈datum.input.pools i→(I.absNorm:ℝ)≤ Y) := by
  intro datum
  constructor
  · apply le_trans _ hN
    change Fintype.card (liveIndices j.2.val)≤ Fintype.card α
    simpa only [Fintype.card_coe] using Finset.card_le_univ (liveIndices j.2.val)
  · exact actual_child_pool_cap s _ R j.2 _ t Y hpool

attribute [local irreducible] geometryLowActualChain geometryLowActualGeometry geometryLowSecondDatum
attribute [-instance] geometryMainLowFullDecidable in
private theorem eventual_low_chain_source_caps (N : ℕ) (window bs pad L : ℝ)
    (hwindow : 0≤ window) (hbs : 1≤ bs) (hpad : 0< pad) (hL : 0≤ L) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧
      ∀{ι : Type}[Fintype ι][DecidableEq ι](s : Input ι),
      Fintype.card ι≤ N → (∀i,logWindow (s.lo i) (s.hi i)≤ window) →
      s.b₁≤ bs → s.b₂≤ bs →
      (∀side j,Cycle61.Physical.sourcePlainScales s.toData.toSource side j≤ Z^L) →
      ∀(q : Chain s)(B₂ : actualAllocations q.first.pools q.E₂)(χ₂ : Character)(t₂ : ℝ),
      let src:=commonData (withHeight q.first χ₂ t₂) q.E₂ q.R₂ B₂
      src.toSource.allowance Z≤ pad ∧
        ∀(D : Ideal O)(alloc : Allocation D (Finset.univ : Finset _))
          (side : Bool)(j : Fin 2),finalPlain src side D alloc j≤ Z^L := by
  filter_upwards [eventual_two_common_low_source_caps N window bs pad L hwindow hbs hpad hL] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι _ _ s hcard hw hb₁ hb₂ hplain q B₂ χ₂ t₂
  exact hz.2 s hcard hw hb₁ hb₂ hplain q.C₁ q.R₁ q.B₁ q.η₁ q.t₁ q.E₂ q.R₂ B₂ χ₂ t₂

set_option linter.defProp false in
private def lowFullDynamicSpec {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (_hA : 0< A) (_hWs : Function.support W⊆Icc A B) (_hW : ContDiff ℝ ∞ W)
    (_hB : 0≤ B) (_ha : 0< a) (_ha' : a≤1/4) (_hb : 1≤ b)
    (_hBmask : 0≤ Bmask) (_hMcap : 0< Mcap) (_hεold : 0<εold)
    (_hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (_hRw : 0≤ Rwidth) (_hdmax : 0≤ dmax) (_hτ : 0<τ) (_hε : 0<ε)
    (_he : 0< e) (_he' : e<1/1000) (_hκ : 0<κ) (_hη : 0≤η)
    (_hbudget : 8*e*Rwidth+κ≤ε) (_hmargin : 0< margin)
    (_hd : 0< d) (_hdsupply : Mcap+Bmask+margin≤ d) (_hdm : d≤ dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (_hbs : 1≤ bs) (_hew : 0<εwidth) (_hep : 0<εpad) (_hmin : 0< Mmin)
    (εshell : ℝ) (_heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(_hCs : 1≤ Cs)
    (supply εv Bnorm εlabels : ℝ)(_hsupply : 0< supply)(_hev : 0<εv)
    (_hBnorm : 0≤ Bnorm)(_hel : 0<εlabels)
    (degree : ℕ)(Sp : Finset (ℕ×ℕ))
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤ M)(Cg Z : ℝ) : Prop :=
    ∀(hZ : 1< Z)(s : Input α)(θ : α→ RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh aLow : ℝ)(i : ℕ),
      Fintype.card α≤ N → (∀j,s.M j≤ Cs) →
      supply≤ s.lower → Matches M H hH s η₀ θ w σ freq W B Z → s.η=ηseed → s.upper≤ bs → s.b₁=b → s.b₂=b →
      (∀j,0≤ w j) → (∀j,w j≤ Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      (∀j,w j/d≤ Rwidth) → 0≤ mesh → (∀j,w j≤ mesh) → (∀j,lo≤σ j) → (∀j,σ j≤ hi) →
      0≤ height → (∀j,|freq j|≤ height) → 51/100≤ aLow → aLow≤167/200 →
      |v|+height+Z^τ/2≤(3*i+2:ℕ)*Z^τ → (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^η →
    ∀(Mrow omega ξ : ℝ),Mmin≤ Mrow → 0≤ omega → 0≤ξ → Mrow+εwidth*Mrow+ξ/2≤ Mcap →
      ((17/500)*Mrow≤∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j))≤(1/25)*Mrow) →
      length Z s.X₁+length Z s.X₂+Cycle61.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤ Cycle61.Arithmetic.B*Mrow →
    ∀{Label : Type}[Fintype Label],∀(reflected second : Bool)
      (first : Label→ FirstSourceLabel)
      (_hf : ∀l,Supported (first l).1.1 ∧ Supported (first l).1.2)
      (_heq : ∀l,primeSupport (first l).1.1=primeSupport (first l).1.2)
      (Rfirst : Ideal O)
      (alloc : (l : Label)→ actualAllocations s.pools
        (if reflected then (first l).1.2 else (first l).1.1))
      (χfirst : Label→ Character)(tfirst : Label→ℝ),
    (∀l,frozenCoefficient (alloc l).val
      (if reflected then (first l).1.2 else (first l).1.1) Rfirst s.ν s.W s.P≠0) →
    let childSrc := fun l=>child s (if reflected then (first l).1.2 else (first l).1.1)
      Rfirst (alloc l) (χfirst l) (tfirst l)
    ∀(R seed : Label→ Ideal O)(K Tsec : Label→ℝ)(reserve : ℝ),
    (∀l,Squarefree (seed l)) → (∀l,(childSrc l).W₁ 0=0) → (∀l,(childSrc l).W₂ 0=0) →
    (∀l,CenteredMomentOriginalCommonHarmonic.sourceRadius (childSrc l)≤ Z^Bnorm) →
    ∀(Tfirst p exponent : ℝ),1≤ Tfirst → p≤ Bnorm →
    ∀seed₀ : Ideal O,Squarefree seed₀ → seed₀≠0 →
    Function.Injective (fun l=>(first l,seed l)) →
    (∀l,seed₀∣(first l).1.1 ∧ seed₀∣(first l).1.2) →
    (∀l,((first l).1.1.absNorm:ℝ)≤ Z^Bnorm ∧ ((first l).1.2.absNorm:ℝ)≤ Z^Bnorm) →
    (∀l,((commonRadical (first l).1.1 (first l).1.2).absNorm:ℝ)≤ Z^p) →
    (∀l,lowGeometryExponent reflected Z (Real.logb Z (volume s)) (first l)≤ exponent) →
    (∀l,Tfirst≤((seed l).absNorm:ℝ) ∧ ((seed l).absNorm:ℝ)<2*Tfirst) →
    ∀(rows : Finset ((l : Label)×ActualSecondBlockIndex (childSrc l) (R l) (seed l)
      (K l) (Tsec l) Z ξ))
      (hU : ∀r∈rows,r.2.2.1∈inactiveSubsets r.2.1.val.val.1 r.2.1.val.val.2)
      (box : Finset (Fin 4→ℤ)),
    (∀r∈rows,actualSecondDyad (childSrc r.1) (R r.1) (seed r.1)
      (K r.1) (Tsec r.1) Z ξ r.2∈box) →
    let label := fun r : rows=>actualSecondSupportedLabel (childSrc r.val.1)
      (R r.val.1) (seed r.val.1) (K r.val.1) (Tsec r.val.1) Z ξ r.val.2 (hU r.val r.property)
    let cell := Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
    let amp := Mrow*Cycle61.Arithmetic.amp cell
    ∀q : rows→ Chain s,
    ∀g : (r : rows)→ LiveMainGeometry s (q r) Z Mrow amp omega ξ bs (Fintype.card α),
    (∀r,(q r).C₁=(if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)) →
    (∀r,(g r).D₁=(if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)) →
    (∀r,(g r).datum.C=(label r).1.1) → (∀r,(g r).datum.D=(label r).1.2) →
    (∀r,HEq (g r).datum.inactive (label r).2.val) →
    (∀r,(q r).E₂=(if second then (label r).1.2 else (label r).1.1)) →
    (∀r,(g r).datum.K=firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first r.val.1)) →
    omega=frequencyLoss Z 32 ξ+reserve →
    ∀(χ : rows→ RayFourExpansion.RayCharacter)(hP : ∀r,(q r).R₂*(q r).E₂≠0)
      (hPN : ∀r,(((q r).R₂*(q r).E₂).absNorm:ℝ)≤ Z^Bmask),
    let st := fun r=>retainedState Z Bmask hZ ((g r).datum.τ (χ r)) (internalQ Q η₀)
      ((q r).R₂*(q r).E₂) (hP r) (hPN r) (g r).datum.radius (g r).datum.C (g r).datum.D (g r).datum.inactive
    let src := fun r=>withHeight (q r).first ((g r).datum.τ (χ r)) v
    ∀(divisorSeed : rows→ Ideal O)(hE₂ : ∀r,Supported (q r).E₂),(∀r,divisorSeed r∣(q r).E₂) →
    ∀(Ds : Finset (Ideal O))(T pad : ℝ),1≤ T →
      (∀D∈Ds,Squarefree D ∧ T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
    ∀p₀ : Profiles a b,s.W₁=(p₀.profile 0 : ℝ→ℂ) → s.W₂=(p₀.profile 1 : ℝ→ℂ) →
    (∀r,∀B₂ : actualAllocations (src r).pools (q r).E₂,
      commonScalar (src r) (q r).E₂ (q r).R₂ B₂≠0 →
      (commonData (src r) (q r).E₂ (q r).R₂ B₂).toSource.allowance Z≤ pad) →
    (∀r,∀B₂ : actualAllocations (src r).pools (q r).E₂,
      commonScalar (src r) (q r).E₂ (q r).R₂ B₂≠0 →
      ∀D∈Ds,∀al∈(commonData (src r) (q r).E₂ (q r).R₂ B₂).toSource.active D,∀side : Bool,
      finalPlain (commonData (src r) (q r).E₂ (q r).R₂ B₂) side D al 0≤ Z^L ∧
      finalPlain (commonData (src r) (q r).E₂ (q r).R₂ B₂) side D al 1≤ Z^L) →
    let low := fun r=>ActualLow M H hH (st r) η₀ (inf_le_left.trans hQM) inf_le_right
      aLow e (3*(i+1:ℕ)*Z^τ)
    ∀(zs : rows→ Finset O)(weight : rows→ O→ℝ),(∀r,∀z∈zs r,0≤ weight r z) →
      (∀r,∀z∈zs r,(st r).radial.keep z ∧ low r z) →
      (∀r,∀z∈zs r,weight r z≤((st r).radial.profile (‖eisEmbedding z‖^2/(st r).radial.scale)).re) →
    ∀(mass : Label→ℝ)(physical loss : ℝ),0≤ physical → (∀l,0≤ mass l) →
      (∀l,mass l≤ physical*Z^loss) →
    let c := fun r=>mass r.val.1/volume (childSrc r.val.1)*
      (g r).datum.K*normalizer (g r).datum.C (g r).datum.D (g r).datum.inactive
    let error := εwidth*Mrow+ξ/2-Mrow*(1/3750000)+εold+2*ε*d*(Fintype.card α:ℝ)+
      (2*Cycle61.Arithmetic.q0/9)*(omega+εpad*Mrow)+Cycle61.Arithmetic.q0*mesh+pad
    (∑r,c r*(∑D∈Ds,∑z∈zs r,weight r z*
      ‖normalizedColumn (src r) (q r).E₂ (hE₂ r) (q r).R₂ (divisorSeed r) D z‖^2))≤
      Cg*(2*b^2*Cs^(4*N))*QuadraticInitialBound.diagonalControl ballProfile*(p₀.control Sp)^2*
        (1+|v|+height)^degree*(2*T)^(3*εshell)*(box.card:ℝ)*physical*
        Z^(loss+amp+p+exponent+error+εv+Bnorm*εshell+εlabels)/(seed₀.absNorm:ℝ)

set_option linter.defProp false in
private def lowFullSpec {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0< A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤ B) (ha : 0< a) (ha' : a≤1/4) (hb : 1≤ b)
    (hBmask : 0≤ Bmask) (hMcap : 0< Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤ Rwidth) (hdmax : 0≤ dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0< d) (hdsupply : Mcap+Bmask+margin≤ d) (hdm : d≤ dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤ bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0< Mmin)
    (εshell : ℝ) (heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(hCs : 1≤ Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0< supply)(hev : 0<εv)
    (hBnorm : 0≤ Bnorm)(hel : 0<εlabels)
    (degree : ℕ)(Sp : Finset (ℕ×ℕ)) : Prop :=
    ∀η₀ : Character, ∀Q : Ideal O,
    ∀hQM : Q≤ M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃Cg : ℝ, 0< Cg ∧ ∀ᶠZ : ℝ in atTop,2≤ Z ∧
    lowFullDynamicSpec (α:=α) M H hH
      W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel degree Sp η₀ Q hQM Cg Z

set_option linter.defProp false in
private def lowFullKernel {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0< A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤ B) (ha : 0< a) (ha' : a≤1/4) (hb : 1≤ b)
    (hBmask : 0≤ Bmask) (hMcap : 0< Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤ Rwidth) (hdmax : 0≤ dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0< d) (hdsupply : Mcap+Bmask+margin≤ d) (hdm : d≤ dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤ bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0< Mmin)
    (εshell : ℝ) (heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(hCs : 1≤ Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0< supply)(hev : 0<εv)
    (hBnorm : 0≤ Bnorm)(hel : 0<εlabels) :
    Σdegree : ℕ,ΣSp : Finset (ℕ×ℕ),PLift (lowFullSpec (α:=α) M H hH
      W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel degree Sp)
 :=
  let hbase := actual_selected_low_paid_columns (α:=α) M H hH
    W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
    ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
    supply εv Bnorm εlabels hsupply hev hBnorm hel
  let degree:=Classical.choose hbase
  let hd:=Classical.choose_spec hbase
  let Sp:=Classical.choose hd
  let hcolumn:=Classical.choose_spec hd
  ⟨degree,Sp,PLift.up hcolumn⟩

attribute [local irreducible] lowFullKernel

private def lowFullScalarFactor
    (Cg b Cs control v height physical Z exponent seedNorm : ℝ)
    (N degree boxCard : ℕ) : ℝ :=
  Cg*(2*b^2*Cs^(4*N))*QuadraticInitialBound.diagonalControl ballProfile*control^2*
    (1+|v|+height)^degree*(boxCard:ℝ)*physical*Z^exponent/seedNorm

private theorem lowFullScalarFactor_nonneg
    (Cg b Cs control v height physical Z exponent seedNorm : ℝ)
    (N degree boxCard : ℕ)
    (hCg : 0≤ Cg)(hCs : 0≤ Cs)(hheight : 0≤ height)(hphysical : 0≤ physical)
    (hZ : 0< Z)(hseed : 0≤ seedNorm) :
    0≤ lowFullScalarFactor Cg b Cs control v height physical Z exponent seedNorm N degree boxCard := by
  have hd:=QuadraticInitialBound.diagonalControl_nonneg ballProfile
  unfold lowFullScalarFactor
  positivity

set_option maxHeartbeats 200000 in
set_option linter.unusedVariables false in
set_option linter.defProp false in
private def lowFullLiteralSpec {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0< A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤ B) (ha : 0< a) (ha' : a≤1/4) (hb : 1≤ b)
    (hBmask : 0≤ Bmask) (hMcap : 0< Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤ Rwidth) (hdmax : 0≤ dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0< d) (hdsupply : Mcap+Bmask+margin≤ d) (hdm : d≤ dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤ bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0< Mmin)
    (εshell : ℝ) (heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(hCs : 1≤ Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0< supply)(hev : 0<εv)
    (hBnorm : 0≤ Bnorm)(hel : 0<εlabels)
    (ap εmass Bmass : ℝ)(hap : 0< ap)(hemass : 0≤εmass)
    (U εunion : ℝ)(hUcap : 0≤ U)(heunion : 0<εunion)
    (window pad : ℝ)(hwindow : 0≤ window)(hpad : 0< pad)(hL0 : 0≤ L)
    (degree : ℕ)(Sp : Finset (ℕ×ℕ))(Cg Cu : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤ M)(Z : ℝ) : Prop :=
  ∀(hZ : 1< Z)(s : Input α)(θ : α→ RayQuotient.Characters M H)(w σ freq : α→ℝ)
        (heightV height mesh aLow : ℝ)(i : ℕ)
        (hcard : Fintype.card α≤ N)(hmass : ∀j,s.M j≤ Cs)(hsupply' : supply≤ s.lower)
        (hm : Matches M H hH s η₀ θ w σ freq W B Z)(hsη : s.η=ηseed)
        (hsupper : s.upper≤ bs)(hsb₁ : s.b₁=b)(hsb₂ : s.b₂=b)
        (hw : ∀j,0≤ w j)(hwL : ∀j,w j≤ Cycle25.Energy.commonMesh Mcap Bmask L εold)
        (hwr : ∀j,w j/d≤ Rwidth)(hmesh : 0≤ mesh)(hwm : ∀j,w j≤ mesh)
        (hσlo : ∀j,lo≤σ j)(hσhi : ∀j,σ j≤ hi)(hheight : 0≤ height)(hfreq : ∀j,|freq j|≤ height)
        (haLow : 51/100≤ aLow)(haLow' : aLow≤167/200)
        (hfreqbin : |heightV|+height+Z^τ/2≤(3*i+2:ℕ)*Z^τ)
        (hhigh : (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^η)
        (Mrow reserve ξ : ℝ)(hMmin : Mmin≤ Mrow)
        (hω : 0≤ frequencyLoss Z 32 ξ+reserve)(hξ : 0≤ξ)
        (hMcap' : Mrow+εwidth*Mrow+ξ/2≤ Mcap)
        (hzslot : (17/500)*Mrow≤∑j,Real.logb Z (s.P j) ∧
          (∑j,Real.logb Z (s.P j))≤(1/25)*Mrow)
        (haff : length Z s.X₁+length Z s.X₂+Cycle61.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤
          Cycle61.Arithmetic.B*Mrow)
        {Label : Type}[Fintype Label]
        (reflected second : Bool)(R seed₀ : Ideal O)(bin : ℤ×(Fin 5→ℤ))(t : ℝ)
        (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
        let first:=fun l=>geometryFirstLabel s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let cell:=Cycle61.Arithmetic.cellUpper
          (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
        let amp:=Mrow*Cycle61.Arithmetic.amp cell
        let childSrc:=fun l=>geometryLowFirstChild reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t (firstIndex l)
        let Rchild:=fun l=>R*geometryColumnIdeal reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let seed:=fun l=>(firstIndex l).1.val.2.1.val
        let K:=fun l=>firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first l)
        let Tsec:=fun l=>firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve bs
          (Fintype.card α) (first l)
        ∀(hf : ∀l,Supported (first l).1.1 ∧ Supported (first l).1.2)
          (heq : ∀l,primeSupport (first l).1.1=primeSupport (first l).1.2)
          (hf₁ : ∀l,frozenCoefficient (firstIndex l).2.val
            (geometryColumnIdeal reflected s R seed₀ (Z^Mrow) Z ξ
              (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
            R s.ν s.W s.P≠0)
          (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)
          (hsource : ∀l,CenteredMomentOriginalCommonHarmonic.sourceRadius (childSrc l)≤ Z^Bnorm)
          (Tfirst p exponent : ℝ)(hTfirst : 1≤ Tfirst)(hp : p≤ Bnorm)
          (hs₀ : Squarefree seed₀)(hs₀0 : seed₀≠0)
          (hinj : Function.Injective (fun l=>(first l,seed l)))
          (hfirstseed : ∀l,seed₀∣(first l).1.1 ∧ seed₀∣(first l).1.2)
          (hfirstnorm : ∀l,((first l).1.1.absNorm:ℝ)≤ Z^Bnorm ∧ ((first l).1.2.absNorm:ℝ)≤ Z^Bnorm)
          (hrad : ∀l,((commonRadical (first l).1.1 (first l).1.2).absNorm:ℝ)≤ Z^p)
          (hgeom : ∀l,lowGeometryExponent reflected Z (Real.logb Z (volume s)) (first l)≤ exponent)
          (hfirstshell : ∀l,Tfirst≤((seed l).absNorm:ℝ) ∧ ((seed l).absNorm:ℝ)<2*Tfirst)
          (rows : Finset ((l : Label)×GeometryLowSecondIndex reflected s R seed₀ Z Mrow amp ξ reserve bs t
              (Fintype.card α) hZ bin (firstIndex l)))
          (hU : ∀r∈rows,r.2.2.1∈inactiveSubsets r.2.1.val.val.1 r.2.1.val.val.2)
          (box : Finset (Fin 4→ℤ))
          (hbox : ∀r∈rows,actualSecondDyad (childSrc r.1) (Rchild r.1) (seed r.1)
            (K r.1) (Tsec r.1) Z ξ r.2∈box),
        let datum : rows→ SecondInputDatum α:=fun r : rows=>geometryLowSecondDatum reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2
        ∀(B₂ : (r : rows)→ actualAllocations (childSrc r.val.1).pools
            (if second then (datum r).D else (datum r).C))
          (rwitness : (r : rows)→ secondLiveRows (fun _:Unit=>(datum r).block))
          (hf₂ : ∀r,frozenCoefficient (B₂ r).val
            (if second then (datum r).D else (datum r).C) (datum r).R
            (childSrc r.val.1).ν (childSrc r.val.1).W (childSrc r.val.1).P≠0),
        let q:=fun r : rows=>geometryLowActualChain reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 second (B₂ r)
        let g:=fun r : rows=>geometryLowActualGeometry reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 second (B₂ r)
          (rwitness r) (hf₁ r.val.1) (hf₂ r)
        ∀(χ : rows→ RayFourExpansion.RayCharacter)
          (hP : ∀r,(q r).R₂*(q r).E₂≠0)
          (hPN : ∀r,(((q r).R₂*(q r).E₂).absNorm:ℝ)≤ Z^Bmask),
        let st:=fun r=>retainedState Z Bmask hZ ((g r).datum.τ (χ r)) (internalQ Q η₀)
          ((q r).R₂*(q r).E₂) (hP r) (hPN r) (g r).datum.radius (g r).datum.C (g r).datum.D (g r).datum.inactive
        let low:=fun r=>ActualLow M H hH (st r) η₀ (inf_le_left.trans hQM) inf_le_right
          aLow e (3*(i+1:ℕ)*Z^τ)
        ∀(divisorSeed : rows→ Ideal O)(hE₂ : ∀r,Supported (q r).E₂)
          (hdivisor : ∀r,divisorSeed r∣(q r).E₂)(p₀ : Profiles a b)
          (hp₁ : s.W₁=(p₀.profile 0 : ℝ→ℂ))(hp₂ : s.W₂=(p₀.profile 1 : ℝ→ℂ))
          (zs : rows→ Finset O)(weight : rows→ O→ℝ)
          (hnonneg : ∀r,∀z∈zs r,0≤ weight r z)
          (hkeep : ∀r,∀z∈zs r,(st r).radial.keep z ∧ low r z)
          (hweight : ∀r,∀z∈zs r,weight r z≤
            ((st r).radial.profile (‖eisEmbedding z‖^2/(st r).radial.scale)).re)
          (Ψ : 𝓢(ℝ,ℂ))
          (hsourceOriginal : CenteredMomentOriginalCommonHarmonic.sourceRadius s≤ Z^Bmass)
          (hplain₁ : ∀x,s.W₁ x≠0→ ap≤ x)(hplain₂ : ∀x,s.W₂ x≠0→ ap≤ x)
          (sideLower : ℝ)
          (hside : ∀l,sideLower≤ geometryHighSide reflected (Real.logb Z (volume s))
            (geometryExponents s R seed₀ (Z^Mrow) Z ξ (firstIndex l).1.val.1.val))
          (hpool : ∀j I,I∈s.pools j→(I.absNorm:ℝ)≤ Z^U)
          (hwindowSource : ∀j,logWindow (s.lo j) (s.hi j)≤ window)
          (hplainScale : ∀side j,Cycle61.Physical.sourcePlainScales s.toData.toSource side j≤ Z^L),
        let src:=fun r=>withHeight (q r).first ((g r).datum.τ (χ r)) heightV
        let Ds:=fun r : rows=>(datum r).block.divisors.filter Squarefree
        let unionDs:=sharedProjectors Ds
        let firstMass:=fun l=>geometryFirstHighMass reflected s R seed₀ Ψ Mrow Z ξ εmass
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let physical:=geometryHighFactor reflected (geometrySupportConstant N supply ap ap) bin
        let error:=εwidth*Mrow+ξ/2-Mrow*(1/3750000)+εold+2*ε*d*(Fintype.card α:ℝ)+
          (2*Cycle61.Arithmetic.q0/9)*(frequencyLoss Z 32 ξ+reserve+εpad*Mrow)+Cycle61.Arithmetic.q0*mesh+pad
        let exponentFull:=(Bmass*εmass-sideLower)+amp+p+exponent+error+εv+Bnorm*εshell+εlabels
        let factor : ℝ:=lowFullScalarFactor Cg b Cs (p₀.control Sp) heightV height physical Z
          exponentFull (seed₀.absNorm:ℝ) N degree box.card
        let cost:=fun (r : rows)(D : Ideal O)=>
          (firstMass r.val.1/volume (childSrc r.val.1)*(g r).datum.K*
            normalizer (g r).datum.C (g r).datum.D (g r).datum.inactive)*
          (∑z∈zs r,weight r z*‖normalizedColumn (src r) (q r).E₂ (hE₂ r) (q r).R₂ (divisorSeed r) D z‖^2)
        (∑r,∑D∈Ds r,cost r D)≤
          factor*(Cu*Z^(εunion+3*(((N:ℝ)+2)*U)*εshell))

set_option maxHeartbeats 80000 in
set_option linter.defProp false in
def actual_geometry_selected_low_full_columns {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0< A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤ B) (ha : 0< a) (ha' : a≤1/4) (hb : 1≤ b)
    (hBmask : 0≤ Bmask) (hMcap : 0< Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤ Rwidth) (hdmax : 0≤ dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0< d) (hdsupply : Mcap+Bmask+margin≤ d) (hdm : d≤ dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤ bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0< Mmin)
    (εshell : ℝ) (heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(hCs : 1≤ Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0< supply)(hev : 0<εv)
    (hBnorm : 0≤ Bnorm)(hel : 0<εlabels)
    (ap εmass Bmass : ℝ)(hap : 0< ap)(hemass : 0≤εmass)
    (U εunion : ℝ)(hUcap : 0≤ U)(heunion : 0<εunion)
    (window pad : ℝ)(hwindow : 0≤ window)(hpad : 0< pad)(hL0 : 0≤ L) :
    Σdegree : ℕ,ΣSp : Finset (ℕ×ℕ),ΣCu : ℝ,
      PLift (0< Cu) ×
      (∀(η₀ : Character)(Q : Ideal O)(hQM : Q≤ M),
        internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
        ΣCg : ℝ,PLift (0< Cg ∧ ∀ᶠZ : ℝ in atTop,2≤ Z ∧
          lowFullLiteralSpec (α:=α) M H hH
      W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      degree Sp Cg Cu η₀ Q hQM Z)) :=
by
  exact
    let kernel := lowFullKernel (α:=α) M H hH
      W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel
    let degree:=kernel.1
    let Sp:=kernel.2.1
    let unionBase:=actual_second_low_weighted_shells.{0,0} (α:=α) N U εshell εunion hUcap heshell.le heunion
    let Cu:=Classical.choose unionBase
    let hu:=Classical.choose_spec unionBase
    let sourceCaps:=eventual_low_chain_source_caps N window b pad L hwindow hb hpad hL0
    ⟨degree,Sp,Cu,⟨PLift.up hu.1,fun (η₀ : Character)(Q : Ideal O)(hQM : Q≤ M)
        (hQ0 : internalQ Q η₀≠0)(hQt : internalQ Q η₀≠⊤)
        (hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)})=>
      let hcbase:=kernel.2.2.down η₀ Q hQM hQ0 hQt hQ72
      let Cg:=Classical.choose hcbase
      let hc:=Classical.choose_spec hcbase
      ⟨Cg,PLift.up (And.intro hc.1 (show ∀ᶠZ : ℝ in atTop,2≤ Z ∧
        lowFullLiteralSpec (α:=α) M H hH
        W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
        Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
        ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
        supply εv Bnorm εlabels hsupply hev hBnorm hel
        ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
        degree Sp Cg Cu η₀ Q hQM Z from by
        filter_upwards [hc.2,hu.2,sourceCaps] with Z hz hzu hzsource
        refine ⟨hz.1,?_⟩
        exact fun (hZ : 1< Z)(s : Input α)(θ : α→ RayQuotient.Characters M H)(w σ freq : α→ℝ)
          (heightV height mesh aLow : ℝ)(i : ℕ)
          (hcard : Fintype.card α≤ N)(hmass : ∀j,s.M j≤ Cs)(hsupply' : supply≤ s.lower)
          (hm : Matches M H hH s η₀ θ w σ freq W B Z)(hsη : s.η=ηseed)
          (hsupper : s.upper≤ bs)(hsb₁ : s.b₁=b)(hsb₂ : s.b₂=b)
          (hw : ∀j,0≤ w j)(hwL : ∀j,w j≤ Cycle25.Energy.commonMesh Mcap Bmask L εold)
          (hwr : ∀j,w j/d≤ Rwidth)(hmesh : 0≤ mesh)(hwm : ∀j,w j≤ mesh)
          (hσlo : ∀j,lo≤σ j)(hσhi : ∀j,σ j≤ hi)(hheight : 0≤ height)(hfreq : ∀j,|freq j|≤ height)
          (haLow : 51/100≤ aLow)(haLow' : aLow≤167/200)
          (hfreqbin : |heightV|+height+Z^τ/2≤(3*i+2:ℕ)*Z^τ)
          (hhigh : (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^η)
          (Mrow reserve ξ : ℝ)(hMmin : Mmin≤ Mrow)
          (hω : 0≤ frequencyLoss Z 32 ξ+reserve)(hξ : 0≤ξ)
          (hMcap' : Mrow+εwidth*Mrow+ξ/2≤ Mcap)
          (hzslot : (17/500)*Mrow≤∑j,Real.logb Z (s.P j) ∧
            (∑j,Real.logb Z (s.P j))≤(1/25)*Mrow)
          (haff : length Z s.X₁+length Z s.X₂+Cycle61.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤
            Cycle61.Arithmetic.B*Mrow)
          {Label : Type}[Fintype Label]
          (reflected second : Bool)(R seed₀ : Ideal O)(bin : ℤ×(Fin 5→ℤ))(t : ℝ)
          (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed₀ (Z^Mrow) Z ξ
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)=>
          let first:=fun l=>geometryFirstLabel s R seed₀ (Z^Mrow) Z ξ
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
          let cell:=Cycle61.Arithmetic.cellUpper
            (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
          let amp:=Mrow*Cycle61.Arithmetic.amp cell
          let childSrc:=fun l=>geometryLowFirstChild reflected s R seed₀ (Z^Mrow) Z ξ
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t (firstIndex l)
          let Rchild:=fun l=>R*geometryColumnIdeal reflected s R seed₀ (Z^Mrow) Z ξ
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
          let seed:=fun l=>(firstIndex l).1.val.2.1.val
          let K:=fun l=>firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first l)
          let Tsec:=fun l=>firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve bs
            (Fintype.card α) (first l)
          fun (hf : ∀l,Supported (first l).1.1 ∧ Supported (first l).1.2)
            (heq : ∀l,primeSupport (first l).1.1=primeSupport (first l).1.2)
            (hf₁ : ∀l,frozenCoefficient (firstIndex l).2.val
              (geometryColumnIdeal reflected s R seed₀ (Z^Mrow) Z ξ
                (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
              R s.ν s.W s.P≠0)
            (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)
            (hsource : ∀l,CenteredMomentOriginalCommonHarmonic.sourceRadius (childSrc l)≤ Z^Bnorm)
            (Tfirst p exponent : ℝ)(hTfirst : 1≤ Tfirst)(hp : p≤ Bnorm)
            (hs₀ : Squarefree seed₀)(hs₀0 : seed₀≠0)
            (hinj : Function.Injective (fun l=>(first l,seed l)))
            (hfirstseed : ∀l,seed₀∣(first l).1.1 ∧ seed₀∣(first l).1.2)
            (hfirstnorm : ∀l,((first l).1.1.absNorm:ℝ)≤ Z^Bnorm ∧ ((first l).1.2.absNorm:ℝ)≤ Z^Bnorm)
            (hrad : ∀l,((commonRadical (first l).1.1 (first l).1.2).absNorm:ℝ)≤ Z^p)
            (hgeom : ∀l,lowGeometryExponent reflected Z (Real.logb Z (volume s)) (first l)≤ exponent)
            (hfirstshell : ∀l,Tfirst≤((seed l).absNorm:ℝ) ∧ ((seed l).absNorm:ℝ)<2*Tfirst)
            (rows : Finset ((l : Label)×GeometryLowSecondIndex reflected s R seed₀ Z Mrow amp ξ reserve bs t
              (Fintype.card α) hZ bin (firstIndex l)))
            (hU : ∀r∈rows,r.2.2.1∈inactiveSubsets r.2.1.val.val.1 r.2.1.val.val.2)
            (box : Finset (Fin 4→ℤ))
            (hbox : ∀r∈rows,actualSecondDyad (childSrc r.1) (Rchild r.1) (seed r.1)
              (K r.1) (Tsec r.1) Z ξ r.2∈box)=>
          let datum : rows→ SecondInputDatum α:=fun r : rows=>geometryLowSecondDatum reflected s R seed₀ Z Mrow amp ξ reserve bs t
            (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2
          fun (B₂ : (r : rows)→ actualAllocations (childSrc r.val.1).pools
              (if second then (datum r).D else (datum r).C))
            (rwitness : (r : rows)→ secondLiveRows (fun _:Unit=>(datum r).block))
            (hf₂ : ∀r,frozenCoefficient (B₂ r).val
              (if second then (datum r).D else (datum r).C) (datum r).R
              (childSrc r.val.1).ν (childSrc r.val.1).W (childSrc r.val.1).P≠0)=>
          let q:=fun r : rows=>geometryLowActualChain reflected s R seed₀ Z Mrow amp ξ reserve bs t
            (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 second (B₂ r)
          let g:=fun r : rows=>geometryLowActualGeometry reflected s R seed₀ Z Mrow amp ξ reserve bs t
            (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 second (B₂ r)
            (rwitness r) (hf₁ r.val.1) (hf₂ r)
          let fields:=fun r : rows=>actual_geometry_low_paid_fields reflected s R seed₀ Z Mrow amp ξ reserve bs t
            (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 (hU r.val r.property)
            second (B₂ r) (rwitness r) (hf₁ r.val.1) (hf₂ r)
          let hrow:=hz.2 hZ s θ w σ freq heightV height mesh aLow i hcard hmass hsupply' hm hsη hsupper hsb₁ hsb₂
            hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh
            Mrow (frequencyLoss Z 32 ξ+reserve) ξ hMmin hω hξ hMcap' hzslot haff
            reflected second first hf heq R (fun l=>(firstIndex l).2)
            (fun l=>geometryColumnCharacter reflected s R seed₀ (Z^Mrow) Z ξ
              (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
            (fun _=>t) hf₁ Rchild seed K Tsec reserve
            (fun l=>actual_first_live_squarefree
              (geometryFirstSource s R seed₀ (Z^Mrow) Z ξ
                (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
              (fun _=>logAnnulus) (firstIndex l).1.val (firstIndex l).1.property)
            (fun _=>hw₁) (fun _=>hw₂) hsource Tfirst p exponent hTfirst hp seed₀ hs₀ hs₀0 hinj hfirstseed
            hfirstnorm hrad hgeom hfirstshell rows hU box hbox q g
            (fun r=>(fields r).1) (fun r=>(fields r).2.1) (fun r=>(fields r).2.2.1)
            (fun r=>(fields r).2.2.2.1) (fun r=>(fields r).2.2.2.2.1)
            (fun r=>(fields r).2.2.2.2.2.1) (fun r=>(fields r).2.2.2.2.2.2) rfl
          fun (χ : rows→ RayFourExpansion.RayCharacter) hP hPN divisorSeed hE₂ hdivisor (p₀ : Profiles a b) hp₁ hp₂
            (zs : rows→ Finset O)(weight : rows→ O→ℝ)
            (hnonneg : ∀r,∀z∈zs r,0≤ weight r z) hkeep hweight
            (Ψ : 𝓢(ℝ,ℂ)) hsourceOriginal hplain₁ hplain₂
            (sideLower : ℝ)
            (hside : ∀l,sideLower≤ geometryHighSide reflected (Real.logb Z (volume s))
              (geometryExponents s R seed₀ (Z^Mrow) Z ξ (firstIndex l).1.val.1.val))
            (hpool : ∀j I,I∈s.pools j→(I.absNorm:ℝ)≤ Z^U)
            (hwindowSource : ∀j,logWindow (s.lo j) (s.hi j)≤ window)
            (hplainScale : ∀side j,Cycle61.Physical.sourcePlainScales s.toData.toSource side j≤ Z^L)=>
          let src:=fun r=>withHeight (q r).first ((g r).datum.τ (χ r)) heightV
          let Ds:=fun r : rows=>(datum r).block.divisors.filter Squarefree
          let unionDs:=sharedProjectors Ds
          let firstMass:=fun l=>geometryFirstHighMass reflected s R seed₀ Ψ Mrow Z ξ εmass
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
          let physical:=geometryHighFactor reflected (geometrySupportConstant N supply ap ap) bin
          let error:=εwidth*Mrow+ξ/2-Mrow*(1/3750000)+εold+2*ε*d*(Fintype.card α:ℝ)+
            (2*Cycle61.Arithmetic.q0/9)*(frequencyLoss Z 32 ξ+reserve+εpad*Mrow)+Cycle61.Arithmetic.q0*mesh+pad
          let exponentFull:=(Bmass*εmass-sideLower)+amp+p+exponent+error+εv+Bnorm*εshell+εlabels
          let factor : ℝ:=lowFullScalarFactor Cg b Cs (p₀.control Sp) heightV height physical Z
            exponentFull (seed₀.absNorm:ℝ) N degree box.card
          let cost:=fun (r : rows)(D : Ideal O)=>
            (firstMass r.val.1/volume (childSrc r.val.1)*(g r).datum.K*
              normalizer (g r).datum.C (g r).datum.D (g r).datum.inactive)*
            (∑z∈zs r,weight r z*‖normalizedColumn (src r) (q r).E₂ (hE₂ r) (q r).R₂ (divisorSeed r) D z‖^2)
          let hcommonCaps:=fun (r : rows)(B : actualAllocations (q r).first.pools (q r).E₂)=>
            hzsource.2 s hcard hwindowSource hsb₁.le hsb₂.le hplainScale
              (q r) B ((g r).datum.τ (χ r)) heightV
          (show (∑r,∑D∈Ds r,cost r D)≤
            factor*(Cu*Z^(εunion+3*(((N:ℝ)+2)*U)*εshell)) from by
            have hphysical : 0≤ physical := by
              cases reflected <;> simp only [physical,geometryHighFactor,ite_true]
              · exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (geometryDCompensator_pos bin).le
              · exact (inv_pos.mpr (geometryDCompensator_pos bin)).le
            have hCg : 0< Cg := hc.1
            have hfirstMass (l : Label) : 0≤ firstMass l :=
              geometry_first_high_mass_nonneg reflected s R seed₀ Ψ Mrow Z ξ εmass
                (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
            have hmassBound (l : Label) : firstMass l≤ physical*Z^(Bmass*εmass-sideLower) :=
              actual_geometry_low_uniform_mass reflected N supply ap hsupply hap s R seed₀ Ψ
                Mrow Z ξ Bmass εmass sideLower hZ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hemass
                hcard hsupply' hs₀ hw₁ hw₂ hsourceOriginal hplain₁ hplain₂ bin (firstIndex l).1.val (hside l)
            have hfactor : 0≤ factor :=
              lowFullScalarFactor_nonneg Cg b Cs (p₀.control Sp) heightV height physical Z
                exponentFull (seed₀.absNorm:ℝ) N degree box.card hCg.le
                (zero_le_one.trans hCs) hheight hphysical (zero_lt_one.trans hZ) (Nat.cast_nonneg _)
            have hcost (r : rows)(D : Ideal O) : 0≤ cost r D := by
              dsimp only [cost]
              apply mul_nonneg
              · exact mul_nonneg (mul_nonneg (div_nonneg
                  (geometry_first_high_mass_nonneg reflected s R seed₀ Ψ Mrow Z ξ εmass
                    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex r.val.1).1.val)
                  (CenteredMomentAmplificationChildInput.volume_pos _).le) (g r).datum.K_pos.le)
                  (normalizer_pos _ _ (g r).datum.hC _).le
              · exact Finset.sum_nonneg (fun z hz=>mul_nonneg (hnonneg r z hz) (sq_nonneg _))
            have hs (r : rows)(D : Ideal O)(hD : D∈Ds r) : Squarefree D := (Finset.mem_filter.mp hD).2
            have hsourcecap (r : rows):=
              actual_geometry_low_second_source_caps reflected s R seed₀ Z Mrow amp ξ reserve bs t
                (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 N hcard (Z^U) hpool
            have hcap (r : rows)(D : Ideal O)(hD : D∈Ds r) : (D.absNorm:ℝ)≤ Z^(((N:ℝ)+2)*U) :=
              (second_datum_projector_cap (datum r) N Z U (hsourcecap r).1 hZ.le hUcap
                (hsourcecap r).2 D (Finset.mem_filter.mp hD).1).2
            have hshell (n : ℤ)(hn : n∈selectedShells unionDs) :
                (∑r,∑D∈shell unionDs n,cost r D)≤ factor*(2*dyadicScale n)^(3*εshell) := by
              have hscale:=shared_projector_shell_scale Ds Z (((N:ℝ)+2)*U) hcap n hn
              have hcolumns:=hrow χ hP hPN divisorSeed hE₂ hdivisor (shell unionDs n) (dyadicScale n) pad
                hscale.1 (fun D hD=>let h:=shared_projector_shell_gates Ds n D hD; ⟨h.1,h.2.2⟩)
                p₀ hp₁ hp₂ (fun r B hB=>(hcommonCaps r B).1)
                (fun r B hB D hD al hal side=>⟨(hcommonCaps r B).2 D al side 0,(hcommonCaps r B).2 D al side 1⟩)
                zs weight hnonneg hkeep hweight firstMass physical (Bmass*εmass-sideLower)
                hphysical hfirstMass hmassBound
              convert hcolumns using 1
              · apply Finset.sum_congr rfl
                intro r hr
                dsimp only [cost]
                rw [Finset.mul_sum]
                dsimp only [src,childSrc,geometryLowFirstChild,first,geometryColumnIdeal,geometryFirstLabel]
                rfl
              · dsimp only [factor,lowFullScalarFactor,exponentFull,error]
                ring
            have hfull:=low_shared_shell_contraction Ds hs cost hcost factor εshell hshell
            apply hfull.trans
            apply mul_le_mul_of_nonneg_left _ hfactor
            have hdatum:=hzu.2 datum (fun r=>(hsourcecap r).1) (fun r=>(hsourcecap r).2)
            simpa only [Ds,shared_squarefree_shells] using hdatum)
        ))⟩⟩⟩

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_selected_low_full_columns
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_low_second_source_caps

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainLowFull -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainLowQuantitativePayment; sha256 440420ab4636fe1a8aa9f3cd8aff85ba2460e12f6665053076fe5ae6161a4f4c -/
section
                                                       
                                                                    
                                                       
                                                         
                                                       
                                                                   

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentSourceLiveColumn
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceMass CenteredMomentRankinRadical CenteredMomentFirstDiscardedEnergy
open CenteredMomentLogDyadic CenteredMomentWholeDivisorShell CenteredMomentSlotRatios
open CenteredMomentCommonPairedSource
open CenteredMomentFirstChildProfileControl
open Cycle61FinalNatural Cycle61Moment.LowBranch
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentCanonicalFirst
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentEligibleEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale
open CenteredMomentCommonLinearNormalization CenteredMomentSourceLiveColumn
open Cycle61Moment LocalMoment
open Cycle61FinalLow
open Cycle61Moment.LowBranch Cycle61FinalNatural Cycle61FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle61FinalProfiles

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal HeckeFamily.O) [NeZero M]
variable (H : Subgroup (HeckeFamily.O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

local notation "O" => HeckeFamily.O
local instance geometryMainLowQuantitativeDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def mainLowQuantitativeFactor
    (Cg b Cs control v height physical Z exponent seedNorm : ℝ)
    (N degree boxCard : ℕ) : ℝ :=
  Cg*(2*b^2*Cs^(4*N))*QuadraticInitialBound.diagonalControl ballProfile*control^2*
    (1+|v|+height)^degree*(boxCard:ℝ)*physical*Z^exponent/seedNorm



/-- Literal buffered choice on a signed ordinary source row. It depends
on the actual natural state, never on the first shell or residual ideal. -/
def mainLowCanonicalSelector
    (d : SecondInputDatum α) (χ₀ χ ψ : RayFourExpansion.RayCharacter) (Q : Ideal O)
    (hQ : Q≤ Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (Z Bmask : ℝ) (hZ : 1< Z) (second : Bool)
    (hP : d.R*(if second then d.D else d.C)≠0)
    (hPN : ((d.R*(if second then d.D else d.C)).absNorm:ℝ)≤ Z^Bmask)
    (η₀ : Character) (hQM : Q≤ M) (hQη : Q≤η₀.modulus)
    (e T : ℝ) (he : 0< e) (hT : 2< T)
    (hβlo : 51/100≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8) :
    mainLowSourceRows second (ordinarySecondDatum d χ₀ Q m) (fun _=>True)→ BufferIndex e :=
  let st:=retainedState Z Bmask hZ (if second then d.τ ψ⁻¹ else d.τ χ) Q
    (d.R*(if second then d.D else d.C)) hP hPN d.radius d.C d.D d.inactive
  fun z=>Classical.choose (actual_geometry_zero_partition M H hH st η₀ hQM hQη z.val
    (actual_main_low_source_admission d χ₀ χ ψ Q hQ m hm hml hm2 Z Bmask hZ second hP hPN
      (fun _=>True) z.val z.property).1 e T he hT hβlo hβhi)

/-- The canonical index retains the full buffered zero-bin certificate,
so high and low consumers share one literal partition. -/
theorem actual_main_low_canonical_zero_bin
    (d : SecondInputDatum α) (χ₀ χ ψ : RayFourExpansion.RayCharacter) (Q : Ideal O)
    (hQ : Q≤ Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (Z Bmask : ℝ) (hZ : 1< Z) (second : Bool)
    (hP : d.R*(if second then d.D else d.C)≠0)
    (hPN : ((d.R*(if second then d.D else d.C)).absNorm:ℝ)≤ Z^Bmask)
    (η₀ : Character) (hQM : Q≤ M) (hQη : Q≤η₀.modulus)
    (e T : ℝ) (he : 0< e) (hT : 2< T)
    (hβlo : 51/100≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8) :
    let st:=retainedState Z Bmask hZ (if second then d.τ ψ⁻¹ else d.τ χ) Q
      (d.R*(if second then d.D else d.C)) hP hPN d.radius d.C d.D d.inactive
    ∀z : mainLowSourceRows second (ordinarySecondDatum d χ₀ Q m) (fun _=>True),
      GeometryZeroBin M H hH st η₀ hQM hQη z.val
        (actual_main_low_source_admission d χ₀ χ ψ Q hQ m hm hml hm2 Z Bmask hZ second hP hPN
          (fun _=>True) z.val z.property).1 e T
        (mainLowCanonicalSelector M H hH d χ₀ χ ψ Q hQ m hm hml hm2 Z Bmask hZ second
          hP hPN η₀ hQM hQη e T he hT hβlo hβhi z) := by
  intro st z
  exact Classical.choose_spec (actual_geometry_zero_partition M H hH st η₀ hQM hQη z.val
    (actual_main_low_source_admission d χ₀ χ ψ Q hQ m hm hml hm2 Z Bmask hZ second hP hPN
      (fun _=>True) z.val z.property).1 e T he hT hβlo hβhi)

/-- The canonical choice gives all low-kernel gates at unit weight. -/
theorem actual_main_low_canonical_payment_bins
    (d : SecondInputDatum α) (χ₀ χ ψ : RayFourExpansion.RayCharacter) (Q : Ideal O)
    (hQ : Q≤ Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (Z Bmask : ℝ) (hZ : 1< Z) (second : Bool)
    (hP : d.R*(if second then d.D else d.C)≠0)
    (hPN : ((d.R*(if second then d.D else d.C)).absNorm:ℝ)≤ Z^Bmask)
    (η₀ : Character) (hQM : Q≤ M) (hQη : Q≤η₀.modulus)
    (e T : ℝ) (he : 0< e) (hT : 2< T)
    (hβlo : 51/100≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8) :
    let st:=retainedState Z Bmask hZ (if second then d.τ ψ⁻¹ else d.τ χ) Q
      (d.R*(if second then d.D else d.C)) hP hPN d.radius d.C d.D d.inactive
    let rows:=mainLowSourceRows second (ordinarySecondDatum d χ₀ Q m) (fun _=>True)
    let select:=mainLowCanonicalSelector M H hH d χ₀ χ ψ Q hQ m hm hml hm2 Z Bmask hZ second
      hP hPN η₀ hQM hQη e T he hT hβlo hβhi
    ∀p z,z∈mainLowPaymentRows rows select p→ 
      st.radial.keep z ∧ ActualLow M H hH st η₀ hQM hQη (167/200) e (3*(p.1.val+1:ℕ)*T) z ∧
      1≤(st.radial.profile (normValue z/st.radial.scale)).re ∧
      1≤ p.1.val ∧ p.1.val≤ bufferCount e := by
  intro st rows select p z hz
  have ha (x : rows) := actual_main_low_source_admission d χ₀ χ ψ Q hQ m hm hml hm2
    Z Bmask hZ second hP hPN (fun _=>True) x.val x.property
  obtain ⟨hzrows,hsel,hlow⟩ := (mem_main_low_payment_rows rows select p z).mp hz
  have hg:=ha ⟨z,hzrows⟩
  have hbin : GeometryZeroBin M H hH st η₀ hQM hQη z hg.1 e T p := by
    have hb:=Classical.choose_spec (actual_geometry_zero_partition M H hH st η₀ hQM hQη
      z hg.1 e T he hT hβlo hβhi)
    change GeometryZeroBin M H hH st η₀ hQM hQη z hg.1 e T (select ⟨z,hzrows⟩) at hb
    rw [hsel] at hb
    exact hb
  refine ⟨hg.1,?_,hg.2.2,hbin.1,hbin.2.1⟩
  apply actual_main_low_bin_admission M H hH st η₀ hQM hQη z hg.1 e T p hbin hlow
  simpa only [normValue_eq_embedding] using hg.2.2

/-- The same literal selector on the complete physical family, before
projector shells or low/high restrictions. `Label` may already carry the
original full-block nonzero filter and one selected first allocation. -/
def mainLowFamilyCanonicalSelector {Label : Type*} [Fintype Label]
    (d : Label→ SecondInputDatum α) (χ₀ : Label→ RayFourExpansion.RayCharacter) (Q : Ideal O)
    (hQ : Q≤ Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (Z Bmask : ℝ) (hZ : 1< Z) (second : Bool)
    (hP : ∀l,(d l).R*(if second then (d l).D else (d l).C)≠0)
    (hPN : ∀l,(((d l).R*(if second then (d l).D else (d l).C)).absNorm:ℝ)≤ Z^Bmask)
    (η₀ : Character) (hQM : Q≤ M) (hQη : Q≤η₀.modulus)
    (e T : ℝ) (he : 0< e) (hT : 2< T)
    (hβlo : 51/100≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8) :
    secondLiveRows (fun l=>(ordinarySecondDatum (d l) (χ₀ l) Q m).block)→ BufferIndex e :=
  fun r=>mainLowCanonicalSelector M H hH (d r.val.1) (χ₀ r.val.1) r.val.2.1 r.val.2.2.1
    Q hQ m hm hml hm2 Z Bmask hZ second (hP r.val.1) (hPN r.val.1)
    η₀ hQM hQη e T he hT hβlo hβhi
    ⟨mainLowSignedRow second r.val.2.2.2.val,by
      apply (mem_main_low_source_rows second _ (fun _=>True) _).mpr
      refine ⟨r.val.2.2.2,?_,rfl,True.intro⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp r.property).2⟩⟩

/-- The literal first-child height is retained in each actual second datum. -/
theorem actual_main_low_quantitative_height_identity
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z)
    (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)
    (n : GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q)
    (second : Bool) (t₀ u height τ : ℝ)
    (hsmall : 2*(1+|t|+height+2*Real.pi*(|t₀|+|u|))≤ Z^τ) :
    let d:=geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n
    d.input.t=t ∧
      |d.input.t+2*Real.pi*(u-(if second then -t₀ else t₀))|+height+Z^τ/2≤5*Z^τ := by
  intro d
  have ht : d.input.t=t := rfl
  refine ⟨ht,?_⟩
  rw [ht]
  exact main_low_payment_shifted_height_envelope second t height t₀ u (Z^τ)
    (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) hsmall
private theorem mainLowQuantitativeFactor_nonneg
    (Cg b Cs control v height physical Z exponent seedNorm : ℝ)
    (N degree boxCard : ℕ)
    (hCg : 0≤ Cg)(hCs : 0≤ Cs)(hheight : 0≤ height)(hphysical : 0≤ physical)
    (hZ : 0< Z)(hseed : 0≤ seedNorm) :
    0≤ mainLowQuantitativeFactor Cg b Cs control v height physical Z exponent seedNorm N degree boxCard := by
  have hd:=QuadraticInitialBound.diagonalControl_nonneg ballProfile
  unfold mainLowQuantitativeFactor
  positivity

/-- The four first-geometry endpoint losses cost sixteen, independently
of the moving source height and of the supported arithmetic labels. -/
theorem main_low_quantitative_factor_bin_payment
    (Cg b Cs control v height physical Z base p exponent sideLower seedNorm : ℝ)
    (N degree boxCard : ℕ) (hZ : 1< Z)
    (hledger : p+exponent-sideLower=4*Real.logb Z 2) :
    mainLowQuantitativeFactor Cg b Cs control v height physical Z
      (base-sideLower+p+exponent) seedNorm N degree boxCard=
      16*mainLowQuantitativeFactor Cg b Cs control v height physical Z
        base seedNorm N degree boxCard := by
  have he : base-sideLower+p+exponent=base+4*Real.logb Z 2 := by linarith
  unfold mainLowQuantitativeFactor
  rw [he,Real.rpow_add (zero_lt_one.trans hZ),geometry_low_bin_slack_payment Z hZ]
  ring

/-- The complete selected scalar cost, staged independently of physical
block types so the public receipt does not normalize their ancestry. -/
def mainLowCompleteSelectedCost {Label : Type*} [Fintype Label]
    (ordinaryRows : Label→ Finset O) {e : ℝ}
    (select : (r : Label)→ ordinaryRows r→ BufferIndex e)
    (Ds : Label→ Finset (Ideal O)) (coefficient : Label→ Ideal O→ ℝ)
    (value : Label→ Ideal O→ O→ ℝ) : ℝ :=
  ∑r,∑D∈Ds r,coefficient r D*
    (∑z : ordinaryRows r,if bufferValue e (select r z)<167/200 then value r D z.val else 0)

/-- Exact complete signed low-source sum. The selector partitions a row
once, and bins with zero index are empty by the genuine admission receipt.
This structural contraction charges only the fixed buffered-bin cardinal. -/
theorem main_low_payment_complete_cost_le
    {Label : Type*} [Fintype Label]
    (ordinaryRows : Label→ Finset O) {e : ℝ}
    (select : (r : Label)→ ordinaryRows r→ BufferIndex e)
    (Ds : Label→ Finset (Ideal O)) (coefficient : Label→ Ideal O→ ℝ)
    (value : Label→ Ideal O→ O→ ℝ) (bound : ℝ) (hbound : 0≤ bound)
    (hpositive : ∀r p z,z∈mainLowPaymentRows (ordinaryRows r) (select r) p→ 1≤ p.1.val)
    (hbin : ∀p : BufferIndex e,1≤ p.1.val→ 
      (∑r,∑D∈Ds r,coefficient r D*
        (∑z∈mainLowPaymentRows (ordinaryRows r) (select r) p,value r D z))≤ bound) :
    (∑r,∑D∈Ds r,coefficient r D*
      (∑z : ordinaryRows r,
        if bufferValue e (select r z)<167/200 then value r D z.val else 0))≤
      (Fintype.card (BufferIndex e):ℝ)*bound := by
  classical
  have heq : (∑r,∑D∈Ds r,coefficient r D*
      (∑z : ordinaryRows r,
        if bufferValue e (select r z)<167/200 then value r D z.val else 0))=
      ∑p : BufferIndex e,∑r,∑D∈Ds r,coefficient r D*
        (∑z∈mainLowPaymentRows (ordinaryRows r) (select r) p,value r D z) := by
    calc
      _=∑r,∑D∈Ds r,∑p : BufferIndex e,coefficient r D*
          (∑z∈mainLowPaymentRows (ordinaryRows r) (select r) p,value r D z) := by
        apply Finset.sum_congr rfl
        intro r _
        apply Finset.sum_congr rfl
        intro D _
        rw [main_low_payment_complete_low_sum,Finset.mul_sum]
      _=∑r,∑p : BufferIndex e,∑D∈Ds r,coefficient r D*
          (∑z∈mainLowPaymentRows (ordinaryRows r) (select r) p,value r D z) := by
        apply Finset.sum_congr rfl
        intro r _
        exact Finset.sum_comm
      _=_ := Finset.sum_comm
  rw [heq]
  calc
    _≤∑_p : BufferIndex e,bound := by
      apply Finset.sum_le_sum
      intro p _
      by_cases hp : 1≤ p.1.val
      · exact hbin p hp
      · have hz : ∀r,mainLowPaymentRows (ordinaryRows r) (select r) p=∅ := by
          intro r
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro z hm
          exact hp (hpositive r p z hm)
        simp only [hz,Finset.sum_empty,mul_zero,Finset.sum_const_zero]
        exact hbound
    _=_ := by simp

set_option linter.unusedVariables false in
set_option linter.defProp false in
def MainLowQuantitativeBinSpec {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0< A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤ B) (ha : 0< a) (ha' : a≤1/4) (hb : 1≤ b)
    (hBmask : 0≤ Bmask) (hMcap : 0< Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤ Rwidth) (hdmax : 0≤ dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0< d) (hdsupply : Mcap+Bmask+margin≤ d) (hdm : d≤ dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤ bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0< Mmin)
    (εshell : ℝ) (heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(hCs : 1≤ Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0< supply)(hev : 0<εv)
    (hBnorm : 0≤ Bnorm)(hel : 0<εlabels)
    (ap εmass Bmass : ℝ)(hap : 0< ap)(hemass : 0≤εmass)
    (U εunion : ℝ)(hUcap : 0≤ U)(heunion : 0<εunion)
    (window pad : ℝ)(hwindow : 0≤ window)(hpad : 0< pad)(hL0 : 0≤ L)
    (degree : ℕ)(Sp : Finset (ℕ×ℕ))(Cg Cu : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤ M) (hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)}) (Z : ℝ) : Prop :=
  ∀(hZ : 1< Z)(s : Input α)(θ : α→ RayQuotient.Characters M H)(w σ freq : α→ ℝ)
        (heightV height mesh : ℝ)
        (hcard : Fintype.card α≤ N)(hmass : ∀j,s.M j≤ Cs)(hsupply' : supply≤ s.lower)
        (hm : Matches M H hH s η₀ θ w σ freq W B Z)(hsη : s.η=ηseed)
        (hsupper : s.upper≤ bs)(hsb₁ : s.b₁=b)(hsb₂ : s.b₂=b)
        (hw : ∀j,0≤ w j)(hwL : ∀j,w j≤ Cycle25.Energy.commonMesh Mcap Bmask L εold)
        (hwr : ∀j,w j/d≤ Rwidth)(hmesh : 0≤ mesh)(hwm : ∀j,w j≤ mesh)
        (hσlo : ∀j,lo≤σ j)(hσhi : ∀j,σ j≤ hi)(hheight : 0≤ height)(hfreq : ∀j,|freq j|≤ height)
        (hT : 2< Z^τ)
        (hfreqbin : |heightV|+height+Z^τ/2≤5*Z^τ)
        (hβhi : HeckeZeroSupremum.beta≤7/8)
        (Mrow reserve ξ : ℝ)(hMmin : Mmin≤ Mrow)
        (hω : 0≤ frequencyLoss Z 32 ξ+reserve)(hξ : 0≤ξ)
        (hMcap' : Mrow+εwidth*Mrow+ξ/2≤ Mcap)
        (hzslot : (17/500)*Mrow≤∑j,Real.logb Z (s.P j) ∧
          (∑j,Real.logb Z (s.P j))≤(1/25)*Mrow)
        (haff : length Z s.X₁+length Z s.X₂+Cycle61.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤
          Cycle61.Arithmetic.B*Mrow)
        {Label : Type}[Fintype Label]
        (reflected second : Bool)(R seed₀ : Ideal O)(bin : ℤ×(Fin 5→ ℤ))(t : ℝ)
        (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
        let first:=fun l=>geometryFirstLabel s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let cell:=Cycle61.Arithmetic.cellUpper
          (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
        let amp:=Mrow*Cycle61.Arithmetic.amp cell
        let childSrc:=fun l=>geometryLowFirstChild reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t (firstIndex l)
        let Rchild:=fun l=>R*geometryColumnIdeal reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let seed:=fun l=>(firstIndex l).1.val.2.1.val
        let K:=fun l=>firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first l)
        let Tsec:=fun l=>firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve bs
          (Fintype.card α) (first l)
        let p:=((bin.2 2:ℝ)+1)*Real.logb Z 2
        let c : Fin 5:=if reflected then 1 else 0
        let exponent:=Real.logb Z (volume s)-(bin.2 c:ℝ)*Real.logb Z 2+
          ((bin.2 3:ℝ)+1)*Real.logb Z 2+((bin.2 4:ℝ)+1)*Real.logb Z 2
        let sideLower:=(bin.2 2:ℝ)*Real.logb Z 2+Real.logb Z (volume s)-
          ((bin.2 c:ℝ)+1)*Real.logb Z 2+(bin.2 3:ℝ)*Real.logb Z 2+(bin.2 4:ℝ)*Real.logb Z 2
        ∀(hf₁ : ∀l,frozenCoefficient (firstIndex l).2.val
            (geometryColumnIdeal reflected s R seed₀ (Z^Mrow) Z ξ
              (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
            R s.ν s.W s.P≠0)
          (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)
          (hsource : ∀l,CenteredMomentOriginalCommonHarmonic.sourceRadius (childSrc l)≤ Z^Bnorm)
          (Tfirst : ℝ)(hTfirst : 1≤ Tfirst)(hp : p≤ Bnorm)
          (hs₀ : Squarefree seed₀)(hs₀0 : seed₀≠0)
          (hinj : Function.Injective (fun l=>(first l,seed l)))
          (hfirstshell : ∀l,Tfirst≤((seed l).absNorm:ℝ) ∧ ((seed l).absNorm:ℝ)<2*Tfirst)
          (rows : Finset ((l : Label)×GeometryLowSecondIndex reflected s R seed₀ Z Mrow amp ξ reserve bs t
              (Fintype.card α) hZ bin (firstIndex l)))
          (hOriginal : ∀r∈rows,
            (⟨firstIndex r.1,r.2⟩ : GeometryMainSecondIndex reflected s R seed₀ Z Mrow amp ξ reserve bs t
              (Fintype.card α) hZ bin)∈geometryMainNonzeroBlocks reflected s R seed₀ Z Mrow amp ξ reserve bs t
                (Fintype.card α) hZ bin hw₁ hw₂)
          (hU : ∀r∈rows,r.2.2.1∈inactiveSubsets r.2.1.val.val.1 r.2.1.val.val.2)
          (box : Finset (Fin 4→ ℤ))
          (hbox : ∀r∈rows,actualSecondDyad (childSrc r.1) (Rchild r.1) (seed r.1)
            (K r.1) (Tsec r.1) Z ξ r.2∈box),
        let datum : rows→ SecondInputDatum α:=fun r : rows=>geometryLowSecondDatum reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2
        ∀(B₂ : (r : rows)→ actualAllocations (childSrc r.val.1).pools
            (if second then (datum r).D else (datum r).C))
          (rwitness : (r : rows)→ secondLiveRows (fun _:Unit=>(datum r).block))
          (hf₂ : ∀r,frozenCoefficient (B₂ r).val
            (if second then (datum r).D else (datum r).C) (datum r).R
            (childSrc r.val.1).ν (childSrc r.val.1).W (childSrc r.val.1).P≠0),
        let q:=fun r : rows=>geometryLowActualChain reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 second (B₂ r)
        let g:=fun r : rows=>geometryLowActualGeometry reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 second (B₂ r)
          (rwitness r) (hf₁ r.val.1) (hf₂ r)
        ∀(χ₀ : rows→ RayFourExpansion.RayCharacter)(χ ψ : RayFourExpansion.RayCharacter)
          (m : O)(hm₀ : m≠0)(hml : goodLambda∣m)(hm₂ : (2:O)∣m)
          (hP : ∀r,(q r).R₂*(q r).E₂≠0)
          (hPN : ∀r,(((q r).R₂*(q r).E₂).absNorm:ℝ)≤ Z^Bmask)
          (divisorSeed : rows→ Ideal O)(hE₂ : ∀r,Supported (q r).E₂)
          (hdivisor : ∀r,divisorSeed r∣(q r).E₂)(p₀ : Profiles a b)
          (hp₁ : s.W₁=(p₀.profile 0 : ℝ→ ℂ))(hp₂ : s.W₂=(p₀.profile 1 : ℝ→ ℂ))
          (Ψ : 𝓢(ℝ,ℂ))
          (hsourceOriginal : CenteredMomentOriginalCommonHarmonic.sourceRadius s≤ Z^Bmass)
          (hplain₁ : ∀x,s.W₁ x≠0→ ap≤ x)(hplain₂ : ∀x,s.W₂ x≠0→ ap≤ x)
          (hpool : ∀j I,I∈s.pools j→ (I.absNorm:ℝ)≤ Z^U)
          (hwindowSource : ∀j,logWindow (s.lo j) (s.hi j)≤ window)
          (hplainScale : ∀side j,Cycle61.Physical.sourcePlainScales s.toData.toSource side j≤ Z^L),
        let ray:=if second then ψ⁻¹ else χ
        let ordinaryRows:=fun r : rows=>mainLowSourceRows second
          (ordinarySecondDatum (datum r) (χ₀ r) (internalQ Q η₀) m) (fun _=>True)
        let canonical:=fun r : rows=>mainLowCanonicalSelector M H hH (datum r) (χ₀ r) χ ψ
          (internalQ Q η₀) hQ72 m hm₀ hml hm₂ Z Bmask hZ second
          (by exact hP r) (by exact hPN r) η₀ (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hbeta hβhi
        ∃select : (r : rows)→ ordinaryRows r→ BufferIndex e,
          (∀r,select r=canonical r) ∧
          (∀r pbin z,z∈mainLowPaymentRows (ordinaryRows r) (select r) pbin→ 1≤ pbin.1.val) ∧
        let src:=fun r=>withHeight (q r).first ((g r).datum.τ ray) heightV
        let Ds:=fun r : rows=>(datum r).block.divisors.filter Squarefree
        let unionDs:=sharedProjectors Ds
        let firstMass:=fun l=>geometryFirstHighMass reflected s R seed₀ Ψ Mrow Z ξ εmass
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let physical:=geometryHighFactor reflected (geometrySupportConstant N supply ap ap) bin
        let error:=εwidth*Mrow+ξ/2-Mrow*(1/3750000)+εold+2*ε*d*(Fintype.card α:ℝ)+
          (2*Cycle61.Arithmetic.q0/9)*(frequencyLoss Z 32 ξ+reserve+εpad*Mrow)+Cycle61.Arithmetic.q0*mesh+pad
        let exponentFull:=Bmass*εmass+amp+error+εv+Bnorm*εshell+εlabels
        let factor : ℝ:=mainLowQuantitativeFactor Cg b Cs (p₀.control Sp) heightV height physical Z
          exponentFull (seed₀.absNorm:ℝ) N degree box.card
        let coefficient:=fun (r : rows)(_D : Ideal O)=>
          firstMass r.val.1/volume (childSrc r.val.1)*(g r).datum.K*
            normalizer (g r).datum.C (g r).datum.D (g r).datum.inactive
        let value:=fun (r : rows)(D : Ideal O)(z : O)=>
          ‖normalizedColumn (src r) (q r).E₂ (hE₂ r) (q r).R₂ (divisorSeed r) D z‖^2
        (∀pbin : BufferIndex e,1≤ pbin.1.val→ 
          (∑r,∑D∈Ds r,coefficient r D*
            (∑z∈mainLowPaymentRows (ordinaryRows r) (select r) pbin,value r D z))≤
          (16*factor)*(Cu*Z^(εunion+3*(((N:ℝ)+2)*U)*εshell))) ∧
        mainLowCompleteSelectedCost ordinaryRows select Ds coefficient value≤
          (Fintype.card (BufferIndex e):ℝ)*((16*factor)*(Cu*Z^(εunion+3*(((N:ℝ)+2)*U)*εshell)))

attribute [local irreducible] geometryMainNonzeroBlocks MainLowQuantitativeBinSpec mainLowCompleteSelectedCost
  actual_geometry_selected_low_full_columns

set_option maxHeartbeats 320000 in
def actual_main_low_quantitative_bins {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0< A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤ B) (ha : 0< a) (ha' : a≤1/4) (hb : 1≤ b)
    (hBmask : 0≤ Bmask) (hMcap : 0< Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤ Rwidth) (hdmax : 0≤ dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0< d) (hdsupply : Mcap+Bmask+margin≤ d) (hdm : d≤ dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤ bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0< Mmin)
    (εshell : ℝ) (heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(hCs : 1≤ Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0< supply)(hev : 0<εv)
    (hBnorm : 0≤ Bnorm)(hel : 0<εlabels)
    (ap εmass Bmass : ℝ)(hap : 0< ap)(hemass : 0≤εmass)
    (U εunion : ℝ)(hUcap : 0≤ U)(heunion : 0<εunion)
    (window pad : ℝ)(hwindow : 0≤ window)(hpad : 0< pad)(hL0 : 0≤ L) (hτgap : 2*τ< d*η) (hBmassNorm : Bmass≤ Bnorm) :
    Σdegree : ℕ,ΣSp : Finset (ℕ×ℕ),ΣCu : ℝ,
      PLift (0< Cu) ×
      (∀(η₀ : Character)(Q : Ideal O)(hQM : Q≤ M),
        internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → ∀hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)},     
        ΣCg : ℝ,PLift (0< Cg ∧ ∀ᶠZ : ℝ in atTop,2≤ Z ∧
          MainLowQuantitativeBinSpec (α:=α) M H hH
      W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      degree Sp Cg Cu η₀ Q hQM hQ72 Z)) := by
  let k:=actual_geometry_selected_low_full_columns (α:=α) M H hH
      W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
  refine ⟨k.1,k.2.1,k.2.2.1,k.2.2.2.1,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  let hc:=k.2.2.2.2 η₀ Q hQM hQ0 hQt hQ72
  refine ⟨hc.1,PLift.up ⟨hc.2.down.1,?_⟩⟩
  filter_upwards [hc.2.down.2,eventual_main_low_payment_high_gate e τ d η hτ hτgap] with Z hz hg
  refine ⟨hz.1,?_⟩
  unfold MainLowQuantitativeBinSpec
  intro hZ s θ w σ freq heightV height mesh hcard hmass hsupply' hm hsη hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq hT hfreqbin hβhi
    Mrow reserve ξ hMmin hω hξ hMcap' hzslot haff Label _ reflected second R seed₀ bin t firstIndex
    first cell amp childSrc Rchild seed K Tsec p c exponent sideLower hf₁ hw₁ hw₂ hsource
    Tfirst hTfirst hp hs₀ hs₀0 hinj hfirstshell
    rows hOriginal hU box hbox datum B₂ rwitness hf₂ q g χ₀ χ ψ m hm₀ hml hm₂ hP hPN
    divisorSeed hE₂ hdivisor p₀ hp₁ hp₂ Ψ hsourceOriginal hplain₁ hplain₂ hpool
    hwindowSource hplainScale ray ordinaryRows canonical
  have hsourceNorm : CenteredMomentOriginalCommonHarmonic.sourceRadius s≤ Z^Bnorm :=
    hsourceOriginal.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hBmassNorm)
  have hfirst:=actual_main_low_first_source_gates reflected s R seed₀ (Z^Mrow) Z ξ Bnorm
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hs₀ hw₁ hw₂ hsourceNorm bin firstIndex
  have hf:=fun l=>And.intro (hfirst l).1 (hfirst l).2.1
  have heq:=fun l=>(hfirst l).2.2.1
  have hfirstseed:=fun l=>And.intro (hfirst l).2.2.2.1 (hfirst l).2.2.2.2.1
  have hfirstnorm:=fun l=>And.intro (hfirst l).2.2.2.2.2.1 (hfirst l).2.2.2.2.2.2.1
  have hscalar:=actual_geometry_low_bin_scalar_gates s R seed₀ (Z^Mrow) Z ξ Bmass
    (Real.logb Z (volume s)) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hZ hs₀ hw₁ hw₂
    hsourceOriginal bin reflected
  have hrad := fun l=>(hscalar.2 (firstIndex l).1.val).1
  have hgeom := fun l=>(hscalar.2 (firstIndex l).1.val).2.1
  have hside := fun l=>(hscalar.2 (firstIndex l).1.val).2.2
  have hfields (r : rows) : (g r).datum=datum r ∧
      (q r).R₂*(q r).E₂=(datum r).R*(if second then (datum r).D else (datum r).C) := ⟨rfl,rfl⟩
  let st:=fun r : rows=>retainedState Z Bmask hZ ((g r).datum.τ ray) (internalQ Q η₀)
    ((q r).R₂*(q r).E₂) (hP r) (hPN r) (g r).datum.radius (g r).datum.C (g r).datum.D (g r).datum.inactive
  have hst (r : rows) : st r=retainedState Z Bmask hZ
      (if second then (datum r).τ ψ⁻¹ else (datum r).τ χ) (internalQ Q η₀)
      ((datum r).R*(if second then (datum r).D else (datum r).C))
      (by rw [←(hfields r).2];exact hP r) (by rw [←(hfields r).2];exact hPN r)
      (datum r).radius (datum r).C (datum r).D (datum r).inactive := by
    cases second <;> rfl
  let select:=canonical
  have hselect (r : rows):=actual_main_low_canonical_payment_bins M H hH (datum r) (χ₀ r) χ ψ
    (internalQ Q η₀) hQ72 m hm₀ hml hm₂ Z Bmask hZ second
    (by rw [←(hfields r).2];exact hP r) (by rw [←(hfields r).2];exact hPN r)
    η₀ (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hbeta hβhi
  refine ⟨select,fun _=>rfl,fun r pbin z hz=>(hselect r pbin z hz).2.2.2.1,?_⟩
  intro src Ds unionDs firstMass physical error exponentFull factor coefficient value
  have hbins : ∀pbin : BufferIndex e,1≤ pbin.1.val→ 
      (∑r,∑D∈Ds r,coefficient r D*
        (∑z∈mainLowPaymentRows (ordinaryRows r) (select r) pbin,value r D z))≤
      (16*factor)*(k.2.2.1*Z^(εunion+3*(((N:ℝ)+2)*U)*εshell)) := by
    intro pbin hpbin
    have hbin:=main_low_payment_height_bin pbin hpbin heightV height (Z^τ)
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) hfreqbin
    have hlow : (51/100:ℝ)≤167/200 := by norm_num
    have hk:=hz.2 hZ s θ w σ freq heightV height mesh (167/200) pbin.1.val
      hcard hmass hsupply' hm hsη hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq
      hlow (le_refl _) hbin (hg.2.2 pbin) Mrow reserve ξ hMmin hω hξ hMcap' hzslot haff
      reflected second R seed₀ bin t firstIndex hf heq hf₁ hw₁ hw₂ hsource
      Tfirst p exponent hTfirst hp hs₀ hs₀0 hinj hfirstseed hfirstnorm hrad hgeom hfirstshell
      rows hU box hbox B₂ rwitness hf₂ (fun _=>ray) hP hPN
      divisorSeed hE₂ hdivisor p₀ hp₁ hp₂
      (fun r=>mainLowPaymentRows (ordinaryRows r) (select r) pbin) (fun _ _=>(1:ℝ))
      (fun _ _ _=>zero_le_one)
      (fun r z hz=>by
        have h:=(hselect r pbin z hz)
        change (st r).radial.keep z ∧ ActualLow M H hH (st r) η₀
          (inf_le_left.trans hQM) inf_le_right (167/200) e (3*(pbin.1.val+1:ℕ)*Z^τ) z
        simpa only [hst r] using (And.intro h.1 h.2.1))
      (fun r z hz=>by
        have h:=(hselect r pbin z hz).2.2.1
        change (1:ℝ)≤((st r).radial.profile (‖eisEmbedding z‖^2/(st r).radial.scale)).re
        simpa only [hst r,normValue_eq_embedding] using h)
      Ψ hsourceOriginal hplain₁ hplain₂ sideLower hside hpool hwindowSource hplainScale
    change (∑r : rows,∑D∈Ds r,
      (firstMass r.val.1/volume (childSrc r.val.1)*(g r).datum.K*
        normalizer (g r).datum.C (g r).datum.D (g r).datum.inactive)*
        (∑z∈mainLowPaymentRows (ordinaryRows r) (select r) pbin,
          (1:ℝ)*‖normalizedColumn (src r) (q r).E₂ (hE₂ r) (q r).R₂ (divisorSeed r) D z‖^2))≤
      mainLowQuantitativeFactor hc.1 b Cs (p₀.control k.2.1) heightV height physical Z
        ((Bmass*εmass-sideLower)+amp+p+exponent+error+εv+Bnorm*εshell+εlabels)
        (seed₀.absNorm:ℝ) N k.1 box.card*
        (k.2.2.1*Z^(εunion+3*(((N:ℝ)+2)*U)*εshell)) at hk
    have hexp : (Bmass*εmass-sideLower)+amp+p+exponent+error+εv+Bnorm*εshell+εlabels=
        exponentFull-sideLower+p+exponent := by dsimp only [exponentFull];ring
    rw [hexp,main_low_quantitative_factor_bin_payment hc.1 b Cs (p₀.control k.2.1)
      heightV height physical Z exponentFull p exponent sideLower (seed₀.absNorm:ℝ)
      N k.1 box.card hZ hscalar.1] at hk
    simpa only [one_mul] using hk

  refine ⟨hbins,?_⟩
  have hphysical : 0≤ physical :=
    (geometry_high_factor_pos reflected (geometrySupportConstant N supply ap ap) bin
      (geometrySupportConstant_pos N supply ap ap hsupply hap hap)).le
  have hfactor : 0≤ factor := mainLowQuantitativeFactor_nonneg hc.1 b Cs (p₀.control k.2.1)
    heightV height physical Z exponentFull (seed₀.absNorm:ℝ) N k.1 box.card
    hc.2.down.1.le (zero_le_one.trans hCs) hheight hphysical (zero_lt_one.trans hZ) (by positivity)
  unfold mainLowCompleteSelectedCost
  exact main_low_payment_complete_cost_le ordinaryRows select Ds coefficient value _
    (mul_nonneg (mul_nonneg (by norm_num) hfactor) (mul_nonneg k.2.2.2.1.down.le (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)))
    (fun r pbin z hz=>(hselect r pbin z hz).2.2.2.1) hbins

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.mainLowFamilyCanonicalSelector
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_low_canonical_zero_bin
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_low_quantitative_height_identity
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_low_canonical_payment_bins
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_low_quantitative_factor_bin_payment
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_low_payment_complete_cost_le
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_low_quantitative_bins

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainLowQuantitativePayment -/
