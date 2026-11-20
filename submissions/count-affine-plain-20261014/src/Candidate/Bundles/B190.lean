/- Cycle61 successor parameter adaptation by Zhongpai Gao, with AI assistance. Nominal θ=4374299/5000000, q=67/100; exact reserves and actual source consumers are changed by scoped ownership maps. Original notices/provenance remain intact. Full source replay and independent verification are pending. -/
/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B135
import Candidate.Bundles.B163
import Candidate.Bundles.B164
import Candidate.Bundles.B166
import Candidate.Bundles.B168
import Candidate.Bundles.B183

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAllocationCardinality; sha256 6dbc42904f7f40b3f03687779c347d16c31d24ab36f331d246f1837bd14bb817 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                         

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn
local notation "O" => HeckeFamily.O

variable {ι : Type*} [Fintype ι]
variable (reflected : Bool) (s : Input ι) (R seed : Ideal O)
  (K Z ξ M A : ℝ) (hK : 0< K) (key : ℤ×(Fin 5→ℤ))
  (weight : Cycle61JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
  (n N : ℕ) (hn : n≤ N) (b : ℝ)
  (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))
  (B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed K Z ξ hK key j))

include hn

/-- This changes only the outer allocation weight. The physical source and
its Fourier cutoff must retain their actual slot cardinality. -/
theorem geometry_allocation_weight_card_scale :
    geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j B=
      (max 1 b)^(N-n)*geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight n b j B := by
  classical
  have hp : (max 1 b)^N=(max 1 b)^(N-n)*(max 1 b)^n := by
    rw [←pow_add,Nat.sub_add_cancel hn]
  unfold geometryAllocationWeight
  dsimp only
  split_ifs
  · rw [hp]
    ring
  · simp

theorem geometry_allocation_weight_card_mono :
    geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight n b j B≤
      geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j B := by
  rw [geometry_allocation_weight_card_scale reflected s R seed K Z ξ M A hK key weight n N hn b j B]
  have hp : (1:ℝ)≤(max 1 b)^(N-n):=one_le_pow₀ (le_max_left 1 b)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hp
    (geometryAllocationWeight_nonneg reflected s R seed K Z ξ M A hK key weight n b j B)

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_allocation_weight_card_scale
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_allocation_weight_card_mono

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAllocationCardinality -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineErrorAggregate; sha256 aed33f77949dedee474922c9b21b5aeedc18b24f6375c356078a31f2e5268b14 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                                
                                                                 
                                                                    
                                                         

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationErrorEnergy
open CenteredMomentPrimeElements CenteredMomentAllocatedRayDictionary CenteredMomentSectorLocalization
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstAnnularInput
open RayFourExpansion Cycle61Moment CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O
attribute [local instance] geometryErrorOrdinaryContractionDecidable

/-- The literal signed Mellin shift admits independent polynomial weights. -/
theorem geometry_error_analytic_height_factor (second : Bool)(v height t u : ℝ)
    (degree : ℕ)(hh : 0≤ height) :
    (1+|v+2*Real.pi*(u-(if second then -t else t))|+height)^degree≤
      (2+4*Real.pi)^degree*(1+|v|+height)^degree*(1+‖t‖)^degree*(1+‖u‖)^degree := by
  have hs : |u-(if second then -t else t)|≤|t|+|u| := by
    cases second <;> simp only [Bool.false_eq_true,reduceIte,sub_neg_eq_add]
    · exact (abs_sub u t).trans_eq (add_comm _ _)
    · exact (abs_add_le u t).trans_eq (add_comm _ _)
  have ha : |v+2*Real.pi*(u-(if second then -t else t))|≤|v|+2*Real.pi*(|t|+|u|) := by
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_of_nonneg (by positivity : 0≤2*Real.pi)]
    exact add_le_add_right (mul_le_mul_of_nonneg_left hs (by positivity : 0≤2*Real.pi)) _
  have hb:=geometry_shifted_height_product v height t u hh
  have hx : 1+|v+2*Real.pi*(u-(if second then -t else t))|+height≤
      (2+4*Real.pi)*(1+|v|+height)*(1+|t|)*(1+|u|) := by
    have hp : 0≤1+|v|+height+2*Real.pi*(|t|+|u|):=by positivity
    calc
      _≤1+|v|+height+2*Real.pi*(|t|+|u|) := by linarith only [ha]
      _≤2*(1+|v|+height+2*Real.pi*(|t|+|u|)) := by linarith only [hp]
      _≤ _:=hb
  have hp:=pow_le_pow_left₀ (by positivity : 0≤1+|v+2*Real.pi*(u-(if second then -t else t))|+height) hx degree
  simpa only [mul_pow,Real.norm_eq_abs] using hp

/-- A generic packet before the concrete geometry allocation is transported. -/
def geometryErrorActiveScalarPacket {ι : Type} [Fintype ι]
    (s : Input ι) (reflected second : Bool) (l : FirstSourceLabel) (L R C : Ideal O)
    (B : actualAllocations s.pools C) (χ : Character) (t : ℝ)
    (υ : Character) (v : ℝ) (p : O) (k : ℕ) (Z M amp δ reserve error εcommon : ℝ) : ℝ :=
  let u:=child s C R B χ t
  ∑Bp : actualAllocations (activeInput u).pools ((Ideal.span {p})^k),
    let source:=child u ((Ideal.span {p})^k) (R*C)
      (errorActiveAllocation u _ Bp) υ v
    ∑label∈actualSecondLabels source ((R*C)*(Ideal.span {p})^k) L,
      extractedErrorLabelScalar reflected second l label Z M amp δ reserve error εcommon
        (volume s) (volume source) p k

/-- Preserve the literal allocation value while transporting its membership proof. -/
def geometryErrorTransportAllocation {ι : Type} [Fintype ι] (s : Input ι)
    (C D : Ideal O) (h : C=D) (B : actualAllocations s.pools C) : actualAllocations s.pools D :=
  ⟨B.val,by rw [←h]; exact B.property⟩

/-- Transport the allocator explicitly before comparing physical packets. -/
theorem geometry_error_active_scalar_packet_eq_physical {ι : Type} [Fintype ι]
    (s : Input ι) (reflected second : Bool) (l : FirstSourceLabel) (L R C : Ideal O)
    (B : actualAllocations s.pools C) (hC : C=if reflected then l.1.2 else l.1.1)
    (χ : Character) (t : ℝ) (υ : Character) (v : ℝ) (p : O) (k : ℕ)
    (Z M amp δ reserve error εcommon : ℝ) :
    geometryErrorActiveScalarPacket s reflected second l L R C B χ t υ v p k Z M amp δ reserve error εcommon=
    geometryErrorPhysicalScalarPacket s reflected second l L R
      (geometryErrorTransportAllocation s C _ hC B) χ t υ v p k Z M amp δ reserve error εcommon := by
  subst C
  have hB : geometryErrorTransportAllocation s (if reflected then l.1.2 else l.1.1)
      (if reflected then l.1.2 else l.1.1) rfl B=B := Subtype.ext rfl
  rw [hB]
  let C₀:=if reflected then l.1.2 else l.1.1
  let u₀:=child s C₀ R B χ t
  let Q₀:=Ideal.span {p}
  let f : actualAllocations u₀.pools (Q₀^k)→ℝ:=fun Bp=>
    let source:=child u₀ (Q₀^k) (R*C₀) Bp υ v
    ∑label∈actualSecondLabels source ((R*C₀)*Q₀^k) L,
      extractedErrorLabelScalar reflected second l label Z M amp δ reserve error εcommon
        (volume s) (volume source) p k
  exact (error_lifted_active_allocations_sum u₀ Q₀ k f).symm

/-- Separate analytic Mellin heights and pay the explicit menu box and
physical scalar exponents. The sum contains no new analytic hypothesis. -/
theorem geometry_error_scalar_height_box_payment
    (second : Bool)(Z v height te u total ray Cg control lower box Cb K eproj eshell ebox ephysical L₂ : ℝ)
    (degree windowDegree : ℕ)(hZ : 1< Z)(hh : 0≤ height)(hray : 0≤ ray)(hg : 0≤ Cg)
    (hl : 0< lower)(hb : 0≤ box)(hCb : 0≤ Cb)(hK : 0≤ K)(hdegree : degree≤2*windowDegree)
    (hbox : box≤ Cb*Z^ebox)
    (hpaid : total≤(ray*Cg*control^2*(1+|v+2*Real.pi*(u-(if second then -te else te))|+height)^degree*
      Z^(eproj+3*L₂*eshell))*(box/lower)*(K*Z^ephysical)) :
    total≤(ray*Cg*control^2*(2+4*Real.pi)^degree*(Cb/lower)*K*(1+|v|+height)^degree*
      Z^(eproj+3*L₂*eshell+ebox+ephysical))*(1+‖te‖)^degree*(1+‖u‖)^(2*windowDegree) := by
  have hv:=geometry_error_analytic_height_factor second v height te u degree hh
  have h1 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hv (by positivity : 0≤ ray*Cg*control^2))
    (Real.rpow_nonneg (zero_lt_one.trans hZ).le (eproj+3*L₂*eshell))
  have h2 := mul_le_mul h1 (div_le_div_of_nonneg_right hbox hl.le)
    (div_nonneg hb hl.le) (by positivity)
  have h3 := mul_le_mul_of_nonneg_right h2 (by positivity : 0≤ K*Z^ephysical)
  have hu : (1+‖u‖)^degree≤(1+‖u‖)^(2*windowDegree) :=
    pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg u) : (1:ℝ)≤1+‖u‖) hdegree
  calc
    total≤ _ := hpaid.trans h3
    _=(ray*Cg*control^2*(2+4*Real.pi)^degree*(Cb/lower)*K*(1+|v|+height)^degree*
      Z^(eproj+3*L₂*eshell+ebox+ephysical))*(1+‖te‖)^degree*(1+‖u‖)^degree := by
      simp only [Real.rpow_add (zero_lt_one.trans hZ)]
      ring
    _≤ _:=mul_le_mul_of_nonneg_left hu (by positivity)

variable {α : Type}[Fintype α][DecidableEq α]
section Source
variable (reflected second : Bool)(s : Input α)(R seed : Ideal O)
  (Z M amp ξ reserve b t v error εcommon Mprice Aprice : ℝ)(hZ : 1< Z)
  (key : ℤ×(Fin 5→ℤ))(P : Finset (Ideal O))
  (phase : Cycle61JointSource.SourceCoordinate s R seed (Z^M) Z ξ→ℂ)
  (υ : GeometryLowFirstIndex (α:=α) reflected s R seed (Z^M) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key→ elementPool P→ Fin 3→ RayCharacter→ Character)
local notation "hK" => Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
local notation "First" => GeometryLowFirstIndex (α:=α) reflected s R seed (Z^M) Z ξ hK key
local notation "Sources" => GeometryJointErrorSourceIndex (α:=α) reflected s R seed Z M ξ t hZ key P

private theorem geometry_error_column_eq_label (q : First) :
    geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key q.1.val=
      if reflected then (geometryFirstLabel s R seed (Z^M) Z ξ hK key q.1.val).1.2
      else (geometryFirstLabel s R seed (Z^M) Z ξ hK key q.1.val).1.1 := by
  rfl

private def geometryJointErrorFirstAllocation (q : First) :
    actualAllocations s.pools (if reflected then
      (geometryFirstLabel s R seed (Z^M) Z ξ hK key q.1.val).1.2 else
      (geometryFirstLabel s R seed (Z^M) Z ξ hK key q.1.val).1.1) :=
  geometryErrorTransportAllocation s _ _
    (geometry_error_column_eq_label reflected s R seed Z M ξ hZ key q) q.2

private def geometryJointErrorRawScalarPacket (q : First)(p : elementPool P)(i : Fin 3)(ψ : RayCharacter) : ℝ :=
  geometryErrorActiveScalarPacket s reflected second
    (geometryFirstLabel s R seed (Z^M) Z ξ hK key q.1.val) q.1.val.2.1.val R
    (geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key q.1.val) q.2
    (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK key q.1.val) t
    (υ q p i ψ) v p.val (errorIndex i+1) Z M amp (frequencyLoss Z 32 ξ) reserve error εcommon

private theorem geometry_joint_error_raw_scalar_packet_eq_physical
    (q : First)(p : elementPool P)(i : Fin 3)(ψ : RayCharacter) :
    geometryJointErrorRawScalarPacket reflected second s R seed Z M amp ξ reserve t v error εcommon hZ key P υ q p i ψ=
    geometryErrorPhysicalScalarPacket s reflected second
      (geometryFirstLabel s R seed (Z^M) Z ξ hK key q.1.val) q.1.val.2.1.val R
      (geometryJointErrorFirstAllocation reflected s R seed Z M ξ hZ key q)
      (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK key q.1.val) t
      (υ q p i ψ) v p.val (errorIndex i+1) Z M amp (frequencyLoss Z 32 ξ) reserve error εcommon := by
  exact geometry_error_active_scalar_packet_eq_physical s reflected second _ _ R _ q.2
    (geometry_error_column_eq_label reflected s R seed Z M ξ hZ key q) _ t _ v _ _ Z M amp _ reserve error εcommon

/-- One literal source-local label sum, before the sigma carrier is collected. -/
def geometryJointErrorRawScalarLabelSum (l : Sources) : ℝ :=
  let source:=geometryErrorChild reflected s R seed Z M ξ t hZ key
    l.1 l.2.1.val l.2.2.1 l.2.2.2.2 (υ l.1 l.2.1 l.2.2.1 l.2.2.2.1) v
  ∑label∈actualSecondLabels source
      ((R*geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key l.1.1.val)*
        (Ideal.span {l.2.1.val})^(errorIndex l.2.2.1+1)) l.1.1.val.2.1.val,
    extractedErrorLabelScalar reflected second
      (geometryFirstLabel s R seed (Z^M) Z ξ hK key l.1.1.val) label
      Z M amp (frequencyLoss Z 32 ξ) reserve error εcommon (volume s) (volume source)
      l.2.1.val (errorIndex l.2.2.1+1)

private theorem geometry_joint_error_raw_scalar_packet_eq_labels
    (q : First)(p : elementPool P)(i : Fin 3)(ψ : RayCharacter) :
    geometryJointErrorRawScalarPacket reflected second s R seed Z M amp ξ reserve t v error εcommon hZ key P υ q p i ψ=
    ∑Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s R seed (Z^M) Z ξ hK key t q)).pools
        ((Ideal.span {p.val})^(errorIndex i+1)),
      geometryJointErrorRawScalarLabelSum reflected second s R seed Z M amp ξ reserve t v error εcommon hZ key P υ
        ⟨q,p,i,ψ,Bp⟩ := by
  rfl

/-- Exact raw scalar menu; its first allocation weight is undivided and its
56/P payment is retained inside each prime/branch term. -/
def geometryJointErrorRawScalarCost (n : ℕ) : ℝ :=
  ∑l : Sources,
    ((56/(P.card:ℝ))*geometryAllocationWeight reflected s R seed (Z^M) Z ξ Mprice Aprice
      hK key phase n b l.1.1.val l.1.2*(16*(errorIndex l.2.2.1+2:ℝ)))*
    geometryJointErrorRawScalarLabelSum reflected second s R seed Z M amp ξ reserve t v error εcommon hZ key P υ l

/-- The corresponding first-source physical scalar sum. -/
def geometryJointErrorPhysicalScalarCost (n : ℕ) : ℝ :=
  ∑q : First,geometryAllocationWeight reflected s R seed (Z^M) Z ξ Mprice Aprice hK key phase n b
    q.1.val q.2*geometryErrorPhysicalCompleteCost s reflected second
      (geometryFirstLabel s R seed (Z^M) Z ξ hK key q.1.val) q.1.val.2.1.val R
      (geometryJointErrorFirstAllocation reflected s R seed Z M ξ hZ key q)
      (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK key q.1.val) t P (υ q) v
      Z M amp (frequencyLoss Z 32 ξ) reserve error εcommon

/-- Sigma collection reproduces the genuine physical complete cost exactly. -/
theorem geometry_joint_error_raw_scalar_cost_eq_physical (n : ℕ) :
  geometryJointErrorRawScalarCost reflected second s R seed Z M amp ξ reserve b t v error εcommon
    Mprice Aprice hZ key P phase υ n=
  geometryJointErrorPhysicalScalarCost reflected second s R seed Z M amp ξ reserve b t v error εcommon
    Mprice Aprice hZ key P phase υ n := by
  unfold geometryJointErrorRawScalarCost geometryJointErrorPhysicalScalarCost geometryErrorPhysicalCompleteCost
  simp only [Fintype.sum_sigma,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro row _
  apply Finset.sum_congr rfl
  intro alloc _
  let q : First:=⟨row,alloc⟩
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro ψ _
  have hp:=geometry_joint_error_raw_scalar_packet_eq_physical reflected second s R seed Z M amp ξ reserve
    t v error εcommon hZ key P υ q p i ψ
  let coeff:ℝ:=(56/(P.card:ℝ))*geometryAllocationWeight reflected s R seed (Z^M) Z ξ Mprice Aprice
    hK key phase n b q.1.val q.2*(16*(errorIndex i+2:ℝ))
  let f:=fun Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s R seed (Z^M) Z ξ hK key t q)).pools
      ((Ideal.span {p.val})^(errorIndex i+1))=>
    geometryJointErrorRawScalarLabelSum reflected second s R seed Z M amp ξ reserve t v error εcommon hZ key P υ
      ⟨q,p,i,ψ,Bp⟩
  have hs := (Finset.mul_sum (s:=Finset.univ) (f:=f) coeff).symm
  have hpacket := geometry_joint_error_raw_scalar_packet_eq_labels reflected second s R seed Z M amp ξ reserve
    t v error εcommon hZ key P υ q p i ψ
  refine hs.trans ((congrArg (fun x:ℝ=>coeff*x) hpacket.symm).trans ?_)
  rw [hp]
  ring

private theorem geometry_error_source_physical_cost_nonneg
    (hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)(q : First) :
    0≤ geometryErrorPhysicalCompleteCost s reflected second
      (geometryFirstLabel s R seed (Z^M) Z ξ hK key q.1.val) q.1.val.2.1.val R
      (geometryJointErrorFirstAllocation reflected s R seed Z M ξ hZ key q)
      (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK key q.1.val) t P (υ q) v
      Z M amp (frequencyLoss Z 32 ξ) reserve error εcommon :=
  geometry_error_physical_complete_cost_nonneg s reflected second _ _ R _ _ t P (υ q) v Z M amp
    _ reserve error εcommon (zero_lt_one.trans hZ).le
    (actual_first_live_squarefree (geometryFirstSource s R seed (Z^M) Z ξ hK key)
      (fun _=>CenteredMomentLogDyadic.logAnnulus) q.1.val q.1.property) hz₁ hz₂

/-- The positivity comes from the genuine physical supported-label cost. -/
theorem geometry_joint_error_raw_scalar_cost_nonneg (n : ℕ)
    (hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0) :
    0≤ geometryJointErrorRawScalarCost reflected second s R seed Z M amp ξ reserve b t v error εcommon
      Mprice Aprice hZ key P phase υ n := by
  rw [geometry_joint_error_raw_scalar_cost_eq_physical]
  unfold geometryJointErrorPhysicalScalarCost
  exact Finset.sum_nonneg (fun q _=>mul_nonneg
    (geometryAllocationWeight_nonneg reflected s R seed (Z^M) Z ξ Mprice Aprice hK key phase n b q.1.val q.2)
    (geometry_error_source_physical_cost_nonneg reflected second s R seed Z M amp ξ reserve t v error εcommon hZ key P υ hz₁ hz₂ q))

/-- Only the outer allocation payment is enlarged. The raw source and its
actual-cardinality Fourier data remain fixed. -/
theorem geometry_joint_error_raw_scalar_cost_card_mono (n N : ℕ)(hn : n≤ N)
    (hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0) :
    geometryJointErrorRawScalarCost reflected second s R seed Z M amp ξ reserve b t v error εcommon
      Mprice Aprice hZ key P phase υ n≤
    geometryJointErrorRawScalarCost reflected second s R seed Z M amp ξ reserve b t v error εcommon
      Mprice Aprice hZ key P phase υ N := by
  rw [geometry_joint_error_raw_scalar_cost_eq_physical,geometry_joint_error_raw_scalar_cost_eq_physical]
  unfold geometryJointErrorPhysicalScalarCost
  exact Finset.sum_le_sum (fun q _=>mul_le_mul_of_nonneg_right
    (geometry_allocation_weight_card_mono reflected s R seed (Z^M) Z ξ Mprice Aprice hK key phase n N hn b q.1.val q.2)
    (geometry_error_source_physical_cost_nonneg reflected second s R seed Z M amp ξ reserve t v error εcommon hZ key P υ hz₁ hz₂ q))


/-- The numerical right side is exactly the frozen raw menu label conclusion.
All analytic estimation is supplied by that named conclusion before collection. -/
theorem geometry_joint_error_scalar_menu_collect
    (n : ℕ)(menu : Sources→ℝ)(analytic lower boxCard : ℝ)
    (hmenu : ∀l,menu l≤ analytic*
      (((56/(P.card:ℝ))*geometryAllocationWeight reflected s R seed (Z^M) Z ξ Mprice Aprice
        hK key phase n b l.1.1.val l.1.2*(16*(errorIndex l.2.2.1+2:ℝ))/lower)*
        (boxCard*geometryJointErrorRawScalarLabelSum reflected second s R seed Z M amp ξ reserve
          t v error εcommon hZ key P υ l))) :
    (∑l,menu l)≤ analytic*(boxCard/lower)*
      geometryJointErrorRawScalarCost reflected second s R seed Z M amp ξ reserve b t v error εcommon
        Mprice Aprice hZ key P phase υ n := by
  calc
    _≤∑l : Sources,analytic*
      (((56/(P.card:ℝ))*geometryAllocationWeight reflected s R seed (Z^M) Z ξ Mprice Aprice
        hK key phase n b l.1.1.val l.1.2*(16*(errorIndex l.2.2.1+2:ℝ))/lower)*
        (boxCard*geometryJointErrorRawScalarLabelSum reflected second s R seed Z M amp ξ reserve
          t v error εcommon hZ key P υ l)) := Finset.sum_le_sum (fun l _=>hmenu l)
    _=_ := by
      unfold geometryJointErrorRawScalarCost
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun l _=>by ring)

/-- Join a genuine physical scalar payment after the exact source carrier is
collected. There is no extra first-label, ray, or extraction-allocation fee. -/
theorem geometry_joint_error_scalar_menu_physical_payment
    (n N : ℕ)(hn : n≤ N)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (menu : Sources→ℝ)(analytic lower boxCard Rpaid : ℝ)
    (ha : 0≤ analytic)(hl : 0< lower)(hb : 0≤ boxCard)
    (hmenu : ∀l,menu l≤ analytic*
      (((56/(P.card:ℝ))*geometryAllocationWeight reflected s R seed (Z^M) Z ξ Mprice Aprice
        hK key phase n b l.1.1.val l.1.2*(16*(errorIndex l.2.2.1+2:ℝ))/lower)*
        (boxCard*geometryJointErrorRawScalarLabelSum reflected second s R seed Z M amp ξ reserve
          t v error εcommon hZ key P υ l)))
    (hphysical : geometryJointErrorPhysicalScalarCost reflected second s R seed Z M amp ξ reserve b t v error εcommon
      Mprice Aprice hZ key P phase υ N≤ Rpaid) :
    (∑l,menu l)≤ analytic*(boxCard/lower)*Rpaid := by
  have hc := geometry_joint_error_raw_scalar_cost_card_mono reflected second s R seed Z M amp ξ reserve
    b t v error εcommon Mprice Aprice hZ key P phase υ n N hn hz₁ hz₂
  rw [←geometry_joint_error_raw_scalar_cost_eq_physical] at hphysical
  exact (geometry_joint_error_scalar_menu_collect reflected second s R seed Z M amp ξ reserve b t v error εcommon
    Mprice Aprice hZ key P phase υ n menu analytic lower boxCard hmenu).trans
    (mul_le_mul_of_nonneg_left (hc.trans hphysical) (mul_nonneg ha (div_nonneg hb hl.le)))

/-- Collect the exact source menu, pay the physical sum, and separate all
Mellin heights while retaining the explicit box cost. -/
theorem geometry_joint_error_scalar_menu_height_box_payment
    (n N : ℕ)(hn : n≤ N)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (menu : Sources→ℝ)(ray Cg control lower box Cb Kpaid height te u eproj eshell ebox ephysical L₂ : ℝ)
    (degree windowDegree : ℕ)(hh : 0≤ height)(hray : 0≤ ray)(hg : 0≤ Cg)
    (hl : 0< lower)(hb : 0≤ box)(hCb : 0≤ Cb)(hKpaid : 0≤ Kpaid)
    (hdegree : degree≤2*windowDegree)(hbox : box≤ Cb*Z^ebox)
    (hmenu : ∀l,menu l≤
      (ray*Cg*control^2*(1+|v+2*Real.pi*(u-(if second then -te else te))|+height)^degree*Z^(eproj+3*L₂*eshell))*
      (((56/(P.card:ℝ))*geometryAllocationWeight reflected s R seed (Z^M) Z ξ Mprice Aprice
        hK key phase n b l.1.1.val l.1.2*(16*(errorIndex l.2.2.1+2:ℝ))/lower)*
        (box*geometryJointErrorRawScalarLabelSum reflected second s R seed Z M amp ξ reserve
          t v error εcommon hZ key P υ l)))
    (hphysical : geometryJointErrorPhysicalScalarCost reflected second s R seed Z M amp ξ reserve b t v error εcommon
      Mprice Aprice hZ key P phase υ N≤ Kpaid*Z^ephysical) :
    (∑l,menu l)≤
      (ray*Cg*control^2*(2+4*Real.pi)^degree*(Cb/lower)*Kpaid*(1+|v|+height)^degree*
        Z^(eproj+3*L₂*eshell+ebox+ephysical))*(1+‖te‖)^degree*(1+‖u‖)^(2*windowDegree) := by
  have hp := geometry_joint_error_scalar_menu_physical_payment reflected second s R seed Z M amp ξ reserve
    b t v error εcommon Mprice Aprice hZ key P phase υ n N hn hz₁ hz₂ menu
    (ray*Cg*control^2*(1+|v+2*Real.pi*(u-(if second then -te else te))|+height)^degree*Z^(eproj+3*L₂*eshell))
    lower box (Kpaid*Z^ephysical) (by positivity) hl hb hmenu hphysical
  exact geometry_error_scalar_height_box_payment second Z v height te u (∑l,menu l)
    ray Cg control lower box Cb Kpaid eproj eshell ebox ephysical L₂ degree windowDegree
    hZ hh hray hg hl hb hCb hKpaid hdegree hbox (by simpa only [mul_assoc] using hp)

end Source

attribute [local irreducible] Finset.univ

/-- Normalize the row scale before specializing the dependent first carrier.
The input remains abstract while the literal Z^1 equality is eliminated. -/
theorem geometry_joint_error_physical_scalar_cost_one_payment
    (reflected second : Bool)(s : Input α)(R seed : Ideal O)
    (Z amp ξ reserve b t v error εcommon Mprice Aprice : ℝ)(hZ : 1< Z)
    (key : ℤ×(Fin 5→ℤ))(P : Finset (Ideal O))(Φ : 𝓢(ℝ,ℂ))(n : ℕ)(Rpaid : ℝ)
    (hpaid :
      let hK:=zero_lt_one.trans hZ
      let rows:=firstLiveColumns (geometryFirstSource s R seed Z Z ξ hK key) (fun _=>CenteredMomentLogDyadic.logAnnulus)
      ∀υ : (j : rows)→ actualAllocations s.pools
          (geometryColumnIdeal reflected s R seed Z Z ξ hK key j.val)→ elementPool P→ Fin 3→ RayCharacter→ Character,
      (∑j : rows,∑B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed Z Z ξ hK key j.val),
        geometryAllocationWeight reflected s R seed Z Z ξ Mprice Aprice hK key
          (fun q=>normPhase (coordinateBlock s R seed Φ Z Z ξ q)) n b j.val B*
        geometryErrorPhysicalCompleteCost s reflected second
          (geometryFirstLabel s R seed Z Z ξ hK key j.val) j.val.2.1.val R B
          (geometryColumnCharacter reflected s R seed Z Z ξ hK key j.val) t P (υ j B) v
          Z 1 amp (frequencyLoss Z 32 ξ) reserve error εcommon)≤ Rpaid) :
    ∀υ : GeometryLowFirstIndex reflected s R seed (Z^(1:ℝ)) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key→ elementPool P→ Fin 3→ RayCharacter→ Character,
    geometryJointErrorPhysicalScalarCost reflected second s R seed Z 1 amp ξ reserve b t v error εcommon
      Mprice Aprice hZ key P (fun q=>normPhase (coordinateBlock s R seed Φ (Z^(1:ℝ)) Z ξ q)) υ n≤ Rpaid := by
  let PaidAt (K₀ : ℝ) : Prop :=
    ∀hK₀ : 0< K₀,
    let rows:=firstLiveColumns (geometryFirstSource s R seed K₀ Z ξ hK₀ key) (fun _=>CenteredMomentLogDyadic.logAnnulus)
    ∀υ : GeometryLowFirstIndex reflected s R seed K₀ Z ξ hK₀ key→ elementPool P→ Fin 3→ RayCharacter→ Character,
    (∑j : rows,∑B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed K₀ Z ξ hK₀ key j.val),
      geometryAllocationWeight reflected s R seed K₀ Z ξ Mprice Aprice hK₀ key
        (fun q=>normPhase (coordinateBlock s R seed Φ K₀ Z ξ q)) n b j.val B*
      geometryErrorPhysicalCompleteCost s reflected second
        (geometryFirstLabel s R seed K₀ Z ξ hK₀ key j.val) j.val.2.1.val R B
        (geometryColumnCharacter reflected s R seed K₀ Z ξ hK₀ key j.val) t P (υ ⟨j,B⟩) v
        Z 1 amp (frequencyLoss Z 32 ξ) reserve error εcommon)≤ Rpaid
  have hbase : PaidAt Z := by
    intro hK₀ rows υ
    exact hpaid (fun j B=>υ ⟨j,B⟩)
  have hpow : PaidAt (Z^(1:ℝ)) := Eq.mpr (congrArg PaidAt (Real.rpow_one Z)) hbase
  intro υ
  have hp:=hpow (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) υ
  unfold geometryJointErrorPhysicalScalarCost geometryJointErrorFirstAllocation geometryErrorTransportAllocation
  simp only [Fintype.sum_sigma]
  convert hp using 1 <;> rfl

open Filter CenteredMomentCommonProfile CenteredMomentEnergyState CenteredMomentEnergyBands Cycle61FinalProfiles
open CenteredMomentOriginalCommonHarmonic Cycle61InitialSource CenteredMomentLogDyadic
variable (rayM : Ideal O) [NeZero rayM]
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤ H)

attribute [local irreducible] geometryErrorPhysicalCompleteCost geometryAllocationWeight
set_option backward.isDefEq.respectTransparency true in
/-- The genuine affine scalar theorem pays the raw joint carrier with its
actual slot cardinality; the only carrier transport is Z^1=Z. -/
theorem affine_error_frequency_loss_raw_scalar_bound
    (Sbad : Finset (Ideal O)) (W : ℝ→ℂ)(hW : Continuous W)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (εv ε εaffine εshell ξ εalloc mesh K Z : ℝ)
    (hpaid : AffineErrorFrequencyLossScalarBound (α:=α) rayM H hH Sbad W hW hWs
      εv ε εaffine εshell ξ εalloc mesh K Z)
    (hZ : 1< Z)(T : Finset α)(η₀ : Character)(θ : T→ RayQuotient.Characters rayM H)
    (w σ freq : T→ℝ)(hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
    (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(p : Profiles (1/4) (9/4))
    (t X₁ X₂ : ℝ)(hX₁ : 0< X₁)(hX₂ : 0< X₂)
    (hw : ∀i,0≤ w i)(hwm : ∀i,w i≤ mesh)
    (hlo₁ : (41/100:ℝ)≤ length Z X₁)(hlo₂ : (41/100:ℝ)≤ length Z X₂)
    (hhi₁ : length Z X₁≤(44/100:ℝ))(hhi₂ : length Z X₂≤(44/100:ℝ))
    (hwlo : (17/500:ℝ)≤∑i,w i)(hwhi : (∑i,w i)≤(1/25:ℝ))
    (reflected second : Bool)(error εcommon reserve : ℝ)
    (hecommon : 0≤εcommon)(hloss : error+εv+4*εcommon+ε≤64*geometryLossUnit 1 εaffine)
    (Φ : 𝓢(ℝ,ℂ))(bin : ℤ×(Fin 5→ℤ))(height vheight : ℝ) :
    letI : DecidableEq T:=Classical.decEq T
    let inp:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
    let amp:=Cycle61.Arithmetic.amp (Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell (∑i,w i)))
    let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^amp)
    let phase:=fun q=>normPhase (coordinateBlock inp 1 1 Φ (Z^(1:ℝ)) Z ξ q)
    ∀υ : GeometryLowFirstIndex reflected inp 1 1 (Z^(1:ℝ)) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) bin→ elementPool P→ Fin 3→ RayCharacter→ Character,
    geometryJointErrorRawScalarCost reflected second inp 1 1 Z 1 amp ξ reserve (9/4) height vheight error εcommon
      1 (Real.logb Z (volume inp)) hZ bin P phase υ (Fintype.card T)≤
    16*geometryHighFactor reflected (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) bin*K*
      Z^(4*εalloc+εshell-(7/60000000:ℝ)) := by
  letI : DecidableEq T:=Classical.decEq T
  intro inp amp P phase
  have hz₁ : inp.W₁ 0=0 := by
    by_contra hn
    have hp:=(p.support 0 hn).1
    norm_num at hp
  have hz₂ : inp.W₂ 0=0 := by
    by_contra hn
    have hp:=(p.support 1 hn).1
    norm_num at hp
  have hn : Fintype.card T≤ Fintype.card α := Fintype.card_le_of_injective _ Subtype.val_injective
  intro υ
  apply le_trans (geometry_joint_error_raw_scalar_cost_card_mono reflected second inp 1 1 Z 1 amp ξ reserve
    (9/4) height vheight error εcommon 1 (Real.logb Z (volume inp)) hZ bin P phase υ
    (Fintype.card T) (Fintype.card α) hn hz₁ hz₂)
  rw [geometry_joint_error_raw_scalar_cost_eq_physical]
  dsimp only [phase]
  apply geometry_joint_error_physical_scalar_cost_one_payment
  intro hK₀ rows₀ υ₀
  have hp:=hpaid hZ T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂
    hw hwm hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi reflected second error εcommon reserve hecommon hloss Φ bin
    height υ₀ vheight
  convert hp using 1 <;> rfl

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_error_analytic_height_factor
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_error_active_scalar_packet_eq_physical
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_joint_error_raw_scalar_cost_eq_physical

#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_joint_error_raw_scalar_cost_nonneg
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_joint_error_raw_scalar_cost_card_mono

#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_joint_error_scalar_menu_collect
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_joint_error_scalar_menu_physical_payment

#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_error_frequency_loss_raw_scalar_bound

#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_error_scalar_height_box_payment

#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_joint_error_physical_scalar_cost_one_payment

#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_joint_error_scalar_menu_height_box_payment

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineErrorAggregate -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorJointNormalizedTransport; sha256 5d3318b9c6f5eeae782f479c0c86b95aea1a3434bd064d59a5183b947fea1dc4 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                                    
                                                                      
                                                                   

set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentOriginalCommonHarmonic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstAnnularInput
open CenteredMomentAmplificationErrorEnergy CenteredMomentPrimeElements
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondEnergySplit
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondLiveBlock CenteredMomentSecondLocalization CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentSourceMass CenteredMomentCommonHeightEnvelope CenteredMomentHeckeColumnWindow
open CenteredMomentSecondHeightFamily
open Cycle61FinalNatural Cycle61Moment Cycle61FinalError
open CenteredMomentCommonPairedSource
local notation "O" => HeckeFamily.O
attribute [local instance] geometryErrorOrdinaryContractionDecidable
local instance errorJointNormalizedSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := errorNormalizedFullFamilySumDecidableEq
universe u v

theorem error_normalized_column_ideal_congr {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (R seed L : Ideal O) (z : O) (h : C=D) :
    normalizedColumn s C hC R seed L z=normalizedColumn s D hD R seed L z := by
  cases h
  rfl

/-- Pointwise column equality and scalar equality determine the positive label sum. -/
theorem error_normalized_label_congr {ι β : Type*} [Fintype ι] [Fintype β]
    [DecidableEq ι] [DecidableEq β] (d : SecondInputDatum ι) (g : SecondInputDatum β)
    (hb : d.block=g.block)
    (hv : CenteredMomentExceptionalAmplitudePair.volume d.input.toData=
      CenteredMomentExceptionalAmplitudePair.volume g.input.toData)
    (hC : d.C=g.C) (hD : d.D=g.D) (hτ : d.τ=g.τ) (ht : d.input.t=g.input.t)
    (hc : ∀η v C (h : Supported C) L z,
      normalizedColumn (withHeight d.input η v) C h d.R d.seed L z =
      normalizedColumn (withHeight g.input η v) C h g.R g.seed L z)
    (side : Bool) (w : ℂ) (t u : ℝ) :
    secondNormalizedLabelSum side d w t u=secondNormalizedLabelSum side g w t u := by
  unfold secondNormalizedLabelSum
  generalize hd : d.block=bd
  generalize hg : g.block=bg
  have hbg : bd=bg := hd.symm.trans (hb.trans hg)
  cases hbg
  simp only [hv,hτ,ht]
  apply Finset.sum_congr rfl
  intro χ _
  apply Finset.sum_congr rfl
  intro ψ _
  apply Finset.sum_congr rfl
  intro D _
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  cases side <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · rw [hc]
    exact congrArg (fun c : ℂ=>‖c‖^2)
      (error_normalized_column_ideal_congr _ _ _ _ _ _ _ _ _ hC)
  · rw [hc]
    exact congrArg (fun c : ℂ=>‖c‖^2)
      (error_normalized_column_ideal_congr _ _ _ _ _ _ _ _ _ hD)

/-- The equality-instance cast preserves volume before any source is specialized. -/
theorem error_normalized_cast_volume {ι : Type*} [Fintype ι]
    (eqι : DecidableEq ι) (d : @SecondInputDatum ι _ eqι) :
    (letI := Classical.decEq ι; CenteredMomentExceptionalAmplitudePair.volume
      (cast (congrArg (fun eq=>@SecondInputDatum ι _ eq)
        (Subsingleton.elim eqι (Classical.decEq ι))) d).input.toData) =
      (letI := eqι; CenteredMomentExceptionalAmplitudePair.volume d.input.toData) := by
  have he : eqι=Classical.decEq ι := Subsingleton.elim _ _
  cases he
  rfl

/-- The stored instance cast and embedding preserve the source volume. -/
theorem error_normalized_cast_image_volume {ι β : Type*}
    [Fintype ι] [Fintype β] (eqι : DecidableEq ι)
    (d : @SecondInputDatum ι _ eqι) (e : ι↪β) :
    CenteredMomentExceptionalAmplitudePair.volume
      ((cast (congrArg (fun eq=>@SecondInputDatum ι _ eq)
        (Subsingleton.elim eqι (Classical.decEq ι))) d).image e).input.toData =
      (letI := eqι; CenteredMomentExceptionalAmplitudePair.volume d.input.toData) := by
  exact (second_datum_image_volume e _).trans (error_normalized_cast_volume eqι d)

/-- Share the raw source datum in the statement and its ordinary kernel proof. -/
private def buildErrorJointVolume (g : Lean.Syntax) (wantType : Bool) :
    Lean.Elab.Term.TermElabM Lean.Expr := do
  let dg ← Lean.Elab.Term.elabTerm g none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let dg ← Lean.instantiateMVars dg
  let some image ← Lean.Meta.unfoldDefinition? dg true
    | Lean.throwError "expected the stored joint datum definition"
  let ia := image.getAppArgs
  unless image.getAppFn.isConstOf ``SecondInputDatum.image && ia.size=6 do
    Lean.throwError "expected the stored datum image"
  let ca := ia[5]!.getAppArgs
  unless ca.size=4 do Lean.throwError "expected the canonical instance cast"
  let rt ← Lean.Meta.inferType ca[3]!
  Lean.Meta.withLetDecl `rawDatum rt ca[3]! fun raw => do
    let proof ← Lean.Meta.mkAppOptM ``error_normalized_cast_image_volume
      #[some ca[0]!,some ia[1]!,some ca[1]!,some ia[3]!,some ca[2]!,some raw,some ia[4]!]
    let result ← if wantType then Lean.Meta.inferType proof else pure proof
    Lean.Meta.mkLetFVars #[raw] result

elab "errorJointVolume%(" g:term ")" : term =>
  buildErrorJointVolume g false
elab "errorJointVolumeType%(" g:term ")" : term =>
  buildErrorJointVolume g true

/-- Emit an explicitly typed proof constant through Lean's checked declaration path.
The type and ordinary proof are captured together; no kernel checks are bypassed. -/
elab "checked_error_proof " name:ident binders:bracketedBinder* " := " proof:term : command => do
  let declName := (← Lean.getCurrNamespace) ++ name.getId
  Lean.Elab.Command.runTermElabM fun vars =>
    Lean.Elab.Term.elabBinders binders fun xs => do
      let value ← Lean.Elab.Term.elabTerm proof none
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let value ← Lean.instantiateMVars value
      let value ← Lean.Meta.mkLambdaFVars xs value
      let value ← Lean.Meta.mkLambdaFVars vars value (usedOnly := true)
      let value ← Lean.Elab.Term.levelMVarToParam value
      let value ← Lean.instantiateMVars value
      let type ← Lean.Meta.inferType value
      unless ← Lean.Meta.isProp type do Lean.throwError "expected a theorem proposition"
      let params := (Lean.collectLevelParams (Lean.collectLevelParams {} type) value).params.toList
      let es := ShareCommon.shareCommon' #[type,value]
      let decl := Lean.Declaration.defnDecl { name := declName, levelParams := params, type := es[0]!, value := es[1]!, hints := .regular 1, safety := .safe }
      Lean.Elab.Term.ensureNoUnassignedMVars decl
      let auxName := Lean.mkPrivateName (← Lean.getEnv) (declName ++ `_proof)
      let preDef : Lean.Elab.PreDefinition := { ref := name, kind := .«def», levelParams := params, modifiers := { visibility := .«private» }, declName := auxName, binders := .missing, type := es[0]!, value := es[1]!, termination := default }
      Lean.Elab.addNonRec ((← Lean.getLCtx),(← Lean.Meta.getLocalInstances)) preDef
      let info ← Lean.getConstInfo auxName
      let publicDecl := Lean.Declaration.defnDecl { name := declName, levelParams := info.levelParams, type := info.type, value := Lean.mkConst auxName (info.levelParams.map Lean.mkLevelParam), hints := .regular 1, safety := .safe }
      Lean.Elab.Term.ensureNoUnassignedMVars publicDecl
      Lean.addDecl publicDecl


/-- Use the frozen projection interfaces and their literal carrier instances. -/
elab "errorJointFieldLabel%(" g:term "," χ:term "," Q:term "," m:term "," side:term "," w:term "," t:term "," u:term ")" : term => do
  let dg ← Lean.Elab.Term.elabTerm g none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let dg ← Lean.instantiateMVars dg
  let args := dg.getAppArgs
  let levels := dg.getAppFn.constLevels!
  let chr ← Lean.Elab.Term.elabTerm χ none
  let qr ← Lean.Elab.Term.elabTerm Q none
  let mr ← Lean.Elab.Term.elabTerm m none
  let sr ← Lean.Elab.Term.elabTerm side none
  let wr ← Lean.Elab.Term.elabTerm w none
  let tt ← Lean.Elab.Term.elabTerm t none
  let uu ← Lean.Elab.Term.elabTerm u none
  let hb := Lean.mkAppN (Lean.mkConst ``geometry_joint_error_ordinary_datum_block levels) (args++#[chr,qr,mr])
  let hbt ← Lean.Meta.whnf (← Lean.Meta.inferType hb)
  let ea := hbt.getAppArgs
  unless hbt.getAppFn.isConstOf ``Eq && ea.size=3 do Lean.throwError "expected the frozen block equality"
  let ga := ea[1]!.getAppArgs
  let ra := ea[2]!.getAppArgs
  unless ga.size=4 && ra.size=4 do Lean.throwError "expected the exact datum block projections"
  let fields := Lean.mkAppN (Lean.mkConst ``geometry_joint_error_datum_fields levels) args
  let hC ← Lean.Meta.mkAppM ``And.left #[fields]
  let tail ← Lean.Meta.mkAppM ``And.right #[fields]
  let hD ← Lean.Meta.mkAppM ``And.left #[tail]
  let tail ← Lean.Meta.mkAppM ``And.right #[tail]
  let hτ ← Lean.Meta.mkAppM ``And.left #[tail]
  let ht ← Lean.Meta.mkAppM ``And.right #[tail]
  let hv := Lean.mkAppN (Lean.mkConst `OAI.SevenEighths.Cycle61InitialMass.geometry_joint_error_datum_volume levels) args
  let hc := Lean.mkAppN (Lean.mkConst ``geometry_joint_error_datum_column levels) args
  Lean.Meta.mkAppOptM ``error_normalized_label_congr
    #[some ga[0]!,some ra[0]!,some ga[1]!,some ra[1]!,some ga[2]!,some ra[2]!,
      some ga[3]!,some ra[3]!,some hb,some hv,some hC,some hD,some hτ,some ht,some hc,
      some sr,some wr,some tt,some uu]

/-- Read the exact checked sigma RHS, without reconstructing a datum record. -/
elab "errorJointRawSum%(" proof:term ")" : term => do
  let e ← Lean.Elab.Term.elabTerm proof none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let ty ← Lean.Meta.whnf (← Lean.Meta.inferType (← Lean.instantiateMVars e))
  let args := ty.getAppArgs
  unless ty.getAppFn.isConstOf ``Eq && args.size=3 do
    Lean.throwError "expected an exact normalized-sum equality"
  pure args[2]!

/-- Extract one literal summand from the checked raw sigma RHS. -/
elab "errorJointRawSource%(" proof:term "," source:term ")" : term => do
  let e ← Lean.Elab.Term.elabTerm proof none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let ty ← Lean.Meta.whnf (← Lean.Meta.inferType (← Lean.instantiateMVars e))
  let rhs := ty.getAppArgs[2]!
  let args := rhs.getAppArgs
  unless rhs.getAppFn.isConstOf ``Finset.sum && args.size=5 do
    Lean.throwError "expected the literal source sum"
  let l ← Lean.Elab.Term.elabTerm source none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  pure (Lean.mkApp args[4]! (← Lean.instantiateMVars l)).headBeta

/-- Transport positive source sums without a source-label cardinality. -/
theorem error_normalized_effective_sigma_congr
    {α S : Type*} [Fintype α] [DecidableEq α] [Fintype S]
    {B : S→ Type*} [∀s,Fintype (B s)]
    {ι : S→ Type*} [∀s,Fintype (ι s)] [∀s,DecidableEq (ι s)]
    (g : Sigma B→ SecondInputDatum α) (d : (s : S)→ B s→ SecondInputDatum (ι s))
    (w : Sigma B→ℂ) (W : 𝓢(ℝ,ℂ))
    (hb : ∀j : Sigma B,(g j).block=(d j.1 j.2).block)
    (hl : ∀(j : Sigma B) side c t u,
      secondNormalizedLabelSum side (g j) c t u=
      secondNormalizedLabelSum side (d j.1 j.2) c t u)
    (side : Bool) (t u : ℝ) :
    secondNormalizedSum side g
      (secondEffectiveWeight (fun j=>(g j).block) w W) t u=
    ∑s,secondNormalizedSum side (d s)
      (secondEffectiveWeight (fun b=>(d s b).block) (fun b=>w ⟨s,b⟩) W) t u := by
  rw [second_normalized_sum_labels,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro s _
  rw [second_normalized_sum_labels]
  apply Finset.sum_congr rfl
  intro b _
  dsimp only [secondEffectiveWeight]
  simp only [hb ⟨s,b⟩]
  exact hl ⟨s,b⟩ side _ t u

/-- A source-sum envelope controls every ratio fiber with H=1. -/
theorem error_normalized_bound_of_source_sum
    {α S : Type*} [Fintype α] [DecidableEq α] [Fintype S]
    {B : S→ Type*} [∀s,Fintype (B s)]
    {ι : S→ Type*} [∀s,Fintype (ι s)] [∀s,DecidableEq (ι s)]
    (g : Sigma B→ SecondInputDatum α) (d : (s : S)→ B s→ SecondInputDatum (ι s))
    (w : Sigma B→ℂ) (W : 𝓢(ℝ,ℂ)) (degree windowDegree : ℕ) (E : ℝ)
    (hb : ∀j : Sigma B,(g j).block=(d j.1 j.2).block)
    (hl : ∀(j : Sigma B) side c t u,
      secondNormalizedLabelSum side (g j) c t u=
      secondNormalizedLabelSum side (d j.1 j.2) c t u)
    (hfull : ∀side t u,
      (∑s,secondNormalizedSum side (d s)
        (secondEffectiveWeight (fun b=>(d s b).block) (fun b=>w ⟨s,b⟩) W) t u)≤
      (E*(1+‖t‖)^degree)*(1+‖u‖)^(2*windowDegree)) :
    SecondNormalizedBound W degree windowDegree g w (fun _=>E) (fun _=>1) := by
  apply second_normalized_bound_of_full W degree windowDegree g w E
  intro side t u
  rw [error_normalized_effective_sigma_congr g d w W hb hl]
  exact hfull side t u


variable {α : Type u} [Fintype α]
section Actual
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
  (Z M amp ξ reserve b t : ℝ) (hZ : 1< Z) (key : ℤ×(Fin 5→ℤ))
local notation "N" => Fintype.card α
local notation "hK" => Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
variable (P : Finset (Ideal O))
  (υ : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key→ elementPool P→ Fin 3→ RayCharacter→ Character)
  (Mprice Aprice : ℝ)
  (weight : Cycle61JointSource.SourceCoordinate s R seed (Z^M) Z ξ→ℂ)
  (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
local notation "Sources" => GeometryJointErrorSourceIndex (reflected:=reflected) (s:=s) (R:=R) (seed:=seed) (Z:=Z) (M:=M) (ξ:=ξ) (t:=t) (hZ:=hZ) (key:=key) (P:=P)
local notation "Selected" => GeometryJointErrorSelectedIndex reflected s R seed Z M amp ξ reserve b t hZ key P υ hz₁ hz₂
local notation "datum" => geometryJointErrorDatum reflected s R seed Z M amp ξ reserve b t hZ key P υ hz₁ hz₂
local notation "coeff" => geometryJointErrorWeight reflected s R seed Z M amp ξ reserve b t hZ key P υ Mprice Aprice weight hz₁ hz₂

set_option maxHeartbeats 100000 in
set_option Elab.async false in
checked_error_proof geometry_joint_error_datum_volume (j : Selected) :=
  errorJointVolume%((datum j))
set_option maxHeartbeats 100000 in
set_option Elab.async false in
checked_error_proof geometry_joint_error_normalized_label
    (j : Selected) (χ : RayCharacter) (Q : Ideal O) (m : O)
    (side : Bool) (w : ℂ) (tₑ u : ℝ) :=
  errorJointFieldLabel%((datum j),χ,Q,m,side,w,tₑ,u)



set_option maxHeartbeats 100000 in
set_option Elab.async false in
checked_error_proof geometry_joint_error_normalized_sum
    (χ : Selected→ RayCharacter) (Q : Ideal O) (W : 𝓢(ℝ,ℂ))
    (side : Bool) (tₑ u : ℝ) :=
  letI : ∀l : Sources,DecidableEq ↥(liveIndices l.1.2.val) := fun _ a b=>a.instDecidableEq b;
  let raw := fun l : Sources=>fun n : geometryErrorNonzeroBlocks
      reflected s R seed Z M amp ξ reserve b t N hZ key l.1 l.2.1.val l.2.2.1 l.2.2.2.2
      (υ l.1 l.2.1 l.2.2.1 l.2.2.2.1) t hz₁ hz₂=>
    ordinarySecondDatum
      (geometryErrorSecondDatum reflected s R seed Z M amp ξ reserve b t N hZ key
        l.1 l.2.1.val l.2.2.1 l.2.2.2.2 (υ l.1 l.2.1 l.2.2.1 l.2.2.2.1) t hz₁ hz₂ n.val)
      (χ ⟨l,n⟩) Q fixedBadMask;
  let hb := fun j : Selected=>
    geometry_joint_error_ordinary_datum_block reflected s R seed Z M amp ξ reserve b t
      hZ key P υ hz₁ hz₂ j (χ j) Q fixedBadMask;
  let hl := fun (j : Selected) (side : Bool) (c : ℂ) (tₑ u : ℝ)=>
    geometry_joint_error_normalized_label reflected s R seed Z M amp ξ reserve b t
      hZ key P υ hz₁ hz₂ j (χ j) Q fixedBadMask side c tₑ u;
  error_normalized_effective_sigma_congr
    (fun j : Selected=>ordinarySecondDatum (datum j) (χ j) Q fixedBadMask)
    raw coeff W hb hl side tₑ u


/-- The exact raw source sum from the checked sigma transport. -/
def geometryJointErrorRawNormalizedSum
    (χ : Selected→ RayCharacter) (Q : Ideal O) (W : 𝓢(ℝ,ℂ))
    (side : Bool) (tₑ u : ℝ) : ℝ :=
  errorJointRawSum%((geometry_joint_error_normalized_sum reflected s R seed Z M amp ξ reserve b t
    hZ key P υ Mprice Aprice weight hz₁ hz₂ χ Q W side tₑ u))

/-- One summand of the exact source sum. -/
def geometryJointErrorRawNormalizedSource
    (χ : Selected→ RayCharacter) (Q : Ideal O) (W : 𝓢(ℝ,ℂ))
    (side : Bool) (tₑ u : ℝ) (l : Sources) : ℝ :=
  errorJointRawSource%((geometry_joint_error_normalized_sum reflected s R seed Z M amp ξ reserve b t
    hZ key P υ Mprice Aprice weight hz₁ hz₂ χ Q W side tₑ u),l)

set_option maxHeartbeats 100000 in
set_option Elab.async false in
checked_error_proof geometry_joint_error_raw_sum_sources
    (χ : Selected→ RayCharacter) (Q : Ideal O) (W : 𝓢(ℝ,ℂ))
    (side : Bool) (tₑ u : ℝ) :=
  show geometryJointErrorRawNormalizedSum reflected s R seed Z M amp ξ reserve b t
    hZ key P υ Mprice Aprice weight hz₁ hz₂ χ Q W side tₑ u=
    ∑l : Sources,geometryJointErrorRawNormalizedSource reflected s R seed Z M amp ξ reserve b t
      hZ key P υ Mprice Aprice weight hz₁ hz₂ χ Q W side tₑ u l from by rfl

set_option maxHeartbeats 100000 in
set_option Elab.async false in
checked_error_proof geometry_joint_error_raw_source
    (χ : Selected→ RayCharacter) (Q : Ideal O) (W : 𝓢(ℝ,ℂ))
    (side : Bool) (tₑ u : ℝ) (l : Sources) :=
  show geometryJointErrorRawNormalizedSource reflected s R seed Z M amp ξ reserve b t
    hZ key P υ Mprice Aprice weight hz₁ hz₂ χ Q W side tₑ u l=
    geometryErrorRawNormalizedSum reflected s R seed Z M amp ξ reserve b t N hZ key
      l.1 l.2.1.val l.2.2.1 l.2.2.2.2 (υ l.1 l.2.1 l.2.2.1 l.2.2.2.1) t hz₁ hz₂
      P (geometryAllocationWeight reflected s R seed (Z^M) Z ξ Mprice Aprice
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key weight N b l.1.1.val l.1.2) W
      (fun n : geometryErrorNonzeroBlocks reflected s R seed Z M amp ξ reserve b t N hZ key
        l.1 l.2.1.val l.2.2.1 l.2.2.2.2 (υ l.1 l.2.1 l.2.2.1 l.2.2.2.1) t hz₁ hz₂=>n.val)
      (fun n=>χ ⟨l,n⟩) Q side tₑ u from by rfl

set_option maxHeartbeats 100000 in
set_option Elab.async false in
checked_error_proof geometry_joint_error_normalized_bound
    (χ : Selected→ RayCharacter) (Q : Ideal O) (W : 𝓢(ℝ,ℂ))
    (degree windowDegree : ℕ) (numerator : ℝ)
    (hfull : ∀side tₑ u,
      geometryJointErrorRawNormalizedSum reflected s R seed Z M amp ξ reserve b t
        hZ key P υ Mprice Aprice weight hz₁ hz₂ χ Q W side tₑ u≤
      (numerator*(1+‖tₑ‖)^degree)*(1+‖u‖)^(2*windowDegree)) :=
  second_normalized_bound_of_full W degree windowDegree
    (fun j : Selected=>ordinarySecondDatum (datum j) (χ j) Q fixedBadMask)
    coeff numerator (fun side tₑ u=>
      (geometry_joint_error_normalized_sum reflected s R seed Z M amp ξ reserve b t
        hZ key P υ Mprice Aprice weight hz₁ hz₂ χ Q W side tₑ u).le.trans (hfull side tₑ u))

end Actual

end
end OAI.SevenEighths.Cycle61InitialMass



#print axioms OAI.SevenEighths.Cycle61InitialMass.error_normalized_label_congr
#print axioms OAI.SevenEighths.Cycle61InitialMass.error_normalized_cast_volume
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_joint_error_datum_volume

#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_joint_error_normalized_label

#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_joint_error_normalized_sum

#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_joint_error_normalized_bound

#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_joint_error_raw_source

#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_joint_error_raw_sum_sources

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorJointNormalizedTransport -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineErrorFamily; sha256 3f4e0a50256bef25b5285b282d1fdc6278c926dd463690d976794d3e3b251182 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                                      
                                                                
                                                                         
                                                            

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 100000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationErrorEnergy
open CenteredMomentPrimeElements CenteredMomentAllocatedRayDictionary CenteredMomentSectorLocalization
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstAnnularInput
open RayFourExpansion Cycle61Moment CenteredMomentFiniteProfileExceptional
open CenteredMomentCommonProfile CenteredMomentEnergyState CenteredMomentEnergyBands
open Cycle61InitialSource CenteredMomentAmplificationRadicalFamily CenteredMomentChildRows
open CenteredMomentAmplificationActiveFactor CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O
attribute [local instance] geometryErrorOrdinaryContractionDecidable
attribute [local irreducible] Finset.univ SecondInputDatum.block geometryErrorSecondDatum geometryErrorNonzeroBlocks
  geometryErrorChild geometryLowFirstChild geometryJointErrorDatum geometryJointErrorWeight
  geometryJointErrorRawNormalizedSource geometryJointErrorPhysicalScalarCost geometryJointErrorRawScalarLabelSum

variable {α : Type} [Fintype α]
section Zero
variable (reflected : Bool)(s : Input α)(R seed : Ideal O)
  (Z M amp ξ reserve b t : ℝ)(hZ : 1< Z)(key : ℤ×(Fin 5→ℤ))(P : Finset (Ideal O))
  (υ : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key→ elementPool P→ Fin 3→ RayCharacter→ Character)
  (Mprice Aprice : ℝ)(weight : Cycle61JointSource.SourceCoordinate s R seed (Z^M) Z ξ→ℂ)
  (hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
local notation "Sources" => GeometryJointErrorSourceIndex (reflected:=reflected) (s:=s) (R:=R) (seed:=seed)
  (Z:=Z) (M:=M) (ξ:=ξ) (t:=t) (hZ:=hZ) (key:=key) (P:=P)
local notation "Selected" => GeometryJointErrorSelectedIndex reflected s R seed Z M amp ξ reserve b t hZ key P υ hz₁ hz₂

/-- Zero first coefficients contribute zero without removing original labels. -/
theorem affine_error_family_raw_source_zero
    (χ : Selected→ RayCharacter)(Q : Ideal O)(W : 𝓢(ℝ,ℂ))(side : Bool)(te u : ℝ)(l : Sources)
    (hzero : geometryAllocationWeight reflected s R seed (Z^M) Z ξ Mprice Aprice
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key weight (Fintype.card α) b l.1.1.val l.1.2=0) :
    geometryJointErrorRawNormalizedSource reflected s R seed Z M amp ξ reserve b t hZ key P υ
      Mprice Aprice weight hz₁ hz₂ χ Q W side te u l=0 := by
  rw [geometry_joint_error_raw_source]
  unfold geometryErrorRawNormalizedSum
  simp only [hzero,errorNormalizedCoefficient,mul_zero,zero_mul,zero_div,Complex.ofReal_zero]
  exact actual_geometry_error_zero_normalized_sum _ _ _ _ _
end Zero


open CenteredMomentNaturalFixedRaySource CenteredMomentSecondInputCapacitySource
variable (rayM : Ideal O) [NeZero rayM]
local instance affineErrorFamilyFiniteQuotient : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ)(hH : RayOrthogonality.globalUnits rayM≤ H)

/-- The actual complete error family is uniform before all moving source data. -/
theorem actual_affine_error_normalized_family
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβ : 51/100≤ HeckeZeroSupremum.beta)
    (Ψ : 𝓢(ℝ,ℂ))(ηseed η₀ : Character)(Q : Ideal O)(hQM : Q≤ rayM)
    (hQ : internalQ Q η₀≠0)(hQt : internalQ Q η₀≠⊤)(hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)})
    (εaffine mesh : ℝ)(hε : 0<εaffine)(hmesh0 : 0≤ mesh)
    (hmesh : mesh<(62485051/9854400000:ℝ)/2)
    (hmeshμ : mesh≤ geometryLossUnit 1 εaffine/8)
    (hmeshcap : mesh≤ Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 εaffine/8)) :
    ∀T : Finset α,∃degree windowDegree dN : ℕ,∃SN : Finset (ℕ×ℕ),∃Cn : ℝ,0≤ Cn ∧
      ∀ᶠZ : ℝ in atTop,
        GeometryAffineErrorNormalizedSpec rayM H hH Sbad W hW.continuous hWs Ψ ηseed η₀ mesh εaffine T
          degree windowDegree (internalQ Q η₀) SN dN Cn Z := by
  let μ:=geometryLossUnit 1 εaffine
  let N:=Fintype.card α
  let L₂:=3*((N:ℝ)+2)
  let δ:=geometryFinalDictionaryRate μ 31 3 4 3 130 L₂ N
  have hμ : 0<μ:=geometry_loss_unit_pos 1 εaffine (by norm_num) hε
  have hμcap : μ≤1/128 := by
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδ : 0<δ:=(geometry_final_dictionary_budgets μ 31 3 4 3 130 L₂ N hμ
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by dsimp [L₂];positivity)).1
  have hδcap : δ≤μ/8 := by
    have hh:=(geometry_final_dictionary_budgets μ 31 3 4 3 130 L₂ N hμ
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by dsimp [L₂];positivity)).2.2.1
    linarith only [hh,hμ]
  obtain ⟨Cs,hCs,hcaps⟩:=eventual_actual_affine_exceptional_source_gates (α:=α) rayM H hH W hW.continuous hWs
  obtain ⟨K,hK,hscalar⟩:=eventual_actual_affine_error_normalized_scalar_schedule (α:=α) rayM H hH
    Sbad hbad W hW.continuous hWs εaffine mesh hε hmesh
  obtain ⟨Cb,hCb,hbox⟩:=eventual_actual_geometry_error_absolute_box N 130 1 (9/4) (9/4) (μ/64) δ
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith only [hμcap]) hδ
  intro T
  let : DecidableEq T:=Classical.decEq T
  obtain ⟨degree,Sp,hmenu⟩:=actual_finiteT_affine_error_normalized_menu (α:=α) rayM H hH W hWs hW T
    ηseed μ Cs hμ hCs hβ
  obtain ⟨Cg,hCg,hpaid⟩:=hmenu η₀ Q hQM hQ hQt hQ72
  let ray:ℝ:=(Fintype.card RayCharacter:ℝ)^2
  let lower:=lowerFactor N 1 (1/4)
  have hlower : 0< lower:=lowerFactor_pos N 1 (1/4) (by norm_num) (by norm_num)
  let Cn:=ray*Cg*(2+4*Real.pi)^degree*(Cb/lower)*16*K
  have hCn : 0≤ Cn := by dsimp [Cn,ray];positivity
  refine ⟨degree,degree,degree,Sp,Cn,hCn,?_⟩
  filter_upwards [hcaps,hscalar,hpaid,hbox,eventual_geometry_small_frequency μ hμ,
    eventual_actual_geometry_affine_error_puncture_of_scales N,
    eventual_actual_affine_error_prime_width rayM H Sbad hbad,
    eventual_actual_affine_exceptional_child_coprime rayM H hH Sbad hbad W hW.continuous hWs mesh hmesh]
    with Z hc hscalarZ hpaidZ hb hω hpuncture hprimeWidth hcoprime
  intro hZ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂ hw hwm hlo₁ hlo₂ hhi₁ hhi₂
    hwlo hwhi hcone reflected key firstHeight height hheight hfreq s μ' N' δ' amp P control exponent υ hυ
  have caps:=hc.2 T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hlo₁ hlo₂ hhi₁ hhi₂ hwhi
  have paid:=actual_affine_error_normalized_menu_source_aligned (α:=T) rayM H hH W hW.continuous hWs
    N μ δ Cs Cg Sp degree ηseed η₀ Q Z hZ hpaidZ.2 θ w σ freq hσ state hη p
    t X₁ X₂ hX₁ hX₂ height mesh hμ hμcap hw (fun j=>(hwm j).trans hmeshcap)
    hmesh0 hwm hheight hfreq ⟨hwlo,hwhi⟩ hhi₁ hhi₂ hcone caps
  have cell:=actual_affine_error_cell_gates (α:=T) rayM H hH η₀ θ W hW.continuous hWs w σ freq hσ
    state p t X₁ X₂ hX₁ hX₂ hZ ⟨hwlo,hwhi⟩ hcone
  have hcell : 3401/100000≤ Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell (∑j,w j)) ∧
      Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell (∑j,w j))≤1/25 := by
    simpa only [cell.1] using cell.2.2.2
  have hamp : |amp|≤130 := by
    have ha:=Cycle61.Arithmetic.amp_bounds hcell
    exact (abs_of_nonneg (le_trans (by norm_num) ha.1)).le.trans (ha.2.trans (by norm_num))
  let error:=μ/8+μ/128+μ/8+geometryFinalErrorDictionaryRate μ N*(Fintype.card T:ℝ)+
    (frequencyLoss Z 32 (μ/64)+μ/8+μ/8)/6+(3/4)*mesh+δ
  have herr : error≤μ := geometry_final_error_raw_loss μ
    (frequencyLoss Z 32 (μ/64)+μ/8) mesh (Fintype.card T) N hμ caps.card hω.2.2 hmeshμ
  have hloss : error+μ/8+4*δ+μ/8≤64*μ := by
    have hh:=geometry_final_error_physical_loss μ error hμ herr
    linarith only [hh,hδcap]
  let phase:=fun q=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z (μ/64) q)
  have hphysical (second : Bool) := affine_error_frequency_loss_raw_scalar_bound (α:=α) rayM H hH
    Sbad W hW.continuous hWs (μ/8) (μ/8) εaffine δ (μ/64) δ mesh K Z hscalarZ.2 hZ T η₀
    θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hwm hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi
    reflected second error δ (μ/8) hδ.le hloss Ψ key firstHeight firstHeight υ
  have hz₁ : s.W₁ 0=0:=caps.zero₁
  have hz₂ : s.W₂ 0=0:=caps.zero₂
  let χ:=fun _ : GeometryJointErrorSelectedIndex reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4)
    firstHeight hZ key P υ hz₁ hz₂=>(1:RayCharacter)
  refine ⟨χ,(fun _=>1),?_,?_⟩
  · intro _ _;norm_num
  apply geometry_joint_error_normalized_bound reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4)
    firstHeight hZ key P υ 1 (Real.logb Z (volume s)) phase hz₁ hz₂ χ (internalQ Q η₀) ballProfile
  intro second te u
  rw [geometry_joint_error_raw_sum_sources]
  let box:=geometryErrorAbsoluteBox Z N 130 1 (9/4)
  let Hactual:=geometryHighFactor reflected (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key
  have hHactual : 0≤ Hactual:=by dsimp only [Hactual];rw [geometry_affine_support_constant];exact (geometry_high_factor_pos reflected 64 key (by norm_num)).le
  have htotal:=geometry_joint_error_scalar_menu_height_box_payment reflected second s 1 1 Z 1 amp
    (μ/64) (μ/8) (9/4) firstHeight firstHeight error δ 1 (Real.logb Z (volume s)) hZ key P phase υ
    (Fintype.card T) (Fintype.card T) le_rfl hz₁ hz₂
    (fun l=>geometryJointErrorRawNormalizedSource reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4)
      firstHeight hZ key P υ 1 (Real.logb Z (volume s)) phase hz₁ hz₂ χ (internalQ Q η₀)
      ballProfile second te u l)
    ray Cg (p.control Sp) lower (box.card:ℝ) Cb (16*Hactual*K) height te u δ δ δ
    (4*δ+δ-7/60000000) L₂ degree degree hheight (by dsimp [ray];positivity) hCg.le
    hlower (Nat.cast_nonneg _) hCb.le (mul_nonneg (mul_nonneg (by norm_num) hHactual) hK.le) (by omega) hb.2.1
    (by
      intro l
      let q:=l.1
      let prime:=l.2.1
      let i:=l.2.2.1
      let ψ:=l.2.2.2.1
      let Bp:=l.2.2.2.2
      let weight:=geometryAllocationWeight reflected s 1 1 (Z^(1:ℝ)) Z (μ/64) 1
        (Real.logb Z (volume s)) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key phase
        (Fintype.card T) (9/4) q.1.val q.2
      by_cases hf : frozenCoefficient q.2.val
        (geometryColumnIdeal reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key q.1.val) 1 s.ν s.W s.P=0
      · have hwzero : weight=0:=actual_geometry_error_first_weight_zero reflected s 1 1 (Z^(1:ℝ))
          Z (μ/64) 1 (Real.logb Z (volume s)) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
          key phase (Fintype.card T) (9/4) q.1.val q.2 hf
        have hz:=affine_error_family_raw_source_zero (α:=T) reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4)
          firstHeight hZ key P υ 1 (Real.logb Z (volume s)) phase hz₁ hz₂ χ (internalQ Q η₀)
          ballProfile second te u l hwzero
        apply hz.le.trans_eq
        change 0=_*((56/(P.card:ℝ)*weight*_/_)*_)
        rw [hwzero];simp only [mul_zero,zero_mul,zero_div]
      · have hp:=(actual_affine_error_prime_norm_cap rayM H Sbad hbad Z hZ _ hcell) prime
        have hcp:=hcoprime.2 (ι:=T) η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hwm
          _ hcell.1 hcell.2 prime
          (geometryColumnIdeal reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key q.1.val) 1 q.2
          (geometryColumnCharacter reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key q.1.val) firstHeight
        have hcop : ∀j I,I∈(geometryLowFirstChild reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key firstHeight q).slots j→
          IsCoprime (Ideal.span {prime.val}) I:=by
          unfold geometryLowFirstChild;exact hcp
        have hsource : sourceRadius s≤ Z^(130:ℝ):=caps.sourceCap.trans
          (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num))
        have hA : |Real.logb Z (volume s)|≤130:=caps.volumeLog.trans (by norm_num)
        have hωabs : |frequencyLoss Z 32 (μ/64)+μ/8|≤130:=by
          rw [abs_of_nonneg (by linarith only [hω.2.1,hμ])]
          linarith only [hω.2.2,hμcap]
        have hboxRows:=hb.2.2 reflected s 1 1 1 amp (μ/8) firstHeight hZ caps.card caps.endpoints
          (by simp) hz₁ hz₂ hsource hA (by norm_num) hamp hωabs key q hf prime.val hp.1 i hcop
          Bp (υ q prime i ψ) firstHeight
        have hraw:=actual_geometry_affine_error_raw_normalized_menu s Z μ δ amp Cs Cg N Sp degree η₀ Q
          height mesh hZ p caps paid (by linarith only [hω.2.1,hμ]) reflected firstHeight key q prime.val i hp.1
          hcop Bp (υ q prime i ψ) firstHeight ψ (hυ q prime i ψ) hf
          (hprimeWidth.2 _ hcell.1 hcell.2 prime)
          (fun n side=>hpuncture.2 reflected s 1 p Cs amp (μ/64) (μ/8) firstHeight hZ caps
            (by simp) key q prime.val hp.1 hp.2 i Bp (υ q prime i ψ) firstHeight n side)
          P weight (geometryAllocationWeight_nonneg ..) ballProfile second te u box hboxRows.2.2.2.2
        have he:=geometry_joint_error_raw_source (α:=T) reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4)
          firstHeight hZ key P υ 1 (Real.logb Z (volume s)) phase hz₁ hz₂ χ (internalQ Q η₀)
          ballProfile second te u l
        apply he.le.trans
        unfold geometryErrorNormalizedMenuLabelsConclusion at hraw
        simp only [Fintype.sum_unique] at hraw
        have heerror : μ/8*1+μ/64/2+μ/8+geometryFinalErrorDictionaryRate μ N*(Fintype.card T:ℝ)+
          (frequencyLoss Z 32 (μ/64)+μ/8+μ/8*1)/6+(3/4)*mesh+δ=error:=by dsimp only [error];ring
        simp only [heerror] at hraw
        convert hraw using 1
        unfold geometryJointErrorRawScalarLabelSum
        dsimp only [ray,lower,weight,q,prime,i,ψ,Bp,L₂]
        ring)
    (by
      have hp:=hphysical second
      rw [geometry_joint_error_raw_scalar_cost_eq_physical] at hp
      simpa only [Hactual,geometry_affine_support_constant] using hp)
  apply htotal.trans_eq
  dsimp only [Cn,control,Hactual]
  rw [show δ+3*L₂*δ+δ+(4*δ+δ-7/60000000)=exponent by dsimp [exponent,δ',μ',N',δ,L₂,N];ring]
  ring
end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_error_family_raw_source_zero

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_affine_error_normalized_family

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineErrorFamily -/
