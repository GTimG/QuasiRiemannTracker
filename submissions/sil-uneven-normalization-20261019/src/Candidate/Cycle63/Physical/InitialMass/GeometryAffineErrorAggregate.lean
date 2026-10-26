/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorScalarTransport
import Candidate.Cycle63.Physical.InitialMass.GeometryAllocationCardinality
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorOrdinaryContraction
import Candidate.Cycle63.Physical.InitialMass.GeometryShiftedHeight

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationErrorEnergy
open CenteredMomentPrimeElements CenteredMomentAllocatedRayDictionary CenteredMomentSectorLocalization
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstAnnularInput
open RayFourExpansion Cycle63Moment CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O
attribute [local instance] geometryErrorOrdinaryContractionDecidable

/-- The literal signed Mellin shift admits independent polynomial weights. -/
theorem geometry_error_analytic_height_factor (second : Bool)(v height t u : ℝ)
    (degree : ℕ)(hh : 0≤height) :
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
      _≤_:=hb
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
    (degree windowDegree : ℕ)(hZ : 1<Z)(hh : 0≤height)(hray : 0≤ray)(hg : 0≤Cg)
    (hl : 0<lower)(hb : 0≤box)(hCb : 0≤Cb)(hK : 0≤K)(hdegree : degree≤2*windowDegree)
    (hbox : box≤Cb*Z^ebox)
    (hpaid : total≤(ray*Cg*control^2*(1+|v+2*Real.pi*(u-(if second then -te else te))|+height)^degree*
      Z^(eproj+3*L₂*eshell))*(box/lower)*(K*Z^ephysical)) :
    total≤(ray*Cg*control^2*(2+4*Real.pi)^degree*(Cb/lower)*K*(1+|v|+height)^degree*
      Z^(eproj+3*L₂*eshell+ebox+ephysical))*(1+‖te‖)^degree*(1+‖u‖)^(2*windowDegree) := by
  have hv:=geometry_error_analytic_height_factor second v height te u degree hh
  have h1 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hv (by positivity : 0≤ray*Cg*control^2))
    (Real.rpow_nonneg (zero_lt_one.trans hZ).le (eproj+3*L₂*eshell))
  have h2 := mul_le_mul h1 (div_le_div_of_nonneg_right hbox hl.le)
    (div_nonneg hb hl.le) (by positivity)
  have h3 := mul_le_mul_of_nonneg_right h2 (by positivity : 0≤K*Z^ephysical)
  have hu : (1+‖u‖)^degree≤(1+‖u‖)^(2*windowDegree) :=
    pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg u) : (1:ℝ)≤1+‖u‖) hdegree
  calc
    total≤_ := hpaid.trans h3
    _=(ray*Cg*control^2*(2+4*Real.pi)^degree*(Cb/lower)*K*(1+|v|+height)^degree*
      Z^(eproj+3*L₂*eshell+ebox+ephysical))*(1+‖te‖)^degree*(1+‖u‖)^degree := by
      simp only [Real.rpow_add (zero_lt_one.trans hZ)]
      ring
    _≤_:=mul_le_mul_of_nonneg_left hu (by positivity)

variable {α : Type}[Fintype α][DecidableEq α]
section Source
variable (reflected second : Bool)(s : Input α)(R seed : Ideal O)
  (Z M amp ξ reserve b t v error εcommon Mprice Aprice : ℝ)(hZ : 1<Z)
  (key : ℤ×(Fin 5→ℤ))(P : Finset (Ideal O))
  (phase : Cycle63JointSource.SourceCoordinate s R seed (Z^M) Z ξ→ℂ)
  (υ : GeometryLowFirstIndex (α:=α) reflected s R seed (Z^M) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key→elementPool P→Fin 3→RayCharacter→Character)
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
    0≤geometryErrorPhysicalCompleteCost s reflected second
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
    0≤geometryJointErrorRawScalarCost reflected second s R seed Z M amp ξ reserve b t v error εcommon
      Mprice Aprice hZ key P phase υ n := by
  rw [geometry_joint_error_raw_scalar_cost_eq_physical]
  unfold geometryJointErrorPhysicalScalarCost
  exact Finset.sum_nonneg (fun q _=>mul_nonneg
    (geometryAllocationWeight_nonneg reflected s R seed (Z^M) Z ξ Mprice Aprice hK key phase n b q.1.val q.2)
    (geometry_error_source_physical_cost_nonneg reflected second s R seed Z M amp ξ reserve t v error εcommon hZ key P υ hz₁ hz₂ q))

/-- Only the outer allocation payment is enlarged. The raw source and its
actual-cardinality Fourier data remain fixed. -/
theorem geometry_joint_error_raw_scalar_cost_card_mono (n N : ℕ)(hn : n≤N)
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
    (hmenu : ∀l,menu l≤analytic*
      (((56/(P.card:ℝ))*geometryAllocationWeight reflected s R seed (Z^M) Z ξ Mprice Aprice
        hK key phase n b l.1.1.val l.1.2*(16*(errorIndex l.2.2.1+2:ℝ))/lower)*
        (boxCard*geometryJointErrorRawScalarLabelSum reflected second s R seed Z M amp ξ reserve
          t v error εcommon hZ key P υ l))) :
    (∑l,menu l)≤analytic*(boxCard/lower)*
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
    (n N : ℕ)(hn : n≤N)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (menu : Sources→ℝ)(analytic lower boxCard Rpaid : ℝ)
    (ha : 0≤analytic)(hl : 0<lower)(hb : 0≤boxCard)
    (hmenu : ∀l,menu l≤analytic*
      (((56/(P.card:ℝ))*geometryAllocationWeight reflected s R seed (Z^M) Z ξ Mprice Aprice
        hK key phase n b l.1.1.val l.1.2*(16*(errorIndex l.2.2.1+2:ℝ))/lower)*
        (boxCard*geometryJointErrorRawScalarLabelSum reflected second s R seed Z M amp ξ reserve
          t v error εcommon hZ key P υ l)))
    (hphysical : geometryJointErrorPhysicalScalarCost reflected second s R seed Z M amp ξ reserve b t v error εcommon
      Mprice Aprice hZ key P phase υ N≤Rpaid) :
    (∑l,menu l)≤analytic*(boxCard/lower)*Rpaid := by
  have hc := geometry_joint_error_raw_scalar_cost_card_mono reflected second s R seed Z M amp ξ reserve
    b t v error εcommon Mprice Aprice hZ key P phase υ n N hn hz₁ hz₂
  rw [←geometry_joint_error_raw_scalar_cost_eq_physical] at hphysical
  exact (geometry_joint_error_scalar_menu_collect reflected second s R seed Z M amp ξ reserve b t v error εcommon
    Mprice Aprice hZ key P phase υ n menu analytic lower boxCard hmenu).trans
    (mul_le_mul_of_nonneg_left (hc.trans hphysical) (mul_nonneg ha (div_nonneg hb hl.le)))

/-- Collect the exact source menu, pay the physical sum, and separate all
Mellin heights while retaining the explicit box cost. -/
theorem geometry_joint_error_scalar_menu_height_box_payment
    (n N : ℕ)(hn : n≤N)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (menu : Sources→ℝ)(ray Cg control lower box Cb Kpaid height te u eproj eshell ebox ephysical L₂ : ℝ)
    (degree windowDegree : ℕ)(hh : 0≤height)(hray : 0≤ray)(hg : 0≤Cg)
    (hl : 0<lower)(hb : 0≤box)(hCb : 0≤Cb)(hKpaid : 0≤Kpaid)
    (hdegree : degree≤2*windowDegree)(hbox : box≤Cb*Z^ebox)
    (hmenu : ∀l,menu l≤
      (ray*Cg*control^2*(1+|v+2*Real.pi*(u-(if second then -te else te))|+height)^degree*Z^(eproj+3*L₂*eshell))*
      (((56/(P.card:ℝ))*geometryAllocationWeight reflected s R seed (Z^M) Z ξ Mprice Aprice
        hK key phase n b l.1.1.val l.1.2*(16*(errorIndex l.2.2.1+2:ℝ))/lower)*
        (box*geometryJointErrorRawScalarLabelSum reflected second s R seed Z M amp ξ reserve
          t v error εcommon hZ key P υ l)))
    (hphysical : geometryJointErrorPhysicalScalarCost reflected second s R seed Z M amp ξ reserve b t v error εcommon
      Mprice Aprice hZ key P phase υ N≤Kpaid*Z^ephysical) :
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
    (Z amp ξ reserve b t v error εcommon Mprice Aprice : ℝ)(hZ : 1<Z)
    (key : ℤ×(Fin 5→ℤ))(P : Finset (Ideal O))(Φ : 𝓢(ℝ,ℂ))(n : ℕ)(Rpaid : ℝ)
    (hpaid :
      let hK:=zero_lt_one.trans hZ
      let rows:=firstLiveColumns (geometryFirstSource s R seed Z Z ξ hK key) (fun _=>CenteredMomentLogDyadic.logAnnulus)
      ∀υ : (j : rows)→actualAllocations s.pools
          (geometryColumnIdeal reflected s R seed Z Z ξ hK key j.val)→elementPool P→Fin 3→RayCharacter→Character,
      (∑j : rows,∑B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed Z Z ξ hK key j.val),
        geometryAllocationWeight reflected s R seed Z Z ξ Mprice Aprice hK key
          (fun q=>normPhase (coordinateBlock s R seed Φ Z Z ξ q)) n b j.val B*
        geometryErrorPhysicalCompleteCost s reflected second
          (geometryFirstLabel s R seed Z Z ξ hK key j.val) j.val.2.1.val R B
          (geometryColumnCharacter reflected s R seed Z Z ξ hK key j.val) t P (υ j B) v
          Z 1 amp (frequencyLoss Z 32 ξ) reserve error εcommon)≤Rpaid) :
    ∀υ : GeometryLowFirstIndex reflected s R seed (Z^(1:ℝ)) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key→elementPool P→Fin 3→RayCharacter→Character,
    geometryJointErrorPhysicalScalarCost reflected second s R seed Z 1 amp ξ reserve b t v error εcommon
      Mprice Aprice hZ key P (fun q=>normPhase (coordinateBlock s R seed Φ (Z^(1:ℝ)) Z ξ q)) υ n≤Rpaid := by
  let PaidAt (K₀ : ℝ) : Prop :=
    ∀hK₀ : 0<K₀,
    let rows:=firstLiveColumns (geometryFirstSource s R seed K₀ Z ξ hK₀ key) (fun _=>CenteredMomentLogDyadic.logAnnulus)
    ∀υ : GeometryLowFirstIndex reflected s R seed K₀ Z ξ hK₀ key→elementPool P→Fin 3→RayCharacter→Character,
    (∑j : rows,∑B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed K₀ Z ξ hK₀ key j.val),
      geometryAllocationWeight reflected s R seed K₀ Z ξ Mprice Aprice hK₀ key
        (fun q=>normPhase (coordinateBlock s R seed Φ K₀ Z ξ q)) n b j.val B*
      geometryErrorPhysicalCompleteCost s reflected second
        (geometryFirstLabel s R seed K₀ Z ξ hK₀ key j.val) j.val.2.1.val R B
        (geometryColumnCharacter reflected s R seed K₀ Z ξ hK₀ key j.val) t P (υ ⟨j,B⟩) v
        Z 1 amp (frequencyLoss Z 32 ξ) reserve error εcommon)≤Rpaid
  have hbase : PaidAt Z := by
    intro hK₀ rows υ
    exact hpaid (fun j B=>υ ⟨j,B⟩)
  have hpow : PaidAt (Z^(1:ℝ)) := Eq.mpr (congrArg PaidAt (Real.rpow_one Z)) hbase
  intro υ
  have hp:=hpow (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) υ
  unfold geometryJointErrorPhysicalScalarCost geometryJointErrorFirstAllocation geometryErrorTransportAllocation
  simp only [Fintype.sum_sigma]
  convert hp using 1 <;> rfl

open Filter CenteredMomentCommonProfile CenteredMomentEnergyState CenteredMomentEnergyBands Cycle63FinalProfiles
open CenteredMomentOriginalCommonHarmonic Cycle63InitialSource CenteredMomentLogDyadic
variable (rayM : Ideal O) [NeZero rayM]
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)

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
    (hZ : 1<Z)(T : Finset α)(η₀ : Character)(θ : T→RayQuotient.Characters rayM H)
    (w σ freq : T→ℝ)(hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
    (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(p : Profiles (1/4) (9/4))
    (t X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂)
    (hw : ∀i,0≤w i)(hwm : ∀i,w i≤mesh)
    (hlo₁ : (41/100:ℝ)≤length Z X₁)(hlo₂ : (41/100:ℝ)≤length Z X₂)
    (hhi₁ : length Z X₁≤(44/100:ℝ))(hhi₂ : length Z X₂≤(44/100:ℝ))
    (hwlo : (17/500:ℝ)≤∑i,w i)(hwhi : (∑i,w i)≤(1/25:ℝ))
    (reflected second : Bool)(error εcommon reserve : ℝ)
    (hecommon : 0≤εcommon)(hloss : error+εv+4*εcommon+ε≤64*geometryLossUnit 1 εaffine)
    (Φ : 𝓢(ℝ,ℂ))(bin : ℤ×(Fin 5→ℤ))(height vheight : ℝ) :
    letI : DecidableEq T:=Classical.decEq T
    let inp:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
    let amp:=Cycle63.Arithmetic.amp (Cycle63.Arithmetic.cellUpper (Cycle63.Moment.originalCell (∑i,w i)))
    let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^amp)
    let phase:=fun q=>normPhase (coordinateBlock inp 1 1 Φ (Z^(1:ℝ)) Z ξ q)
    ∀υ : GeometryLowFirstIndex reflected inp 1 1 (Z^(1:ℝ)) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) bin→elementPool P→Fin 3→RayCharacter→Character,
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
  have hn : Fintype.card T≤Fintype.card α := Fintype.card_le_of_injective _ Subtype.val_injective
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
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_error_analytic_height_factor
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_error_active_scalar_packet_eq_physical
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_joint_error_raw_scalar_cost_eq_physical

#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_joint_error_raw_scalar_cost_nonneg
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_joint_error_raw_scalar_cost_card_mono

#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_joint_error_scalar_menu_collect
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_joint_error_scalar_menu_physical_payment

#print axioms OAI.SevenEighths.Cycle63InitialMass.affine_error_frequency_loss_raw_scalar_bound

#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_error_scalar_height_box_payment

#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_joint_error_physical_scalar_cost_one_payment

#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_joint_error_scalar_menu_height_box_payment
