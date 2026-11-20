/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Pack native live bank metadata; no energy, moment or count field. -/
import Candidate.C092.transport.MixedOffsetCountCentered
set_option autoImplicit false
namespace QRH.Cycle092.MixedOffsetCount
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorAmplitudeFirst HeckeDetectorPhysicalSelection
open QRH.Record12518109Count Cycle25ProbeFinalAssembly QRH.Cycle092.PacketJoinE49
open QRH.Cycle092.MixedOffsetBank QRH.Cycle092.MixedCenteredFaces

/-- All fields are actual native data, exact presentation identities,
original-row inclusions or scalar geometric guards. There is no analytic
moment, cardinality estimate, physical-packet or mixed-price field. -/
structure MiddleBank (D : Cycle25.Weighted.MomentData) (S : WeightedSourceData D)
    (η : Character) (Z : ℝ) where
  d : ℝ
  a : ℝ
  T : ℝ
  allowance : ℝ
  height : ℝ
  q : ℝ
  t₀ : ℝ
  γ : ℝ
  meshBank : ℝ
  εa : ℝ
  factor : ℝ
  i : ℕ
  j : Offset
  d_min : (1/200:ℝ) ≤ d
  a_min : 51/100<a
  delta_max : 2*a-1 ≤ 3/4
  height_nonneg : 0 ≤ height
  frequency : 2*Real.pi*allowance+(3*i:ℕ)*T ≤ height
  gamma_nonneg : 0 ≤ γ
  cutoff_min : 1 ≤ t₀-γ
  cutoff_max : t₀ ≤ 3/2
  mesh_nonneg : 0 ≤ meshBank
  collar_nonneg : 0 ≤ εa
  support_collar : D.ε ≤ 3*εa
  available : Return.window.Available (2*a-1) (q/(2*a-1))
  baseline_cutoff : t₀=Return.cutoffI (2*a-1) (q/(2*a-1))
  base : Presented D S η Z d a t₀ T allowance i
  current : Presented D S η Z d a (cutoff t₀ γ j) T allowance i
  prior : Presented D S η Z d a (cutoff t₀ γ (previous j)) T allowance i
  currentSlice : Slice current
  priorSlice : Slice prior
  base_nonempty : base.batch.rows.Nonempty
  base_mean : ∀u∈base.batch.rows,rowMean base.batch.slots (Z^d) ((2*a-1)/2) base.batch.binWidth base.batch.widths
    (physical S.modulus ⊤ (fun u:FreeRow=>u.val) base.batch.profile base.batch.upper
      base.batch.widths base.batch.external (Z^d)) u=q
  base_height : ∀s,|(base.batch.external s).im| ≤ height
  current_height : ∀s,|(current.batch.external s).im| ≤ height
  prior_height : ∀s,|(prior.batch.external s).im| ≤ height
  base_mesh : base.batch.mesh ≤ meshBank
  current_mesh : currentSlice.fiber.mesh ≤ meshBank
  current_mean : currentSlice.fiber.q=q
  inverse_min : anchorLeft ≤ currentSlice.fiber.r
  inverse_max : currentSlice.fiber.r ≤ anchorTop
  ordinary_min : anchorLeft ≤ 2*currentSlice.fiber.m
  ordinary_max : 2*currentSlice.fiber.m ≤ anchorTop
  prior_long : j.val=0 ∨ 1 ≤ priorSlice.fiber.r
  directed_scale : (2*a-1)*factor ≤ 5/6-(2*a-1)
  common : Finset FreeRow
  common_base : common⊆base.batch.rows
  common_current : common⊆currentSlice.fiber.rows
  common_prior : common⊆priorSlice.fiber.rows

/-- Chosen early source constants only; this record contains no estimate. -/
structure CountConstants where
  K₀ : ℝ
  Ki : ℝ
  C₀ : ℝ
  Cr : ℝ
  Ci : ℝ
  J₀ : ℕ
  Jr : ℕ
  Ji : ℕ
  K₀_nonneg : 0 ≤ K₀
  Ki_nonneg : 0 ≤ Ki
  C₀_pos : 0<C₀
  Cr_pos : 0<Cr
  Ci_pos : 0<Ci

namespace MiddleBank
variable {D : Cycle25.Weighted.MomentData} {S : WeightedSourceData D} {η : Character} {Z : ℝ}
def baseScale (B : MiddleBank D S η Z) : ℝ := Z^B.d
def delta (B : MiddleBank D S η Z) : ℝ := 2*B.a-1
def p (B : MiddleBank D S η Z) : ℝ := B.q/B.delta
def m (B : MiddleBank D S η Z) : ℝ := B.t₀/3
def k (B : MiddleBank D S η Z) : ℝ := Return.kI B.p
def R (B : MiddleBank D S η Z) : ℝ := Return.valueI B.delta B.p
def xi (B : MiddleBank D S η Z) : ℝ := offset B.γ B.j
def H (B : MiddleBank D S η Z) : ℝ := B.factor*max 0 (B.xi-B.γ/65536-3*B.εa)
def loss (B : MiddleBank D S η Z) : ℝ := countLoss D.ε B.meshBank D.t
def coefficient (B : MiddleBank D S η Z) (K : CountConstants) : ℝ :=
  countCoefficient (Fintype.card (Sum Bool (RayQuotient.Characters S.modulus ⊤)))
    (Fintype.card B.base.batch.Bin) B.baseScale B.height K.K₀ K.Ki K.C₀ K.Cr K.Ci K.J₀ K.Jr K.Ji
def centered (B : MiddleBank D S η Z) : ℝ :=
  center B.k B.currentSlice.fiber.r B.currentSlice.fiber.m B.m B.H
def penalty (B : MiddleBank D S η Z) (lo hi M : ℝ) : ℝ :=
  QRH.Cycle090.witnessPenalty lo hi (-hi*(B.xi+3*B.εa)) B.H M B.currentSlice.fiber.m

def CountConclusion (B : MiddleBank D S η Z) (K : CountConstants) : Prop :=
  (B.common.card:ℝ) ≤ B.coefficient K*B.baseScale^(B.R-B.delta*B.centered+B.loss) ∧
  ∀lo hi M : ℝ,0 ≤ lo → lo ≤ B.k → B.k ≤ hi → B.m ≤ M →
    B.penalty lo hi M ≤ B.k*(B.currentSlice.fiber.m-B.m)+B.centered ∧
    (B.common.card:ℝ) ≤ B.coefficient K*B.baseScale^(B.R-
      B.delta*(B.penalty lo hi M-B.k*(B.currentSlice.fiber.m-B.m))+B.loss)
end MiddleBank

/-- A single compact record feeds the authentic source suppliers. Constants
are selected before all live banks, current/previous indices and row sets. -/
theorem actual_middle_bank_count (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
    ∃mesh : ℝ→ℝ,(∀t,0<t → 0< mesh t) ∧
    ∀ (D : Cycle25.Weighted.MomentData) (S : WeightedSourceData D),
      (∀s,D.ell s ≤ mesh D.t/200) → (∀s,D.ell s ≤ Cycle25.sourceMesh D.t/200) →
      D.ε ≤ 1/10000000 → D.t ≤ 1/10000000 →
    ∀κplain : ℝ,7/10 ≤ κplain → κplain ≤ 3/4 → 2*HeckeZeroSupremum.beta-1 ≤ κplain →
    ∀η : Character,∃K : CountConstants,∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀B : MiddleBank D S η Z,B.CountConclusion K := by
  obtain ⟨mesh,hm,hcount⟩:=actual_centered_bank_count hβ
  refine ⟨mesh,hm,?_⟩
  intro D S hfine hstandard he ht κ hk hk' hkβ
  obtain ⟨K₀,Ki,hK₀,hKi,hcount⟩:=hcount D S hfine hstandard he ht κ hk hk' hkβ
  intro η
  obtain ⟨J₀,Jr,Ji,C₀,Cr,Ci,hC₀,hCr,hCi,hcount⟩:=hcount η
  let K : CountConstants:=⟨K₀,Ki,C₀,Cr,Ci,J₀,Jr,Ji,hK₀,hKi,hC₀,hCr,hCi⟩
  refine ⟨K,?_⟩
  filter_upwards [hcount] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro B
  exact hZ.2 B.d B.a B.T B.allowance B.height B.q B.t₀ B.γ B.meshBank B.εa B.factor B.i B.j
    B.d_min B.a_min B.delta_max B.height_nonneg B.frequency B.gamma_nonneg B.cutoff_min B.cutoff_max
    B.mesh_nonneg B.collar_nonneg B.support_collar B.available B.baseline_cutoff
    B.base B.current B.prior B.currentSlice B.priorSlice B.base_nonempty B.base_mean B.base_height
    B.current_height B.prior_height B.base_mesh B.current_mesh B.current_mean B.inverse_min B.inverse_max
    B.ordinary_min B.ordinary_max B.prior_long B.directed_scale B.common B.common_base B.common_current B.common_prior

#print axioms actual_middle_bank_count
end
end QRH.Cycle092.MixedOffsetCount
