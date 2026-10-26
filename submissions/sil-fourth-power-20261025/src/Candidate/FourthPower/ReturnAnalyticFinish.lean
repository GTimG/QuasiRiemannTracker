/- Copyright (c) 2026 Sil. Apache-2.0.
Scalar estimates for physical energy reconstruction and the
downward source domain. The numerator formula follows PR69
Return/GenericScalar.lean, retaining its physical weights and using the
list-envelope of the seventeen admission windows.
The physical numerator and common probe are assembled separately.
-/
import Candidate.FourthPower.ReturnFeedback
import Candidate.FourthPower.ReturnSourceFaces

set_option autoImplicit false
namespace Candidate.FourthPower.ReturnAnalyticFinish
noncomputable section
open ReturnCertificate ReturnEnvelopeBridge ReturnFeedback ReturnSourceFaces

/-- Reciprocal-Mellin shift at our exact geometry. -/
def signalShift : ℝ := -(4+y-x)/6

def signal (β : ℝ) : ℝ := β+signalShift

/-- The count exponent is literally GenericCount.envelope for our CountScheme.
No older countingR exponent is substituted for the selected seventeen windows. -/
def numeratorExponent (k d C δ p : ℝ) : ℝ :=
  -y/2+ell*(17/50-1/2)+ell*δ*p+
    d*((3*upstreamEnvelope k δ p+1)/4-17/50)-δ*p*C/2

def kernelExponent (a e : ℝ) : ℝ :=
  x*(1/2-17/50)+a+16*e+17/50-1

theorem signal_at_boundary : signal theta = x/2+(y-x)/12 := by
  simpa only [signal,signalShift,sub_eq_add_neg,neg_div] using geometry_identities.2

/-- The exact scalar identity at the same count exponent as the actual
SelectedCountBound. This is the insertion point in Source.Mask/OldCollect. -/
theorem numerator_kernel_identity {k δ p : ℝ} (d C e : ℝ)
    (hk : 7/10 ≤ k) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) :
    numeratorExponent k d C δ p+kernelExponent ((1+δ)/2) e =
      returnValue d C δ p (variableEnvelope k δ p)+signalShift+16*e := by
  unfold numeratorExponent
  rw [upstreamEnvelope_eq_variable hk hδ hp]
  dsimp only [kernelExponent,returnValue,signalShift,x,y]
  ring

/-- Literal finite source losses: the names and weights follow the existing
physical packet proof. No bound on an actual packet is made a premise. -/
structure LossData where
  front : ℝ
  frequency : ℝ
  scalar : ℝ
  mass : ℝ
  count : ℝ
  moment : ℝ
  selection : ℝ
  mesh : ℝ
  slack : ℝ

def weightedSourceLoss (d δ : ℝ) (L : LossData) : ℝ :=
  L.front+L.frequency+L.slack*ell+
    d*(L.scalar+L.mass+(3*L.count+L.moment)/4+L.selection/2+δ*L.mesh/4)

/-- Expanding the actual source packet introduces precisely the numerator
exponent above. q/delta is the masked weighted mean, with no changed envelope. -/
theorem source_packet_exponent (k d C δ q : ℝ) (L : LossData)
    (hd : d ≠ 0) (hδ : δ ≠ 0) :
    L.front+L.frequency-y/2-(4/25)*ell+L.slack*ell+
      d*(L.scalar+L.mass+q*(ell/d)-q*(C/d)/2+
        (3*(upstreamEnvelope k δ (q/δ)+L.count)+1+L.moment)/4+
        L.selection/2+δ*L.mesh/4-17/50) =
      numeratorExponent k d C δ (q/δ)+weightedSourceLoss d δ L := by
  unfold numeratorExponent weightedSourceLoss
  field_simp [hd,hδ]
  <;> ring

/-- Our checked scalar feedback discharges the physical packet's exponent
inequality, including both old/new capacities and the fixed conductor join.
It does not itself prove the estimate for a finite physical numerator. -/
theorem physical_packet_certificate {β d δ p e height : ℝ} (L : LossData)
    (hβ : theta < β) (hd : d ∈ Set.Icc d0 dplus)
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2))
    (hbudget : 16*e+weightedSourceLoss d δ L+height ≤ (β-theta)/4) :
    numeratorExponent (2*β-1) d (variableCapacity (2*β-1) d) δ p+
      kernelExponent ((1+δ)/2) e+weightedSourceLoss d δ L <
      signal β-reserve/2-(β-theta)/2-height := by
  have hk : 7/10 ≤ 2*β-1 := by
    have hc := complementary_guards.feedback_k
    dsimp only [kappa] at hc
    linarith
  have hid := numerator_kernel_identity d (variableCapacity (2*β-1) d) e hk hδ hp
  have hreturn := contrary_return hβ hd hδ hp
  have hr : 0 < reserve := by norm_num [reserve]
  change returnValue d (variableCapacity (2*β-1) d) δ p
      (variableEnvelope (2*β-1) δ p)-β ≤ _ at hreturn
  unfold signal
  linarith only [hid,hreturn,hbudget,hr]

/-- The entire downward physical domain is included in the ACTUAL full
SourceFace, including zero slots and either plain length below 2/5.
This is the precise replacement for small_plain_shortening/small_slot_shortening.
No source estimate is claimed: the full UniformUnitFaceSource remains required. -/
theorem physical_full_face_downward {d t m₁ m₂ s : ℝ}
    (hd : ds ≤ d) (hd' : d ≤ dplus) (ht : 0 ≤ t) (ht' : t ≤ shiftCutoff)
    (hm₁0 : 0 ≤ m₁) (hm₂0 : 0 ≤ m₂) (hs0 : 0 ≤ s)
    (hm₁ : m₁ ≤ shiftedPlain d t) (hm₂ : m₂ ≤ shiftedPlain d t)
    (hs : s ≤ shiftedWidth d t) :
    fullSourceFace.Admissible m₁ m₂ s 1 := by
  have hL : 0 < physicalSlope := by norm_num [physicalSlope]
  have hwidth := (shifted_width_bounds hd hd' ht ht').2
  have hcap : s ≤ physicalFace.cap := by
    change s ≤ 43/1000
    have hh : sPhysical ≤ (43/1000:ℝ) := by norm_num [sPhysical]
    exact hs.trans (hwidth.trans hh)
  have hraw : s ≤ (physicalIntercept-2*shiftedPlain d t)/physicalSlope :=
    hs.trans (min_le_right _ _)
  have hraw' := (le_div_iff₀ hL).1 hraw
  have hbudget : (m₁+m₂)+physicalFace.slope*s ≤ physicalFace.intercept := by
    change m₁+m₂+physicalSlope*s ≤ physicalIntercept
    nlinarith only [hm₁,hm₂,hraw']
  have hglobal := Face.source_domain physicalFace_included hs0 hcap hbudget
  have hsl : 0 ≤ sourceSlope*s := mul_nonneg (by norm_num [sourceSlope]) hs0
  change 0*1 ≤ m₁ ∧ m₁ ≤ sourceB*1 ∧ 0*1 ≤ m₂ ∧ m₂ ≤ sourceB*1 ∧
    0*1 ≤ s ∧ s ≤ sourceCap*1 ∧ m₁+m₂+sourceSlope*s ≤ sourceB*1
  norm_num only [mul_one,zero_mul]
  exact ⟨hm₁0,by linarith [hglobal.2],hm₂0,by linarith [hglobal.2],
    hs0,hglobal.1,hglobal.2⟩

/- NO endpoint theorem follows here. Required actual reconstruction, using
the above two inlets and ReturnActualCount.selected_count_from_full_source:
  full initial radial source -> finite physical pair -> Fourier pair;
  reflected retained/original/active fourth moments -> selected source packet;
  canonical amplitude class + masked count with the same seventeen windows;
  all error masks + conductor bands -> actual FullW cells -> finite numerator;
  signed Gram + high approximation -> actual UniformCommonProbe;
  Cycle25.beta_le_of_common_probe -> Hecke/Dirichlet nonvanishing.
Precise theorem names, uniformity order and the four incompatible old guards
are recorded in return-analytic-finish-findings.txt. No placeholder premise for
any of those missing analytic conclusions is introduced here.
-/

end
end Candidate.FourthPower.ReturnAnalyticFinish
