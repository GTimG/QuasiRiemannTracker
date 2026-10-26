/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The finite minimum chooses the cutoff before the Batch. Both inverse amplifier
parameter pairs are saved globally; the actual moment sums remain explicit. -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.CountScheme
import Submissions.hailey_collet_1252270103.Record1252270103Return.WindowBatch
import Submissions.hailey_collet_1252270103.Cycle25.Assembly.Count.Adaptive
set_option autoImplicit false
namespace QRH.Record1252270103Return.GenericCount
noncomputable section
variable [scheme:CountScheme]
set_option maxHeartbeats 200000
open scoped Classical BigOperators ContDiff
open Set Filter OAI OAI.SevenEighths QRH.Record12518109Count
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst Cycle25DetectorRowCount
open HeckeDetectorFixedAmplitudeCount

theorem fixed_amplitude_envelope_count
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀ y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃ co κo Ko ca κa Ka : ℝ,
      0<co ∧ co≤1 ∧ 0<κo ∧ 0≤Ko ∧ 0<ca ∧ ca≤1 ∧ 0<κa ∧ 0≤Ka ∧
      ∀ᶠ U : ℝ in atTop,
      ∀ (κplain a ε T allowance ν C height q : ℝ) (i : ℕ),
      1<U → 51/100<a → 2*a-1≤3/4 → 0≤ε → ε≤1/10000000 →
      7/10≤κplain → κplain≤3/4 → 0<ν → ν≤1/10000000 → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      ∀ choice : Choice, choice.Available (2*a-1) (q/(2*a-1)) →
      choice.value κplain (2*a-1) (q/(2*a-1)) = envelope κplain (2*a-1) (q/(2*a-1)) →
      ∀ {Label Slot : Type} [Fintype Label]
        (B : Batch M H Label Slot U a ε (choice.cutoff κplain (2*a-1) (q/(2*a-1))) T allowance i),
      B.rows.Nonempty →
      (∀ u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external U) u=q) →
      (∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
        Cycle25DetectorRawFiber.Moments (B.fiber bin label left right hne) κplain co κo C height εm) →
      (∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
        Cycle25DetectorRawFiber.Moments (B.fiber bin label left right hne) scheme.naturalκ ca κa C height εm) →
      (∀ w∈scheme.windows, ∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
        AffineMarkedMoment (B.fiber bin label left right hne) w.face C height εm) →
      (B.rows.card:ℝ) ≤ (Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2*
        max (fiberConstant C height Ko) (fiberConstant C height Ka)*(Fintype.card B.Bin:ℝ)*
        U^(envelope κplain (2*a-1) (q/(2*a-1))+159*ε+εm+B.mesh+7*ν) := by
  obtain ⟨co,κo,Ko,hco,hco1,hκo,hKo,hold⟩ :=
    Cycle25ProbeHighRowFamily.balanced_adaptive_count_from_raw_moments
      M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  obtain ⟨ca,κa,Ka,hca,hca1,hκa,hKa,hnew⟩ := fixed_amplitude_window_count
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨co,κo,Ko,ca,κa,Ka,hco,hco1,hκo,hKo,hca,hca1,hκa,hKa,?_⟩
  filter_upwards [hold,hnew] with U hold hnew
  intro κplain a ε T allowance ν C height q i hU ha hd hε hεsmall hk hkhi hν hνhi hC hh hf
    choice hAvail hvalue Label Slot _ B hne hq oldmom newmom rawmom
  have promote (K R : ℝ)
      (hK : fiberConstant C height K ≤ max (fiberConstant C height Ko) (fiberConstant C height Ka))
      (hR : R = envelope κplain (2*a-1) (q/(2*a-1)))
      (hc : (B.rows.card:ℝ) ≤ (Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2*
        fiberConstant C height K*(Fintype.card B.Bin:ℝ)*U^(R+159*ε+εm+B.mesh+7*ν)) :
      (B.rows.card:ℝ) ≤ (Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2*
        max (fiberConstant C height Ko) (fiberConstant C height Ka)*(Fintype.card B.Bin:ℝ)*
        U^(envelope κplain (2*a-1) (q/(2*a-1))+159*ε+εm+B.mesh+7*ν) := by
    rw [hR] at hc
    apply hc.trans
    have h1 := mul_le_mul_of_nonneg_left hK
      (show 0 ≤ (Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2 by positivity)
    have h2 := mul_le_mul_of_nonneg_right h1 (show 0 ≤ (Fintype.card B.Bin:ℝ) by positivity)
    exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (zero_lt_one.trans hU).le _)
  cases choice with
  | old =>
    have hb := hold a ε T allowance κplain ν C height q i hU ha hd hε
      (by linarith) hk hkhi hν hC hh hf B hne hq oldmom
    rw [← QRH.Record12518109Return.countingR_eq_actual hk] at hb
    exact promote Ko _ (le_max_left _ _) hvalue hb
  | affine w =>
    have hb := hnew scheme.naturalκ scheme.natural_lo scheme.natural_hi w a ε T allowance ν C height q i hU ha hd hε hεsmall
      hν hνhi hC hh hf hAvail.2 B hq newmom (rawmom w hAvail.1)
    exact promote Ka _ (le_max_right _ _) hvalue hb
end
end QRH.Record1252270103Return.GenericCount
#print axioms QRH.Record1252270103Return.GenericCount.fixed_amplitude_envelope_count
