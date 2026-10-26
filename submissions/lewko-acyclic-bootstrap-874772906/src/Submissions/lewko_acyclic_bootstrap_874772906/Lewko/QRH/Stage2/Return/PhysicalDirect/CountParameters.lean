/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The finite minimum chooses the cutoff before the Batch. Both inverse amplifier
parameter pairs are saved globally; the actual moment sums remain explicit. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.Schedule
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.SelectedBatch
set_option autoImplicit false
open QRH.LewkoStage2Return

namespace QRH.LewkoStage2Return.GenericPhysical.PhysicalDirect
variable [Geometry.Parameters] [Geometry.Bounds] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
open QRH.Record12518109Count
open QRH.LewkoStage2Return.GenericCount
noncomputable section
set_option maxHeartbeats 200000
open scoped Classical BigOperators ContDiff
open Set Filter OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst Cycle25DetectorRowCount
open HeckeDetectorFixedAmplitudeCount

structure CountParameters (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (εm : ℝ) where
  co : ℝ
  κo : ℝ
  Ko : ℝ
  ca : ℝ
  κa : ℝ
  Ka : ℝ
  co_pos : 0<co
  co_one : co≤1
  κo_pos : 0<κo
  Ko_nonneg : 0≤Ko
  ca_pos : 0<ca
  ca_one : ca≤1
  κa_pos : 0<κa
  Ka_nonneg : 0≤Ka
  counted :
      ∀ᶠ U : ℝ in atTop,
      ∀ (κplain a ε T allowance ν C height q : ℝ) (i : ℕ),
      1<U → 51/100<a → 2*a-1≤3/4 → 0≤ε → ε≤1/10000000 →
      7/10≤κplain → κplain≤3/4 → 0<ν → ν≤1/10000000 → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      ∀ {Label Slot : Type} [Fintype Label]
        (B : Batch M H Label Slot U a ε (GenericCount.selectedCutoff κplain (2*a-1) (q/(2*a-1))) T allowance i),
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
        U^(GenericCount.envelope κplain (2*a-1) (q/(2*a-1))+159*ε+εm+B.mesh+7*ν)

theorem exists_count_parameters
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀ y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) : Nonempty (CountParameters M H εm) := by
  obtain ⟨co,κo,Ko,ca,κa,Ka,hco,hco1,hκo,hKo,hca,hca1,hκa,hKa,hcount⟩ :=
    fixed_amplitude_selected_envelope_count M H hH S φ hφ hφc hφp hφ0 hφne
      a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  exact ⟨⟨co,κo,Ko,ca,κa,Ka,hco,hco1,hκo,hKo,hca,hca1,hκa,hKa,hcount⟩⟩
end
end QRH.LewkoStage2Return.GenericPhysical.PhysicalDirect
#print axioms QRH.LewkoStage2Return.GenericPhysical.PhysicalDirect.exists_count_parameters
