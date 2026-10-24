/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The finite minimum chooses the cutoff before the Batch. Both inverse amplifier
parameter pairs are saved globally; the actual moment sums remain explicit. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.EnvelopeBatch
set_option autoImplicit false
namespace QRH.RH20261023Return.GenericCount
noncomputable section
variable [scheme:CountScheme]
set_option maxHeartbeats 200000
open scoped Classical BigOperators ContDiff
open Set Filter OAI OAI.SevenEighths QRH.Record12518109Count
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst Cycle25DetectorRowCount
open HeckeDetectorFixedAmplitudeCount

theorem fixed_amplitude_selected_envelope_count
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
      ∀ {Label Slot : Type} [Fintype Label]
        (B : Batch M H Label Slot U a ε (selectedCutoff κplain (2*a-1) (q/(2*a-1))) T allowance i),
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
  obtain ⟨co,κo,Ko,ca,κa,Ka,hco,hco1,hκo,hKo,hca,hca1,hκa,hKa,hcount⟩ :=
    fixed_amplitude_envelope_count M H hH S φ hφ hφc hφp hφ0 hφne
      a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨co,κo,Ko,ca,κa,Ka,hco,hco1,hκo,hKo,hca,hca1,hκa,hKa,?_⟩
  filter_upwards [hcount] with U hcount
  intro κplain a ε T allowance ν C height q i hU ha hd hε hεsmall hk hkhi hν hνhi hC hh hf
    Label Slot _ B hne hq oldmom newmom rawmom
  exact hcount κplain a ε T allowance ν C height q i hU ha hd hε hεsmall hk hkhi
    hν hνhi hC hh hf (selectedChoice κplain (2*a-1) (q/(2*a-1)))
    (selectedChoice_available _ _ _) (selectedChoice_value _ _ _) B hne hq oldmom newmom rawmom
end
end QRH.RH20261023Return.GenericCount
#print axioms QRH.RH20261023Return.GenericCount.fixed_amplitude_selected_envelope_count
