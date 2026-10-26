/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Uses Cycle25's actual Batch.card_bound and fixed-amplitude fiber equality. -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.WindowFiber
import Submissions.hailey_collet_1252270103.Cycle25.Assembly.Count.FixedAmplitude
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Return
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter OAI OAI.SevenEighths QRH.Record12518109Count
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst Cycle25DetectorRowCount
open HeckeDetectorFixedAmplitudeCount
theorem fixed_amplitude_window_count
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃c κ K₀ : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠU : ℝ in atTop,
      ∀naturalκ:ℝ,7/10≤naturalκ → naturalκ≤3/4 → ∀w:AdmittedWindow naturalκ,
      ∀(a ε T allowance ν C height q:ℝ) (i:ℕ),
      1<U → 51/100<a → 2*a-1≤3/4 → 0≤ε → ε≤1/10000000 →
      0<ν → ν≤1/10000000 → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      w.Available (2*a-1) (q/(2*a-1)) →
      ∀{Label Slot:Type} [Fintype Label]
      (B:Batch M H Label Slot U a ε (w.cutoff (2*a-1) (q/(2*a-1))) T allowance i),
      (∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u:FreeRow=>u.val) B.profile B.upper B.widths B.external U) u=q) →
      (∀bin j J K,∀hne:(B.fiberRows bin j J K).Nonempty,
        Cycle25DetectorRawFiber.Moments (B.fiber bin j J K hne) naturalκ c κ C height εm) →
      (∀bin j J K,∀hne:(B.fiberRows bin j J K).Nonempty,
        AffineMarkedMoment (B.fiber bin j J K hne) w.face C height εm) →
      (B.rows.card:ℝ)≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2*fiberConstant C height K₀*
        (Fintype.card B.Bin:ℝ)*U^(w.value (2*a-1) (q/(2*a-1))+159*ε+εm+B.mesh+7*ν) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hcount⟩ := count_fiber_at_window
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hcount] with U hcount
  intro naturalκ hk hk1 w a ε T allowance ν C height q i hU ha hd hε hεhi hν hνhi hC hh hf hAvail Label Slot _ B hq moments affine
  have hb := B.card_bound (fiberConstant C height K₀)
    (fun _=>w.value (2*a-1) (q/(2*a-1))+159*ε+εm+B.mesh+7*ν)
    (fiberConstant_bounds C height K₀ hC hh hK).1 (zero_lt_one.trans hU) (by
      intro bin j J K hne
      have hc' := hcount naturalκ hk hk1 w a ε _ T allowance ν C height i
        hU ha hd hε hεhi hν hνhi hC hh hf (B.fiber bin j J K hne)
      rw [fiber_mean_eq B q hq bin j J K hne] at hc'
      exact hc' hAvail rfl (moments bin j J K hne) (affine bin j J K hne))
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using hb

end
end QRH.Record1252270103Return
#print axioms QRH.Record1252270103Return.fixed_amplitude_window_count
