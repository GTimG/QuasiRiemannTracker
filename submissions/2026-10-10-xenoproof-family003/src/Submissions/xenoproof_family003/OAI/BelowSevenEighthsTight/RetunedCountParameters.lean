import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RetunedAdaptiveCount

/- Uniform count constants for retuned geometry, conditional on actual moments. -/
set_option autoImplicit false

namespace BelowSevenEighthsTight.FiberExtension

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
open OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst RowCountExtension

structure RetunedCountParameters (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (εm : ℝ) where
  cB : ℝ
  kB : ℝ
  cH : ℝ
  kH : ℝ
  cB_pos : 0<cB
  cB_one : cB≤1
  kB_pos : 0<kB
  cH_pos : 0<cH
  cH_one : cH≤1
  kH_pos : 0<kH
  balanced : ∃K₀ : ℝ,0≤K₀ ∧ ∀ᶠU : ℝ in atTop,
      ∀(a ε T allowance Δ κ₀ capacity ν C height q : ℝ) (i : ℕ),
      1<U → 51/100<a → 2*a-1≤5/6 → 0≤ε → ε≤1/1000 →
      0≤Δ → 13/18≤κ₀ → κ₀≤3/4 → capacity=κ₀+2*Δ → capacity≤1 → 0<ν → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      ∀{Label Slot : Type} [Fintype Label] (B : Batch M H Label Slot U a ε (cutoff κ₀ (2*a-1) q) T allowance i),
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external U) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        CapacityMoments (B.fiber bin j J K hne) capacity cB kB C height εm) →
      (B.rows.card:ℝ)≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2* fiberConstant C height K₀*
        (Fintype.card B.Bin:ℝ)*
        U^(rowEnvelope (1/(3*κ₀)) (2*a-1) (1/2-q/(2*a-1))+
          Δ/4+159*ε+εm+B.mesh+7*ν)
  high : ∃K₀ : ℝ,0≤K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε T allowance κ₀ capacity C height q : ℝ) (i : ℕ),
      1<U → 5/6<2*a-1 → a≤1 → 0≤ε → ε≤1/1000 → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤height →
      ∀ {Label Slot : Type} [Fintype Label] (B : Batch M H Label Slot U a ε (cutoff κ₀ (2*a-1) q) T allowance i),
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        CapacityMoments (B.fiber bin j J K hne) capacity cH kH C height εm) →
      (B.rows.card : ℝ)≤(Fintype.card Label:ℝ)*(HeckeDetectorWitnessRows.dyadicLength U:ℝ)^2*
        fiberConstant C height K₀*(Fintype.card B.Bin:ℝ)*U^(1-(2*a-1)+78*ε+εm)

theorem exists_retuned_count_parameters
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    Nonempty (RetunedCountParameters M H εm) := by
  obtain ⟨cB,kB,KB,hcB,hcB1,hkB,hKB,hbalanced⟩ := balanced_adaptive_count_from_raw_moments M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  obtain ⟨cH,kH,KH,hcH,hcH1,hkH,hKH,hhigh⟩ := high_adaptive_count_from_raw_moments M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  exact ⟨⟨cB,kB,cH,kH,hcB,hcB1,hkB,hcH,hcH1,hkH,⟨KB,hKB,hbalanced⟩,⟨KH,hKH,hhigh⟩⟩⟩

#print axioms exists_retuned_count_parameters

end

end BelowSevenEighthsTight.FiberExtension
