import Cycle25.Assembly.Count.Adaptive
import Cycle25.Assembly.Count.Endpoint



namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.Cycle25ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst Cycle25DetectorRowCount

structure CountParameters (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (εm : ℝ) where
  c : ℝ
  k : ℝ
  c_pos : 0<c
  c_one : c≤1
  k_pos : 0<k
  balanced : ∃K₀ : ℝ,0≤K₀ ∧ ∀ᶠU : ℝ in atTop,
      ∀(a ε T allowance κplain ν C height q : ℝ) (i : ℕ),
      1<U → 51/100<a → 2*a-1≤3/4 → 0≤ε → ε≤1/1000 →
      7/10≤κplain → κplain≤3/4 → 0<ν → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      ∀{Label Slot : Type} [Fintype Label] (B : Batch M H Label Slot U a ε (cutoff (2*a-1) (q/(2*a-1)) κplain) T allowance i),
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external U) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Cycle25DetectorRawFiber.Moments (B.fiber bin j J K hne) κplain c k C height εm) →
      (B.rows.card:ℝ)≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2* fiberConstant C height K₀*
        (Fintype.card B.Bin:ℝ)*
        U^(rowCount (2*a-1) (q/(2*a-1)) κplain+
          159*ε+εm+B.mesh+7*ν)

theorem exists_count_parameters
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    Nonempty (CountParameters M H εm) := by
  obtain ⟨c,k,K,hc,hc1,hk,hK,hcount⟩ := balanced_adaptive_count_from_raw_moments
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  exact ⟨⟨c,k,hc,hc1,hk,⟨K,hK,hcount⟩⟩⟩

end SevenEighths.Cycle25ProbeHighRowFamily
end
end OAI
