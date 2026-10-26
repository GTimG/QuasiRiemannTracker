/- Copyright (c) 2026 Sil. Apache-2.0.
Direct first whole-kernel integration from explicit raw side energies.
Independent KL/KR and the reflected/conjugated right row are retained.
This is a mechanism with an explicit energy supply, not a source theorem.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedFirstRawScalar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RepairedFirstRawKernel
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcreteTraceCRT ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst CenteredMomentSourceMass
open CenteredMomentSecondWindowBudget CenteredMomentSecondHeightFamily CenteredMomentLogDyadic
open CenteredMomentCauchy CenteredMomentSmooth
open MixedPrincipalPair MixedPrincipalWindow MixedFirstAveragedWindow MixedFirstPhysicalApplication
open RepairedFirstRawSides RepairedFirstRawWindows
open ActualEisensteinCubic CenteredMomentSecondIdealBlockBound
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

def matrix (s : Source ι a b) (ha : 0 < a) (C D : Id) (hC : Supported C) (hD : Supported D)
    (E : Finset (CommonIndex C D)) (u : Id) (τL τR : Character) (t : ℝ)
    (rows : Finset O) (Φ : 𝓢(ℝ,ℂ)) (K K₀ H₀ A₀ B₀ : ℝ) : ℂ :=
  ∑z∈rows,commonPhase C D hC (1,z)*
    weightedPair s ha C D 1 u hC.1 hD.1 τL τR t t (fun _ => 1) 1 (1,z)
      (physicalKernel Φ (fun _ => logAnnulus) C D E K K₀ H₀ A₀ B₀ z)

theorem paired_column_bound (s : Source ι a b) (ha : 0 < a)
    (C D : Id) (hC : Supported C) (hD : Supported D) (u : Id) (τL τR : Character)
    (t θ A₀ B₀ KL KR : ℝ) (hA₀ : 0 < A₀) (hB₀ : 0 < B₀) (hKL : 0 < KL) (hKR : 0 < KR)
    (rows : Finset O) (hrowsL : ∀z∈rows,‖eisEmbedding z‖^2 ≤ KL)
    (hrowsR : ∀z∈rows,‖eisEmbedding z‖^2 ≤ KR)
    (J : ℕ) (EL ER : ℝ) (hEL : 0 ≤ EL) (hER : 0 ≤ ER)
    (hleft : ∀v : ℝ,rawEnergy s ha D C hC u τL v KL ≤ EL*(1+‖v‖)^(2*J))
    (hright : ∀v : ℝ,rawEnergy s ha C D hD u τR v KR ≤ ER*(1+‖v‖)^(2*J)) :
    Real.sqrt (∑z∈rows,‖leftColumn Finset.univ
      (rowVector s ha D C 1 u hC.1 τL t (fun _ => 1) 1 false (1,z)) logAnnulus
      (fun I : Columns s D C hC.1 => Real.log ((I.val.absNorm:ℝ)/A₀)) θ‖^2)*
    Real.sqrt (∑z∈rows,‖rightColumn Finset.univ
      (rowVector s ha C D 1 u hD.1 τR t (fun _ => 1) 1 true (1,z)) logAnnulus
      (fun I : Columns s C D hD.1 => Real.log ((I.val.absNorm:ℝ)/B₀)) θ‖^2) ≤
      (windowBudget J t EL*windowBudget J t ER)*(1+‖θ‖)^(2*J) := by
  have hl := left_column_bound s ha D C hC u τL t θ A₀ KL hA₀ hKL rows hrowsL J EL hEL hleft
  have hr := right_column_bound s ha C D hD u τR t θ B₀ KR hB₀ hKR rows hrowsR J ER hER hright
  have hLp : 0 ≤ windowBudget J t EL*(1+‖θ‖)^J :=
    mul_nonneg (windowBudget_nonneg _ _ _) (pow_nonneg (by positivity) _)
  have hRp : 0 ≤ windowBudget J t ER*(1+‖θ‖)^J :=
    mul_nonneg (windowBudget_nonneg _ _ _) (pow_nonneg (by positivity) _)
  have hLs := Real.sqrt_le_iff.mpr ⟨hLp,hl⟩
  have hRs := Real.sqrt_le_iff.mpr ⟨hRp,hr⟩
  apply (mul_le_mul hLs hRs (Real.sqrt_nonneg _) hLp).trans_eq
  rw [show 2*J=J*2 by omega,pow_mul]
  ring

set_option maxHeartbeats 800000 in
/-- Kernel constant is chosen before the source, radii, common ideals,
profiles and u. Raw side estimates are the ONLY analytic supply premise. -/
theorem kernel_from_raw (Φ : 𝓢(ℝ,ℂ)) (J : ℕ) :
    ∃ Ckernel : ℝ, 0 ≤ Ckernel ∧
    ∀ s : Source ι a b, ∀ ha : 0 < a,
    ∀ (C D : Id) (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D)),
    ∀ (u : Id) (τL τR : Character) (t K K₀ H₀ A₀ B₀ KL KR : ℝ),
      0 < K₀ → 0 < H₀ → 0 < A₀ → 0 < B₀ → 0 < KL → 0 < KR →
    ∀ rows : Finset O,(∀z∈rows,‖eisEmbedding z‖^2 ≤ KL) → (∀z∈rows,‖eisEmbedding z‖^2 ≤ KR) →
    ∀ EL ER : ℝ,0 ≤ EL → 0 ≤ ER →
    (∀v : ℝ,rawEnergy s ha D C hC u τL v KL ≤ EL*(1+‖v‖)^(2*J)) →
    (∀v : ℝ,rawEnergy s ha C D hD u τR v KR ≤ ER*(1+‖v‖)^(2*J)) →
      ‖matrix s ha C D hC hD E u τL τR t rows Φ K K₀ H₀ A₀ B₀‖ ≤
        Ckernel*(windowBudget J t EL*windowBudget J t ER) := by
  obtain ⟨Ckernel,hCkernel,hkernel⟩ := whole_kernel_row_estimate Φ (fun _ => logAnnulus)
    (fun _ => Real.log 4) (fun _ => Real.log_nonneg (by norm_num))
    (fun _ y hy => logAnnulus_enclosure y hy) 0 (2*J)
  refine ⟨Ckernel,hCkernel,?_⟩
  intro s ha C D hC hD E u τL τR t K K₀ H₀ A₀ B₀ KL KR hK₀ hH₀ hA₀ hB₀ hKL hKR rows hrowsL hrowsR EL ER hEL hER hl hr
  let e := primeSubsetGenerator (fun P : CommonIndex C D => P.val) E
  let Rwin := K₀*H₀/(A₀*B₀)
  have hRwin : 0 < Rwin := div_pos (mul_pos hK₀ hH₀) (mul_pos hA₀ hB₀)
  let c := fun z : O => rowVector s ha D C 1 u hC.1 τL t (fun _ => 1) 1 false (1,z)
  let d := fun z : O => rowVector s ha C D 1 u hD.1 τR t (fun _ => 1) 1 true (1,z)
  let xL := fun I : Columns s D C hC.1 => Real.log ((I.val.absNorm:ℝ)/A₀)
  let xR := fun I : Columns s C D hD.1 => Real.log ((I.val.absNorm:ℝ)/B₀)
  let phase₀ := fun _z : O => Real.log (((K/‖eisEmbedding e‖^2)/‖eisEmbedding (activeConductor C D)‖^2)/K₀)
  let phase₁ := fun z : O => Real.log (‖eisEmbedding z‖^2/H₀)
  have he := hkernel Rwin hRwin rows Finset.univ Finset.univ c d xL xR phase₀ phase₁
    (fun z => commonPhase C D hC (1,z)) (fun z _ => commonPhase_norm C D hC (1,z))
    (fun z _ => logAnnulus_norm _) (fun z _ => logAnnulus_norm _)
    (windowBudget J t EL*windowBudget J t ER)
    (mul_nonneg (windowBudget_nonneg _ _ _) (windowBudget_nonneg _ _ _))
    (fun θ => paired_column_bound s ha C D hC hD u τL τR t θ A₀ B₀ KL KR hA₀ hB₀ hKL hKR
      rows hrowsL hrowsR J EL ER hEL hER hl hr)
  simpa only [pow_zero,one_mul,matrix,weightedPair,physicalKernel,c,d,xL,xR,phase₀,phase₁,Rwin,e] using he

end
end Candidate.FourthPower.RepairedFirstRawKernel
