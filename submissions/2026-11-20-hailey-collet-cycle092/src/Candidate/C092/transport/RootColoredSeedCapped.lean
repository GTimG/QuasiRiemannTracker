/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Original ordered source geometry discharges the actual second zero/tail.
   Fixed and regular signed groups remain the physical children. -/
import Candidate.C092.transport.RootColoredSeedActual

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RootColoredSeed
noncomputable section
local instance (priority := 2000) instDecEqCapped {κ : Type*} {p : κ → Prop} : DecidableEq (Subtype p) := Classical.decEq _
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentEnergyBands
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow
open MixedOriginalNormCap MixedOriginalTail MixedInnerExceptionalBlock
open MixedPrincipalAllocations MixedFirstLiveSource
open QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.Cycle090 QRH.Cycle092.NativeStrip
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

open QRH.Cycle092.RawSides (residualSeedsQ selectionScaleQ residualCapQ allocated_residual_caps_Q root_pool_of_boxes selected_width_Q allocated_residual_pool_le)
open CenteredMomentFirstSectors CenteredMomentHeckeColumnWindow CenteredMomentActiveSource
open CenteredMomentCompleteCommon
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentSourceMass CompletedGauss
variable {ι : Type*} [Fintype ι] {a b : ℝ}
theorem original_second_zero_tail_Q_caps (N : ℕ) (ξ : ℝ) (hξ : 0 < ξ) :
    ∃ Cz Ct : ℝ, 0 < Cz ∧ 0 < Ct ∧ ∀ᶠ Z : ℝ in atTop, 3 ≤ Z ∧
    ∀ (ι : Type) [Fintype ι] (s : Source ι (1/4) (9/4)), Fintype.card ι ≤ N →
    ∀ (cover : OriginalEnclosure s) (w : ι → ℝ), (∀ i,0 ≤ w i) → (∀ i,s.P i = Z^(w i)) →
    ∀ n y : ℝ, sourceY0 ≤ y → y ≤ sourceY → n ≤ sourceRatio*y →
      Box n y (sourceWidth n y) (length Z s.X₁) (length Z s.X₂) (∑ i,w i) →
      poolCap s ≤ Z^(8:ℝ) →
    ∀ (C D : Id) (hD : D ≠ 0) (G : Id) (B : actualAllocations (tuplePools s) G)
      (J : Finset (liveIndices B.val)), (∑ j ∈ J,w j.val) ≤ 3/5000 →
    ∀ (η₁ η₂ ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t K : ℝ),
      1/2 ≤ K → K ≤ Z^(40:ℝ) →
    let r := restOf s (by norm_num) cover G B J
    let V := residualSeedsQ s (by norm_num) cover C D hD G B J
    let W := selectionScaleQ s (by norm_num) cover G B J
    let X := residualCapQ r
    let Tsec := secondCutoffQ X K W
    zeroTerms r (by norm_num) (idealCoeff η₁) (idealCoeff η₂) V ψ t (16*K*W^4) ≤ Cz*profileCap r^2*K*Z^(93/100:ℝ) ∧
    tailTerms r (by norm_num) (idealCoeff η₁) (idealCoeff η₂) V ψ t (16*K*W^4) Tsec Z ξ ≤ Ct*profileCap r^2*Z^(-22:ℝ) ∧
    (∑ v ∈ V,energy r (by norm_num) (idealCoeff η₁) (idealCoeff η₂) v ψ t (16*K*W^4)) ≤
      Cz*profileCap r^2*K*Z^(93/100:ℝ) +
      groupedPartTerms true r (by norm_num) (idealCoeff η₁) (idealCoeff η₂) ψ χ₀ Q m t (16*K*W^4) Tsec Z ξ X +
      Ct*profileCap r^2*Z^(-22:ℝ) +
      groupedPartTerms false r (by norm_num) (idealCoeff η₁) (idealCoeff η₂) ψ χ₀ Q m t (16*K*W^4) Tsec Z ξ X := by
  obtain ⟨Cz,hCz,hzero⟩ := zero_terms_Q N
  obtain ⟨Ct,hCt,htail⟩ := tail_terms_Q ξ hξ
  refine ⟨Cz,Ct,hCz,hCt,?_⟩
  filter_upwards [allocated_residual_caps_Q N, selected_width_Q N,
    htail,eventually_ge_atTop (3:ℝ)] with Z hcapQ hwidthQ htailQ hZ3
  refine ⟨hZ3,?_⟩
  intro ι _ s hN cover w hw hP n y hy hy' hn hX hpool C D hD G B J hJ η₁ η₂ ψ χ₀ Q m t K hK hKcap
  dsimp only
  let r := restOf s (by norm_num) cover G B J
  let V := residualSeedsQ s (by norm_num) cover C D hD G B J
  let W := selectionScaleQ s (by norm_num) cover G B J
  let X := residualCapQ r
  let Tsec := secondCutoffQ X K W
  have hZ := hcapQ.1
  have hZ0 := zero_lt_one.trans hZ
  have hNres : Fintype.card (Rest J) ≤ N := by
    refine (Fintype.card_le_of_injective (fun j : Rest J => j.val.val) ?_).trans hN
    intro x y hxy
    exact Subtype.ext (Subtype.ext hxy)
  have hNlive : Fintype.card (liveIndices B.val) ≤ N :=
    (Fintype.card_le_of_injective (fun j : liveIndices B.val => j.val) Subtype.val_injective).trans hN
  have hcap : sourceNormCap r.P (9/4) r.T r.d ≤ Z^(919/1000:ℝ) :=
    (hcapQ.2 ι s hN cover w hP n y hy hy' hn hX).2 G B J
  have hpr : poolCap r ≤ Z^(8:ℝ) := (allocated_residual_pool_le s (by norm_num) cover G B J).trans hpool
  have hWV := hwidthQ.2 (liveIndices B.val) (fun j => w j.val) hNlive (fun j => hw j.val) J hJ
  have hWeq : W = ∏ j ∈ J,2*Z^(w j.val) := by
    change (∏ j ∈ J,2*s.P j.val) = _
    simp_rw [hP]
  have hW : 1 ≤ W ∧ W ≤ Z^(1/1000:ℝ) := hWeq ▸ hWV
  have hUs : ∀ u ∈ concreteArtificial s C D hD, Squarefree u := by
    intro u hu
    have hm := (Finset.mem_filter.mp hu).2
    by_contra hsq
    exact hm (by rw [UniqueFactorizationMonoid.moebius_of_not_squarefree hsq, Int.cast_zero])
  have hUX : ∀ u ∈ concreteArtificial s C D hD, (u.absNorm : ℝ) ≤ Z^(8:ℝ) :=
    fun u hu => (QRH.SilDensitySplit.CubeFree.Second.ProviderDiag.artificial_norm_le
      s (by norm_num) C D hD u hu).trans hpool
  have hV0 : ∀ v ∈ V,v ≠ 0 := Vset_ne_bot (allocatedLiveSource s (by norm_num) cover G B)
    (fun _ => rfl) J (concreteArtificial s C D hD)
  have hVcap : ∀ v ∈ V,(v.absNorm : ℝ) ≤ Z^(8:ℝ) :=
    Vset_norm_le (allocatedLiveSource s (by norm_num) cover G B) (fun _ => rfl) J
      (concreteArtificial s C D hD) (by norm_num) hUs _ hUX hpr
  have hcomp : CompleteSeeds r (by norm_num) (idealCoeff η₁) (idealCoeff η₂) V :=
    ⟨Vset_squarefree _ _ _ _, actual_vset_div _ _ _ _ _ η₁ η₂⟩
  have hK0 : 0 ≤ K := by linarith
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hnormX : sourceNormCap r.P (9/4) r.T r.d ≤ X := le_max_right _ _
  have hXcap : X ≤ Z^(919/1000:ℝ) := max_le (Real.one_le_rpow hZ.le (by norm_num)) hcap
  have hz := hzero (Rest J) (1/4) (9/4) r hNres (by norm_num) η₁ η₂ V hV0 ψ t Z K W hZ3 hK0
    (zero_le_one.trans hW.1) hW.2 hcap hVcap
  have ht := htailQ.2 (Rest J) (1/4) (9/4) r (by norm_num) (by norm_num) η₁ η₂ V hV0 ψ t K W X
    hK hKcap hW.1 hW.2 (hpr.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num)))
    hX0 hnormX hXcap hVcap
  refine ⟨hz,ht,?_⟩
  have hnorm : ∀ I ∈ sourceColumns r, TwistedRawSource.sourceColumn r (by norm_num) (idealCoeff η₁) (idealCoeff η₂) 1 I ≠ 0 → (I.absNorm : ℝ) ≤ X := by
    intro I _ hI
    exact (TwistedRawSource.sourceColumn_cap r (by norm_num) (idealCoeff η₁) (idealCoeff η₂) 1 I hI).2.trans hnormX
  have hp := residual_poisson_grouped r (by norm_num) (idealCoeff η₁) (idealCoeff η₂) V hcomp ψ χ₀ Q m t (16*K*W^4)
    Tsec Z ξ X (by
      have hK' : 0 < K := by linarith
      have hW' : 0 < W := zero_lt_one.trans_le hW.1
      positivity) hnorm
  exact hp.trans (add_le_add (add_le_add (add_le_add hz le_rfl) ht) le_rfl)

#print axioms original_second_zero_tail_Q_caps
end
end QRH.Cycle092.RootColoredSeed
