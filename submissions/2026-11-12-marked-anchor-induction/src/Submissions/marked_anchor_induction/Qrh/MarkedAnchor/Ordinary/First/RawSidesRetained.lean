/- Copyright (c) 2026 Sil. Apache-2.0.
Seam 0 at the level of the whole first retained aggregate (`SummedRetainedRawSides`,
`uniform_retained_of_summed_raw_sides`; BALANCED form).

Template: FP `RepairedFirstRawRetained.uniform_retained_of_raw_sides`, whose conclusion is
kept verbatim. Differences:
* the per-block contract is `Second.Concrete.BalancedSummedRawSideBounds` (the sum over the
  first artificial divisors stays inside the Cauchy inequality, CF §4) instead of FP's
  per-divisor `RawSideBounds`;
* consequently only the common band mass `bandMass` is paid
  (`uniform_common_band_mass`), not the common-and-artificial mass;
* the child radii are the uncompleted `childScale Z κ (n 1)` on blocks with
  `dyadicScale (n 1) ≥ 1/2` (the forked `BandGeometry`); the other blocks have no rows.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.First.RawSidesBlock
import Submissions.sil_density_split_20261026.CubeFree.FP.MixedFirstPaidRetained

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qrh.MarkedAnchor.Ordinary.First
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.First
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcreteTraceCRT ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst CenteredMomentSourceMass
open CenteredMomentActiveSource CenteredMomentSourceRow CenteredMomentSecondHeightFamily
open CenteredMomentFirstDiscardedEnergy CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentFirstSectorLocalization CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentSecondWindowBudget
open FP.MixedPrincipalPair FP.MixedPrincipalWindow FP.MixedOriginalNormCap FP.MixedOriginalTail
open FP.MixedFirstPhysicalApplication FP.MixedFirstPhysicalBudget FP.MixedFirstCommonSum
open FP.MixedFirstRetainedFixed FP.MixedFirstPaidRetained
open FP.MixedFirstExceptionalNormalization
open FP.RepairedFirstRawSides FP.RepairedFirstRawScalar FP.RepairedFirstRawBlock
open FP.MixedInnerExceptionalBlock CenteredMomentFirstSectors CenteredMomentFirstSectorTransform
open Second.Concrete
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- The summed (balanced) analytic contract for every actual first retained band and its
actual ideals, at the uncompleted child radius `childScale Z κ (n 1)`. -/
def SummedRetainedRawSides (s : Source ι a b) (ha : 0 < a) (η : Character)
    (K Z ξ κ H A loss : ℝ) (J : ℕ) : Prop :=
  ∀ p : Labels s ha 1, ∀ E ∈ inactiveSubsets p.val.1 p.val.2,
  ∀ n : Blocks (effectiveScale p.val.1 p.val.2 E K)
      (firstRadius s p.val.1 p.val.2 E K Z ξ) (H/p.val.1.absNorm) (H/p.val.2.absNorm),
    1/2 ≤ dyadicScale (n 1) →
    BalancedSummedRawSideBounds s ha η p.val.1 p.val.2
      (commonLabels_supported (activeSource (sourceColumns s) (sourceCoefficient s ha 1)) p).1
      (commonLabels_supported (activeSource (sourceColumns s) (sourceCoefficient s ha 1)) p).2 E
      (FP.MixedFirstExceptionalWindow.childScale Z κ (n 1))
      (FP.MixedFirstExceptionalWindow.childScale Z κ (n 1)) A Z loss J

theorem summed_retained_blocks (s : Source ι a b) (ha : 0 < a) (η : Character) (t : ℝ)
    (Φ : 𝓢(ℝ,ℂ)) (K Z ξ H : ℝ) (hK : 0 < K) (hsource : sourceNormCap s.P b s.T s.d ≤ H) :
    retainedEnergy η (fixedBadMask*idealGenerator s.R) 1 t (sourceColumns s)
      (sourceCoefficient s ha 1) Φ K (sourceVolume s) Z ξ =
      ∑ p : Labels s ha 1, ∑ E ∈ inactiveSubsets p.val.1 p.val.2,
        ∑ n : Blocks (effectiveScale p.val.1 p.val.2 E K) (firstRadius s p.val.1 p.val.2 E K Z ξ)
            (H/p.val.1.absNorm) (H/p.val.2.absNorm),
          blockTerm s ha η t p.val.1 p.val.2
            (commonLabels_supported (activeSource (sourceColumns s) (sourceCoefficient s ha 1)) p).1
            (commonLabels_supported (activeSource (sourceColumns s) (sourceCoefficient s ha 1)) p).2 E
            (fixedRows (firstRadius s p.val.1 p.val.2 E K Z ξ) (fun i => (n i:ℤ)))
            Φ K (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)) := by
  have he := selected_retained_fixed s ha 1 1 η t Φ K Z ξ H hK hsource
  rw [retained_selected_one] at he
  simpa only [blockTerm, block_selected_one] using he

set_option maxHeartbeats 1800000 in
/-- **Balanced Seam 0 for the first retained aggregate**: the conclusion of FP
`uniform_retained_of_raw_sides`, from the summed balanced contract; only the common band
mass is paid. -/
theorem uniform_retained_of_summed_raw_sides (Φ : 𝓢(ℝ,ℂ)) (J : ℕ)
    (B Bfrequency εmass : ℝ) (hB : 0 ≤ B) (hfreq : 0 ≤ Bfrequency) (hεmass : 0 < εmass) :
    ∃ Cret : ℝ, 0 ≤ Cret ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ s : Source ι a b, ∀ ha : 0 < a, s.d = (1,1) →
    ∀ (η : Character) (t K H ξ κ Tsecond Btail A loss : ℝ),
      0 < K → 0 < H → sourceNormCap s.P b s.T s.d ≤ H → H ≤ Z^B → 0 ≤ A →
      BandGeometry s ha 1 K Z ξ κ 1 Tsecond H Btail Bfrequency →
      SummedRetainedRawSides s ha η K Z ξ κ H A loss J →
      ‖retainedEnergy η (fixedBadMask*idealGenerator s.R) 1 t (sourceColumns s)
        (sourceCoefficient s ha 1) Φ K (sourceVolume s) Z ξ‖/sourceVolume s ≤
      Cret*(4/a^2)*fixedPresentationCost*((η.modulus.absNorm:ℝ)*K)*(windowMass J t)^2*A*
        Z^(loss+εmass) := by
  obtain ⟨Ckernel, hCkernel, hblock⟩ := block_of_summed_raw_sides (ι := ι) (a := a) (b := b) Φ J
  obtain ⟨Cmass, hCmass, hmass⟩ := uniform_common_band_mass.{u} B Bfrequency 1 εmass
    hB hfreq (by norm_num) hεmass
  refine ⟨256*Ckernel*Cmass, by positivity, ?_⟩
  filter_upwards [hmass] with Z hm
  have hZ : 1 < Z := by linarith [hm.1]
  have hz := zero_lt_one.trans hZ
  refine ⟨hZ, ?_⟩
  intro s ha hunit η t K H ξ κ Tsecond Btail A loss hK hH hsource hHcap hA hgeometry hsides
  let radius := fun (p : Labels s ha 1) (E : Finset (CommonIndex p.val.1 p.val.2)) =>
    firstRadius s p.val.1 p.val.2 E K Z ξ
  let Front := 256*Ckernel*(4/a^2)*fixedPresentationCost*((η.modulus.absNorm:ℝ)*K)*
    (windowMass J t)^2*A*Z^loss
  have hFront : 0 ≤ Front := by
    have hf := fixedPresentationCost_pos
    dsimp only [Front]
    positivity
  have hmassActual := hm.2 ι a b s ha 1 (by simp) one_ne_zero K H hK hH hsource hHcap
    radius (fun p E => by simpa only [one_mul] using hgeometry.radius p E)
  simp only [map_one, Nat.cast_one, div_one] at hmassActual
  let term := fun (p : Labels s ha 1) (E : Finset (CommonIndex p.val.1 p.val.2))
      (n : Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
        (H/p.val.1.absNorm) (H/p.val.2.absNorm)) =>
    blockTerm s ha η t p.val.1 p.val.2
      (commonLabels_supported (activeSource (sourceColumns s) (sourceCoefficient s ha 1)) p).1
      (commonLabels_supported (activeSource (sourceColumns s) (sourceCoefficient s ha 1)) p).2 E
      (fixedRows (radius p E) (fun i => (n i:ℤ))) Φ K
      (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3))
  have hpoint (p : Labels s ha 1) (E : Finset (CommonIndex p.val.1 p.val.2))
      (hE : E ∈ inactiveSubsets p.val.1 p.val.2)
      (n : Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
        (H/p.val.1.absNorm) (H/p.val.2.absNorm)) :
      ‖term p E n‖/sourceVolume s ≤ Front*commonWeight p.val.1 p.val.2 E := by
    have hw := common_weight_nonneg p.val.1 p.val.2 E
    by_cases hdy : 1/2 ≤ dyadicScale (n 1)
    swap
    · have hempty := fixedRows_eq_empty (radius p E) (fun i => (n i:ℤ)) (not_le.mp hdy)
      have h0 : term p E n = 0 := by
        dsimp only [term]
        rw [hempty]
        simp [blockTerm, CenteredMomentFirstPhysicalSource.block]
      rw [h0, norm_zero, zero_div]
      exact mul_nonneg hFront hw
    have hp := commonLabels_supported (activeSource (sourceColumns s) (sourceCoefficient s ha 1)) p
    have hCD := (commonLabels_data _ _ p.val.1 p.val.2 p.property).2.2
    obtain ⟨_, _, hrows⟩ := hgeometry.children p E hE n hdy
    have hKc : 0 < FP.MixedFirstExceptionalWindow.childScale Z κ (n 1) := by
      unfold FP.MixedFirstExceptionalWindow.childScale
      exact Real.rpow_pos_of_pos hz _
    have hrowsK : ∀ z ∈ fixedRows (radius p E) (fun i => (n i:ℤ)),
        ‖eisEmbedding z‖^2 ≤ FP.MixedFirstExceptionalWindow.childScale Z κ (n 1) :=
      fun z hz' => by
        simpa only [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span] using hrows z hz'
    exact hblock s ha hunit η t p.val.1 p.val.2 hp.1 hp.2 hCD E
      (fixedRows (radius p E) (fun i => (n i:ℤ))) (fixedRows_nonzero _ _)
      K (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3))
      (FP.MixedFirstExceptionalWindow.childScale Z κ (n 1))
      (FP.MixedFirstExceptionalWindow.childScale Z κ (n 1))
      Z A loss hK (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _)
      hKc hKc hZ hA hrowsK hrowsK (hsides p E hE n hdy)
  have htriangle :
      ‖∑ p : Labels s ha 1, ∑ E ∈ inactiveSubsets p.val.1 p.val.2, ∑ n, term p E n‖ ≤
        ∑ p : Labels s ha 1, ∑ E ∈ inactiveSubsets p.val.1 p.val.2, ∑ n, ‖term p E n‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro p _
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro E _
    exact norm_sum_le _ _
  rw [summed_retained_blocks s ha η t Φ K Z ξ H hK hsource]
  change ‖∑ p : Labels s ha 1, ∑ E ∈ inactiveSubsets p.val.1 p.val.2, ∑ n, term p E n‖/
    sourceVolume s ≤ _
  calc
    _ ≤ (∑ p : Labels s ha 1, ∑ E ∈ inactiveSubsets p.val.1 p.val.2, ∑ n, ‖term p E n‖)/
        sourceVolume s :=
      div_le_div_of_nonneg_right htriangle (sourceVolume_pos s).le
    _ = ∑ p : Labels s ha 1, ∑ E ∈ inactiveSubsets p.val.1 p.val.2, ∑ n,
        ‖term p E n‖/sourceVolume s := by
      simp only [Finset.sum_div]
    _ ≤ ∑ p : Labels s ha 1, ∑ E ∈ inactiveSubsets p.val.1 p.val.2,
        ∑ _n : Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
            (H/p.val.1.absNorm) (H/p.val.2.absNorm),
          Front*commonWeight p.val.1 p.val.2 E :=
      Finset.sum_le_sum (fun p _ => Finset.sum_le_sum (fun E hE =>
        Finset.sum_le_sum (fun n _ => hpoint p E hE n)))
    _ = Front*bandMass s ha 1 K H radius := by
      simp only [bandMass, Finset.mul_sum]
    _ ≤ Front*(Cmass*Z^εmass) := mul_le_mul_of_nonneg_left hmassActual hFront
    _ = _ := by
      dsimp only [Front]
      rw [Real.rpow_add hz]
      ring

end
end Qrh.MarkedAnchor.Ordinary.First
