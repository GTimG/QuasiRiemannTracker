/- Copyright (c) 2026 Sil. Apache-2.0.
Actual first common/unit/dyadic/Möbius closure, conditional only on the
EXPLICIT raw-side supply and explicit numerical first-band geometry.
The numerical geometry is discharged by the separate actual adapter.
-/
import Candidate.FourthPower.RepairedFirstRawBlock
import Candidate.FourthPower.MixedFirstActualBandGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RepairedFirstRawRetained
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcreteTraceCRT ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst CenteredMomentSourceMass
open CenteredMomentActiveSource CenteredMomentSourceRow CenteredMomentSecondHeightFamily
open CenteredMomentFirstDiscardedEnergy CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentFirstMixedRightTransport
open CenteredMomentFirstSectorLocalization CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentSecondWindowBudget
open MixedPrincipalPair MixedPrincipalWindow MixedOriginalNormCap MixedOriginalTail
open MixedFirstPhysicalApplication MixedFirstPhysicalBudget MixedFirstCommonSum
open MixedFirstRetainedFixed MixedFirstPaidRetained MixedFirstActualBandGeometry
open MixedFirstExceptionalNormalization MixedFirstCutoffs
open RepairedFirstRawSides RepairedFirstRawScalar RepairedFirstRawBlock
open MixedInnerExceptionalBlock CenteredMomentFirstSectors CenteredMomentFirstSectorTransform
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- Exact analytic contract to be delivered by Raw/Small: both original
raw sides for every ACTUAL first retained band and its actual ideals.
No alternate source, unallocated energy, or common radius is substituted. -/
def RetainedRawSides (s : Source ι a b) (ha : 0 < a) (η : Character)
    (K Z ξ κ H A loss : ℝ) (J : ℕ) : Prop :=
  ∀ p : Labels s ha 1, ∀ E∈inactiveSubsets p.val.1 p.val.2,
  ∀ n : Blocks (effectiveScale p.val.1 p.val.2 E K)
      (firstRadius s p.val.1 p.val.2 E K Z ξ) (H/p.val.1.absNorm) (H/p.val.2.absNorm),
    RawSideBounds s ha η p.val.1 p.val.2
      (commonLabels_supported (activeSource (sourceColumns s) (sourceCoefficient s ha 1)) p).1
      (commonLabels_supported (activeSource (sourceColumns s) (sourceCoefficient s ha 1)) p).2 E
      (nominalChildScale p.val.1 p.val.2 E K (sourceVolume s) Z κ (n 1))
      (nominalChildScale p.val.2 p.val.1 (swapSubset p.val.1 p.val.2 E) K (sourceVolume s) Z κ (n 1))
      A Z loss J

theorem actual_retained_blocks (s : Source ι a b) (ha : 0 < a) (η : Character) (t : ℝ)
    (Φ : 𝓢(ℝ,ℂ)) (K Z ξ H : ℝ) (hK : 0 < K) (hsource : sourceNormCap s.P b s.T s.d ≤ H) :
    retainedEnergy η (fixedBadMask*idealGenerator s.R) 1 t (sourceColumns s)
      (sourceCoefficient s ha 1) Φ K (sourceVolume s) Z ξ=
      ∑p : Labels s ha 1,∑E∈inactiveSubsets p.val.1 p.val.2,
        ∑n : Blocks (effectiveScale p.val.1 p.val.2 E K) (firstRadius s p.val.1 p.val.2 E K Z ξ)
            (H/p.val.1.absNorm) (H/p.val.2.absNorm),
          blockTerm s ha η t p.val.1 p.val.2
            (commonLabels_supported (activeSource (sourceColumns s) (sourceCoefficient s ha 1)) p).1
            (commonLabels_supported (activeSource (sourceColumns s) (sourceCoefficient s ha 1)) p).2 E
            (fixedRows (firstRadius s p.val.1 p.val.2 E K Z ξ) (fun i => (n i:ℤ)))
            Φ K (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)) := by
  have he := selected_retained_fixed s ha 1 1 η t Φ K Z ξ H hK hsource
  rw [retained_selected_one] at he
  simpa only [blockTerm,block_selected_one] using he

set_option maxHeartbeats 1800000 in
/-- Actual first finite mass is discharged internally. RawSideBounds
is still an explicit supply contract. BandGeometry has only the listed
cutoff/row/norm inequalities and is supplied by the actual adapter. -/
theorem uniform_retained_of_raw_sides (Φ : 𝓢(ℝ,ℂ)) (J : ℕ)
    (B Bfrequency BA εmass : ℝ) (hB : 0 ≤ B) (hfreq : 0 ≤ Bfrequency)
    (hBA : 0 ≤ BA) (hεmass : 0 < εmass) (hb : 0 ≤ b) :
    ∃ Cret : ℝ, 0 ≤ Cret ∧ ∀ᶠZ : ℝ in atTop,1 < Z ∧
    ∀ s : Source ι a b, ∀ ha : 0 < a, s.d=(1,1) →
    ∀ (η : Character) (t K H ξ κ Tsecond Btail A loss : ℝ),
      0 < K → 0 < H → sourceNormCap s.P b s.T s.d ≤ H → H ≤ Z^B → poolCap s ≤ Z^BA → 0 ≤ A →
      BandGeometry s ha 1 K Z ξ κ 1 Tsecond H Btail Bfrequency →
      RetainedRawSides s ha η K Z ξ κ H A loss J →
      ‖retainedEnergy η (fixedBadMask*idealGenerator s.R) 1 t (sourceColumns s)
        (sourceCoefficient s ha 1) Φ K (sourceVolume s) Z ξ‖/sourceVolume s ≤
      Cret*(4/a^2)*fixedPresentationCost*((η.modulus.absNorm:ℝ)*K)*(windowMass J t)^2*A*Z^(loss+εmass) := by
  obtain ⟨Ckernel,hCkernel,hblock⟩ := block_of_raw_sides (ι:=ι) (a:=a) (b:=b) Φ J
  obtain ⟨Cmass,hCmass,hmass⟩ := uniform_common_artificial_band_mass.{u} B Bfrequency BA 1 εmass
    hB hfreq hBA (by norm_num) hεmass
  refine ⟨256*Ckernel*Cmass,by positivity,?_⟩
  filter_upwards [hmass] with Z hm
  have hZ : 1 < Z := by linarith [hm.1]
  have hz := zero_lt_one.trans hZ
  refine ⟨hZ,?_⟩
  intro s ha hunit η t K H ξ κ Tsecond Btail A loss hK hH hsource hHcap hpool hA hgeometry hsides
  let radius := fun (p : Labels s ha 1) (E : Finset (CommonIndex p.val.1 p.val.2)) =>
    firstRadius s p.val.1 p.val.2 E K Z ξ
  let divisors := fun (p : Labels s ha 1) (_E : Finset (CommonIndex p.val.1 p.val.2)) =>
    artificialDivisors s p.val.1 p.val.2
      (commonLabels_supported (activeSource (sourceColumns s) (sourceCoefficient s ha 1)) p).2.1
  let Front := 256*Ckernel*(4/a^2)*fixedPresentationCost*((η.modulus.absNorm:ℝ)*K)*(windowMass J t)^2*A*Z^loss
  have hFront : 0 ≤ Front := by
    have hf := fixedPresentationCost_pos
    dsimp only [Front]
    positivity
  have hmassActual := hm.2 ι a b s ha 1 (by simp) one_ne_zero K H hK hH hsource hHcap
    radius (fun p E => by simpa only [one_mul] using hgeometry.radius p E)
    divisors (fun p E u hu _ =>
      (artificial_norm s hb p.val.1 p.val.2
        (commonLabels_supported (activeSource (sourceColumns s) (sourceCoefficient s ha 1)) p).2.1 u hu).2.trans hpool)
  simp only [map_one,Nat.cast_one,div_one] at hmassActual
  let term := fun (p : Labels s ha 1) (E : Finset (CommonIndex p.val.1 p.val.2))
      (n : Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
        (H/p.val.1.absNorm) (H/p.val.2.absNorm)) =>
    blockTerm s ha η t p.val.1 p.val.2
      (commonLabels_supported (activeSource (sourceColumns s) (sourceCoefficient s ha 1)) p).1
      (commonLabels_supported (activeSource (sourceColumns s) (sourceCoefficient s ha 1)) p).2 E
      (fixedRows (radius p E) (fun i => (n i:ℤ))) Φ K
      (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3))
  have hpoint (p : Labels s ha 1) (E : Finset (CommonIndex p.val.1 p.val.2))
      (hE : E∈inactiveSubsets p.val.1 p.val.2)
      (n : Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
        (H/p.val.1.absNorm) (H/p.val.2.absNorm)) :
      ‖term p E n‖/sourceVolume s ≤ Front*commonWeight p.val.1 p.val.2 E*
        artificialMass s p.val.1 p.val.2
          (commonLabels_supported (activeSource (sourceColumns s) (sourceCoefficient s ha 1)) p).2.1 := by
    have hp := commonLabels_supported (activeSource (sourceColumns s) (sourceCoefficient s ha 1)) p
    have hCD := (commonLabels_data _ _ p.val.1 p.val.2 p.property).2.2
    obtain ⟨_,_,_,_,hrows⟩ := hgeometry.children p E hE n
    exact hblock s ha hunit η t p.val.1 p.val.2 hp.1 hp.2 hCD E
      (fixedRows (radius p E) (fun i => (n i:ℤ))) (fixedRows_nonzero _ _)
      K (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3))
      (nominalChildScale p.val.1 p.val.2 E K (sourceVolume s) Z κ (n 1))
      (nominalChildScale p.val.2 p.val.1 (swapSubset p.val.1 p.val.2 E) K (sourceVolume s) Z κ (n 1))
      Z A loss hK (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _)
      (Real.rpow_pos_of_pos hz _) (Real.rpow_pos_of_pos hz _) hZ hA
      (fun z hz' => by simpa only [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span] using (hrows z hz').1)
      (fun z hz' => by simpa only [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span] using (hrows z hz').2)
      (hsides p E hE n)
  have htriangle :
      ‖∑p : Labels s ha 1,∑E∈inactiveSubsets p.val.1 p.val.2,∑n,term p E n‖ ≤
        ∑p : Labels s ha 1,∑E∈inactiveSubsets p.val.1 p.val.2,∑n,‖term p E n‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro p hp
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro E hE
    exact norm_sum_le _ _
  rw [actual_retained_blocks s ha η t Φ K Z ξ H hK hsource]
  change ‖∑p : Labels s ha 1,∑E∈inactiveSubsets p.val.1 p.val.2,∑n,term p E n‖/sourceVolume s ≤ _
  calc
    _ ≤ (∑p : Labels s ha 1,∑E∈inactiveSubsets p.val.1 p.val.2,∑n,‖term p E n‖)/sourceVolume s :=
      div_le_div_of_nonneg_right htriangle (sourceVolume_pos s).le
    _ = ∑p : Labels s ha 1,∑E∈inactiveSubsets p.val.1 p.val.2,∑n,‖term p E n‖/sourceVolume s := by
      simp only [Finset.sum_div]
    _ ≤ ∑p : Labels s ha 1,∑E∈inactiveSubsets p.val.1 p.val.2,
        ∑_n : Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
            (H/p.val.1.absNorm) (H/p.val.2.absNorm),
          Front*commonWeight p.val.1 p.val.2 E*artificialMass s p.val.1 p.val.2
            (commonLabels_supported (activeSource (sourceColumns s) (sourceCoefficient s ha 1)) p).2.1 :=
      Finset.sum_le_sum (fun p _ => Finset.sum_le_sum (fun E hE =>
        Finset.sum_le_sum (fun n _ => hpoint p E hE n)))
    _ = Front*(∑p : Labels s ha 1,∑E∈inactiveSubsets p.val.1 p.val.2,
        ∑_n : Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
            (H/p.val.1.absNorm) (H/p.val.2.absNorm),
          ∑u∈divisors p E,commonWeight p.val.1 p.val.2 E*
            (‖(UniqueFactorizationMonoid.moebius u:ℂ)‖/(u.absNorm:ℝ))) := by
      simp only [artificialMass,divisors,Finset.mul_sum,mul_assoc]
    _ ≤ Front*(Cmass*Z^εmass) := mul_le_mul_of_nonneg_left hmassActual hFront
    _ = _ := by
      dsimp only [Front]
      rw [Real.rpow_add hz]
      ring

end
end Candidate.FourthPower.RepairedFirstRawRetained

