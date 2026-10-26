/- Copyright (c) 2026 Sil. Apache-2.0.
The actual common-label, inactive-subset and first dyadic-band mass.
The coefficient is the literal restricted source, possibly avoidSource;
the source is fixed before any selected-product averaging. No energy
bound is assumed. Only full norm, source-volume and cutoff caps enter.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedInnerExceptionalLedger
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstInactiveRadicalMass
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalDyadicCount
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.MobiusHarmonicMass

set_option autoImplicit false
namespace Candidate.FourthPower.MixedFirstCommonSum
universe u
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentSupportedCorrelation CenteredMomentActiveSource
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate CenteredMomentFirstDiscardedEnergy
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentFirstPhysicalDyadicCount
open CenteredMomentFirstInactiveRadicalMass CenteredMomentRankinRadical
open MixedPrincipalPair MixedPrincipalWindow MixedOriginalNormCap MixedOriginalTail
open MixedInnerExceptionalLedger
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

abbrev Labels (s : Source ι a b) (ha : 0<a) (seed : Id) :=
  ActiveLabel (sourceColumns s) (sourceCoefficient s ha seed)

/-- Precisely the common weight left by the first physical reference
normalization. The inactive Möbius factor has exponent zero here. -/
def commonWeight (C D : Id) (E : Finset (CommonIndex C D)) : ℝ :=
  CenteredMomentFirstInactiveRadicalMass.inactiveWeight C D E 0 /
    (Ideal.absNorm (commonRadical C D):ℝ)

theorem common_weight_nonneg (C D : Id) (E : Finset (CommonIndex C D)) :
    0≤commonWeight C D E :=
  div_nonneg (inactiveWeight_nonneg C D E 0) (Nat.cast_nonneg _)

theorem common_weight_physical (C D : Id) (E : Finset (CommonIndex C D)) :
    commonWeight C D E=
      ‖CenteredMomentFirstPhysicalSource.inactiveWeight C D E‖ /
        (Ideal.absNorm (commonRadical C D):ℝ) := by
  simp only [commonWeight,CenteredMomentFirstInactiveRadicalMass.inactiveWeight,
    Real.rpow_zero,div_one,CenteredMomentFirstPhysicalSource.inactiveWeight]

def bandMass (s : Source ι a b) (ha : 0<a) (seed : Id) (K H : ℝ)
    (radius : (p : Labels s ha seed)→Finset (CommonIndex p.val.1 p.val.2)→ℝ) : ℝ :=
  ∑p : Labels s ha seed,∑E∈inactiveSubsets p.val.1 p.val.2,
    ∑_n : Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
      (H/p.val.1.absNorm) (H/p.val.2.absNorm),
      commonWeight p.val.1 p.val.2 E

/-- Sum the actual common labels, inactive subsets and all retained
physical bands together. Both subpower thresholds precede the source,
profiles, slot type, seed and every common label. The original seed
norm remains in the denominator exactly once. -/
theorem uniform_common_band_mass (B L Cr ε : ℝ)
    (hB : 0≤B) (hL : 0≤L) (hCr : 0<Cr) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,2≤Z ∧
      ∀(ι : Type u) [Fintype ι],∀a b : ℝ,∀s : Source ι a b,∀ha : 0<a,
      ∀seed : Id,Squarefree seed→seed≠0→∀K H : ℝ,0<K→0<H→
      sourceNormCap s.P b s.T s.d≤H→H≤Z^B→
      ∀radius : (p : Labels s ha seed)→Finset (CommonIndex p.val.1 p.val.2)→ℝ,
      (∀p E,radius p E≤Cr*Z^L)→
      bandMass s ha seed K H radius≤C*Z^ε/(seed.absNorm:ℝ) := by
  obtain ⟨Cd,hCd,hd⟩ := original_blocks_subpower B L Cr (ε/2) hB hL hCr (by linarith)
  obtain ⟨Cm,hCm,hm⟩ := actual_inactive_radical_mass B (ε/2) hB (by linarith)
  refine ⟨Cd*Cm,mul_pos hCd hCm,?_⟩
  filter_upwards [hd,eventually_ge_atTop (2:ℝ)] with Z hd hZ
  refine ⟨hZ,?_⟩
  intro ι instι a b s ha seed hseed hseed0 K H hK hH hsource hHcap radius hradius
  have hZ0 : 0<Z := by linarith
  have hmass := hm Z hZ seed hseed hseed0 (sourceColumns s) (sourceCoefficient s ha seed)
    (fun I _ hI=>source_coefficient_seed s ha seed I hI)
    (fun I _ hI=>((original_coefficient_cap s ha seed I hI).2.trans hsource).trans hHcap)
    0 le_rfl
  have hblocks (p : Labels s ha seed) (E : Finset (CommonIndex p.val.1 p.val.2)) :
      (∑_n : Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
        (H/p.val.1.absNorm) (H/p.val.2.absNorm),commonWeight p.val.1 p.val.2 E)≤
        (Cd*Z^(ε/2))*commonWeight p.val.1 p.val.2 E := by
    have hs := commonLabels_supported (activeSource (sourceColumns s) (sourceCoefficient s ha seed))
      _ _ p.property
    have hc := hd p.val.1 p.val.2 hs.1.1 hs.2.1 E K (radius p E) H
      hK hH (hradius p E) hHcap
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
      mul_le_mul_of_nonneg_right hc (common_weight_nonneg p.val.1 p.val.2 E)
  calc
    bandMass s ha seed K H radius≤
        ∑p : Labels s ha seed,∑E∈inactiveSubsets p.val.1 p.val.2,
          (Cd*Z^(ε/2))*commonWeight p.val.1 p.val.2 E := by
      apply Finset.sum_le_sum
      intro p hp
      exact Finset.sum_le_sum (fun E _=>hblocks p E)
    _=(Cd*Z^(ε/2))*(∑p : Labels s ha seed,∑E∈inactiveSubsets p.val.1 p.val.2,
        commonWeight p.val.1 p.val.2 E) := by simp only [Finset.mul_sum]
    _≤(Cd*Z^(ε/2))*(Cm*Z^(ε/2)/(seed.absNorm:ℝ)) :=
      mul_le_mul_of_nonneg_left hmass (mul_nonneg hCd.le (Real.rpow_nonneg hZ0.le _))
    _=(Cd*Cm)*Z^ε/(seed.absNorm:ℝ) := by
      have he : Z^(ε/2)*Z^(ε/2)=Z^ε := by
        rw [←Real.rpow_add hZ0]
        congr 1
        ring
      calc
        _=(Cd*Cm)*(Z^(ε/2)*Z^(ε/2))/(seed.absNorm:ℝ) := by ring
        _=_ := by rw [he]

/-- The artificial projector can vary with the genuine common and
inactive labels. Its whole finite pool is paid once through the exact
Möbius harmonic weight; it is not counted by its cardinality. -/
theorem uniform_common_artificial_band_mass (B L BA Cr ε : ℝ)
    (hB : 0≤B) (hL : 0≤L) (hBA : 0≤BA) (hCr : 0<Cr) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,2≤Z ∧
      ∀(ι : Type u) [Fintype ι],∀a b : ℝ,∀s : Source ι a b,∀ha : 0<a,
      ∀seed : Id,Squarefree seed→seed≠0→∀K H : ℝ,0<K→0<H→
      sourceNormCap s.P b s.T s.d≤H→H≤Z^B→
      ∀radius : (p : Labels s ha seed)→Finset (CommonIndex p.val.1 p.val.2)→ℝ,
      (∀p E,radius p E≤Cr*Z^L)→
      ∀Ds : (p : Labels s ha seed)→Finset (CommonIndex p.val.1 p.val.2)→Finset Id,
      (∀p E,∀D∈Ds p E,(UniqueFactorizationMonoid.moebius D:ℂ)≠0→(D.absNorm:ℝ)≤Z^BA)→
      (∑p : Labels s ha seed,∑E∈inactiveSubsets p.val.1 p.val.2,
        ∑_n : Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
          (H/p.val.1.absNorm) (H/p.val.2.absNorm),
        ∑D∈Ds p E,commonWeight p.val.1 p.val.2 E*
          (‖(UniqueFactorizationMonoid.moebius D:ℂ)‖/(D.absNorm:ℝ)))≤
        C*Z^ε/(seed.absNorm:ℝ) := by
  obtain ⟨Cc,hCc,hcommon⟩ := uniform_common_band_mass B L Cr (ε/2) hB hL hCr (by linarith)
  obtain ⟨Ca,hCa,hart⟩ := CenteredMomentMobiusHarmonicMass.full_mass_subpower BA (ε/2) hBA (by linarith)
  refine ⟨Ca*Cc,mul_pos hCa hCc,?_⟩
  filter_upwards [hcommon,hart] with Z hcommon hart
  refine ⟨hcommon.1,?_⟩
  intro ι instι a b s ha seed hs hs0 K H hK hH hsource hHcap radius hradius Ds hDs
  have hZ : 0<Z := by linarith [hcommon.1]
  have hb := hcommon.2 ι a b s ha seed hs hs0 K H hK hH hsource hHcap radius hradius
  have hpoint (p : Labels s ha seed) (E : Finset (CommonIndex p.val.1 p.val.2)) :
      (∑D∈Ds p E,commonWeight p.val.1 p.val.2 E*
        (‖(UniqueFactorizationMonoid.moebius D:ℂ)‖/(D.absNorm:ℝ)))≤
          (Ca*Z^(ε/2))*commonWeight p.val.1 p.val.2 E := by
    rw [←Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left (hart.2 (Ds p E) (hDs p E))
      (common_weight_nonneg p.val.1 p.val.2 E)).trans_eq (mul_comm _ _)
  calc
    _≤∑p : Labels s ha seed,∑E∈inactiveSubsets p.val.1 p.val.2,
        ∑_n : Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
          (H/p.val.1.absNorm) (H/p.val.2.absNorm),
          (Ca*Z^(ε/2))*commonWeight p.val.1 p.val.2 E := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro E hE
      exact Finset.sum_le_sum (fun n _=>hpoint p E)
    _=(Ca*Z^(ε/2))*bandMass s ha seed K H radius := by
      simp only [bandMass,Finset.mul_sum]
    _≤(Ca*Z^(ε/2))*(Cc*Z^(ε/2)/(seed.absNorm:ℝ)) :=
      mul_le_mul_of_nonneg_left hb (mul_nonneg hCa.le (Real.rpow_nonneg hZ.le _))
    _=(Ca*Cc)*Z^ε/(seed.absNorm:ℝ) := by
      have he : Z^(ε/2)*Z^(ε/2)=Z^ε := by
        rw [←Real.rpow_add hZ]
        congr 1
        ring
      calc
        _=(Ca*Cc)*(Z^(ε/2)*Z^(ε/2))/(seed.absNorm:ℝ) := by ring
        _=_ := by rw [he]

end
end Candidate.FourthPower.MixedFirstCommonSum
