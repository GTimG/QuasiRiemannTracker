/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Common-band mass on actual colored support. -/
import Candidate.C092.transport.TwistedRawBallPhysical
import Candidate.C092.transport.TwistedRawSourceZero
import Submissions.sil_density_split_20261026.CubeFree.FP.MixedFirstCommonSum
set_option autoImplicit false
namespace QRH.Cycle092.TwistedRawBall
universe u
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentSupportedCorrelation CenteredMomentActiveSource
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate CenteredMomentFirstDiscardedEnergy
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentFirstPhysicalDyadicCount
open CenteredMomentFirstInactiveRadicalMass CenteredMomentRankinRadical
open QRH.SilDensitySplit.CubeFree.FP
open MixedFirstCommonSum
open QRH.Cycle092.TwistedRawSource
open MixedPrincipalPair MixedPrincipalWindow MixedOriginalNormCap MixedOriginalTail
open MixedInnerExceptionalLedger
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

abbrev Labels (s : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Id → ℂ) (seed : Id) :=
  ActiveLabel (sourceColumns s) (sourceColumn s ha ω₁ ω₂ seed)

def bandMass (s : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Id → ℂ) (seed : Id) (K H : ℝ)
    (radius : (p : Labels s ha ω₁ ω₂ seed)→Finset (CommonIndex p.val.1 p.val.2)→ℝ) : ℝ :=
  ∑p : Labels s ha ω₁ ω₂ seed,∑E∈inactiveSubsets p.val.1 p.val.2,
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
      ∀(ι : Type u) [Fintype ι],∀a b : ℝ,∀s : Source ι a b,∀ha : 0<a, ∀ω₁ ω₂ : Id → ℂ,
      ∀seed : Id,Squarefree seed→seed≠0→∀K H : ℝ,0<K→0<H→
      sourceNormCap s.P b s.T s.d≤H→H≤Z^B→
      ∀radius : (p : Labels s ha ω₁ ω₂ seed)→Finset (CommonIndex p.val.1 p.val.2)→ℝ,
      (∀p E,radius p E≤Cr*Z^L)→
      bandMass s ha ω₁ ω₂ seed K H radius≤C*Z^ε/(seed.absNorm:ℝ) := by
  obtain ⟨Cd,hCd,hd⟩ := original_blocks_subpower B L Cr (ε/2) hB hL hCr (by linarith)
  obtain ⟨Cm,hCm,hm⟩ := actual_inactive_radical_mass B (ε/2) hB (by linarith)
  refine ⟨Cd*Cm,mul_pos hCd hCm,?_⟩
  filter_upwards [hd,eventually_ge_atTop (2:ℝ)] with Z hd hZ
  refine ⟨hZ,?_⟩
  intro ι instι a b s ha ω₁ ω₂ seed hseed hseed0 K H hK hH hsource hHcap radius hradius
  have hZ0 : 0<Z := by linarith
  have hmass := hm Z hZ seed hseed hseed0 (sourceColumns s) (sourceColumn s ha ω₁ ω₂ seed)
    (fun I _ hI=>(source_nonzero_masks s ha ω₁ ω₂ seed I hI).2)
    (fun I _ hI=>((sourceColumn_cap s ha ω₁ ω₂ seed I hI).2.trans hsource).trans hHcap)
    0 le_rfl
  have hblocks (p : Labels s ha ω₁ ω₂ seed) (E : Finset (CommonIndex p.val.1 p.val.2)) :
      (∑_n : Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
        (H/p.val.1.absNorm) (H/p.val.2.absNorm),commonWeight p.val.1 p.val.2 E)≤
        (Cd*Z^(ε/2))*commonWeight p.val.1 p.val.2 E := by
    have hs := commonLabels_supported (activeSource (sourceColumns s) (sourceColumn s ha ω₁ ω₂ seed))
      _ _ p.property
    have hc := hd p.val.1 p.val.2 hs.1.1 hs.2.1 E K (radius p E) H
      hK hH (hradius p E) hHcap
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
      mul_le_mul_of_nonneg_right hc (common_weight_nonneg p.val.1 p.val.2 E)
  calc
    bandMass s ha ω₁ ω₂ seed K H radius≤
        ∑p : Labels s ha ω₁ ω₂ seed,∑E∈inactiveSubsets p.val.1 p.val.2,
          (Cd*Z^(ε/2))*commonWeight p.val.1 p.val.2 E := by
      apply Finset.sum_le_sum
      intro p hp
      exact Finset.sum_le_sum (fun E _=>hblocks p E)
    _=(Cd*Z^(ε/2))*(∑p : Labels s ha ω₁ ω₂ seed,∑E∈inactiveSubsets p.val.1 p.val.2,
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


#print axioms uniform_common_band_mass
end
end QRH.Cycle092.TwistedRawBall
