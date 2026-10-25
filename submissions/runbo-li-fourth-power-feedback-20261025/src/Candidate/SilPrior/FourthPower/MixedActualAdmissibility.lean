/- Copyright (c) 2026 Sil. Apache-2.0.
fixed canonical admissibility from actual common support and
explicit polynomial caps. Eta remains AFTER the uniform threshold, so
its modulus cap is an explicit premise. No analytic ledger is assumed.
-/
import Candidate.SilPrior.FourthPower.MixedActualFamily
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonHarmonicMass

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.MixedActualAdmissibility
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentRankinRadical CenteredMomentCommonHarmonicMass
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondChildRadialWidth
open CenteredMomentSecondLiveBlock CenteredMomentSectorLocalization
open CenteredMomentSecondRadicalBudget CenteredMomentSecondBlockAggregate
open CenteredMomentSecondRetainedAggregate
open CenteredMomentActiveSource CenteredMomentFirstSectors
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-- A literal common-index subset is a divisor of the common radical.
This does not bound arbitrary prime powers by their radicals. -/
theorem common_subset_divisor (C D : Id) (U : Finset (CommonIndex C D)) :
    (∏P∈U,P.val)∣commonRadical C D := by
  have hfull : (∏P : CommonIndex C D,P.val)=commonRadical C D := by
    exact Finset.prod_coe_sort (s:=commonSupport C D) (f:=fun P=>P)
  rw [←hfull]
  exact Finset.prod_dvd_prod_of_subset U Finset.univ (fun P=>P.val) (Finset.subset_univ _)

theorem common_subset_norm (C D : Id) (hC : C≠0) (hD : D≠0)
    (U : Finset (CommonIndex C D)) :
    0<((∏P∈U,P.val).absNorm:ℝ) ∧
      ((∏P∈U,P.val).absNorm:ℝ)≤min (C.absNorm:ℝ) D.absNorm := by
  have hdvd := common_subset_divisor C D U
  have hzero : (∏P∈U,P.val)≠0 := ne_zero_of_dvd_ne_zero (commonRadical_ne_zero C D) hdvd
  constructor
  · exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hzero)
  · apply le_trans _ (commonRadical_norm_le C D hC hD)
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (commonRadical_ne_zero C D)))
      (map_dvd Ideal.absNorm hdvd)

/-- A nonzero physical block supplies a positive actual retained radius. -/
theorem actual_nonzero_radius_pos (η : Character) (t : ℝ) (S : Finset Id) (β : Id→ℂ)
    (C D : Id) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (radius : ℝ) (rows : Finset O)
    (Ψ : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4→ℤ)
    (hne : physicalBlock η t S β C D hC hD U radius rows Ψ K n≠0) : 0<radius := by
  obtain ⟨z,hz,_hzd,_hz0,_hscale⟩ :=
    physicalBlock_live_dyadic_witness η t S β C D hC hD U radius rows Ψ K n hne
  exact (liveRows_geometry C D U radius rows z hz).1

/-- The exact ledger used by actual_canonical_geometry has a uniform
fixed cap. The negative common-generator log is discarded only after
proving that this actual integral generator is nonzero. -/
theorem actual_ledger_cap (Z L Meta B Cr ζ radius Hsource : ℝ)
    (hZ : 1<Z) (hCr : 0<Cr) (hradius : 0<radius)
    (hconstant : 16*(fixedFactor:ℝ)*Cr≤Z^ζ)
    (η : Character) (hη : (η.modulus.absNorm:ℝ)≤Z^Meta)
    (S : Finset Id) (β : Id→ℂ)
    (hcolumns : ∀I∈S,β I≠0→(I.absNorm:ℝ)≤Hsource)
    (hsource : Hsource≤Z^B) (hrad : radius≤Cr*Z^L)
    (p : ActiveLabel S β) (U : Finset (CommonIndex p.val.1 p.val.2)) :
    Real.logb Z radius+Real.logb Z (η.modulus.absNorm:ℝ)-
      Real.logb Z (normValue (commonFrequencyGenerator p.val.1 p.val.2))+
      Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (16*(fixedFactor:ℝ))≤
      L+Meta+B+ζ := by
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hs := commonLabels_supported (activeSource S β) _ _ p.property
  have hn := commonLabel_norm_bounds S β Hsource hcolumns p.val.1 p.val.2 p.property
  have hU := common_subset_norm p.val.1 p.val.2 hs.1.1 hs.2.1 U
  have hUN : ((∏P∈U,P.val).absNorm:ℝ)≤Z^B :=
    hU.2.trans ((min_le_left _ _).trans (hn.1.trans hsource))
  have hUlog : Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)≤B := by
    have hh := Real.logb_le_logb_of_le hZ hU.1 hUN
    simpa only [Real.logb_rpow hZ0 hZ.ne'] using hh
  have hηpos : 0<(η.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)
  have hηlog : Real.logb Z (η.modulus.absNorm:ℝ)≤Meta := by
    have hh := Real.logb_le_logb_of_le hZ hηpos hη
    simpa only [Real.logb_rpow hZ0 hZ.ne'] using hh
  have hrlog : Real.logb Z radius≤Real.logb Z Cr+L := by
    have hh := Real.logb_le_logb_of_le hZ hradius hrad
    simpa only [Real.logb_mul hCr.ne' (Real.rpow_pos_of_pos hZ0 L).ne',
      Real.logb_rpow hZ0 hZ.ne'] using hh
  have hGlog : 0≤Real.logb Z (normValue (commonFrequencyGenerator p.val.1 p.val.2)) :=
    Real.logb_nonneg hZ (normValue_ge_one _
      (commonFrequencyGenerator_ne_zero p.val.1 p.val.2 hs.1))
  have hF : (0:ℝ)<fixedFactor := by exact_mod_cast fixedFactor_pos
  have hclog : Real.logb Z (16*(fixedFactor:ℝ))+Real.logb Z Cr≤ζ := by
    have hh := Real.logb_le_logb_of_le hZ (by positivity : 0<16*(fixedFactor:ℝ)*Cr) hconstant
    simpa only [Real.logb_mul (by positivity : 16*(fixedFactor:ℝ)≠0) hCr.ne',
      Real.logb_rpow hZ0 hZ.ne'] using hh
  linarith

/-- Positive slack absorbs the fixed conductor/radius constant before
all eta, source and label parameters. Taking rho=L+Meta+B+zeta is enough. -/
theorem uniform_actual_admissibility (L Meta B Cr ζ Mcap : ℝ)
    (hCr : 0<Cr) (hζ : 0<ζ) (hMcap : L+Meta+B+ζ≤Mcap) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(η : Character)(S : Finset Id)(β : Id→ℂ)(Hsource : ℝ),
      (η.modulus.absNorm:ℝ)≤Z^Meta →
      (∀I∈S,β I≠0→(I.absNorm:ℝ)≤Hsource) → Hsource≤Z^B →
    ∀(p : ActiveLabel S β)(U : Finset (CommonIndex p.val.1 p.val.2))(radius : ℝ),
      0<radius → radius≤Cr*Z^L →
      Real.logb Z radius+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator p.val.1 p.val.2))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (16*(fixedFactor:ℝ))≤
          L+Meta+B+ζ ∧ L+Meta+B+ζ≤Mcap := by
  have hc : ∀ᶠZ : ℝ in atTop,16*(fixedFactor:ℝ)*Cr≤Z^ζ :=
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hζ)) (16*(fixedFactor:ℝ)*Cr)
  filter_upwards [hc,Filter.eventually_gt_atTop (1:ℝ)] with Z hconstant hZ
  refine ⟨hZ,?_⟩
  intro η S β Hsource hη hcolumns hsource p U radius hradius hrad
  exact ⟨actual_ledger_cap Z L Meta B Cr ζ radius Hsource hZ hCr hradius hconstant
    η hη S β hcolumns hsource hrad p U,hMcap⟩

end
end Candidate.SilPrior.FourthPower.MixedActualAdmissibility
