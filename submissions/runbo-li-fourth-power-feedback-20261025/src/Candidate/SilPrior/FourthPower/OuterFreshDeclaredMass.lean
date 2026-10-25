/- Copyright (c) 2026 Sil. Apache-2.0.
Exact cancellation of the moving common/unit normalizer in declaredWidth,
and the actual original-seed common/unit/dyadic harmonic mass.

-/
import Candidate.SilPrior.FourthPower.OuterFreshNonexceptionalBlock
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondBlockHarmonicMass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.OuterFreshDeclaredMass
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open QRH.Record1252270103KernelMass
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical CenteredMomentSectorLocalization
open CenteredMomentFirstSectors CenteredMomentActiveSource CenteredMomentSourceMass
open CenteredMomentFirstPhysicalSource
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondSectorColumns
open CenteredMomentSecondBlockHarmonicMass
open MixedPrincipalPair MixedPrincipalAllocations MixedSupplierFourthRow MixedSupplierSource
open MixedPrincipalWindow
open MixedFirstGeometricCaps MixedFirstChosenEnergy MixedInnerExceptionalLedger
open MixedOriginalNormCap MixedOriginalTail
open OuterFreshSource OuterFreshWindowPair OuterFreshConsumer OuterFreshSelectedWindow
open OuterFreshSelected OuterFreshCutoffAllowance OuterFreshRootAdmission
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq α := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- The common-frequency and unit-product factors in declaredWidth are
the exact inverse of the actual physical normalizer. Both cancel before
the common-label/unit-subset sum. Original source volumes are retained. -/
theorem normalizer_paid_declared_width (q:Data ι)(hP:∀i,0<q.P i)
    (η:Character)(K Z D0 c θ:ℝ)(hK:0<K)(hZ:1<Z)
    (C E:Id)(hC:Supported C)(U:Finset (CommonIndex C E)) :
    normalizer C E U*
      (Z^(declaredWidth q η K Z D0 c θ C E U)/fixedPresentationCost)=
      ((η.modulus.absNorm:ℝ)*K/(frozenVolume q*(selectedVolume q)^2))*
        Z^(D0-c-max (D0-c) 0+3*θ) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hη:0<(η.modulus.absNorm:ℝ):=zero_lt_one.trans_le (ideal_norm_one_le η.modulus_ne_bot)
  have hf:=frozenVolume_pos q hP
  have hs:0<selectedVolume q:=Finset.prod_pos (fun i _=>hP i.val.val)
  have hg:0<normValue (commonFrequencyGenerator C E):=
    normValue_pos _ (commonFrequencyGenerator_ne_zero C E hC)
  have hunitIdeal:(∏P∈U,P.val)≠(0:Id):=
    Finset.prod_ne_zero_iff.mpr (fun P _=>(commonPrime_supported_ideal C E hC P).1)
  have hu:0<((∏P∈U,P.val).absNorm:ℝ):=zero_lt_one.trans_le (ideal_norm_one_le hunitIdeal)
  let drift:=D0-c-max (D0-c) 0+3*θ
  let Rbase:=inputWidth η K Z-Real.logb Z (frozenVolume q)-
    2*Real.logb Z (selectedVolume q)+drift
  have hd:declaredWidth q η K Z D0 c θ C E U=
      Rbase-Real.logb Z (normValue (commonFrequencyGenerator C E))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ) := by
    unfold declaredWidth Rbase drift
    ring
  have hinput:Z^(inputWidth η K Z)=K*(η.modulus.absNorm:ℝ)*fixedPresentationCost := by
    unfold inputWidth
    rw [Real.rpow_add hz,Real.rpow_add hz]
    simp only [Real.rpow_logb hz hZ.ne' hK,Real.rpow_logb hz hZ.ne' hη,
      Real.rpow_logb hz hZ.ne' fixedPresentationCost_pos]
  have hselected:Z^(2*Real.logb Z (selectedVolume q))=(selectedVolume q)^2 := by
    rw [two_mul,Real.rpow_add hz]
    simp only [Real.rpow_logb hz hZ.ne' hs,pow_two]
  have hbase:Z^Rbase=
      (K*(η.modulus.absNorm:ℝ)*fixedPresentationCost/frozenVolume q/(selectedVolume q)^2)*Z^drift := by
    dsimp only [Rbase]
    rw [Real.rpow_add hz,Real.rpow_sub hz,Real.rpow_sub hz,hinput,
      Real.rpow_logb hz hZ.ne' hf,hselected]
  rw [normalizer,actual_partitionNormalizer C E hC U]
  change (normValue (commonFrequencyGenerator C E)/((∏P∈U,P.val).absNorm:ℝ))*
      (Z^(declaredWidth q η K Z D0 c θ C E U)/fixedPresentationCost)=_
  rw [hd,Real.rpow_add hz,Real.rpow_sub hz,
    Real.rpow_logb hz hZ.ne' hg,Real.rpow_logb hz hZ.ne' hu,hbase]
  dsimp only [drift]
  field_simp [hf.ne',hs.ne',hg.ne',hu.ne',fixedPresentationCost_pos.ne']
  <;> ring

theorem normalizer_paid_declared_upper (q:Data ι)(hP:∀i,0<q.P i)
    (η:Character)(K Z D0 c θ:ℝ)(hK:0<K)(hZ:1<Z)
    (C E:Id)(hC:Supported C)(U:Finset (CommonIndex C E)) :
    normalizer C E U*(Z^(declaredWidth q η K Z D0 c θ C E U)/fixedPresentationCost)≤
      ((η.modulus.absNorm:ℝ)*K/(frozenVolume q*(selectedVolume q)^2))*Z^(3*θ) := by
  rw [normalizer_paid_declared_width q hP η K Z D0 c θ hK hZ C E hC U]
  have hfactor:0≤(η.modulus.absNorm:ℝ)*K/(frozenVolume q*(selectedVolume q)^2):=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) hK.le)
      (mul_nonneg (frozenVolume_pos q hP).le (sq_nonneg _))
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith [le_max_left (D0-c) 0])) hfactor

/-- Every actual nonzero block has non-subunit residual column annuli.
The proof is coefficientwise: below one, the corresponding dyadic weight
is zero on every supported nonzero sector ideal. -/
theorem nonzero_column_scales (τ:Character)(t:ℝ)(S:Finset Id)(β:Id→ℂ)
    (C E:Id)(hC:Supported C)(hE:Supported E)(U:Finset (CommonIndex C E))
    (R:ℝ)(rows:Finset O)(Φ:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ)
    (hne:physicalBlock τ t S β C E hC hE U R rows Φ K n≠0) :
    1<dyadicScale (n 2) ∧ 1<dyadicScale (n 3) := by
  constructor
  · by_contra hn
    have hscale:dyadicScale (n 2)≤1:=le_of_not_gt hn
    have hzero (I:sectorPool C hC.1 S):dyadicWeight (n 2) (I.val.absNorm:ℝ)=0:=
      dyadicWeight_zero_high _ _ (hscale.trans (ideal_norm_one_le (sectorPool_supported C hC.1 S I).1))
    apply hne
    simp only [physicalBlock,hzero,mul_zero,zero_mul,Complex.ofReal_zero,
      Finset.sum_const_zero,ite_self]
  · by_contra hn
    have hscale:dyadicScale (n 3)≤1:=le_of_not_gt hn
    have hzero (I:sectorPool E hE.1 S):dyadicWeight (n 3) (I.val.absNorm:ℝ)=0:=
      dyadicWeight_zero_high _ _ (hscale.trans (ideal_norm_one_le (sectorPool_supported E hE.1 S I).1))
    apply hne
    simp only [physicalBlock,hzero,mul_zero,zero_mul,Complex.ofReal_zero,
      Finset.sum_const_zero,ite_self]

/-- After the exact normalizer cancellation, the remaining common and
column denominators dominate the checked harmonic pairWeight. No common
ideal norm is lost before this justified positive scalar comparison. -/
theorem pair_denominator_le (C E:Id)(hC:C≠0)(hE:E≠0)
    (X Y:ℝ)(hX:1≤X)(hY:1≤Y) :
    1/(((C.absNorm:ℝ)*E.absNorm)*Real.sqrt X*Real.sqrt Y)≤pairWeight C E := by
  have hC1:=ideal_norm_one_le hC
  have hE1:=ideal_norm_one_le hE
  have hCE:1≤(C.absNorm:ℝ)*E.absNorm:=one_le_mul_of_one_le_of_one_le hC1 hE1
  have hCE0:0<(C.absNorm:ℝ)*E.absNorm:=zero_lt_one.trans_le hCE
  have hsX:1≤Real.sqrt X:=by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hX
  have hsY:1≤Real.sqrt Y:=by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hY
  have hs:Real.sqrt ((C.absNorm:ℝ)*E.absNorm)≤(C.absNorm:ℝ)*E.absNorm := by
    have hh:=Real.sqrt_le_sqrt (le_mul_of_one_le_right hCE0.le hCE)
    simpa only [←pow_two,Real.sqrt_sq_eq_abs,abs_of_pos hCE0] using hh
  have hden:Real.sqrt ((C.absNorm:ℝ)*E.absNorm)≤
      ((C.absNorm:ℝ)*E.absNorm)*Real.sqrt X*Real.sqrt Y :=
    hs.trans ((le_mul_of_one_le_right hCE0.le hsX).trans
      (le_mul_of_one_le_right (mul_nonneg hCE0.le (Real.sqrt_nonneg _)) hsY))
  exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hCE0) hden

/-- Actual common labels, unit subsets, and their finite dyadic blocks,
on the fixed original supplier support. The original squarefree seed is
proved to divide every active column before the generic mass lemma is used.
This is a scalar mass theorem, not a premise about physical energies. -/
theorem uniform_fixed_common_block_mass (B Lrad Cr ε:ℝ)
    (hB:0≤B)(hL:0≤Lrad)(hCr:0<Cr)(hε:0<ε) :
    ∃Cmass:ℝ,0<Cmass ∧ ∀ᶠZ:ℝ in atTop,
      ∀(ι:Type u)[Fintype ι],∀a b:ℝ,∀s:Source ι a b,∀ha:0<a,
      ∀cover:OriginalEnclosure s,∀u:Id,∀L:Finset ι,∀J:Finset {i//i∉Lᶜ},
      let q:=supplierData s ha u L J
      ∀x:Frozen q,∀seed:Id,Squarefree seed→
      sourceNormCap s.P b s.T s.d≤Z^B→
      ∀K R H:ℝ,0<K→R≤Cr*Z^Lrad→H≤Z^B→
      (∑p:FixedLabel (fixedPool q x (residualSource s ha cover u L J x) seed),
        ∑U:Finset (CommonIndex p.val.1 p.val.2),
        ∑_n:SourceBlocks p.val.1 p.val.2 U K R H,pairWeight p.val.1 p.val.2)≤
        Cmass*Z^ε/(seed.absNorm:ℝ) := by
  obtain ⟨Cmass,hCmass,hmass⟩:=actual_block_harmonic_mass B Lrad Cr ε hB hL hCr hε
  refine ⟨Cmass,hCmass,hmass.mono ?_⟩
  intro Z hZ
  intro ι inst a b s ha cover u L J q x seed hseed hcap K R H hK hR hH
  let ra:=residualSource s ha cover u L J x
  let β:=commonColumn q x seed
  have hcoeff (I:Id) (hn:β I≠0):sourceCoefficient ra ha seed I≠0 := by
    have he:=common_coefficient q x ra ha (residual_matches s ha cover u L J x) seed I
    change commonColumn q x seed I≠0 at hn
    rw [he] at hn
    exact right_ne_zero_of_mul hn
  have hseedI (I:Id) (_hI:I∈sourceColumns ra) (hn:β I≠0):seed∣I:=
    source_coefficient_seed ra ha seed I (hcoeff I hn)
  have hnorm (I:Id) (_hI:I∈sourceColumns ra) (hn:β I≠0):(I.absNorm:ℝ)≤Z^B:=
    ((original_coefficient_cap ra ha seed I (hcoeff I hn)).2.trans
      (residual_norm_cap s ha cover u L J x)).trans hcap
  have he:=hZ seed hseed hseed.ne_zero (sourceColumns ra) β hseedI hnorm K R H hK hR hH
  simp only [ActiveBlocks,ActiveSubsets,Fintype.sum_sigma] at he
  convert he using 1 <;> rfl

end
end Candidate.SilPrior.FourthPower.OuterFreshDeclaredMass
