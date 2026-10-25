/- Copyright (c) 2026 Sil. Apache-2.0.
exact normalization and geometric/harmonic cost of the actual
childEnvelope. No Input-specialized source estimate is used. Every K in
the geometric identities may be K4=16*Koriginal*Wblock^4 literally.
-/
import Candidate.SilPrior.FourthPower.MixedActualEnvelopePhysical
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondBlockHarmonicMass
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondLiveBlock

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.MixedActualGeometry
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open QRH.Record1252270103TwoIdeal
open QRH.Record1252270103KernelMass
open MixedRawEnvelope MixedPhysicalEnvelopes
open CenteredMomentCanonicalFirst CenteredMomentHeckeColumnWindow
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical CenteredMomentSectorLocalization
open CenteredMomentSecondWindowBudget CenteredMomentSecondNonexceptionalScalar
open CenteredMomentSecondRadicalBudget CenteredMomentSecondBlockHarmonicMass
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit CenteredMomentSecondLiveBlock CenteredMomentActiveSource
open CenteredMomentFirstSectors
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-- The exact physical cost after paired-window normalization. -/
def childGeometry (η : Character) (C D : Id) (U : Finset (CommonIndex C D))
    (K : ℝ) (n : Fin 4→ℤ) : ℝ :=
  (outerScalar C D K n*normalizer C D U)/Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*
    childEnvelope η C D U n /
    (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))

/-- One block with decay one, retaining the actual child conductor cost. -/
def childBlockBudget (degree : ℕ) (Cp Z δ volume A base tp K : ℝ)
    (d : Id×Id) (η : Character) (C D : Id) (U : Finset (CommonIndex C D))
    (n : Fin 4→ℤ) : ℝ :=
  Cp*Z^δ*(outerScalar C D K n*normalizer C D U)*
    (windowBudget degree tp (rawBudget volume (A*childEnvelope η C D U n) Z base C d)*
      windowBudget degree tp (rawBudget volume (A*childEnvelope η C D U n) Z base D d))/
    (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))

/-- The same ordinary prefix denominator survives the pairing once,
and both genuine common factors survive as a square root. -/
theorem childBlockBudget_normalized (degree : ℕ)
    (Cp Z δ volume A base tp K : ℝ) (hZ : 0<Z) (hvolume : 0<volume) (hA : 0≤A)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (η : Character)
    (C D : Id) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (n : Fin 4→ℤ) :
    childBlockBudget degree Cp Z δ volume A base tp K d η C D U n/volume =
      (Cp*Z^δ*(A/pairNorm d)*Z^base*heightEnvelope tp^(2*degree)*profileMoment degree^2)*
        childGeometry η C D U K n := by
  have hc : 0<(C.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd' : 0<(D.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hp := pairNorm_pos hd.1 hd.2
  have hchild : 0≤childEnvelope η C D U n := by
    have hdyad := (dyadicScale_pos (n 1)).le
    unfold childEnvelope
    positivity
  have hpower : 0≤Z^base := (Real.rpow_pos_of_pos hZ _).le
  have he := paired_normalized_windows volume (A*childEnvelope η C D U n/pairNorm d)
    (Z^base) (Z^base) (C.absNorm:ℝ) (D.absNorm:ℝ) tp hvolume
    (div_nonneg (mul_nonneg hA hchild) hp.le) hpower hpower hc hd' degree degree
  have hraw (G : Id) :
      rawBudget volume (A*childEnvelope η C D U n) Z base G d =
        volume*(A*childEnvelope η C D U n/pairNorm d)*Z^base/(G.absNorm:ℝ) := by
    unfold rawBudget
    ring
  have hsqrt : Real.sqrt (Z^base*Z^base)=Z^base := by
    rw [←pow_two,Real.sqrt_sq hpower]
  rw [hsqrt,show degree+degree=2*degree by omega] at he
  calc
    _ = Cp*Z^δ*(outerScalar C D K n*normalizer C D U)*
        (windowBudget degree tp
          (volume*(A*childEnvelope η C D U n/pairNorm d)*Z^base/(C.absNorm:ℝ))*
         windowBudget degree tp
          (volume*(A*childEnvelope η C D U n/pairNorm d)*Z^base/(D.absNorm:ℝ))/volume)/
        (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))) := by
      simp only [childBlockBudget,hraw]
      ring
    _ = _ := by rw [he];unfold childGeometry;ring

theorem childGeometry_nonneg (η : Character) (C D : Id) (hC : Supported C)
    (U : Finset (CommonIndex C D)) (K : ℝ) (hK : 0≤K) (n : Fin 4→ℤ) :
    0≤childGeometry η C D U K n := by
  have ho : 0≤outerScalar C D K n := by unfold outerScalar;positivity
  have hn := (normalizer_pos C D hC U).le
  have hc : 0≤childEnvelope η C D U n := by
    have hdyad := (dyadicScale_pos (n 1)).le
    unfold childEnvelope
    positivity
  have hr : 0<dyadicScale (n 0)*dyadicScale (n 1)/
      (dyadicScale (n 2)*dyadicScale (n 3)) :=
    div_pos (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
      (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
  unfold childGeometry
  positivity

/-- Zero physical blocks contribute zero; this prevents unused dyadic
indices from being charged a geometric cost they need not satisfy. -/
def liveChildGeometry (η : Character) (tp : ℝ) (S : Finset Id) (β : Id→ℂ)
    (C D : Id) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (R : ℝ) (rows : Finset O) (Ψ : 𝓢(ℝ,ℂ))
    (K : ℝ) (n : Fin 4→ℤ) : ℝ :=
  if physicalBlock η tp S β C D hC hD U R rows Ψ K n=0 then 0
  else childGeometry η C D U K n

theorem liveChildGeometry_nonneg (η : Character) (tp : ℝ) (S : Finset Id) (β : Id→ℂ)
    (C D : Id) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (R : ℝ) (rows : Finset O) (Ψ : 𝓢(ℝ,ℂ))
    (K : ℝ) (hK : 0≤K) (n : Fin 4→ℤ) :
    0≤liveChildGeometry η tp S β C D hC hD U R rows Ψ K n := by
  unfold liveChildGeometry
  split_ifs
  · exact le_rfl
  · exact childGeometry_nonneg η C D hC U K hK n

theorem liveChildGeometry_le (η : Character) (tp : ℝ) (S : Finset Id) (β : Id→ℂ)
    (C D : Id) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (R : ℝ) (rows : Finset O) (Ψ : 𝓢(ℝ,ℂ))
    (K : ℝ) (hK : 0<K) (n : Fin 4→ℤ) (Hsource : ℝ) (hH : 0≤Hsource)
    (hcolumns : ∀I,β I≠0→(I.absNorm:ℝ)≤Hsource) :
    liveChildGeometry η tp S β C D hC hD U R rows Ψ K n ≤
      (4*(fixedFactor:ℝ)*η.modulus.absNorm*Hsource)*pairWeight C D := by
  unfold liveChildGeometry
  split_ifs with hzero
  · exact mul_nonneg (by positivity) (pairWeight_nonneg C D)
  · have he := actual_source_envelope_scalar η tp S β C D hC hD U R rows Ψ K hK n
      Hsource hcolumns hzero
    simpa only [childGeometry,pairWeight,mul_one_div] using he

/-- Full actual label/block sum. The retained live-label sum is a
subsum with nonnegative terms. The coefficient beta remains literal. -/
def fullRetainedGeometry (η : Character) (tp : ℝ) (S : Finset Id) (β : Id→ℂ)
    (Ψ : 𝓢(ℝ,ℂ)) (K R Hsource : ℝ) (Q : Id) (m : O) (χ₀ : RayCharacter) : ℝ :=
  ∑q : ActiveBlocks S β K R Hsource,
    liveChildGeometry η tp S β q.1.1.val.1 q.1.1.val.2
      (commonLabels_supported (activeSource S β) _ _ q.1.1.property).1
      (commonLabels_supported (activeSource S β) _ _ q.1.1.property).2 q.1.2 R
      (partRows false η χ₀ Q m q.1.1.val.1 q.1.1.val.2 q.1.2 R) Ψ K
      (fun i=>(q.2 i:ℤ))

theorem fullRetainedGeometry_le (η : Character) (tp : ℝ) (S : Finset Id) (β : Id→ℂ)
    (Ψ : 𝓢(ℝ,ℂ)) (K R Hsource : ℝ) (hK : 0<K) (hH : 0≤Hsource)
    (hcolumns : ∀I,β I≠0→(I.absNorm:ℝ)≤Hsource)
    (Q : Id) (m : O) (χ₀ : RayCharacter) :
    fullRetainedGeometry η tp S β Ψ K R Hsource Q m χ₀ ≤
      (4*(fixedFactor:ℝ)*η.modulus.absNorm*Hsource)*
        (∑q : ActiveBlocks S β K R Hsource,pairWeight q.1.1.val.1 q.1.1.val.2) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  exact liveChildGeometry_le η tp S β q.1.1.val.1 q.1.1.val.2
    (commonLabels_supported (activeSource S β) _ _ q.1.1.property).1
    (commonLabels_supported (activeSource S β) _ _ q.1.1.property).2 q.1.2 R
    (partRows false η χ₀ Q m q.1.1.val.1 q.1.1.val.2 q.1.2 R) Ψ K hK
    (fun i=>(q.2 i:ℤ)) Hsource hH hcolumns

/-- Generic harmonic counting closes the geometric cost with the
original squarefree seed. K4 and the outer 1/W are both literal. -/
theorem uniform_fourth_retained_geometry (B L Cr ε : ℝ)
    (hB : 0≤B) (hL : 0≤L) (hCr : 0<Cr) (hε : 0<ε) :
    ∃Cg : ℝ,0<Cg ∧ ∀ᶠZ : ℝ in atTop,
    ∀seed : Id,Squarefree seed → seed≠0 →
    ∀(η : Character)(tp : ℝ)(S : Finset Id)(β : Id→ℂ)(Ψ : 𝓢(ℝ,ℂ)),
      (∀I∈S,β I≠0→seed∣I) →
    ∀(K Wblock R Hsource : ℝ),0<K → 0<Wblock → 0≤Hsource →
      R≤Cr*Z^L → Hsource≤Z^B → (∀I,β I≠0→(I.absNorm:ℝ)≤Hsource) →
    ∀(Q : Id)(m : O)(χ₀ : RayCharacter),
      fullRetainedGeometry η tp S β Ψ (16*K*Wblock^4) R Hsource Q m χ₀/Wblock ≤
        (4*(fixedFactor:ℝ)*η.modulus.absNorm*Hsource)*
          (Cg*Z^ε/(seed.absNorm:ℝ))/Wblock := by
  obtain ⟨Cg,hCg,hg⟩ := actual_block_harmonic_mass B L Cr ε hB hL hCr hε
  refine ⟨Cg,hCg,?_⟩
  filter_upwards [hg] with Z hZ
  intro seed hs hs0 η tp S β Ψ hseed K Wblock R Hsource hK hW hH hR hcap hcolumns Q m χ₀
  have hK4 : 0<16*K*Wblock^4 := by positivity
  have hmass := hZ seed hs hs0 S β hseed (fun I _ hi=>(hcolumns I hi).trans hcap)
    (16*K*Wblock^4) R Hsource hK4 hR hcap
  apply div_le_div_of_nonneg_right _ hW.le
  exact (fullRetainedGeometry_le η tp S β Ψ (16*K*Wblock^4) R Hsource hK4 hH
    hcolumns Q m χ₀).trans (mul_le_mul_of_nonneg_left hmass (by positivity))

end
end Candidate.SilPrior.FourthPower.MixedActualGeometry
