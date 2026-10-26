import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalFixedQSaved

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory
namespace SevenEighths.Cycle61FixedInducing
open CenteredMomentFiniteProfileExceptionalPhysical CenteredMomentFirstCanonicalAllowance
open CenteredMomentSecondPhysicalLedger
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport

open CenteredMomentSecondExceptionalPhysicalSaving CenteredMomentRankinRadical
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

/-- The literal physical block keeps both the positive radius factor and
its centered lattice cancellation before any common-part aggregation. -/
theorem physical_power_identity (Z : ℝ) (hZ : 1<Z)
    (Ck P a e δ θ r c d V K R : ℝ)
    (hc : 0<c) (hd : 0<d) (hV : 0<V) (hK : 0<K) (hR : 0<R) :
    Ck*(P*Z^(2*e+δ-max (r-min (Real.logb Z c) (Real.logb Z d)) 0)*
      (c*d)^θ*V^(1/3:ℝ)*K^(5/6:ℝ)*a^(-2/3:ℝ)*
      Z^(-(Real.logb Z c+Real.logb Z d)/3)/R) =
    Ck*P*a^(-2/3:ℝ)*Z^(2*e+δ+θ*(Real.logb Z c+Real.logb Z d)+
      Real.logb Z V/3+5*Real.logb Z K/6-(Real.logb Z c+Real.logb Z d)/3-
      Real.logb Z R-max (r-min (Real.logb Z c) (Real.logb Z d)) 0) := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have power (x t : ℝ) (hx : 0<x) : x^t=Z^(Real.logb Z x*t) := by
    rw [Real.rpow_mul hz.le,Real.rpow_logb hz hZ.ne' hx]
  rw [power (c*d) θ (mul_pos hc hd), Real.logb_mul hc.ne' hd.ne',
    power V (1/3) hV, power K (5/6) hK]
  have hRi : R⁻¹=Z^(-Real.logb Z R) := by
    rw [Real.rpow_neg hz.le,Real.rpow_logb hz hZ.ne' hR]
  rw [div_eq_mul_inv,hRi]
  calc
    _ = Ck*P*a^(-2/3:ℝ)*(Z^(2*e+δ-max (r-min (Real.logb Z c) (Real.logb Z d)) 0)*
      Z^((Real.logb Z c+Real.logb Z d)*θ)*Z^(Real.logb Z V*(1/3))*
      Z^(Real.logb Z K*(5/6))*Z^(-(Real.logb Z c+Real.logb Z d)/3)*
      Z^(-Real.logb Z R)) := by ring
    _ = _ := by
      repeat rw [←Real.rpow_add hz]
      congr 2
      ring

theorem actual_exceptional_log_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀χ₀:RayCharacter,idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z^Lbound →
      ∀a:ℝ,0<a → (∀I:Ideal O,β I≠0→a*volume s.toData≤(I.absNorm:ℝ)) →
      ∀(R Kphys:ℝ),0<Kphys → ∀n:Fin 4→ℤ,
      ‖physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n‖/volume s.toData≤
        Ck*profileFactor Sprofile s p J Q K*a^(-2/3:ℝ)*
          Z^(2*ε+δ + θ*(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ)) +
            Real.logb Z (volume s.toData)/3 + 5*Real.logb Z Kphys/6 -
            (Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3 -
            Real.logb Z (Ideal.absNorm (commonRadical C D):ℝ) -
            max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0) := by
  obtain ⟨J,Sprofile,hSp,Ck,hCk,hbound⟩ :=
    CenteredMomentFiniteProfileExceptionalFixedQ.actual_saved_exceptional_block
      wlo whi hwlo hwhi lo hi W ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSp,Ck,hCk,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨K,hK,hbound⟩ := hbound Q hQ hQt hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW1 hW2 C D hC hD R0 seed hR0 hsC hsD hCD U A S β
    r hX1 hX2 hY1 hY2 τ hτ rows hn hex1 hex2 hcond1 hcond2 χ0 hη
    m hm hml hm2 hex H hβ hHD a ha hlower R Kphys hKphys n
  have hb := hZ.2 s p hlo hhi hP hW1 hW2 C D hC hD R0 seed hR0 hsC hsD hCD U
    r hX1 hX2 hY1 hY2 τ hτ rows hn hex1 hex2 hcond1 hcond2 χ0 hη
    m hm hml hm2 hex H hβ hHD a ha hlower R Kphys hKphys n
  have hc : 0<(C.absNorm:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd : 0<(D.absNorm:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hp : 0<(Ideal.absNorm (commonRadical C D):ℝ) := by
    rw [← common_ideal_product]
    exact common_product_pos C D hC Finset.univ
  apply hb.trans_eq
  exact physical_power_identity Z hZ.1 _ _ _ _ _ _ _ _ _ _ _ _ hc hd
    (volume_pos s.toData) hKphys hp

end SevenEighths.Cycle61FixedInducing
end
end OAI

#print axioms OAI.SevenEighths.Cycle61FixedInducing.actual_exceptional_log_block
