/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Finite genuine source banks carry the full arbitrary-ray same-row P6 bound,
with one uniform checked price budget before all actual lengths and radii. -/
import Candidate.C092.transport.SourceInverseP6Actual
import Candidate.C092.transport.MediumInversePricePaidBank
namespace QRH.Cycle092.SourceInverseP6
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators ContDiff SchwartzMap
open Filter Set OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyState CenteredMomentWholeSlotDeletion HeckeDetectorRowwisePolynomial
open HeckeDetectorInverseFiberCount HeckeDetectorSupportedWitness HeckeDetectorWitnessRows
open CenteredMomentPrimeSlot CenteredMomentSecondHeightFamily CenteredMomentDetectorEnergyInitialState
open CenteredMomentEnergyBands ConcretePrimeRowBridge
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorPlainFiberSource
open CenteredMomentInductionEnergy
open Qrh.MarkedAnchor.Interface QRH.Cycle092.MediumReplace.Source
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.MediumInversePrice QRH.Cycle092.TinyCore
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_SourceInverseP6Bank_e5fbb177e489e3fa_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

def SourceP6 (ρ : Contract.AnchorRect) : Prop :=
  ∀ (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (εm nativeError : ℝ) (hεm : 0 < εm) (hnativeError : 0 < nativeError)
    {N quota : ℝ} (hN : N ≤ 1/2) (hq0 : 0 ≤ quota) (hqcap : quota < 3/20) (hqmean : quota < (1-2*N)/2)
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (W : ℝ→ℂ) (hWs : Function.support W ⊆ Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (η η₀ ηlong : Character) (Q : Ideal O) (hQM : Q ≤ M) (hQ0 : internalQ Q η₀ ≠ 0)
    (hQt : internalQ Q η₀ ≠ ⊤) (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)})
    (bΦ Mcap Bmask margin R dmin dmax τ εshort ez κ heightCost : ℝ)
    (hbΦ : 2 ≤ bΦ) (hsΦ : Function.support (radialMajorant : ℝ→ℂ) ⊆ Iic bΦ)
    (hmargin : 0 < margin) (hR : 0 ≤ R) (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax)
    (hτ : 0 < τ) (hheight : 4*τ < dmin*heightCost) (hεshort : 0 < εshort)
    (hez : 0 < ez) (hez' : ez < 1/1000) (hκ : 0 < κ) (hκ' : κ ≤ 1) (hcost : 0 ≤ heightCost)
    (hbudget : 12*ez*(R+2)+8*κ+2*heightCost ≤ εshort)
    (profileBound : ℕ→ℝ) (hprofile : ∀ j,0 ≤ profileBound j),
    ∃ inverseMesh nativeMesh : ℝ,0 < inverseMesh ∧ 0 < nativeMesh ∧
    ∃ order : ℕ,∃ Cy : ℝ,0 < Cy ∧
    ∀ (ki kl I : ℕ) (wrmin : ℝ),0 < wrmin →
    ∃ Jc : ℕ,∃ Cc : ℝ,0 < Cc ∧ ∃ degree : ℕ,∃ controls : Finset (ℕ×ℕ),∃ Cl : ℝ,0 < Cl ∧
    ∀ᶠ Z : ℝ in atTop,1 < Z ∧
    ∀ d : ℝ,dmin ≤ d → d ≤ dmax → Mcap+Bmask+margin ≤ d →
    ∀ s : NaturalState Z Bmask bΦ,s.width ≤ Mcap → s.character=η → s.puncture=1 →
    ∀ (hsM : s.fixedModulus ≤ M) (hsη : s.fixedModulus ≤ η₀.modulus)
      (rows : Finset FreeRow) (hkeep : ∀ u∈rows,s.radial.keep u.val),
      (∀ u∈rows,s.radial.profile (‖ConcreteTraceCRT.eisEmbedding u.val‖^2/s.radial.scale) ≠ 0) →
      (∀ u∈rows,rowNorm u ≤ Z^d) →
    ∀ (a ε cutoff T allowance : ℝ) (i : ℕ),51/100 ≤ a → a ≤ 1 → i ≤ I →
    let F := fun u : FreeRow => naturalRow s.character u.val u.property.1
    ∀ ws : ∀ u : rows,SupportedWitness (family M H hH s η₀ (F u.val)) (Z^d) a ε cutoff T allowance i,
    ∀ (label : Option (RayQuotient.Characters M H × RayQuotient.Characters M H)) (r : ℝ),
      (∀ u,(ws u).label=label) → (∀ u,(ws u).r=r) →
      (∀ u : rows,HeckeDetectorZeros.zeroMaximum (family M H hH s η₀ (F u.val))
        (family_nonprincipal M H hH s η₀ hsM hsη (hkeep u.val u.property) (F u.val))
        (3*(i+1 : ℕ)*Z^τ) < a+2*ez) →
    ∀ (Wi : FreeRow→ℝ→ℂ) (Ai Bi σi fi : FreeRow→ℝ) (y : ℝ),
      0 ≤ y → y/d ≤ R →
      (∀ u∈rows,0 < Ai u) → (∀ u∈rows,Function.support (Wi u) ⊆ Icc (Ai u) (Bi u)) →
      (∀ u∈rows,ContDiff ℝ ∞ (Wi u)) →
      (∀ u∈rows,|fi u|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ) →
      (∀ u∈rows,∀ x∈Icc (1-a-6*ez-σi u) (2-σi u),∀ t:ℝ,
        (1+|t|)^2*‖mellin (Wi u) ((x:ℂ)+t*Complex.I)‖ ≤ profileBound 2) →
      (∀ u∈rows,∀ x∈Icc (1-a-6*ez-σi u) (2-σi u),∀ t:ℝ,
        (1+|t|)^(order+2)*‖mellin (Wi u) ((x:ℂ)+t*Complex.I)‖ ≤ profileBound (order+2)) →
    ∀ (θi θl : RayQuotient.Characters M H) (wi vi wl vl tl hi hl e L bi bl X : ℝ)
      (ti : FreeRow→ℝ) (p : Profiles (1/4) (9/4)) (j : Fin 2) (marks : FreeRow→ℂ),
      wrmin ≤ wi → wi ≤ inverseMesh → 0 ≤ hi → (∀ u∈rows,|ti u| ≤ hi) → |vi| ≤ hi →
      2*Real.pi*allowance+(3*i : ℕ)*T ≤ hi → ρ.Admissible r ((ki:ℝ)*wi) 1 →
      (∀ u∈rows,(Z^d)^(e*wi-bi) ≤ ‖annularMark M H hH η η₀ W (Z^d) θi wi vi ti u‖^2) →
      0 ≤ wl → wl/d ≤ nativeMesh → 0 ≤ hl → |vl| ≤ hl → (kl:ℝ)*wl ≤ d*quota →
      0 < X → length (Z^d) X ≤ N →
      (∀ u∈rows,initialKeep ηlong (internalQ Q η₀) u.val) →
      (∀ u∈rows,Z^(e*wl-bl) ≤ ‖normalizedSlot ηlong (fixedBadMask*idealGenerator 1) 1 u.val
        (primePool M H 2 (Z^wl)) (fun J => idealCoeff (relativeCharacter M H hH η₀ θl) J*
          HeckePrimeAnnular.annularWeight W (Z^wl) (33/50) vl J) tl (Z^wl)‖^2) →
      (∀ u∈rows,‖marks u‖^2 ≤ Z^(e*L)) →
    (∑ u∈rows,‖original ηlong (fixedBadMask*idealGenerator 1) 1 u.val (p.profile j) tl X*
      original s.character s.mask 1 u.val (twistProfile (Wi u) (σi u) (fi u)) 0 (Z^y)*marks u‖^2) ≤
      Cy*Real.sqrt (12*(1+hi)*(Cc*(1+hi)^Jc))*
        Real.sqrt (Cl*QuadraticInitialBound.diagonalControl radialMajorant*
          (sourceControl controls (p.profile j))^4*(1+|tl|+hl)^degree)*
      Z^(d+(2*a-1)*y+e*(L-(kl:ℝ)*wl/2)-d*((2*a-1)*r+e*((ki:ℝ)*wi))/2+
        d*εshort+(d*(2*ε+(ki:ℝ)*bi+εm)+d*nativeError+(kl:ℝ)*bl)/2)

theorem source_P6_of_rect (ρ : Contract.AnchorRect)
    (hsource : Contract.UniformInverseRectSource Contract.canonicalFamily ρ) : SourceP6 ρ := by
  intro hβ
  exact actual_regular_source_P6 hβ ρ hsource

open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source
open Qrh.MarkedAnchor.Interface.Contract

theorem paid_source_P6_bank
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    {y e ν : ℝ} (c : Cutoff)
    (hy : y ≤ sourceY)
    (he : 0 ≤ e) (hν : e ≤ ν) (hν1 : ν ≤ 3/4)
    (hg : RootGuard c.inverse c.rootUpper) (hp : PaidWithBand y e ν c) :
    ∃ fee : ℝ, 0 < fee ∧ fee ≤ 1/2 ∧
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/1000 ∧ 3*δ ≤ fee/4 ∧
    ∃ J : ℕ, ∃ bank : Fin J → AnchorRect,
      (∀ i, UniformInverseRectSource canonicalFamily (bank i)) ∧
      (∀ i, SourceP6 (bank i)) ∧
      (∀ r : ℝ, 367/500 ≤ r → r ≤ 1 →
        inverseQuota r ≤ fee/4 ∨
          (0 ≤ inverseQuota r-fee/4 → ∃ i, (bank i).Admissible r (inverseQuota r-fee/4) 1)) ∧
      (∀ n : ℝ, n ≤ sourceRatio*y → ∀ r V : ℝ, 367/500 ≤ r → (c.inverse : ℝ) ≤ r → r ≤ 1 → 0 ≤ V →
        ∀ (live nativeWidth inverseWidth nativeLoss inverseLoss error : ℝ),
          live ≤ sourceWidth n y-(u : ℝ) →
          2*NativeFourthEffective.credit n V-nativeLoss ≤ nativeWidth →
          inverseQuota r-inverseLoss ≤ inverseWidth →
          nativeLoss ≤ fee → inverseLoss ≤ fee → error ≤ fee →
        repeatedPrice y e ν V r live nativeWidth inverseWidth+error < radialAllowance V) := by
  obtain ⟨fee,hfee,hhalf,δ,hδ,hsmall,hδfee,J,bank,hsource,hcover,hpay⟩ :=
    QRH.Cycle092.MediumInversePrice.paid_genuine_inverse_bank hβ c hy he hν hν1 hg hp
  exact ⟨fee,hfee,hhalf,δ,hδ,hsmall,hδfee,J,bank,hsource,
    fun i => source_P6_of_rect (bank i) (hsource i),hcover,hpay⟩

#print axioms paid_source_P6_bank
end
end QRH.Cycle092.SourceInverseP6
