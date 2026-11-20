/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
P.6 on the actual arbitrary-ray source union. Count, native fourth, shorter
upper, same-zero witnesses and original marks all use one enlarged d. -/
import Candidate.C092.transport.SourceInverseP6ActualCount
import Candidate.C092.transport.MediumReplaceSourceUpper
import Candidate.C092.transport.MediumInversePriceJoin
import Candidate.C092.transport.WitnessConductorBank

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
local instance c092LocalInst_Candidate_C092_transport_SourceInverseP6Actual_03866cc42b878608_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

theorem actual_regular_source_P6
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (ρ : Contract.AnchorRect) (hsource : Contract.UniformInverseRectSource Contract.canonicalFamily ρ)
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
    (profileBound : ℕ→ℝ) (hprofile : ∀ j,0 ≤ profileBound j) :
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
        d*εshort+(d*(2*ε+(ki:ℝ)*bi+εm)+d*nativeError+(kl:ℝ)*bl)/2) := by
  obtain ⟨inverseMesh,hInvMesh,hcount⟩ := actual_source_inverse_count ρ hsource εm hεm
  obtain ⟨nativeMesh,hNativeMesh,hnative⟩ := repeated_native_fourth hβ hN hq0 hqcap hqmean hdmin nativeError hnativeError
  obtain ⟨order,Cy,hCy,hshort⟩ := regular_core_short_upper M H hH bΦ Mcap Bmask margin R dmin dmax
    τ εshort ez κ heightCost (by linarith) hmargin hR hdmin hdmax hτ hheight hεshort hez hez' hκ hκ' hcost hbudget profileBound hprofile
  refine ⟨inverseMesh,nativeMesh,hInvMesh,hNativeMesh,order,Cy,hCy,?_⟩
  intro ki kl I wrmin hwrmin
  obtain ⟨Jc,Cc,hCc,hc⟩ := hcount M H hH W hWs hW η η₀ ki wrmin hwrmin
  obtain ⟨degree,controls,Cl,hCl,hn⟩ := hnative kl M H hH W hW hWs bΦ hbΦ hsΦ ηlong η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Uc,hUc⟩ := Filter.eventually_atTop.mp hc
  have hscale := HeckeDetectorDyadicGeometry.uniform_scale_threshold dmin Uc hdmin
  refine ⟨Jc,Cc,hCc,degree,controls,Cl,hCl,?_⟩
  filter_upwards [hscale,hshort η₀ I,hn,eventually_gt_atTop (1:ℝ)] with Z hscale hs hn hZ
  refine ⟨hZ,?_⟩
  intro d hd hd' hds s hswidth hη hpuncture hsM hsη rows hkeep hΦ hnorm a ε cutoff T allowance i ha ha' hiI
  dsimp only
  intro ws label r hlabel hr hnext Wi Ai Bi σi fi y hy hyr hAi hWi hsm hfi hm₂ hmn
    θi θl wi vi wl vl tl hi hl e L bi bl X ti p j marks hwi hwiMesh hhi hti hvi hfreq hadm hattain
    hwl hwlMesh hhl hvl hquota hX hXN hkeepLong hlong hmarks
  have hZp := zero_lt_one.trans hZ
  have hdp : 0 < d := hdmin.trans_le hd
  have hcount := (hUc (Z^d) (hscale d hd)).2 Z Bmask bΦ s hη hpuncture
    (fun u => naturalRow s.character u.val u.property.1) rows hnorm a ε cutoff T allowance i
    (by linarith) ws label r hlabel hr θi wi vi ti hi e bi hwi hwiMesh hhi hti hvi hfreq hadm hattain
  rw [←Real.rpow_mul hZp.le] at hcount
  have hcard : (rows.card:ℝ) ≤ (12*(1+hi)*(Cc*(1+hi)^Jc))*
      Z^(d*(1-((2*a-1)*r+e*((ki:ℝ)*wi)))+d*(2*ε+(ki:ℝ)*bi+εm)) := by
    convert hcount using 1 <;> congr 2 <;> ring
  have hupper (u : FreeRow) (hu : u∈rows) :
      ‖original s.character s.mask 1 u.val (twistProfile (Wi u) (σi u) (fi u)) 0 (Z^y)‖^2 ≤ Cy*Z^((2*a-1)*y+d*εshort) := by
    have hh := hs.2 d hd hd' hds s hswidth hsM hsη u.val (hkeep u hu) (hΦ u hu)
      a i ha ha' hiI (hnext ⟨u,hu⟩) (Wi u) (Ai u) (Bi u) (y/d) (σi u) (fi u)
      (hAi u hu) (hWi u hu) (hsm u hu) (div_nonneg hy hdp.le) hyr (hfi u hu) (hm₂ u hu) (hmn u hu)
    have hlen : (Z^d)^(y/d)=Z^y := by rw [←Real.rpow_mul hZp.le,mul_div_cancel₀ _ hdp.ne']
    rw [hlen,natural_plain_eq_original s _ (Wi u) _ (σi u) (fi u) (Real.rpow_pos_of_pos hZp _),←Real.rpow_mul hZp.le] at hh
    convert hh using 1 <;> congr 2 <;> field_simp <;> ring
  have hfourth := hn d hd θl wl (33/50) vl tl hl e bl hwl hwlMesh le_rfl le_rfl hhl hvl hquota p j X hX hXN rows hkeepLong hnorm hlong
  have hm : (∑ u∈rows,‖original ηlong (fixedBadMask*idealGenerator 1) 1 u.val (p.profile j) tl X‖^4) ≤
      (Cl*QuadraticInitialBound.diagonalControl radialMajorant*(sourceControl controls (p.profile j))^4*(1+|tl|+hl)^degree)*
      Z^(d-e*((kl:ℝ)*wl)+(d*nativeError+(kl:ℝ)*bl)) := by
    convert hfourth using 1 <;> congr 2 <;> ring
  have result := same_rows_price rows
    (fun u => original ηlong (fixedBadMask*idealGenerator 1) 1 u.val (p.profile j) tl X)
    (fun u => original s.character s.mask 1 u.val (twistProfile (Wi u) (σi u) (fi u)) 0 (Z^y)) marks
    Z d (2*a-1) y e L ((kl:ℝ)*wl) ((2*a-1)*r+e*((ki:ℝ)*wi))
    (d*(2*ε+(ki:ℝ)*bi+εm)) (d*nativeError+(kl:ℝ)*bl) (d*εshort)
    (12*(1+hi)*(Cc*(1+hi)^Jc))
    (Cl*QuadraticInitialBound.diagonalControl radialMajorant*(sourceControl controls (p.profile j))^4*(1+|tl|+hl)^degree) Cy
    hZp (by positivity) (by have h := QuadraticInitialBound.diagonalControl_nonneg radialMajorant;positivity) hCy.le hcard hm hupper hmarks
  convert result using 1 <;> congr 2 <;> ring

#print axioms actual_regular_source_P6
end
end QRH.Cycle092.SourceInverseP6
