/- Copyright (c) 2026 Sil. Apache-2.0.
The complete first selected smooth energy for the actual avoided
unit-prefix, live-seed-one source. All three analytic pieces are called
from their proved suppliers. Original seed savings belong to the preceding
allocation, not to an invented first-diagonal denominator.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstPaidRetained
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstRemainder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedFirstFullEnergy
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcretePrimeRowBridge ActualEisensteinCubic RayFourExpansion
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily
open CenteredMomentFirstLocalization CenteredMomentFirstSectorLocalization
open MixedPrincipalPair MixedPrincipalWindow MixedOriginalNormCap MixedOriginalTail
open MixedPrincipalAllocations
open MixedInnerExceptionalBlock MixedHeightEnvelope MixedFirstActualNonexceptional
open MixedFirstFullBudget MixedFirstLiveSource MixedFirstExceptionalApplication
open MixedFirstAvoidance MixedFirstPhysicalApplication MixedFirstPhysicalBudget
open MixedFirstIntegratedWindows MixedFirstPaidCosts MixedFirstPaidPhysical
open MixedFirstPaidRetained MixedFirstGeometricCaps MixedFirstRemainder
open MixedCompletedRows ReferencePrimeEnclosure EisensteinSchwartzPoisson
open QRH.Record1252270103KernelMass (pairNorm)
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

private theorem average_normalization (Ds : Finset Id) (weight : Id→ℝ)
    (W X : ℝ) (hW : 0<W) (f : Id→ℂ) :
    ‖∑F∈Ds,((weight F/W:ℝ):ℂ)*f F‖/X=
      ‖∑F∈Ds,(weight F:ℂ)*f F‖/(X*W) := by
  have hs : (∑F∈Ds,((weight F/W:ℝ):ℂ)*f F)=
      (∑F∈Ds,(weight F:ℂ)*f F)/(W:ℂ) := by
    simp only [Complex.ofReal_div,div_mul_eq_mul_div,Finset.sum_div]
  rw [hs,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hW,div_div]
  rw [mul_comm W X]

variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- One full first-energy estimate. xiFirst is chosen before the eventual
threshold because it determines the actual discarded-tail decay order.
BandGeometry is supplied by uniform_actual_band_geometry; no bound on any
of the three energy pieces is an assumption. -/
theorem uniform_full_first_energy
    (Φ : 𝓢(ℝ,ℂ)) (N Holes : ℕ) (hcard : Fintype.card ι≤N) (Wslot : ℝ→ℂ)
    (a b Mcap L Lslot Lcap Cap BR BG BH Bsource Bη Pexp Mgeom Btail
      ε δ lo hi ξfirst ξsecond saving Bfrequency εsum : ℝ)
    (hWs : Function.support Wslot⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ Wslot)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b) (hMcap0 : 0<Mcap)
    (hL : 0≤L) (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hBR : 0≤BR) (hBG : 0≤BG) (hBH : 0≤BH) (hBsource : 0≤Bsource)
    (hPexp : 0≤Pexp) (hMgeom : 0≤Mgeom) (hBtail : 0≤Btail) (hBGtail : BG≤Btail)
    (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε) (hδ : 0<δ)
    (hgap : (7/10:ℝ)+2*δ<1) (hξfirst : 0<ξfirst) (hξsecond : 0<ξsecond)
    (hMcap : Mgeom+(Bη+BG+ε)+Bsource+ε≤Mcap)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hfrequency : 0≤Bfrequency) (hεsum : 0<εsum)
    (hvolumeExponent : 2*L+Pexp≤Btail)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃U : Controls,∃tailControl : Finset (ℕ×ℕ),
    ∃Cpush Ckernel Csum Czero Ctail : ℝ,
      0<Cpush ∧ 0≤Ckernel ∧ 0<Csum ∧ 0<Czero ∧ 0<Ctail ∧
    ∀η₀ : Character,Q≤η₀.modulus→∃c : Constants,
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : ι→RayQuotient.Characters M Hray)(w σ freq : ι→ℝ)(t V : ℝ)(R₀ : ι→Finset Id),
      (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
      0≤V→(∀i,|freq i|≤V)→(∀i,(R₀ i).card≤Holes)→
    ∀s : Source ι a b,Canonical M Hray hHray Wslot Cap Lcap Z η₀ θ w σ freq t R₀ s→
      s.d=(1,1)→(s.R.absNorm:ℝ)≤Z^BR→s.H⊆enclosure (Cap*Z^Lcap)→
      ((∏I∈holes s.H,I).absNorm:ℝ)≤Z^BH→(∀i,∀P∈s.H,P.val∈R₀ i)→
      s.X₁≤Z^L→s.X₂≤Z^L→s.Y₁≤Z^L→s.Y₂≤Z^L→
      sourceNormCap s.P b s.T s.d≤Z^Bsource→poolCap s≤Z^Btail→
      (∏i,s.P i)≤Z^Pexp→(s.Fhole.absNorm:ℝ)≤Z^BH→
    ∀cover : OriginalEnclosure s,∀η : Character,(η.modulus.absNorm:ℝ)≤Z^Bη→
    ∀(K κpad W Tsecond H : ℝ),0<K→0<W→K≤Z^Btail→K⁻¹≤Z^Btail→
      0≤Tsecond→Tsecond≤Z^(Mgeom-ξsecond)→Tsecond≤Z^Btail→
      1≤sharpSupport s→sharpSupport s≤Z^Btail→W≤Z^Btail→W⁻¹≤Z^Btail→
      0<H→sourceNormCap s.P b s.T s.d≤H→H≤Z^BG→
    ∀(χ₀ : RayCharacter)(msecond : O),msecond≠0→goodLambda∣msecond→(2:O)∣msecond→
    ∀u : Id,u∣s.R→let sActual:=avoidSource s u
    BandGeometry sActual ha 1 K Z ξfirst κpad W Tsecond H Btail Bfrequency→
    ∀Ds : Finset Id,(∀F∈Ds,Supported F)→∀(weight : Id→ℝ)(mass : ℝ),0≤mass→
      (∀F∈Ds,0≤weight F∧weight F≤mass)→(∀F∈Ds,(F.absNorm:ℝ)≤2*W)→
    ∀Rexp Praw Sraw dsel lref c0 omega sigma loss BX : ℝ,
    let p0 : Parameters :=
      { Z:=Z,Kfirst:=K,Tfirst:=0,Cfirst:=1,ξfirst:=ξfirst,κpad:=κpad,W:=W,
        ε:=ε,δ:=δ,Bnorm:=normExponent L Pexp ε,BG:=BG,BX:=BX,R:=Rexp,P:=Praw,S:=Sraw,
        d:=dsel,l:=lref,c0:=c0,omega:=omega,sigma:=sigma,loss:=loss,saving:=saving }
    Gates p0→SourceGeometry p0 s η w→
    ‖∑F∈Ds,((weight F/W:ℝ):ℂ)*finiteHeckeEnergy η (fixedBadMask*idealGenerator s.R) 1 t
      (sourceColumns sActual) (selectedCoefficient sActual ha 1 F) Φ K‖/sourceVolume s≤
      Csum*retainedFactor U c s η Q c0 t V K mass Cpush Ckernel ε*Z^(loss+5*Btail*ε+εsum)+
      ((∑F∈Ds,weight F)/W)*
        (Czero*K*(profileCap s)^2*‖paperRadialFourier Φ 0‖*
          (b^2*(2:ℝ)^Fintype.card ι/pairNorm s.d)*(sourceNormCap s.P b s.T s.d)^ε+
        Ctail*(profileCap s)^2*tailControl.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(-saving)) := by
  obtain ⟨U,Cpush,Ckernel,Csum,hCpush,hCkernel,hCsum,hretained⟩ := uniform_paid_retained
    (ι:=ι) M Hray hHray Φ N Holes hcard Wslot a b Mcap L Lslot Lcap Cap
    BR BG BH Bsource Bη Pexp Mgeom Btail ε δ lo hi ξsecond saving Bfrequency εsum
    hWs hW ha haUpper hb hMcap0 hL hLslot hLcap hCap hBR hBG hBH hBsource hPexp
    hMgeom hBtail hBGtail hCapb hLordinary hε hδ hgap hξsecond hMcap hβ hfrequency hεsum
    Q hQt hQ72 hQM
  obtain ⟨Czero,hCzero,hzero⟩ := selected_first_zero N ε hε
  obtain ⟨tailControl,Ctail,hCtail,htail⟩ := selected_first_tail N b Btail ξfirst saving hBtail hξfirst
  refine ⟨U,tailControl,Cpush,Ckernel,Csum,Czero,Ctail,hCpush,hCkernel,hCsum,hCzero,hCtail,?_⟩
  intro η₀ hη₀
  obtain ⟨c,hretained⟩ := hretained η₀ hη₀
  refine ⟨c,?_⟩
  filter_upwards [hretained,htail] with Z hr ht
  refine ⟨hr.1,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ s hcanonical hunit hR hHholes hholes hHR
    hX₁ hX₂ hY₁ hY₂ hsource hpool hP hF cover η hη K κpad W Tsecond H hK hWblock hKcap hKinv
    hT hTcap hTupper hX hXupper hWupper hWinv hH hsourceH hHcap χ₀ msecond hmsecond hml2 hm22
    u hu sActual hgeometry Ds hDs weight mass hmass hweight hDN
    Rexp Praw Sraw dsel lref c0 omega sigma loss BX p0 hp0 hg0
  have hZ0 := zero_lt_one.trans hr.1
  have hvolume : sourceVolume s≤Z^Btail := by
    change s.X₁*s.X₂*(∏i,s.P i)≤Z^Btail
    calc
      _≤Z^L*Z^L*Z^Pexp := mul_le_mul
        (mul_le_mul hX₁ hX₂ (s.hL.trans_le s.hX₂).le (Real.rpow_nonneg hZ0.le _))
        hP (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.hP i))) (by positivity)
      _=Z^(2*L+Pexp) := by rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0];congr 1;ring
      _≤Z^Btail := Real.rpow_le_rpow_of_exponent_le hr.1.le hvolumeExponent
  have hret := hr.2 θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ s hcanonical hunit
    hR hHholes hholes hHR hX₁ hX₂ hY₁ hY₂ hsource hpool hP hF cover η hη
    K ξfirst κpad W Tsecond H hK hWblock hξfirst.le hT hTcap hTupper hX hXupper hWupper hWinv
    hH hsourceH hHcap χ₀ msecond hmsecond hml2 hm22
    1 (by simp) one_ne_zero u (by simpa only [mul_one] using hu)
    hgeometry Ds hDs weight mass hmass hweight hDN Rexp Praw Sraw dsel lref c0 omega sigma loss BX hp0 hg0
  simp only [map_one,Nat.cast_one,div_one] at hret
  let m:=fixedBadMask*idealGenerator s.R
  let zeroPart : ℂ:=∑F∈Ds,((weight F/W:ℝ):ℂ)*zeroEnergy η m 1 t
    (sourceColumns sActual) (selectedCoefficient sActual ha 1 F) Φ K
  let retainedPart : ℂ:=∑F∈Ds,((weight F/W:ℝ):ℂ)*CenteredMomentFirstSectorLocalization.retainedEnergy η m 1 t
    (sourceColumns sActual) (selectedCoefficient sActual ha 1 F) Φ K (sourceVolume s) Z ξfirst
  let tailPart : ℂ:=∑F∈Ds,((weight F/W:ℝ):ℂ)*discardedEnergy η m 1 t
    (sourceColumns sActual) (selectedCoefficient sActual ha 1 F) Φ K (sourceVolume s) Z ξfirst
  have hz := hzero ι a b sActual hcard ha (zero_lt_one.trans_le hb) 1 η m 1 t K W Φ hK.le hWblock
    Ds weight (fun F hF=>(hweight F hF).1)
  have htt := ht.2 ι a sActual hcard ha (zero_le_one.trans hb) 1 η m 1 t K W Φ hK hWblock
    hpool hvolume hKcap hKinv Ds weight (fun F hF=>(hweight F hF).1)
  have hz' : ‖zeroPart‖/sourceVolume s≤((∑F∈Ds,weight F)/W)*
      (Czero*K*(profileCap s)^2*‖paperRadialFourier Φ 0‖*
        (b^2*(2:ℝ)^Fintype.card ι/pairNorm s.d)*(sourceNormCap s.P b s.T s.d)^ε) := by
    dsimp only [zeroPart]
    rw [average_normalization Ds weight W (sourceVolume s) hWblock]
    exact hz
  have ht' : ‖tailPart‖/sourceVolume s≤((∑F∈Ds,weight F)/W)*
      (Ctail*(profileCap s)^2*tailControl.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(-saving)) := by
    dsimp only [tailPart]
    rw [average_normalization Ds weight W (sourceVolume s) hWblock]
    exact htt
  have hml : goodLambda∣m :=
    (show goodLambda∣fixedBadMask from dvd_mul_right _ _).trans (dvd_mul_right _ _)
  have hm2 : (2:O)∣m :=
    (show (2:O)∣fixedBadMask from dvd_mul_left _ _).trans (dvd_mul_right _ _)
  have hsplit : (∑F∈Ds,((weight F/W:ℝ):ℂ)*finiteHeckeEnergy η m 1 t
      (sourceColumns sActual) (selectedCoefficient sActual ha 1 F) Φ K)=
      zeroPart+retainedPart+tailPart := by
    simp_rw [finiteHeckeEnergy_sector_localized η m 1 t hml hm2
      (sourceColumns sActual) (selectedCoefficient sActual ha 1 _) Φ K (sourceVolume s) Z ξfirst hK]
    simp only [mul_add,Finset.sum_add_distrib]
    rfl
  change ‖∑F∈Ds,((weight F/W:ℝ):ℂ)*finiteHeckeEnergy η m 1 t
    (sourceColumns sActual) (selectedCoefficient sActual ha 1 F) Φ K‖/sourceVolume s≤_
  rw [hsplit]
  have htri : ‖zeroPart+retainedPart+tailPart‖≤‖zeroPart‖+‖retainedPart‖+‖tailPart‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_add_le zeroPart retainedPart) (le_refl ‖tailPart‖))
  apply (div_le_div_of_nonneg_right htri (sourceVolume_pos s).le).trans
  rw [add_div,add_div]
  calc
    _≤((∑F∈Ds,weight F)/W)*
        (Czero*K*(profileCap s)^2*‖paperRadialFourier Φ 0‖*
          (b^2*(2:ℝ)^Fintype.card ι/pairNorm s.d)*(sourceNormCap s.P b s.T s.d)^ε)+
      Csum*retainedFactor U c s η Q c0 t V K mass Cpush Ckernel ε*Z^(loss+5*Btail*ε+εsum)+
      ((∑F∈Ds,weight F)/W)*
        (Ctail*(profileCap s)^2*tailControl.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(-saving)) :=
      add_le_add (add_le_add hz' hret) ht'
    _=_ := by ring

end
end Candidate.FourthPower.MixedFirstFullEnergy
