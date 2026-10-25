/- Copyright (c) 2026 Sil. Apache-2.0.
Actual grouped first energy with constructed band geometry and explicit
fiber/push losses. No energy, BandGeometry, or grouped mass estimate is
an input.
-/
import Candidate.Feedback.FourthPower.MixedFirstFullEnergy
import Candidate.Feedback.FourthPower.MixedFirstActualBandGeometry
import Candidate.Feedback.FourthPower.MixedFirstSelectedMass
import Candidate.Feedback.FourthPower.MixedFirstProfileEnvelope

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.Feedback.FourthPower.MixedFirstUniformEnergy
universe u v
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcretePrimeRowBridge ActualEisensteinCubic RayFourExpansion
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily
open CenteredMomentFiniteProfileExceptional
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedOriginalNormCap MixedOriginalTail MixedInnerExceptionalBlock MixedHeightEnvelope
open MixedFirstActualNonexceptional MixedFirstFullBudget MixedFirstExceptionalApplication
open MixedFirstAvoidance MixedFirstPhysicalApplication MixedFirstIntegratedWindows
open MixedFirstPaidCosts MixedFirstPaidRetained MixedFirstGeometricCaps
open MixedFirstFullEnergy MixedFirstActualBandGeometry MixedFirstCutoffs
open MixedFirstProfileEnvelope MixedFirstSelectedMass
open MixedCompletedRows ReferencePrimeEnclosure EisensteinSchwartzPoisson
open QRH.Record1252270103KernelMass (pairNorm)
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι]

/- Scalar monotonicity is separated from dependent Source records to
keep elaboration finite. This is only an inequality of real numbers. -/
private theorem full_cost_mono
    (Z Csum Cret Crem Cf Czero Ctail K Neta KslotPow Aprof Fzero Ftail dimcap
      retained prof mass dim cap r f z saving : ℝ)
    (hZ : 0<Z) (hCs : 0≤Csum) (hCr : 0≤Cret) (hCm : 0≤Crem) (hCf : 0≤Cf)
    (hCz : 0≤Czero) (hCt : 0≤Ctail) (hK : 0≤K) (hη : 0≤Neta)
    (hKs : 0≤KslotPow) (hA : 0≤Aprof) (hFz : 0≤Fzero) (hFt : 0≤Ftail)
    (hdimcap : 0≤dimcap) (hprof : 0≤prof) (hdim : 0≤dim) (hcap : 0≤cap)
    (hret : retained≤Cret*(Neta*K)*(Cf*KslotPow*Z^f)*Aprof)
    (hp : prof≤Crem*Aprof) (hm : mass≤256*(Cf*KslotPow*Z^f))
    (hd : dim≤dimcap) (hc : cap≤Z^z) :
    Csum*retained*Z^r+mass*(Czero*K*prof*Fzero*dim*cap+Ctail*prof*Ftail*Z^(-saving))≤
      Aprof*KslotPow*((Csum*Cret*Cf)*(Neta*K)*Z^(r+f)+
        (256*Cf*Czero*Crem*Fzero*dimcap)*K*Z^(z+f)+
        (256*Cf*Ctail*Crem*Ftail)*Z^(-saving+f)) := by
  have hpow (e : ℝ) : 0≤Z^e := Real.rpow_nonneg hZ.le _
  have hzero : Czero*K*prof*Fzero*dim*cap≤
      Czero*K*(Crem*Aprof)*Fzero*dimcap*Z^z := by
    gcongr
  have htail : Ctail*prof*Ftail*Z^(-saving)≤Ctail*(Crem*Aprof)*Ftail*Z^(-saving) := by
    gcongr
  have hrem0 : 0≤Czero*K*prof*Fzero*dim*cap+Ctail*prof*Ftail*Z^(-saving) := by positivity
  have hm0 : 0≤256*(Cf*KslotPow*Z^f) := by positivity
  have hrem := mul_le_mul hm (add_le_add hzero htail) hrem0 hm0
  have hr := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hret hCs) (hpow r)
  apply (add_le_add hr hrem).trans_eq
  rw [Real.rpow_add hZ r f,Real.rpow_add hZ z f,Real.rpow_add hZ (-saving) f]
  ring

private theorem three_constants (ar az atail n k x y z : ℝ)
    (hr : 0≤ar) (hz : 0≤az) (ht : 0≤atail)
    (hn : 0≤n) (hk : 0≤k) (hx : 0≤x) (hy : 0≤y) (hzz : 0≤z) :
    ar*(n*k)*x+az*k*y+atail*z≤(1+ar+az+atail)*(n*k*x+k*y+z) := by
  have h1 : ar≤1+ar+az+atail := by linarith
  have h2 : az≤1+ar+az+atail := by linarith
  have h3 : atail≤1+ar+az+atail := by linarith
  have hh := add_le_add (add_le_add
    (mul_le_mul_of_nonneg_right h1 (mul_nonneg (mul_nonneg hn hk) hx))
    (mul_le_mul_of_nonneg_right h2 (mul_nonneg hk hy)))
    (mul_le_mul_of_nonneg_right h3 hzz)
  convert hh using 1 <;> ring

variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- Complete selected first energy with one polynomial profile/height
factor. The source slot type is fixed before the constants, as in the
upstream FullEnergy theorem; the supplier slot type may vary freely.

BandGeometry, full-pool/source caps, second cutoff, selected mass and
profile caps are all derived. The remaining Gates and SourceGeometry
are only the original scalar mixed/native/reference inequalities.
The denominator is the actual padded selected scale.
-/
theorem uniform_grouped_first_energy
    (Φ : 𝓢(ℝ,ℂ)) (N Holes : ℕ) (hcard : Fintype.card ι≤N) (Wslot : ℝ→ℂ)
    (a b Mcap B Lslot Lcap Cap BR BH Bη ε δ lo hi ξfirst ξsecond κpad
      saving εsum δfiber cstar Kslot : ℝ)
    (hWs : Function.support Wslot⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ Wslot)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b) (hMcap0 : 0<Mcap)
    (hB : 1≤B) (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hBR : 0≤BR) (hBH : 0≤BH) (hCapb : b≤Cap) (hBcap : B≤Lcap)
    (hε : 0<ε) (hδ : 0<δ) (hgap : (7/10:ℝ)+2*δ<1)
    (hξfirst : 0<ξfirst) (hξsecond : 0<ξsecond) (hκpad : 0<κpad)
    (hMcap : geometryExponent (sourceExponent B) ξsecond+
      (Bη+sourceExponent B+ε)+sourceExponent B+ε≤Mcap)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hεsum : 0<εsum) (hδfiber : 0<δfiber) (hcstar : 0<cstar) (hKslot : 1≤Kslot)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus→
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : ι→RayQuotient.Characters M Hray)(w σ freq : ι→ℝ)(t V : ℝ)(R₀ : ι→Finset Id),
      (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
      0≤V→(∀i,|freq i|≤V)→(∀i,(R₀ i).card≤Holes)→
    ∀s : Source ι a b,Canonical M Hray hHray Wslot Cap Lcap Z η₀ θ w σ freq t R₀ s→
      s.d=(1,1)→(∀i,s.M i≤Kslot)→(s.R.absNorm:ℝ)≤Z^BR→
      s.H⊆enclosure (Cap*Z^Lcap)→((∏I∈holes s.H,I).absNorm:ℝ)≤Z^BH→
      (∀i,∀P∈s.H,P.val∈R₀ i)→(s.Fhole.absNorm:ℝ)≤Z^BH→
      Z^(-B)≤s.L→s.X₁≤Z^B→s.X₂≤Z^B→s.Y₁≤Z^B→s.Y₂≤Z^B→(∏i,s.P i)≤Z^B→
    ∀cover : OriginalEnclosure s,∀η : Character,(η.modulus.absNorm:ℝ)≤Z^Bη→
    ∀K : ℝ,0<K→K≤Z^B→K⁻¹≤Z^B→1≤sharpSupport s→
    ∀(χ₀ : RayCharacter)(msecond : O),msecond≠0→goodLambda∣msecond→(2:O)∣msecond→
    ∀u : Id,u∣s.R→∀(α : Type v) [Fintype α],∀q : MixedSupplierFourthRow.Data α,
      Fintype.card α≤N→(∀i,0<q.P i)→(∀i,∀I∈q.pool i,(I.absNorm:ℝ)≤2*q.P i)→
      (∀i,∀I∈q.pool i,‖q.ν i I‖≤1)→(∀i x,‖q.Wslot i x‖≤Kslot)→
      MixedSelectedVolume.scale q≤Z^B→(MixedSelectedVolume.scale q)⁻¹≤Z^B→
    ∀Rexp Praw Sraw dsel lref c0 omega sigma loss BX : ℝ,cstar≤c0→
    let p0 : Parameters :=
      { Z:=Z,Kfirst:=K,Tfirst:=0,Cfirst:=1,ξfirst:=ξfirst,κpad:=κpad,
        W:=MixedSelectedVolume.scale q,ε:=ε,δ:=δ,Bnorm:=normExponent B B ε,
        BG:=sourceExponent B,BX:=BX,R:=Rexp,P:=Praw,S:=Sraw,d:=dsel,l:=lref,c0:=c0,
        omega:=omega,sigma:=sigma,loss:=loss,saving:=saving }
    Gates p0→SourceGeometry p0 s η w→
    let Bt := tailExponent (sourceExponent B) ξfirst κpad
    let A := sourceControl control s.W₁*sourceControl control s.W₂
    let H := height t V s.t₁ s.t₂
    ‖∑F∈MixedSupplierPositive.selectedProducts q,
        ((MixedSupplierPositive.groupedWeight q F/MixedSelectedVolume.scale q:ℝ):ℂ)*
        finiteHeckeEnergy η (fixedBadMask*idealGenerator s.R) 1 t
          (sourceColumns (avoidSource s u)) (selectedCoefficient (avoidSource s u) ha 1 F) Φ K‖/
        sourceVolume s≤
      C*Kslot^(2*N)*A^2*H^J*
        ((η.modulus.absNorm:ℝ)*K*Z^(loss+5*Bt*ε+εsum+Bt*δfiber)+
          K*Z^(sourceExponent B*ε+Bt*δfiber)+Z^(-saving+Bt*δfiber)) := by
  let B0 := sourceExponent B
  let Bt := tailExponent B0 ξfirst κpad
  let Mg := geometryExponent B0 ξsecond
  have hB0 : 1≤B0 := by dsimp only [B0,sourceExponent];linarith
  have hBB0 : B≤B0 := by dsimp only [B0,sourceExponent];linarith
  have hB0t : B0≤Bt := by
    dsimp only [Bt,tailExponent,secondExponent,childExponent]
    linarith
  have hBt : 0≤Bt := (zero_le_one.trans hB0).trans hB0t
  have hBMg : 0≤Mg := by dsimp only [Mg,geometryExponent,secondExponent];linarith
  have hfreq : 0≤Bt+ξfirst/2 := by positivity
  have hvol : 2*B+B≤Bt := by
    have : 2*B+B≤B0 := by dsimp only [B0,sourceExponent];linarith
    exact this.trans hB0t
  obtain ⟨U,tailControl,Cpush,Ckernel,Csum,Czero,Ctail,hCpush,hCkernel,hCsum,hCzero,hCtail,hfull⟩ :=
    uniform_full_first_energy (ι:=ι) M Hray hHray Φ N Holes hcard Wslot
      a b Mcap B Lslot Lcap Cap BR B0 BH B0 Bη B Mg Bt ε δ lo hi ξfirst ξsecond
      saving (Bt+ξfirst/2) εsum hWs hW ha haUpper hb hMcap0 (zero_le_one.trans hB)
      hLslot hLcap hCap hBR (zero_le_one.trans hB0) hBH (zero_le_one.trans hB0)
      (zero_le_one.trans hB) hBMg hBt hB0t hCapb hBcap hε hδ hgap hξfirst hξsecond
      hMcap hβ hfreq hεsum hvol Q hQt hQ72 hQM
  obtain ⟨Cf,hCf,hweights⟩ := uniform_grouped_window.{v} N δfiber hδfiber
  have hgeometry := uniform_actual_band_geometry.{u} N b B ξfirst ξsecond κpad
    (zero_lt_one.trans_le hb) hB hξfirst.le hξsecond hκpad
  have hsharp := eventually_sharp_support.{u} N b 1 (by norm_num)
  refine ⟨heightDegree U,profileControl U,?_⟩
  intro η₀ hη₀
  obtain ⟨c,hfull⟩ := hfull η₀ hη₀
  obtain ⟨Cret,Crem,hCret,hCrem,hprofiles⟩ := uniform_first_costs U c Q
    a b cstar Kslot Cpush Ckernel ε ha hcstar hKslot hCpush.le hCkernel N
  let ar := Csum*Cret*Cf
  let az := 256*Cf*Czero*Crem*‖paperRadialFourier Φ 0‖*(b^2*(2:ℝ)^N)
  let atail := 256*Cf*Ctail*Crem*(tailControl.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)
  have har : 0≤ar := by dsimp only [ar];positivity
  have haz : 0≤az := by dsimp only [az];positivity
  have hat : 0≤atail := by dsimp only [atail];positivity
  refine ⟨1+ar+az+atail,by positivity,?_⟩
  filter_upwards [hfull,hgeometry,hsharp] with Z hfullZ hgeometryZ hsharpZ
  refine ⟨hfullZ.1,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreqs hR₀ s hcanonical hunit hMs
    hR hHholes hholes hHR hFhole hmin hX₁ hX₂ hY₁ hY₂ hP cover η hη
    K hK hKcap hKinv hX χ₀ msecond hm hml hm2 u hu α instα q hα hqP hqpool hqν hqW
    hWcap hWinv Rexp Praw Sraw dsel lref c0 omega sigma loss BX hfloor p0 hp0 hg0
  have hZ : 1<Z := hfullZ.1
  have hz : 0<Z := zero_lt_one.trans hZ
  let W := MixedSelectedVolume.scale q
  have hWpos : 0<W := MixedSelectedVolume.scale_pos q hqP
  let sActual := avoidSource s u
  have hg := hgeometryZ.2 ι a sActual ha hcard hmin hX₁ hX₂ hY₁ hY₂ hP
    K W hK hWpos hKcap hKinv hWcap hWinv
  have hsource : sourceNormCap s.P b s.T s.d≤Z^B0 := hg.2.1
  have hpool : poolCap s≤Z^B0 := hg.1
  have hgeom := hg.2.2 1 (Z^B0)
  have hvolcap := (source_volume_caps s Z B hZ hmin hX₁ hX₂ hP).1
  have hpair : pairNorm s.d=1 := by simp only [hunit,pairNorm,map_one,Nat.cast_one,mul_one]
  have hxcap : sharpSupport s≤Z^B0 := by
    have hh := hsharpZ.2 ι a s hcard (3*B) hvolcap
    simpa only [hpair,div_one,B0,sourceExponent] using hh
  have hBtmono : Z^B0≤Z^Bt := Real.rpow_le_rpow_of_exponent_le hZ.le hB0t
  have hBmono : Z^B≤Z^Bt := Real.rpow_le_rpow_of_exponent_le hZ.le (hBB0.trans hB0t)
  have hT : 0≤secondCutoff B0 Z := Real.rpow_nonneg hz.le _
  have hTcap : secondCutoff B0 Z≤Z^(Mg-ξsecond) := by
    dsimp only [secondCutoff,Mg,geometryExponent]
    rw [add_sub_cancel_right]
  have hTupper : secondCutoff B0 Z≤Z^Bt := by
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp only [Bt,tailExponent,childExponent]
    linarith
  have hDN (F : Id) (hF : F∈MixedSupplierPositive.selectedProducts q) : (F.absNorm:ℝ)≤2*W :=
    (MixedSelectedVolume.selected_products_norm q hqpool F hF).trans (by linarith)
  let mass := Cf*Kslot^(2*N)*Z^(Bt*δfiber)
  have hmass : 0≤mass := by dsimp only [mass];positivity
  have hweight := hweights α q hα Kslot hKslot hqν hqW Z W Bt hZ.le hWpos
    (hWcap.trans hBmono) hDN
  have hbound := hfullZ.2 θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreqs hR₀ s
    hcanonical hunit hR hHholes hholes hHR hX₁ hX₂ hY₁ hY₂ hsource (hpool.trans hBtmono)
    hP hFhole cover η hη K κpad W (secondCutoff B0 Z) (Z^B0) hK hWpos
    (hKcap.trans hBmono) (hKinv.trans hBmono) hT hTcap hTupper hX (hxcap.trans hBtmono)
    (hWcap.trans hBmono) (hWinv.trans hBmono) (Real.rpow_pos_of_pos hz _) hsource (le_refl _)
    χ₀ msecond hm hml hm2 u hu hgeom
    (MixedSupplierPositive.selectedProducts q) (MixedSupplierPositive.selected_products_supported q)
    (MixedSupplierPositive.groupedWeight q) mass hmass hweight.1 hDN
    Rexp Praw Sraw dsel lref c0 omega sigma loss BX hp0 hg0
  let A := sourceControl (profileControl U) s.W₁*sourceControl (profileControl U) s.W₂
  let H := height t V s.t₁ s.t₂
  let Ap := A^2*H^(heightDegree U)
  have hH : 1≤H := by
    dsimp only [H,height]
    linarith [abs_nonneg t,norm_nonneg s.t₁,norm_nonneg s.t₂]
  have hAp : 0≤Ap := mul_nonneg (sq_nonneg A) (pow_nonneg (zero_le_one.trans hH) _)
  have hprof := hprofiles ι s hcard hunit hMs c0 t V hfloor hV
  have hret := hprof.2 η K mass hK.le hmass
  have hprof' : (profileCap s)^2≤Crem*Ap :=
    hprof.1.trans_eq (by dsimp only [Ap,A,H];ring)
  have hret' : retainedFactor U c s η Q c0 t V K mass Cpush Ckernel ε≤
      Cret*((η.modulus.absNorm:ℝ)*K)*(Cf*Kslot^(2*N)*Z^(Bt*δfiber))*Ap :=
    hret.trans_eq (by dsimp only [Ap,A,H,mass];ring)
  have hdim : b^2*(2:ℝ)^Fintype.card ι/pairNorm s.d≤b^2*(2:ℝ)^N := by
    rw [hpair,div_one]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hcard) (sq_nonneg b)
  have hsource0 : 0≤sourceNormCap s.P b s.T s.d := by
    rw [MixedFirstLiveRemainders.source_cap_factored,hpair,div_one]
    exact mul_nonneg (mul_nonneg (sq_nonneg b) (pow_nonneg (by norm_num) _))
      (mul_nonneg s.total_pos.le (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.hP i))))
  have hcap : (sourceNormCap s.P b s.T s.d)^ε≤Z^(B0*ε) := by
    apply (Real.rpow_le_rpow hsource0 hsource hε.le).trans_eq
    exact (Real.rpow_mul hz.le _ _).symm
  have hpay := full_cost_mono Z Csum Cret Crem Cf Czero Ctail K (η.modulus.absNorm:ℝ)
    (Kslot^(2*N)) Ap ‖paperRadialFourier Φ 0‖
    (tailControl.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ) (b^2*(2:ℝ)^N)
    (retainedFactor U c s η Q c0 t V K mass Cpush Ckernel ε) ((profileCap s)^2)
    ((∑F∈MixedSupplierPositive.selectedProducts q,MixedSupplierPositive.groupedWeight q F)/W)
    (b^2*(2:ℝ)^Fintype.card ι/pairNorm s.d) ((sourceNormCap s.P b s.T s.d)^ε)
    (loss+5*Bt*ε+εsum) (Bt*δfiber) (B0*ε) saving
    hz hCsum.le hCret.le hCrem.le hCf.le hCzero.le hCtail.le hK.le (Nat.cast_nonneg _)
    (pow_nonneg (zero_le_one.trans hKslot) _) hAp (norm_nonneg _) (by positivity)
    (by positivity) (sq_nonneg _) (by rw [hpair];positivity)
    (Real.rpow_nonneg hsource0 _) hret' hprof' hweight.2 hdim hcap
  apply (hbound.trans hpay).trans
  have hcoef := three_constants ar az atail (η.modulus.absNorm:ℝ) K
    (Z^(loss+5*Bt*ε+εsum+Bt*δfiber)) (Z^(B0*ε+Bt*δfiber)) (Z^(-saving+Bt*δfiber))
    har haz hat (Nat.cast_nonneg _) hK.le (Real.rpow_nonneg hz.le _)
    (Real.rpow_nonneg hz.le _) (Real.rpow_nonneg hz.le _)
  have hh := mul_le_mul_of_nonneg_left hcoef
    (mul_nonneg hAp (pow_nonneg (zero_le_one.trans hKslot) (2*N)))
  convert hh using 1 <;> (try dsimp only [Ap,A,H,ar,az,atail,B0,Bt]) <;> ring

/- Append inside MixedFirstUniformEnergy, before its final `end` lines.
The existing imports, opens, universes, M/Hray/hHray and fixed type iota
are retained. Parent alone runs the pinned Lean checks. -/

/-- One actual grouped first-energy estimate for every live subset of
the fixed original slot type. J, control, C and the eventual event are
chosen before T and all original profiles/heights/allocations. The
canonical slot data are the literal restrictions of the original data.
Both ordinary orientations remain covered by the universal Source.
-/
theorem uniform_grouped_first_energy_subsets
    (Φ : 𝓢(ℝ,ℂ)) (N Holes : ℕ) (hcard : Fintype.card ι≤N) (Wslot : ℝ→ℂ)
    (a b Mcap B Lslot Lcap Cap BR BH Bη ε δ lo hi ξfirst ξsecond κpad
      saving εsum δfiber cstar Kslot : ℝ)
    (hWs : Function.support Wslot⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ Wslot)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b) (hMcap0 : 0<Mcap)
    (hB : 1≤B) (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hBR : 0≤BR) (hBH : 0≤BH) (hCapb : b≤Cap) (hBcap : B≤Lcap)
    (hε : 0<ε) (hδ : 0<δ) (hgap : (7/10:ℝ)+2*δ<1)
    (hξfirst : 0<ξfirst) (hξsecond : 0<ξsecond) (hκpad : 0<κpad)
    (hMcap : geometryExponent (sourceExponent B) ξsecond+
      (Bη+sourceExponent B+ε)+sourceExponent B+ε≤Mcap)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hεsum : 0<εsum) (hδfiber : 0<δfiber) (hcstar : 0<cstar) (hKslot : 1≤Kslot)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus→
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀T : Finset ι,
    ∀(θ : ι→RayQuotient.Characters M Hray)(w σ freq : ι→ℝ)(t V : ℝ)(R₀ : ι→Finset Id),
      (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
      0≤V→(∀i,|freq i|≤V)→(∀i,(R₀ i).card≤Holes)→
    ∀s : Source T a b,Canonical M Hray hHray Wslot Cap Lcap Z η₀
      (fun i=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val) (fun i=>freq i.val)
      t (fun i=>R₀ i.val) s→
      s.d=(1,1)→(∀i,s.M i≤Kslot)→(s.R.absNorm:ℝ)≤Z^BR→
      s.H⊆enclosure (Cap*Z^Lcap)→((∏I∈holes s.H,I).absNorm:ℝ)≤Z^BH→
      (∀i : T,∀P∈s.H,P.val∈R₀ i.val)→(s.Fhole.absNorm:ℝ)≤Z^BH→
      Z^(-B)≤s.L→s.X₁≤Z^B→s.X₂≤Z^B→s.Y₁≤Z^B→s.Y₂≤Z^B→(∏i,s.P i)≤Z^B→
    ∀cover : OriginalEnclosure s,∀η : Character,(η.modulus.absNorm:ℝ)≤Z^Bη→
    ∀K : ℝ,0<K→K≤Z^B→K⁻¹≤Z^B→1≤sharpSupport s→
    ∀(χ₀ : RayCharacter)(msecond : O),msecond≠0→goodLambda∣msecond→(2:O)∣msecond→
    ∀u : Id,u∣s.R→∀(α : Type v) [Fintype α],∀q : MixedSupplierFourthRow.Data α,
      Fintype.card α≤N→(∀i,0<q.P i)→(∀i,∀I∈q.pool i,(I.absNorm:ℝ)≤2*q.P i)→
      (∀i,∀I∈q.pool i,‖q.ν i I‖≤1)→(∀i x,‖q.Wslot i x‖≤Kslot)→
      MixedSelectedVolume.scale q≤Z^B→(MixedSelectedVolume.scale q)⁻¹≤Z^B→
    ∀Rexp Praw Sraw dsel lref c0 omega sigma loss BX : ℝ,cstar≤c0→
    let p0 : Parameters :=
      { Z:=Z,Kfirst:=K,Tfirst:=0,Cfirst:=1,ξfirst:=ξfirst,κpad:=κpad,
        W:=MixedSelectedVolume.scale q,ε:=ε,δ:=δ,Bnorm:=normExponent B B ε,
        BG:=sourceExponent B,BX:=BX,R:=Rexp,P:=Praw,S:=Sraw,d:=dsel,l:=lref,c0:=c0,
        omega:=omega,sigma:=sigma,loss:=loss,saving:=saving }
    Gates p0→SourceGeometry p0 s η (fun i=>w i.val)→
    let Bt := tailExponent (sourceExponent B) ξfirst κpad
    let A := sourceControl control s.W₁*sourceControl control s.W₂
    let H := height t V s.t₁ s.t₂
    ‖∑F∈MixedSupplierPositive.selectedProducts q,
        ((MixedSupplierPositive.groupedWeight q F/MixedSelectedVolume.scale q:ℝ):ℂ)*
        finiteHeckeEnergy η (fixedBadMask*idealGenerator s.R) 1 t
          (sourceColumns (avoidSource s u)) (selectedCoefficient (avoidSource s u) ha 1 F) Φ K‖/
        sourceVolume s≤
      C*Kslot^(2*N)*A^2*H^J*
        ((η.modulus.absNorm:ℝ)*K*Z^(loss+5*Bt*ε+εsum+Bt*δfiber)+
          K*Z^(sourceExponent B*ε+Bt*δfiber)+Z^(-saving+Bt*δfiber)) := by
  have hcardT (T : Finset ι) : Fintype.card T≤N := by
    rw [Fintype.card_coe]
    exact (Finset.card_le_card (Finset.subset_univ T)).trans (by simpa using hcard)
  choose JT controlT hbase using fun T : Finset ι=>
    uniform_grouped_first_energy (ι:=T) M Hray hHray Φ N Holes (hcardT T) Wslot
      a b Mcap B Lslot Lcap Cap BR BH Bη ε δ lo hi ξfirst ξsecond κpad
      saving εsum δfiber cstar Kslot hWs hW ha haUpper hb hMcap0 hB hLslot hLcap
      hCap hBR hBH hCapb hBcap hε hδ hgap hξfirst hξsecond hκpad hMcap hβ
      hεsum hδfiber hcstar hKslot Q hQt hQ72 hQM
  let J := ∑T : Finset ι,JT T
  let control := (Finset.univ : Finset (Finset ι)).biUnion controlT
  have hJT (T : Finset ι) : JT T≤J :=
    Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ T)
  have hcontrol (T : Finset ι) : controlT T⊆control :=
    Finset.subset_biUnion_of_mem controlT (Finset.mem_univ T)
  refine ⟨J,control,?_⟩
  intro η₀ hη₀
  choose CT hCT hbase using fun T : Finset ι=>hbase T η₀ hη₀
  let C := 1+∑T : Finset ι,CT T
  have hC : 0<C := by
    have hn := Finset.sum_nonneg (fun T (_ : T∈(Finset.univ : Finset (Finset ι)))=>(hCT T).le)
    dsimp only [C]
    linarith
  have hCTle (T : Finset ι) : CT T≤C := by
    have hh := Finset.single_le_sum (s:=Finset.univ) (f:=CT)
      (fun U _=>(hCT U).le) (Finset.mem_univ T)
    dsimp only [C]
    linarith
  refine ⟨C,hC,(Filter.eventually_all.mpr hbase).mono ?_⟩
  intro Z hZ
  refine ⟨(hZ ∅).1,?_⟩
  intro T θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreqs hR₀ s hcanonical hunit hMs
    hR hHholes hholes hHR hFhole hmin hX₁ hX₂ hY₁ hY₂ hP cover η hη
    K hK hKcap hKinv hX χ₀ msecond hm hml hm2 u hu α instα q hα hqP hqpool hqν hqW
    hWcap hWinv Rexp Praw Sraw dsel lref c0 omega sigma loss BX hfloor p0 hp0 hg0
  have he := (hZ T).2 (fun i=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val)
    (fun i=>freq i.val) t V (fun i=>R₀ i.val)
    (fun i=>hw i.val) (fun i=>hwL i.val) (fun i=>hσ i.val) (fun i=>hσhi i.val)
    hV (fun i=>hfreqs i.val) (fun i=>hR₀ i.val) s hcanonical hunit hMs
    hR hHholes hholes hHR hFhole hmin hX₁ hX₂ hY₁ hY₂ hP cover η hη
    K hK hKcap hKinv hX χ₀ msecond hm hml hm2 u hu α q hα hqP hqpool hqν hqW
    hWcap hWinv Rexp Praw Sraw dsel lref c0 omega sigma loss BX hfloor hp0 hg0
  have hprofile : sourceControl (controlT T) s.W₁*sourceControl (controlT T) s.W₂≤
      sourceControl control s.W₁*sourceControl control s.W₂ :=
    mul_le_mul (MixedPrincipalPositivePart.control_mono (hcontrol T) s.W₁)
      (MixedPrincipalPositivePart.control_mono (hcontrol T) s.W₂)
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hprofile0 : 0≤sourceControl (controlT T) s.W₁*sourceControl (controlT T) s.W₂ :=
    mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hprofileSq := pow_le_pow_left₀ hprofile0 hprofile 2
  have hheight : 1≤height t V s.t₁ s.t₂ := by
    unfold height
    linarith [abs_nonneg t,norm_nonneg s.t₁,norm_nonneg s.t₂]
  have hheightPow := pow_le_pow_right₀ hheight (hJT T)
  have hslot0 : 0≤Kslot^(2*N) := pow_nonneg (zero_le_one.trans hKslot) _
  have hz : 0<Z := zero_lt_one.trans (hZ T).1
  have hcost : 0≤(η.modulus.absNorm:ℝ)*K*
      Z^(loss+5*(tailExponent (sourceExponent B) ξfirst κpad)*ε+εsum+
        (tailExponent (sourceExponent B) ξfirst κpad)*δfiber)+
      K*Z^(sourceExponent B*ε+(tailExponent (sourceExponent B) ξfirst κpad)*δfiber)+
      Z^(-saving+(tailExponent (sourceExponent B) ξfirst κpad)*δfiber) := by positivity
  dsimp only at he ⊢
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ hcost
  have hc := mul_le_mul_of_nonneg_right (hCTle T) hslot0
  have hp := mul_le_mul hc hprofileSq (sq_nonneg _)
    (mul_nonneg hC.le hslot0)
  exact mul_le_mul hp hheightPow (pow_nonneg (zero_le_one.trans hheight) _)
    (mul_nonneg (mul_nonneg hC.le hslot0) (sq_nonneg _))

end
end Candidate.Feedback.FourthPower.MixedFirstUniformEnergy
