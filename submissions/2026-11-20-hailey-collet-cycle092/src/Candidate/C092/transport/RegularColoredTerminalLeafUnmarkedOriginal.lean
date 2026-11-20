/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual returned unmarked P6 source is applied to the original short
profile and summed over its genuine attaining descriptor rows. -/
import Candidate.C092.transport.P2CommonSourceMetadataReady
import Candidate.C092.transport.RegularColoredTerminalLeafOriginalScale
import Candidate.C092.transport.TerminalActualInverseApplyOriginal
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open CenteredMomentEnergyBands CenteredMomentWholeSlotDeletion CenteredMomentFiniteProfileExceptional
open HeckeDetectorDyadicProfiles
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows HeckeDetectorZeros HeckeDetectorRowwisePolynomial
open ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentHeckeSlots HeckePrimeAnnular
open QRH.Cycle092.WholeSlot
open CenteredMomentPrimeSlot CenteredMomentDetectorPlainFiberSource
open QRH.Cycle092.PairMarkAnchor QRH.Cycle092.TinyCore QRH.Cycle092.MediumReplace.Source
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source QRH.Cycle092.SourceFurtherWitness
open QRH.Cycle092.StrongPair QRH.Cycle092.LowActual QRH.Cycle092.TerminalActualRow
open QRH.Cycle092.P2CommonSourceMetadata
open QRH.Cycle092.RegularColoredForward QRH.Cycle092.SourceInverseP6 QRH.Cycle092.MediumInversePrice
open QRH.Cycle092.OrdinaryColumn Qrh.MarkedAnchor.Interface
local notation "O" =>  HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_RegularColoredTerminalLeafUnmarkedOriginal_d287ad72af8d8291_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

theorem terminal_ready_unmarked_original_at (Slot : Type) [Fintype Slot] (M : Ideal O) [NeZero M] (A : Arithmetic M)
    (n yCell e0 nu0 loss heightLoss : ℝ) (c : Cutoff) (step δ fee : ℝ)
    (εm nativeError N quota dmin dmax price nm buffer : ℝ)
    (P : UnmarkedPacket Slot M A n yCell e0 nu0 loss heightLoss c step δ fee
      εm nativeError N quota dmin dmax price nm buffer) (dBank : Finset ℝ) (G : LateGeometry dmin dmax dBank) (db : dBank) (Bshort : ℝ)
    (Rdy : ReadyUnmarked Slot M A n yCell e0 nu0 loss heightLoss c step δ fee
      εm nativeError N quota dmin dmax price nm buffer P dBank G db Bshort)
    (he0 : 0<e0) (I : ℕ) (Cslot Z : ℝ) (hCslot : 0<Cslot)
    (hAt : UnmarkedAt Slot M A n yCell e0 nu0 loss heightLoss c step δ fee
      εm nativeError N quota dmin dmax price nm buffer P dBank G db Bshort Rdy.order Rdy.Cy I Cslot Z)
    (hcover : ∀(η η₀ : Character) (θ : Slot→RayQuotient.Characters M A.Hr)
      (w v : Slot→ℝ) (t : ℝ) (rows : Finset FreeRow),(∀j,0≤w j) →
      (∀u∈rows,0 < measured M A.Hr A.hHr η η₀ A.W Z (Cslot*Z^buffer) θ w v t u) →
      ∀u∈rows,∃jd,u∈descriptorRows M A.Hr A.hHr rows η η₀ A.W Z (Cslot*Z^buffer) (buffer/2) θ w v t jd) :
    1<Z ∧
    ∀ d : ℝ,dmin ≤ d → d ≤ dmax → G.Mcap db+G.Bmask+G.margin ≤ d →
    ∀ s : NaturalState Z G.Bmask A.bΦ,s.width ≤ G.Mcap db → s.character=A.ηShort → s.puncture=1 →
    ∀ (hsM : s.fixedModulus ≤ M) (hsη : s.fixedModulus ≤ A.baseShort.modulus)
      (rows : Finset FreeRow) (hkeep : ∀ u∈rows,s.radial.keep u.val),
      (∀ u∈rows,s.radial.profile (‖ConcreteTraceCRT.eisEmbedding u.val‖^2/s.radial.scale) ≠ 0) →
      (∀ u∈rows,rowNorm u ≤ Z^d) →
    ∀ (K Je Jν : ℕ) (ε : ℝ)
      (level : rows→Fin (I+1)) (band : rows→Fin (K+1))
      (window : rows→Fin Je×Fin Jν) (cutoffTable : Fin Je×Fin Jν→ℝ)
      (parentWS : ∀ u : rows,SupportedWitness
        (family M A.Hr A.hHr s A.baseShort (naturalRow s.character u.val.val u.val.property.1))
        (Z^d) ((51/100:ℝ)+G.ez*(band u).val) ε (cutoffTable (window u))
        (Z^G.τ) ((Z^d)^(G.τ/(2*dmax))) (level u).val)
      (tag : Fin (I+1)×Fin (K+1)×(Fin Je×Fin Jν)×
        Option (RayQuotient.Characters M A.Hr×RayQuotient.Characters M A.Hr)×
        Fin (dyadicLength (Z^d))×Fin (dyadicLength (Z^d))),
    let parentRows := rows;
    let a := (51/100:ℝ)+G.ez*tag.2.1.val;
    let i := tag.1.val;
    let cutoff := cutoffTable tag.2.2.1;
    let T := Z^G.τ;
    let allowance := (Z^d)^(G.τ/(2*dmax));
    let label := tag.2.2.2.1;
    let left := tag.2.2.2.2.1;
    let right := tag.2.2.2.2.2;
    let r := Real.logb (Z^d) ((2:ℝ)^left.val);
    let rows := classRows parentRows (terminalWitnessKey level band window cutoffTable parentWS) tag;
      a ≤ 1 →
      (∀ u : parentRows,HeckeDetectorZeros.zeroMaximum
        (family M A.Hr A.hHr s A.baseShort (naturalRow s.character u.val.val u.val.property.1))
        (family_nonprincipal M A.Hr A.hHr s A.baseShort hsM hsη (hkeep u.val u.property)
          (naturalRow s.character u.val.val u.val.property.1))
        (3*((level u).val+1 : ℕ)*Z^G.τ) < ((51/100:ℝ)+G.ez*(band u).val)+2*G.ez) →
      0 ≤ ε → ε ≤ 1/1000 → 1 ≤ cutoff → cutoff ≤ 3/2 →
    ∀ (q : Profiles (1/4) (9/4)) (tShort Y : ℝ),
      0 ≤ yCell → yCell/d ≤ G.R → 0 < Y → Y ≤ Z^yCell →
      (∀ x,‖twistProfile (q.profile 1) 0 tShort x‖ ≤ Bshort) →
      |tShort|+Z^G.τ/2 ≤ (3*i+2 : ℕ)*Z^G.τ →
      (∀ x∈Icc (1-a-6*G.ez) 2,∀ t:ℝ,
        (1+|t|)^2*‖mellin (q.profile 1) ((x:ℂ)+t*Complex.I)‖ ≤ 1) →
      (∀ kl : Fin (nativeK buffer dmax+1),∀ x∈Icc (1-a-6*G.ez) 2,∀ t:ℝ,
        (1+|t|)^(Rdy.order kl+2)*‖mellin (q.profile 1) ((x:ℂ)+t*Complex.I)‖ ≤ 1) →
      (∀ kl,sourceControl (P.controls kl) (q.profile 0) ≤ 1) →
    ∀ (θ θLong : Slot→RayQuotient.Characters M A.Hr) (w v vLong : Slot→ℝ)
      (tMark tLong slotHeight eu L X V : ℝ),
      (∀ j,0 ≤ w j) → (∀ j,w j/d ≤ nm) →
      0 ≤ slotHeight → (∀ j,|v j| ≤ slotHeight) → (∀ j,|vLong j| ≤ slotHeight) →
      (∀ u∈rows,∀ j,‖descriptor M A.Hr A.hHr A.ηShort A.baseShort A.W Z θ w v tMark u j‖=
        ‖normalizedSlot A.ηLong (fixedBadMask*idealGenerator 1) 1 u.val (primePool M A.Hr 2 (Z^(w j)))
          (fun I=>idealCoeff (relativeCharacter M A.Hr A.hHr A.baseLong (θLong j)) I*
            HeckePrimeAnnular.annularWeight A.W (Z^(w j)) (33/50) (vLong j) I) tLong (Z^(w j))‖) →
      0 ≤ eu →
      (∑ j,w j) ≤ L →
      0 < X → length (Z^d) X ≤ N →
      (∀ u∈rows,initialKeep A.ηLong (internalQ A.QLong A.baseLong) u.val) →
      (98/100:ℝ) ≤ V → V ≤ d → d ≤ V+3*δ →
      nu0 ≤ 2*a-1+price → 2*a-1 ≤ nu0+step → eu ≤ e0+step →
      (c.inverse:ℝ) ≤ r → cutoff=totalCutoff c → ε ≤ fee →
      0 ≤ L → L ≤ 1 → L ≤ sourceWidth n yCell-(u:ℝ) →
      2*NativeFourthEffective.credit n d-d*quota ≤ fee/2 →
      (r ≤ 1 → inverseQuota r ≤ fee) →
      d*G.ε+(d*(2*ε+εm)+d*nativeError)/2+buffer*(Fintype.card Slot:ℝ) ≤ fee →
      |tMark|+|tLong|+slotHeight ≤ Z^G.τ →
      (∀ u∈rows,e0 ≤ measured M A.Hr A.hHr A.ηShort A.baseShort A.W Z (Cslot*Z^buffer) θ w v tMark u) →
      (∀ u∈rows,measured M A.Hr A.hHr A.ηShort A.baseShort A.W Z (Cslot*Z^buffer) θ w v tMark u ≤ eu) →
    ∀physical : Slot→FreeRow→ℂ,
      (∀u∈rows,∀j,‖physical j u‖=‖descriptor M A.Hr A.hHr A.ηShort A.baseShort A.W Z θ w v tMark u j‖) →
      StrongPair.finiteEnergyOn Finset.univ rows A.ηLong s.character (q.profile 0) (q.profile 1)
        tLong tShort X Y physical ≤
      (Fintype.card Slot:ℝ)*(∑ k : Fin (nativeK buffer dmax+1),
        Cslot^(Fintype.card Slot)*Rdy.Cy k*(192*P.Cc k+1)*
        (P.Cl k*QuadraticInitialBound.diagonalControl radialMajorant+1)*
        (2+2*Real.pi+(3*I:ℕ))^(P.Jc k+1)*(3:ℝ)^(P.degree k))*
      Z^(V+radialAllowance V+loss+heightLoss) := by
  classical
  refine ⟨hAt.1,?_⟩
  intro d hd hd' hds s hs hschar hsp hsM hsη parentRows hkeep hΦ hrow K Je Jν ε level band window cutoffTable parentWS tag
  dsimp only
  intro ha hnext hε hεsmall hcut0 hcut1 q tShort Y hy0 hyR hY hYcap hsup hfreq hmel2 hmel hctl θ θLong w v vLong tMark tLong slotHeight eu L X V
    hw hmesh hh hv hvLong hmarkLong heu hwidth hX hXN hkeepLong hV hdV hdc hν0 hν1 heu' hcut hcutoff hεfee hL hL1 hLwidth hcredit htop hfees hheight hresponse0 hresponse1 physical hphysical
  let key := terminalWitnessKey level band window cutoffTable parentWS
  let rows := classRows parentRows key tag
  have hsub : rows⊆parentRows := classRows_subset parentRows key tag
  have hmask : s.mask=fixedBadMask*idealGenerator 1 := by simp only [NaturalState.mask,hsp]
  have hpositive : ∀u∈rows,0 < measured M A.Hr A.hHr A.ηShort A.baseShort A.W Z (Cslot*Z^buffer) θ w v tMark u :=
    fun u hu=>he0.trans_le (hresponse0 u hu)
  have hcoverRows : ∀u∈rows,∃jd,u∈descriptorRows M A.Hr A.hHr rows A.ηShort A.baseShort A.W Z (Cslot*Z^buffer) (buffer/2) θ w v tMark jd :=
    hcover A.ηShort A.baseShort θ w v tMark rows hw hpositive
  let C : Fin (nativeK buffer dmax+1)→ℝ := fun k=>
    Cslot^(Fintype.card Slot)*Rdy.Cy k*(192*P.Cc k+1)*
      (P.Cl k*QuadraticInitialBound.diagonalControl radialMajorant+1)*
      (2+2*Real.pi+(3*I:ℕ))^(P.Jc k+1)*(3:ℝ)^(P.degree k)
  have hC (k) : 0≤C k := by
    have hc := Rdy.positive k
    have hp := P.positive k
    have hpc := hp.1
    have hpl := hp.2
    have hdg := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
    dsimp [C]
    positivity
  apply terminal_actual_attainer_aggregate M A.Hr A.hHr rows A.ηShort A.baseShort A.W Z (Cslot*Z^buffer) (buffer/2)
    θ w v tMark A.ηLong s.character (q.profile 0) (q.profile 1) tLong tShort X Y physical
    (V+radialAllowance V+loss+heightLoss) (by linarith [hAt.1]) C hC hcoverRows
  intro jd hjd
  have happ := hAt.2 d hd hd' hds s hs hschar hsp hsM hsη parentRows hkeep hΦ hrow K Je Jν ε level band window cutoffTable parentWS tag
    ha hnext hε hεsmall hcut0 hcut1 (fun _=>q.profile 1) (fun _=>1/4) (fun _=>9/4) (fun _=>0) (fun _=>tShort) Y
    hy0 hyR hY hYcap (fun _ _=>by norm_num) (fun _ _=>q.support 1) (fun _ _=>(q.profile 1).smooth ⊤)
    (fun _ _=>TerminalActualInverseApply.twist_profile_support (q.support 1)) (fun _ _=>hsup) (fun _ _=>hfreq)
    (fun u hu x hx t=>hmel2 x (by simpa only [sub_zero] using hx) t)
    (fun kl u hu x hx t=>hmel kl x (by simpa only [sub_zero] using hx) t)
    θ θLong w v vLong tMark tLong slotHeight eu L X V
    hw hmesh hh hv hvLong hmarkLong heu hwidth hX hXN hkeepLong hV hdV hdc hν0 hν1 heu' hcut hcutoff hεfee hL hL1 hLwidth hcredit htop hfees hheight
    jd q 0 hjd
    (fun u hu=>hresponse0 u (Finset.mem_filter.mp hu).1)
    (fun u hu=>hresponse1 u (Finset.mem_filter.mp hu).1)
  obtain ⟨kl,hbound⟩ := happ
  refine ⟨kl,?_⟩
  have heq := terminal_original_product_source s
    (descriptorRows M A.Hr A.hHr rows A.ηShort A.baseShort A.W Z (Cslot*Z^buffer) (buffer/2) θ w v tMark jd)
    (fun u hu=>hkeep u (hsub (Finset.mem_filter.mp hu).1)) A.ηLong hmask (q.profile 0) (q.profile 1) (q.support 1)
    tLong tShort X Y hY physical (fun j u=>descriptor M A.Hr A.hHr A.ηShort A.baseShort A.W Z θ w v tMark u j)
    (fun u hu j=>hphysical u (Finset.mem_filter.mp hu).1 j)
  rw [heq] at hbound
  apply hbound.trans
  have hct0 := sourceControl_nonneg (P.controls kl) (q.profile 0)
  have hct := hctl kl
  have hpow : (sourceControl (P.controls kl) (q.profile 0))^4≤(1:ℝ) := by
    simpa only [one_pow] using pow_le_pow_left₀ hct0 hct 4
  have hpos := P.positive kl
  have hCc := hpos.1
  have hCl := hpos.2
  have hCy := Rdy.positive kl
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
  have hZ0 : 0<Z := by linarith [hAt.1]
  dsimp only [C]
  calc
    _ ≤ (Cslot^(Fintype.card Slot)*Rdy.Cy kl*(192*P.Cc kl+1)*
        (P.Cl kl*QuadraticInitialBound.diagonalControl radialMajorant*(1:ℝ)+1)*
        (2+2*Real.pi+(3*I:ℕ))^(P.Jc kl+1)*(3:ℝ)^(P.degree kl))*
        Z^(V+radialAllowance V+loss+heightLoss) := by
      gcongr <;> positivity
    _ = _ := by simp only [mul_one]

#print axioms terminal_ready_unmarked_original_at
end
end QRH.Cycle092.RegularColoredForward
