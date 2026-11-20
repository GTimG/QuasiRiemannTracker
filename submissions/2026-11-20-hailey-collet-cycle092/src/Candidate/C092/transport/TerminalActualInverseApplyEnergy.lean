/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
P.6 with independent retained-long relative base. Adapted from the checked
SourceInverseP6Actual proof; the actual source dictionary keeps its original
base while the retained long prime slot is re-anchored separately. -/
import Candidate.C092.transport.TerminalActualInverseApplyMember
import Candidate.C092.transport.SourceInverseP6GeneralPairNorm
import Candidate.C092.transport.SourceInverseP6CloseNormalization
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
open QRH.Cycle092.PairMarkAnchor QRH.Cycle092.LowActual
open Qrh.MarkedAnchor.Interface QRH.Cycle092.MediumReplace.Source
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.MediumInversePrice QRH.Cycle092.TinyCore
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_TerminalActualInverseApplyEnergy_6cae3971ea0221c8_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

theorem actual_length_marked_energy
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (ρ : Contract.AnchorRect) (hsource : Contract.UniformInverseRectSource Contract.canonicalFamily ρ)
    (εm nativeError : ℝ) (hεm : 0 < εm) (hnativeError : 0 < nativeError)
    {N quota : ℝ} (hN : N ≤ 1/2) (hq0 : 0 ≤ quota) (hqcap : quota < 3/20) (hqmean : quota < (1-2*N)/2)
    (dmin dmax : ℝ) (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax) :
    ∃ inverseMesh nativeMesh : ℝ,0 < inverseMesh ∧ 0 < nativeMesh ∧
    ∀ (Slot : Type) [Fintype Slot]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (W : ℝ→ℂ) (hWs : Function.support W ⊆ Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (η η₀ ηlong baseLong : Character) (Q : Ideal O) (hQM : Q ≤ M) (hQ0 : internalQ Q baseLong ≠ 0)
    (hQt : internalQ Q baseLong ≠ ⊤) (hQ72 : internalQ Q baseLong ≤ Ideal.span {(72:O)})
    (bΦ : ℝ) (hbΦ : 2 ≤ bΦ)
    (hsΦ : Function.support (radialMajorant : ℝ→ℂ) ⊆ Iic bΦ),
    ∃ Fbound : ℝ,0 < Fbound ∧ ∀ b : ℝ,0 < b →
    let Kbig := ⌈(7/37:ℝ)/(b/dmax)⌉₊+1;
    ∃ Jc : Fin (Kbig+1)→Fin (Kbig+1)→ℕ,
    ∃ Cc : Fin (Kbig+1)→Fin (Kbig+1)→ℝ,
    ∃ degree : Fin (Kbig+1)→Fin (Kbig+1)→ℕ,
    ∃ controls : Fin (Kbig+1)→Fin (Kbig+1)→Finset (ℕ×ℕ),
    ∃ Cl : Fin (Kbig+1)→Fin (Kbig+1)→ℝ,
      (∀ ki kl,0 < Cc ki kl ∧ 0 < Cl ki kl) ∧
    ∀ (Mcap Bmask margin R τ εshort ez κ heightCost : ℝ)
    (hmargin : 0 < margin) (hR : 0 ≤ R)
    (hτ : 0 < τ) (hheight : 4*τ < dmin*heightCost) (hεshort : 0 < εshort)
    (hez : 0 < ez) (hez' : ez < 1/1000) (hκ : 0 < κ) (hκ' : κ ≤ 1) (hcost : 0 ≤ heightCost)
    (hbudget : 12*ez*(R+2)+8*κ+2*heightCost ≤ εshort)
    (Bshort : ℝ) (hBshort : 0 ≤ Bshort)
    (profileBound : ℕ→ℝ) (hprofile : ∀ j,0 ≤ profileBound j) ,
    ∃ order : Fin (Kbig+1)→Fin (Kbig+1)→ℕ,∃ Cy : Fin (Kbig+1)→Fin (Kbig+1)→ℝ,(∀ ki kl,0 < Cy ki kl) ∧
    ∀ I : ℕ,
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
    ∀ (Wi : FreeRow→ℝ→ℂ) (Ai Bi σi fi : FreeRow→ℝ) (y Y : ℝ),
      0 ≤ y → y/d ≤ R → 0 < Y → Y ≤ Z^y →
      (∀ u∈rows,0 < Ai u) → (∀ u∈rows,Function.support (Wi u) ⊆ Icc (Ai u) (Bi u)) →
      (∀ u∈rows,ContDiff ℝ ∞ (Wi u)) →
      (∀ u∈rows,Function.support (twistProfile (Wi u) (σi u) (fi u)) ⊆ Iic (9/4:ℝ)) →
      (∀ u∈rows,∀ x,‖twistProfile (Wi u) (σi u) (fi u) x‖ ≤ Bshort) →
      (∀ u∈rows,|fi u|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ) →
      (∀ u∈rows,∀ x∈Icc (1-a-6*ez-σi u) (2-σi u),∀ t:ℝ,
        (1+|t|)^2*‖mellin (Wi u) ((x:ℂ)+t*Complex.I)‖ ≤ profileBound 2) →
      (∀ ki kl : Fin (Kbig+1),∀ u∈rows,∀ x∈Icc (1-a-6*ez-σi u) (2-σi u),∀ t:ℝ,
        (1+|t|)^(order ki kl+2)*‖mellin (Wi u) ((x:ℂ)+t*Complex.I)‖ ≤ profileBound (order ki kl+2)) →
    ∀ (θ θLong : Slot→RayQuotient.Characters M H) (w v vLong : Slot→ℝ)
      (tMark tLong slotHeight el eu L pay ζ X : ℝ),
      (∀ j,0 ≤ w j) → (∀ j,w j/d ≤ min inverseMesh nativeMesh) →
      0 ≤ slotHeight → (∀ j,|v j| ≤ slotHeight) → (∀ j,|vLong j| ≤ slotHeight) →
      (∀ u∈rows,∀ j,‖descriptor M H hH η η₀ W Z θ w v tMark u j‖=
        ‖normalizedSlot ηlong (fixedBadMask*idealGenerator 1) 1 u.val (primePool M H 2 (Z^(w j)))
          (fun I=>idealCoeff (relativeCharacter M H hH baseLong (θLong j)) I*
            HeckePrimeAnnular.annularWeight W (Z^(w j)) (33/50) (vLong j) I) tLong (Z^(w j))‖) →
      1 ≤ pay → Fbound*Z^b ≤ pay → 0 ≤ el → 0 ≤ eu →
      (∑ j,w j) ≤ L → 0 ≤ ζ → 367/500 ≤ r →
      0 ≤ QRH.Cycle092.Source.inverseQuota r-ζ →
      ρ.Admissible r (QRH.Cycle092.Source.inverseQuota r-ζ) 1 →
      0 < X → length (Z^d) X ≤ N →
      (∀ u∈rows,initialKeep ηlong (internalQ Q baseLong) u.val) →
    ∀ (jd : Slot) (p : Profiles (1/4) (9/4)) (jprofile : Fin 2),
    let selectedRows := descriptorRows M H hH rows η η₀ W Z pay b θ w v tMark jd;
      selectedRows.Nonempty →
      (∀ u∈selectedRows,el ≤ measured M H hH η η₀ W Z pay θ w v tMark u) →
      (∀ u∈selectedRows,measured M H hH η η₀ W Z pay θ w v tMark u ≤ eu) →
    let hi := max (|tMark|+slotHeight) (2*Real.pi*allowance+(3*i:ℕ)*T);
    let hl := |tMark|+|tLong|+slotHeight;
    ∃ ki kl : Fin (Kbig+1),
      ρ.Admissible r ((ki.val:ℝ)*(w jd/d)) 1 ∧
      QRH.Cycle092.Source.inverseQuota r-(ζ+w jd/d) < (ki.val:ℝ)*(w jd/d) ∧
      (kl.val:ℝ)*(w jd) ≤ d*quota ∧
      d*(quota-w jd/d) < (kl.val:ℝ)*(w jd) ∧
    (∑ u∈selectedRows,‖original ηlong (fixedBadMask*idealGenerator 1) 1 u.val
      (p.profile jprofile) tLong X*
      original s.character s.mask 1 u.val (twistProfile (Wi u) (σi u) (fi u)) 0 Y*
      (∏ j,descriptor M H hH η η₀ W Z θ w v tMark u j)‖^2) ≤
      pay^(Fintype.card Slot)*Cy ki kl*Real.sqrt (12*(1+hi)*(Cc ki kl*(1+hi)^(Jc ki kl)))*
        Real.sqrt (Cl ki kl*QuadraticInitialBound.diagonalControl radialMajorant*
          (sourceControl (controls ki kl) (p.profile jprofile))^4*(1+|tLong|+hl)^(degree ki kl))*
      Z^(d+(2*a-1)*y+el*(L-(kl.val:ℝ)*(w jd)/2)-
        d*((2*a-1)*r+el*((ki.val:ℝ)*(w jd/d)))/2+
        d*εshort+(d*(2*ε+εm)+d*nativeError)/2+(eu-el)*L) := by
  obtain ⟨im,nm,him,hnm,hfamily⟩ := actual_length_marked_member
    hβ ρ hsource εm nativeError hεm hnativeError hN hq0 hqcap hqmean dmin dmax hdmin hdmax
  refine ⟨im,nm,him,hnm,?_⟩
  intro Slot _ M _ H hH W hWs hW η η₀ ηlong baseLong Q hQM hQ0 hQt hQ72 bΦ hbΦ hsΦ
  obtain ⟨Fb,hFb,hFbound⟩ := original_descriptor_bound (Slot:=Slot) M H hH W hW.continuous hWs
  refine ⟨Fb,hFb,?_⟩
  intro b hb
  dsimp only
  let Kbig := ⌈(7/37:ℝ)/(b/dmax)⌉₊+1
  have hdmaxp : 0 < dmax := hdmin.trans_le hdmax
  have hwr : 0 < b/dmax := div_pos hb hdmaxp
  choose Jc Cc hCc degree controls Cl hCl hlate using fun (ki kl : Fin (Kbig+1)) =>
    hfamily M H hH W hWs hW η η₀ ηlong baseLong Q hQM hQ0 hQt hQ72 bΦ hbΦ hsΦ ki.val kl.val (b/dmax) hwr
  refine ⟨Jc,Cc,degree,controls,Cl,fun ki kl=>⟨hCc ki kl,hCl ki kl⟩,?_⟩
  intro Mcap Bmask margin R τ εshort ez κ heightCost hmargin hR hτ hheight hεshort hez hez' hκ hκ' hcost hbudget Bshort hBshort profileBound hprofile
  choose order Cy hCy hbound using fun (ki kl : Fin (Kbig+1)) =>
    hlate ki kl Mcap Bmask margin R τ εshort ez κ heightCost hmargin hR hτ hheight hεshort hez hez' hκ hκ' hcost hbudget Bshort hBshort profileBound hprofile
  refine ⟨order,Cy,hCy,?_⟩
  intro I
  have hbnd := Filter.eventually_all.mpr (fun ki=>Filter.eventually_all.mpr (fun kl=>hbound ki kl I))
  filter_upwards [hbnd,eventually_gt_atTop (1:ℝ)] with Z hZall hZ
  refine ⟨hZ,?_⟩
  intro d hd hd' hds s hswidth hη hp hsM hsη rows hkeep hΦ hnorm a ε cutoff T allowance i ha ha' hiI
  try dsimp only
  intro ws label r hlabel hr hnext Wi Ai Bi σi fi y Y hy hyr hY hYcap hAi hWi hsm hsupp hsup hfi hm₂ hmn
    θ θLong w v vLong tMark tLong slotHeight el eu L pay ζ X hw hmesh hheight hv hvLong hLongNorm hpay hcal hel heu hwidth
    hζ hr0 hquota0 hadm hX hXN hkeepLong jd p jprofile
  try dsimp only
  intro hne hlow hupp
  let selectedRows := descriptorRows M H hH rows η η₀ W Z pay b θ w v tMark jd
  have hsub : selectedRows ⊆ rows := Finset.filter_subset _ _
  obtain ⟨u0,hu0⟩ := hne
  have hbj : b < w jd := (Finset.mem_filter.mp hu0).2.1
  have hdp : 0 < d := hdmin.trans_le hd
  have hZp := zero_lt_one.trans hZ
  have hwd : b/dmax ≤ w jd/d := by
    have h1 := div_le_div_of_nonneg_left hb.le hdp hd'
    exact h1.trans (div_le_div_of_nonneg_right hbj.le hdp.le)
  have hwim : w jd/d ≤ im := (hmesh jd).trans (min_le_left _ _)
  have hwnm : w jd/d ≤ nm := (hmesh jd).trans (min_le_right _ _)
  obtain ⟨_,isel,hiadm,hilower⟩ := admitted_inverse_repeat_selection hr0 hζ hadm hwr hwd le_rfl
  obtain ⟨_,nsel,hnupper,hnlower⟩ := finite_repeat_selection hwr hwd le_rfl hq0
    (by linarith : quota ≤ (7/37:ℝ))
  let ki : Fin (Kbig+1) := ⟨isel.card,Nat.lt_succ_of_le (by simpa using isel.card_le_univ)⟩
  let kl : Fin (Kbig+1) := ⟨nsel.card,Nat.lt_succ_of_le (by simpa using nsel.card_le_univ)⟩
  let hi := max (|tMark|+slotHeight) (2*Real.pi*allowance+(3*i:ℕ)*T)
  let hl := |tMark|+|tLong|+slotHeight
  have hhi : 0 ≤ hi := (by positivity : 0 ≤ |tMark|+slotHeight).trans (le_max_left _ _)
  have hhl : 0 ≤ hl := by dsimp [hl]; positivity
  have hti : |tMark| ≤ hi := (le_add_of_nonneg_right hheight).trans (le_max_left _ _)
  have hvi : |v jd| ≤ hi := (hv jd).trans ((le_add_of_nonneg_left (abs_nonneg _)).trans (le_max_left _ _))
  have hvl : |vLong jd| ≤ hl := by
    dsimp [hl]
    linarith [hvLong jd,abs_nonneg tMark,abs_nonneg tLong]
  have hmul (k : ℕ) : d*((k:ℝ)*(w jd/d))=(k:ℝ)*w jd := by field_simp
  have hnupperAbs : (nsel.card:ℝ)*w jd ≤ d*quota := by
    have h := mul_le_mul_of_nonneg_left hnupper hdp.le
    rwa [hmul] at h
  have hnlowerAbs : d*(quota-w jd/d) < (nsel.card:ℝ)*w jd := by
    have h := mul_lt_mul_of_pos_left hnlower hdp
    rwa [hmul] at h
  have hlowi : ∀ u∈selectedRows,(Z^d)^(el*(w jd/d)-0) ≤
      ‖annularMark M H hH η η₀ W (Z^d) (θ jd) (w jd/d) (v jd) (fun _=>tMark) u‖^2 := by
    intro u hu
    rw [descriptor_inverse_scale M H hH η η₀ W hZp hdp.ne',sub_zero,←Real.rpow_mul hZp.le]
    have heq := (Finset.mem_filter.mp hu).2.2
    change Z^(d*(el*(w jd/d))) ≤ ‖descriptor M H hH η η₀ W Z θ w v tMark u jd‖^2
    rw [show d*(el*(w jd/d))=el*w jd by field_simp,heq]
    exact (Real.rpow_le_rpow_of_exponent_le hZ.le
      (mul_le_mul_of_nonneg_right (hlow u hu) (hw jd))).trans
      (le_mul_of_one_le_left (Real.rpow_nonneg hZp.le _) hpay)
  have hlown := pair_native_spike M H hH rows η η₀ ηlong baseLong W hZ hpay
    θ θLong w v vLong tMark tLong jd (hw jd) hLongNorm hlow
  let K := pay^(Fintype.card Slot)*Z^((eu-el)*L)
  have hK : 0 < K := by dsimp [K]; positivity
  let Qmark : FreeRow→ℂ := fun u=>(∏ j,descriptor M H hH η η₀ W Z θ w v tMark u j)/(Real.sqrt K:ℂ)
  have hm : ∀ u∈selectedRows,‖Qmark u‖^2 ≤ Z^(el*L) := by
    intro u hu
    exact normalized_original_product_upper M H hH hZ (by linarith) hb.le hFb.le hcal hel heu
      η η₀ W θ w v tMark u hw (hFbound Z hZ η η₀ θ w v tMark hw u) (hupp u hu) hwidth
  have hE := (hZall ki kl).2 d hd hd' hds s hswidth hη hp hsM hsη selectedRows
    (fun u hu=>hkeep u (hsub hu)) (fun u hu=>hΦ u (hsub hu)) (fun u hu=>hnorm u (hsub hu))
    a ε cutoff T allowance i ha ha' hiI
    (fun u=>ws ⟨u.val,hsub u.property⟩) label r (fun u=>hlabel _) (fun u=>hr _)
    (fun u=>hnext ⟨u.val,hsub u.property⟩)
    Wi Ai Bi σi fi y Y hy hyr hY hYcap (fun u hu=>hAi u (hsub hu)) (fun u hu=>hWi u (hsub hu))
    (fun u hu=>hsm u (hsub hu)) (fun u hu=>hsupp u (hsub hu))
    (fun u hu=>hsup u (hsub hu)) (fun u hu=>hfi u (hsub hu))
    (fun u hu=>hm₂ u (hsub hu)) (fun u hu=>hmn ki kl u (hsub hu))
    (θ jd) (θLong jd) (w jd/d) (v jd) (w jd) (vLong jd) tLong hi hl el L 0 0 X
    (fun _=>tMark) p jprofile Qmark hwd hwim hhi (fun _ _=>hti) hvi (le_max_right _ _) hiadm hlowi
    (hw jd) hwnm hhl hvl
    hnupperAbs
    hX hXN (fun u hu=>hkeepLong u (hsub hu)) (fun u hu=>by simpa only [sub_zero] using hlown u hu) hm
  refine ⟨ki,kl,hiadm,hilower,?_,?_,?_⟩
  · exact hnupperAbs
  · exact hnlowerAbs
  · rw [energy_div_sqrt selectedRows _ _ _ hK]
    apply (mul_le_mul_of_nonneg_left hE hK.le).trans_eq
    dsimp [K]
    simp only [mul_zero,add_zero]
    conv_rhs => rw [Real.rpow_add hZp]
    dsimp only [hi,hl]
    ring

#print axioms actual_length_marked_energy
end
end QRH.Cycle092.SourceInverseP6
