/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual ordinary ticket classes consume the genuine common source event. -/
import Candidate.C092.transport.P2InverseTicketDispatchCosts
import Candidate.C092.transport.RegularColoredTerminalLeafContext
import Candidate.C092.transport.RegularColoredTerminalLeafMarkedOriginal
import Candidate.C092.transport.RegularColoredTerminalLeafUnmarkedOriginal
import Candidate.C092.transport.RegularColoredTerminalLeafDecision
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentEnergyBands CenteredMomentWholeSlotDeletion CenteredMomentFiniteProfileExceptional
open CenteredMomentPrimeSlot CenteredMomentDetectorPlainFiberSource
open HeckeDetectorDyadicProfiles
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows HeckeDetectorZeros
open ConcretePrimeRowBridge ConcreteTraceCRT
open QRH.Cycle092.P2CommonSourceMetadata QRH.Cycle092.TerminalActualRow
open QRH.Cycle092.SourceInverseP6 QRH.Cycle092.WholeSlot QRH.Cycle092.LowActual QRH.Cycle092.StrongPair
open QRH.Cycle092.MediumReplace.Source
open QRH.Cycle092.Source QRH.Cycle092.SourceFurtherWitness QRH.Cycle090 QRH.SourceCertificate
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_P2InverseTicketDispatchActual_857fcef680bc4f89_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {n y loss heightLoss dmin dmax price εm nativeError : ℝ} {cell : Cell}
variable {table : TerminalResponseTable y (loss/10) cell} {dBank : Finset ℝ}
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable {M : Ideal O} [NeZero M] {A : Arithmetic M}
variable {e Vmax smallMesh lowMesh ordinaryMesh εsource buffer : ℝ}
variable {ordinaryBank : Finset (ℝ×ℝ)} {dec : (ℝ×ℝ)→ℝ}
variable {B : TableBank (n:=n) (heightLoss:=heightLoss) (dmin:=dmin) (dmax:=dmax) (price:=price) table dBank εm nativeError}
variable {P : EarlyPackets Slot M A e Vmax smallMesh lowMesh ordinaryMesh εsource buffer ordinaryBank dec B}
variable {G : LateGeometry dmin dmax dBank} {m0 gap : ℝ} {kernel : ℝ→ℂ}

/-- The inverse decision consumes the actual frozen ticket class, genuine
source bank, retained source event and calibrated attainer cover at SAME U.
The original arbitrary profiles are restored after the source call. -/
theorem terminal_actual_inverse_source_at (L : LateBundle P G m0 gap kernel)
    {U V Cslot CLo mesh : ℝ} {I : ℕ}
    (hAt : AtAll P G L.Bshort m0 gap L.sources I Cslot CLo U)
    (T : Finset Slot) (db : dBank)
    (D : TerminalTicketContext T M A G db n y mesh buffer price U V Cslot I table)
    (tag : D.Key) (hoccupied : (D.fiber tag).Nonempty)
    (hinverse : ((table.cutoff tag.2.2.1).inverse:ℝ) ≤
      Real.logb (U^db.val) ((2:ℝ)^tag.2.2.2.2.1.val))
    (ht0 : 0 < (cell.threshold:ℝ)) (hy0 : 0 ≤ y) (hn0 : 0 ≤ n)
    (hdmin : 0 < dmin) (hdb : dmin ≤ db.val) (hdb' : db.val ≤ dmax)
    (hV : (98/100:ℝ) ≤ V) (hVd : V ≤ db.val) (hdV : db.val ≤ V+3*(loss/10))
    (hsupply : G.Mcap db+G.Bmask+G.margin ≤ db.val)
    (hR : y/dmin ≤ G.R) (hmesh : mesh ≤ dmin*B.mesh)
    (hCslot : 0 < Cslot) (hb : 0 ≤ buffer)
    (hwidth : sourceWidth n y-(u:ℝ) ≤ 1)
    (heps : G.ε ≤ 1/7500) (hloss : 0 ≤ loss)
    (hbufferFee : buffer*(Fintype.card Slot:ℝ) ≤ B.feeFloor/1000)
    (hepsilonFee : (dmax+1)*G.ε ≤ B.feeFloor/1000)
    (p : Profiles (1/4) (9/4)) :
    finiteEnergyOn Finset.univ (D.fiber tag) A.ηLong D.state.character
      (p.profile 0) (p.profile 1) D.tLong D.tShort D.X D.Y D.physical ≤
      L.C^4*(p.control L.S)^2*terminalInverseCost L T db tag.2.2.1 I Cslot*
        U^(V+radialAllowance V+loss+heightLoss) := by
  classical
  have hU0 : 0 < U := zero_lt_one.trans hAt.one
  have hd0 : 0 < db.val := hdmin.trans_le hdb
  have hUd : 1 < U^db.val := Real.one_lt_rpow hAt.one hd0
  let χ := fun z : FreeRow=>family M A.Hr A.hHr D.state A.baseShort (naturalRow D.state.character z.val z.property.1)
  let hnp := fun z : D.rows=>family_nonprincipal M A.Hr A.hHr D.state A.baseShort D.modulus_ray D.modulus_base
    (D.keep z.val z.property) (naturalRow D.state.character z.val.val z.val.property.1)
  have hfiber : D.fiber tag = @classRows D.Key (fun a b=>Classical.propDecidable (a=b)) D.rows D.key tag := by
    ext z
    simp only [TerminalTicketContext.fiber,classRows_mem]
  have hocc := terminal_actual_occupied_class D.rows χ hnp U db.val dmax G.τ G.ε G.ez price y (loss/10) cell table
    hUd heps (fun z=>measured M A.Hr A.hHr A.ηShort A.baseShort A.W U (Cslot*U^buffer) D.theta D.w D.v D.tShort z)
    D.ticket D.window D.witness D.window_bound tag
    (by rw [hfiber] at hoccupied
        simpa only [TerminalTicketContext.key] using hoccupied)
  rcases hocc with ⟨hi,ha0,ha1,hwin,hν0,hν1,hm0key,hm1key,hr0key,hcut0,hcut1,hrlower⟩
  have hwin0 : ∀z∈D.fiber tag,table.egrid tag.2.2.1.1 ≤ measured M A.Hr A.hHr A.ηShort A.baseShort A.W U (Cslot*U^buffer) D.theta D.w D.v D.tShort z ∧
      measured M A.Hr A.hHr A.ηShort A.baseShort A.W U (Cslot*U^buffer) D.theta D.w D.v D.tShort z ≤ table.egrid tag.2.2.1.1+loss/10 := by
    rw [hfiber]
    simpa only [TerminalTicketContext.key] using hwin
  let k : WindowKey table := tag.2.2.1
  let r := Real.logb (U^db.val) ((2:ℝ)^tag.2.2.2.2.1.val)
  let a := (51/100:ℝ)+G.ez*tag.2.1.val
  let q := TerminalProfileUniform.unitPair L.S L.C p
  have ha : a ≤ 1 := ha1.trans (by norm_num)
  have he0 : 0 < table.egrid k.1 := ht0.trans_le (table.eBounds k.1).1
  have heu : 0 ≤ table.egrid k.1+loss/10 := by positivity
  have hr : 367/500 ≤ r := hrlower hinverse
  have hsub : D.fiber tag⊆D.rows := classRows_subset _ _ _
  have hrow : ∀z∈D.rows,rowNorm z ≤ U^db.val := fun z hz=>(D.row_norm z hz).trans
    (Real.rpow_le_rpow_of_exponent_le hAt.one.le hVd)
  have hyR : y/db.val ≤ G.R := (div_le_div_of_nonneg_left hy0 hdmin hdb).trans hR
  have hdivmesh : ∀j,D.w j/db.val ≤ B.mesh := by
    intro j
    apply (div_le_iff₀ hd0).mpr
    calc
      D.w j ≤ mesh := D.width_mesh j
      _ ≤ dmin*B.mesh := hmesh
      _ ≤ B.mesh*db.val := by nlinarith only [mul_le_mul_of_nonneg_right hdb B.mesh_pos.le]
  have hfreq : |D.tShort|+U^G.τ/2 ≤ (3*tag.1.val+2:ℕ)*U^G.τ := by
    have ht : |D.tShort| ≤ U^G.τ := by linarith [D.native_height,D.height_nonneg,abs_nonneg D.tLong]
    have hup : 0 < U^G.τ := Real.rpow_pos_of_pos hU0 _
    have hi0 : 0 ≤ (tag.1.val:ℝ) := Nat.cast_nonneg _
    norm_num only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    nlinarith only [ht,hup,mul_nonneg hi0 hup.le]
  have hheight : |D.tShort|+|D.tLong|+D.height ≤ U^G.τ := by linarith [D.native_height,D.height_nonneg]
  have hlongmark : ∀z∈D.fiber tag,∀j,
      ‖descriptor M A.Hr A.hHr A.ηShort A.baseShort A.W U D.theta D.w D.v D.tShort z j‖=
        ‖normalizedSlot A.ηLong (fixedBadMask*idealGenerator 1) 1 z.val (primePool M A.Hr 2 (U^(D.w j)))
          (fun J=>idealCoeff (relativeCharacter M A.Hr A.hHr A.baseLong (D.thetaLong j)) J*
            HeckePrimeAnnular.annularWeight A.W (U^(D.w j)) (33/50) (D.vLong j) J) D.tLong (U^(D.w j))‖ := by
    intro z hz j
    rw [D.long_presentation z (hsub hz) j]
    exact congrArg norm (descriptor_short_anchor M A.Hr A.hHr A.ηLong A.baseLong A.W U
      D.thetaLong D.w (fun _=>33/50) D.vLong D.tLong z j rfl)
  have hshort := L.shortGates L.S L.S_zero L.C L.C_one p L.sources.orders P.controlsBound (L.unitGates p)
    1 false 1 0 D.tShort a G.ez (by norm_num) (by norm_num) (by norm_num)
    ha0.le ha G.hez G.hez_small
  simp only [TerminalActualRow.shortProfile,Bool.false_eq_true,↓reduceIte] at hshort
  have hsup := hshort.2.2.2.1
  have hmellin := hshort.2.2.2.2
  have hctlM : ∀j ki kl,sourceControl ((P.inverse.marked T db k j).controls ki kl) (q.profile 0) ≤ 1 := by
    intro j ki kl
    exact (CenteredMomentEnergyReferenceProfileBudget.control_mono
      (P.controls_bounds.2.2.2.2.1 T db k j ki kl) (q.profile 0)).trans ((L.unitGates p).1 0)
  have hctlU : ∀kl,sourceControl ((P.inverse.unmarked T db k).controls kl) (q.profile 0) ≤ 1 := by
    intro kl
    exact (CenteredMomentEnergyReferenceProfileBudget.control_mono
      (P.controls_bounds.2.2.2.2.2 T db k kl) (q.profile 0)).trans ((L.unitGates p).1 0)
  have hL0 : 0 ≤ ∑j,D.w j := Finset.sum_nonneg (fun j _=>D.width_nonneg j)
  have hL1 : (∑j,D.w j) ≤ 1 := D.width_sum.trans hwidth
  have hXN : length (U^db.val) D.X ≤ terminalNativeCap n db.val :=
    (B.native k db).2.2.2.2.2.2 hU0 (terminal_original_length_cap hAt.one hn0 D.long_cap)
  have herrors := inverse_error_paid B G k T hd0.le hdb' hb hbufferFee hepsilonFee
  have hfeesM : db.val*G.ε+(db.val*(2*G.ε+εm)+db.val*nativeError)/2+buffer*(Fintype.card T:ℝ) ≤ B.feeM k :=
    herrors.2.2.2.trans (B.fees k).2.2.2.1
  have hfeesU : db.val*G.ε+(db.val*(2*G.ε+εm)+db.val*nativeError)/2+buffer*(Fintype.card T:ℝ) ≤ B.feeU k :=
    herrors.2.2.2.trans (B.fees k).2.2.2.2
  have hcreditM : 2*NativeFourthEffective.credit n db.val-db.val*B.quota k db ≤ B.feeM k/2 := by
    have hc := (B.native k db).2.2.2.2.2.1
    have hf := (B.fees k).2.2.2.1
    have hp := (B.fees k).1
    linarith
  have hcreditU : 2*NativeFourthEffective.credit n db.val-db.val*B.quota k db ≤ B.feeU k/2 := by
    have hc := (B.native k db).2.2.2.2.2.1
    have hf := (B.fees k).2.2.2.2
    have hp := (B.fees k).2.1
    linarith
  have hζM : B.ζ ≤ B.feeM k/2 := (B.ζ_fee k).trans (by linarith [(B.fees k).2.2.2.1])
  have hζU : B.ζ ≤ B.feeU k := (B.ζ_fee k).trans (by linarith [(B.fees k).2.2.2.2,(B.fees k).2.1])
  have hresponse0 : ∀z∈D.fiber tag,table.egrid k.1 ≤ measured M A.Hr A.hHr A.ηShort A.baseShort A.W U
      (Cslot*U^buffer) D.theta D.w D.v D.tShort z := fun z hz=>(hwin0 z hz).1
  have hresponse1 : ∀z∈D.fiber tag,measured M A.Hr A.hHr A.ηShort A.baseShort A.W U
      (Cslot*U^buffer) D.theta D.w D.v D.tShort z ≤ table.egrid k.1+loss/10 := fun z hz=>(hwin0 z hz).2
  have hunit : finiteEnergyOn Finset.univ (D.fiber tag) A.ηLong D.state.character
      (q.profile 0) (q.profile 1) D.tLong D.tShort D.X D.Y D.physical ≤
      terminalInverseCost L T db k I Cslot*U^(V+radialAllowance V+loss+heightLoss) := by
    have hcost := terminal_inverse_cost_bounds L T db k I hCslot.le
    have hpow : 0 ≤ U^(V+radialAllowance V+loss+heightLoss) := (Real.rpow_pos_of_pos hU0 _).le
    have hUnmarked (hguard : r ≤ 1 → inverseQuota r ≤ B.feeU k) :
        finiteEnergyOn Finset.univ (D.fiber tag) A.ηLong D.state.character
          (q.profile 0) (q.profile 1) D.tLong D.tShort D.X D.Y D.physical ≤
        terminalInverseUnmarkedCost L T db k I Cslot*U^(V+radialAllowance V+loss+heightLoss) := by
      have hs := (terminal_ready_unmarked_original_at T M A n y (table.egrid k.1)
        (max (table.egrid k.1) (table.νgrid k.2)) loss heightLoss (table.cutoff k)
        (loss/10) (loss/10) (B.feeU k) εm nativeError (terminalNativeCap n db.val) (B.quota k db)
        dmin dmax price (B.nu k db) buffer (P.inverse.unmarked T db k) dBank G db L.Bshort
        (L.sources.unmarked T db k) he0 I Cslot U hCslot (hAt.unmarked T db k) (hAt.cover T)).2
      exact hs db.val hdb hdb' hsupply D.state D.width_bound D.character D.puncture
        D.modulus_ray D.modulus_base D.rows D.keep D.plateau hrow
        ⌊(73/200:ℝ)/G.ez⌋₊ table.Je table.Jν G.ε (fun z=>(D.ticket z).band) (fun z=>(D.ticket z).level)
        D.window (fun k=>totalCutoff (table.cutoff k)) D.witness tag ha (fun z=>(D.ticket z).next)
        G.hε.le (heps.trans (by norm_num)) hcut0 hcut1 q D.tShort D.Y hy0 hyR D.short_positive D.short_cap
        hsup hfreq (fun x hx t=>hmellin 2 L.sources.orders_two x hx t)
        (fun kl x hx t=>hmellin _ (L.sources.unmarked_order T db k kl) x hx t) hctlU
        D.theta D.thetaLong D.w D.v D.vLong D.tShort D.tLong D.height (table.egrid k.1+loss/10)
        (∑j,D.w j) D.X V D.width_nonneg (fun j=>(hdivmesh j).trans (B.unmarked_mesh k db))
        D.height_nonneg D.pitch D.pitchLong hlongmark heu le_rfl D.long_positive hXN
        (fun z hz=>D.long_keep z (hsub hz)) hV hVd hdV hν0 hν1 le_rfl hinverse rfl herrors.2.2.1
        hL0 hL1 D.width_sum hcreditU hguard hfeesU hheight hresponse0 hresponse1 D.physical
        (fun z hz j=>D.short_presentation z (hsub hz) j)
    have hMarked (j : Fin B.J) (hr1 : r ≤ 1) (hq : 0 ≤ inverseQuota r-B.ζ)
        (hρ : (B.rhoBank j).Admissible r (inverseQuota r-B.ζ) 1) :
        finiteEnergyOn Finset.univ (D.fiber tag) A.ηLong D.state.character
          (q.profile 0) (q.profile 1) D.tLong D.tShort D.X D.Y D.physical ≤
        terminalInverseMarkedCost L T db k j I Cslot*U^(V+radialAllowance V+loss+heightLoss) := by
      have hs := (terminal_ready_marked_original_at T M A n y (table.egrid k.1)
        (max (table.egrid k.1) (table.νgrid k.2)) loss heightLoss (table.cutoff k)
        (loss/10) (loss/10) (B.feeM k) (B.rhoBank j) εm nativeError (terminalNativeCap n db.val) (B.quota k db)
        dmin dmax price (B.im k db j) (B.nm k db j) buffer (P.inverse.marked T db k j) dBank G db L.Bshort
        (L.sources.marked T db k j) he0 I Cslot U hCslot (hAt.marked T db k j) (hAt.cover T)).2
      exact hs db.val hdb hdb' hsupply D.state D.width_bound D.character D.puncture
        D.modulus_ray D.modulus_base D.rows D.keep D.plateau hrow
        ⌊(73/200:ℝ)/G.ez⌋₊ table.Je table.Jν G.ε (fun z=>(D.ticket z).band) (fun z=>(D.ticket z).level)
        D.window (fun k=>totalCutoff (table.cutoff k)) D.witness tag ha (fun z=>(D.ticket z).next)
        q D.tShort D.Y hy0 hyR D.short_positive D.short_cap hsup hfreq
        (fun x hx t=>hmellin 2 L.sources.orders_two x hx t)
        (fun ki kl x hx t=>hmellin _ (L.sources.marked_order T db k j ki kl) x hx t) (hctlM j)
        D.theta D.thetaLong D.w D.v D.vLong D.tShort D.tLong D.height (table.egrid k.1+loss/10)
        (∑j,D.w j) B.ζ D.X V D.width_nonneg
        (fun z=>le_min ((hdivmesh z).trans (B.marked_mesh k db j).1) ((hdivmesh z).trans (B.marked_mesh k db j).2))
        D.height_nonneg D.pitch D.pitchLong hlongmark heu le_rfl B.ζ_pos.le hr hq hρ D.long_positive hXN
        (fun z hz=>D.long_keep z (hsub hz)) hV hVd hdV hν0 hν1 le_rfl hinverse hr1 G.hε.le herrors.2.1
        hL0 hL1 D.width_sum hcreditM hζM hfeesM hheight hresponse0 hresponse1 D.physical
        (fun z hz z' =>D.short_presentation z (hsub hz) z')
    rcases terminal_actual_inverse_decision B.rhoBank B.ζ r hr B.cover with hlarge|hsmall|hmarked
    · exact (hUnmarked (terminal_actual_unmarked_guard hζU (Or.inl hlarge))).trans
        (mul_le_mul_of_nonneg_right hcost.2.1 hpow)
    · exact (hUnmarked (terminal_actual_unmarked_guard hζU (Or.inr hsmall))).trans
        (mul_le_mul_of_nonneg_right hcost.2.1 hpow)
    · obtain ⟨hr1,hquota,j,hρ⟩ := hmarked
      exact (hMarked j hr1 (sub_nonneg.mpr hquota.le) hρ).trans
        (mul_le_mul_of_nonneg_right (hcost.2.2 j) hpow)
  have hpaid := terminal_finite_unit_payment Finset.univ (D.fiber tag) A.ηLong D.state.character p
    D.tLong D.tShort D.X D.Y D.physical L.S L.S_zero (zero_lt_one.trans_le L.C_one) hunit
  simpa only [mul_assoc] using hpaid

#print axioms terminal_actual_inverse_source_at
end
end QRH.Cycle092.RegularColoredForward
