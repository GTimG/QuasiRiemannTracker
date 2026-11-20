/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual ordinary ticket classes consume the genuine common source event. -/
import Candidate.C092.transport.RegularColoredTerminalLeafContext
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
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows HeckeDetectorZeros
open ConcretePrimeRowBridge ConcreteTraceCRT
open QRH.Cycle092.P2CommonSourceMetadata QRH.Cycle092.TerminalActualRow
open QRH.Cycle092.SourceInverseP6 QRH.Cycle092.WholeSlot QRH.Cycle092.LowActual QRH.Cycle092.StrongPair
open QRH.Cycle092.MediumReplace.Source
open QRH.Cycle092.Source QRH.Cycle092.SourceFurtherWitness QRH.Cycle090 QRH.SourceCertificate
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_RegularColoredTerminalLeafOrdinaryActual_6ec5047a7693c935_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {n y loss heightLoss dmin dmax price εm nativeError : ℝ} {cell : Cell}
variable {table : TerminalResponseTable y (loss/10) cell} {dBank : Finset ℝ}
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable {M : Ideal O} [NeZero M] {A : Arithmetic M}
variable {e Vmax smallMesh lowMesh ordinaryMesh εsource buffer : ℝ}
variable {ordinaryBank : Finset (ℝ×ℝ)} {dec : (ℝ×ℝ)→ℝ}
variable {B : TableBank (n:=n) (heightLoss:=heightLoss) (dmin:=dmin) (dmax:=dmax) (price:=price) table dBank εm nativeError}
variable {P : EarlyPackets Slot M A e Vmax smallMesh lowMesh ordinaryMesh εsource buffer ordinaryBank dec B}
variable {G : LateGeometry dmin dmax dBank} {m0 gap : ℝ} {kernel : ℝ→ℂ}

def terminalOrdinaryCost (L : LateBundle P G m0 gap kernel) (T : Finset Slot) (db : dBank)
    (I : ℕ) (Cslot : ℝ) : ℝ :=
  (max 1 Cslot)^(Fintype.card T)*
    ((L.sources.ordinary T db).C4*12*P.ordinary.Csource T*QuadraticInitialBound.diagonalControl radialMajorant*(P.ordinary.Crow T)^2)*
    (4:ℝ)^(P.ordinary.degree T)*(1+2*Real.pi+(3*I:ℕ))^(2*P.ordinary.J T+1)

/-- A genuine common ordinary source is invoked on the actual class. Its
window, both dyads, physical widths, source length and slot removal all come
from the original finite data; no class-energy premise is supplied. -/
theorem terminal_actual_ordinary_source_at (L : LateBundle P G m0 gap kernel)
    {U V Cslot CLo mesh conductor : ℝ} {I : ℕ}
    (hAt : AtAll P G L.Bshort m0 gap L.sources I Cslot CLo U)
    (T : Finset Slot) (db : dBank)
    (D : TerminalTicketContext T M A G db n y mesh buffer price U V Cslot I table)
    (tag : D.Key) (hoccupied : (D.fiber tag).Nonempty)
    (hordinary : Real.logb (U^db.val) ((2:ℝ)^tag.2.2.2.2.1.val)  <  ((table.cutoff tag.2.2.1).inverse:ℝ))
    (ht0 : 0  ≤  (cell.threshold:ℝ))
    (hy0 : sourceY0  ≤  y) (hy1 : y  ≤  sourceY) (hyn : y  ≤  n) (hn : n  ≤  sourceRatio*y)
    (hdmin : 0  <  dmin) (hdb : dmin  ≤  db.val) (hdb' : db.val  ≤  dmax)
    (hV : (98/100:ℝ)  ≤  V) (hVd : V  ≤  db.val) (hdV : db.val  ≤  V+3*conductor)
    (hsupply : G.Mcap db+G.Bmask+G.margin  ≤  db.val)
    (hY : 1  ≤  D.Y) (hR : y/dmin  ≤  G.R)
    (hmesh : mesh  ≤  dmin*ordinaryMesh) (hmeshGap : mesh  ≤  gap)
    (hgap : 0  ≤  gap) (hgap1 : gap  ≤  1)
    (hm0 : ∀k,m0  ≤  ((table.cutoff k).ordinary:ℝ))
    (hCslot : L.CslotFloor  ≤  Cslot) (hb : 0  ≤  buffer)
    (hwidth : sourceWidth n y-(u:ℝ)  ≤  1)
    (heps : G.ε  ≤  1/7500) (hloss0 : 0  ≤  loss) (hloss : loss  ≤  (rho:ℝ)/64)
    (hprice : 0  ≤  price) (hpriceFee : price*dmax  ≤  loss/4)
    (hconductor : 3*conductor  ≤  (rho:ℝ)/128)
    (hcapFee : (responseUpper:ℝ)*(dmax*(2*gap)+dmax*gap+gap)  ≤  (rho:ℝ)/128)
    (hwitnessFee : (15/4:ℝ)*dmax*G.ε  ≤  (rho:ℝ)/128)
    (hsourceFee : dmax*εsource  ≤  (rho:ℝ)/128)
    (hbufferFee : buffer*(Fintype.card Slot:ℝ)  ≤  (rho:ℝ)/128)
    (hheightFee : G.τ*(P.degreeBound:ℝ)  ≤  (rho:ℝ)/128)
    (p : Profiles (1/4) (9/4)) :
    finiteEnergyOn Finset.univ (D.fiber tag) A.ηLong D.state.character
      (p.profile 0) (p.profile 1) D.tLong D.tShort D.X D.Y D.physical  ≤  
      (L.sources.ordinary T db).C^4*(p.control (L.sources.ordinary T db).S)^2*
        terminalOrdinaryCost L T db I Cslot*
        U^(V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((QRH.SourceCertificate.H:ℝ)-V)) := by
  classical
  have hU0 : 0  <  U := zero_lt_one.trans hAt.one
  have hd0 : 0  <  db.val := hdmin.trans_le hdb
  have hUd : 1  <  U^db.val := Real.one_lt_rpow hAt.one hd0
  have hypos : 0  ≤  y := by
    have h : (0:ℝ)  ≤  sourceY0 := by norm_num [sourceY0]
    linarith
  have hnpos : 0  ≤  n := hypos.trans hyn
  have hCslot0 : 0  <  Cslot := L.CslotFloor_pos.trans_le hCslot
  have hmask : D.state.mask=fixedBadMask*idealGenerator 1 := by simp only [NaturalState.mask,D.puncture]
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
  rcases hocc with ⟨hi,ha0,ha1,hwin,hν0,hν1,hm0key,hm1key,hr0key,hcut0,hcut1,hinv⟩
  have hwin0 : ∀z∈D.fiber tag,table.egrid tag.2.2.1.1 ≤ measured M A.Hr A.hHr A.ηShort A.baseShort A.W U (Cslot*U^buffer) D.theta D.w D.v D.tShort z ∧
      measured M A.Hr A.hHr A.ηShort A.baseShort A.W U (Cslot*U^buffer) D.theta D.w D.v D.tShort z ≤ table.egrid tag.2.2.1.1+loss/10 := by
    rw [hfiber]
    simpa only [TerminalTicketContext.key] using hwin
  have hshort := terminal_original_short_length hAt.one hdmin hdb hypos hY D.short_cap hR
  rcases hshort with ⟨hr0,hrR,hrY,hrScale⟩
  have hsub : D.fiber tag⊆D.rows := classRows_subset _ _ _
  let σ : T→ℝ := fun _=>33/50
  let rel : T→ℝ := fun j=>D.w j/db.val
  let native := fun j (z : FreeRow)=>normalizedSlot D.state.character D.state.mask 1 z.val
    (originalPools M A.Hr 2 (U^db.val) rel j)
    (originalCoefficients M A.Hr A.hHr A.baseShort D.theta A.W (U^db.val) rel σ D.v j) D.tShort ((U^db.val)^(rel j))
  have hnatives (z : FreeRow) (j : T) : native j z=
      descriptor M A.Hr A.hHr A.ηShort A.baseShort A.W U D.theta D.w D.v D.tShort z j := by
    dsimp only [native,rel,σ]
    rw [hmask,D.character]
    exact (terminal_relative_descriptor M A.Hr A.hHr A.ηShort A.baseShort A.W U db.val hU0 hd0
      D.theta D.w (fun _=>33/50) D.v (fun _=>rfl) D.tShort z j).symm
  have hwrel : ∀j,0  ≤  rel j := fun j=>div_nonneg (D.width_nonneg j) hd0.le
  have hrelmesh : ∀j,rel j  ≤  ordinaryMesh := by
    intro j
    apply (div_le_iff₀ hd0).mpr
    have hmo : 0  ≤  ordinaryMesh := by
      by_contra hmo
      have hneg : dmin*ordinaryMesh  <  0 := mul_neg_of_pos_of_neg hdmin (lt_of_not_ge hmo)
      have hwidthj := (D.width_nonneg j).trans ((D.width_mesh j).trans hmesh)
      linarith
    calc
      D.w j  ≤  mesh := D.width_mesh j
      _  ≤  dmin*ordinaryMesh := hmesh
      _  ≤  ordinaryMesh*db.val := by nlinarith only [mul_le_mul_of_nonneg_right hdb hmo]
  have hrelwidth (j : T) : db.val*rel j=D.w j := by dsimp [rel];field_simp
  have hheight : |D.tShort|+|D.tLong|+D.height+D.height  ≤  U^G.τ := by linarith [D.native_height]
  have hfreq : |D.tShort|+U^G.τ/2  ≤  (3*tag.1.val+2:ℕ)*U^G.τ := by
    have ht : |D.tShort|  ≤  U^G.τ := by linarith [D.native_height,D.height_nonneg,abs_nonneg D.tLong]
    have hup : 0  <  U^G.τ := Real.rpow_pos_of_pos hU0 _
    have hi0 : 0  ≤  (tag.1.val:ℝ) := Nat.cast_nonneg _
    norm_num only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    nlinarith only [ht,hup,mul_nonneg hi0 hup.le]
  have hrow : ∀z∈D.rows,rowNorm z  ≤  U^db.val := fun z hz=>(D.row_norm z hz).trans
    (Real.rpow_le_rpow_of_exponent_le hAt.one.le hVd)
  have hlongnorm : ∀z∈D.fiber tag,∀j,
      ‖normalizedSlot D.state.character (fixedBadMask*idealGenerator 1) 1 z.val
        (originalPools M A.Hr 2 (U^db.val) rel j)
        (originalCoefficients M A.Hr A.hHr A.baseShort D.theta A.W (U^db.val) rel σ D.v j) D.tShort ((U^db.val)^(rel j))‖=
      ‖normalizedSlot A.ηLong (fixedBadMask*idealGenerator 1) 1 z.val
        (originalPools M A.Hr 2 (U^db.val) rel j)
        (originalCoefficients M A.Hr A.hHr A.baseLong D.thetaLong A.W (U^db.val) rel σ D.vLong j) D.tLong ((U^db.val)^(rel j))‖ := by
    intro z hz j
    rw [D.character]
    rw [←terminal_relative_descriptor M A.Hr A.hHr A.ηShort A.baseShort A.W U db.val hU0 hd0 D.theta D.w σ D.v (fun _=>rfl) D.tShort z j]
    rw [←terminal_relative_descriptor M A.Hr A.hHr A.ηLong A.baseLong A.W U db.val hU0 hd0 D.thetaLong D.w σ D.vLong (fun _=>rfl) D.tLong z j]
    exact D.long_presentation z (hsub hz) j
  have hpay : Cslot  ≤  Cslot*U^buffer := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.one_le_rpow hAt.one.le hb) hCslot0.le
  have hz : ∀z : D.fiber tag,∀j,rel j=0 → ‖native j z.val‖^2  ≤  Cslot*U^buffer := by
    intro z j hj
    have hj0 : D.w j=0 := by have hh:=hrelwidth j;rw [hj,mul_zero] at hh;exact hh.symm
    rw [hnatives]
    exact (L.zero_width_paid T hAt.one hCslot A.ηShort A.baseShort D.theta D.w D.v D.tShort D.width_nonneg z.val j hj0).trans hpay
  have hresp : ∀z : D.fiber tag,response U (Cslot*U^buffer) (fun j=>db.val*rel j)
      (fun j=>‖native j z.val‖^2)  ≤  table.egrid tag.2.2.1.1+loss/10 := by
    intro z
    have heq : (fun j=>db.val*rel j)=D.w := funext hrelwidth
    rw [heq,response_norm_congr U (Cslot*U^buffer) D.w (fun j=>native j z.val)
      (fun j=>descriptor M A.Hr A.hHr A.ηShort A.baseShort A.W U D.theta D.w D.v D.tShort z.val j)
      (fun j=>congrArg norm (hnatives z.val j))]
    exact (hwin0 z.val z.property).2
  have hFee := terminal_shared_window_fee hloss0 hloss hprice hdb' hm0key hm1key hpriceFee
  have hbufferT := subset_buffer_paid T hb hbufferFee
  have hheightT : G.τ*((P.ordinary.degree T+2*P.ordinary.J T+1:ℕ):ℝ)  ≤  (rho:ℝ)/128 :=
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (P.degree_bounds.2.2.1 T)) G.hτ.le).trans hheightFee
  have hc0 : sourceY0  ≤  ((table.cutoff tag.2.2.1).ordinary:ℝ) := by
    have hH : 0  <  (QRH.SourceCertificate.H:ℝ) ∧ (QRH.SourceCertificate.H:ℝ)  ≤  1 := by norm_num [QRH.SourceCertificate.H,u]
    have hyy : y  ≤  y/(QRH.SourceCertificate.H:ℝ) := (le_div_iff₀ hH.1).mpr (by nlinarith [mul_le_mul_of_nonneg_right hH.2 hypos])
    exact hy0.trans (hyy.trans (table.ordinaryCap _))
  have helo0 : 0  ≤  table.egrid tag.2.2.1.1 := ht0.trans (table.eBounds _).1
  have hνupper : max (table.egrid tag.2.2.1.1) (table.νgrid tag.2.2.1.2)  ≤  3/4 :=
    max_le ((table.eBounds _).2.trans (by norm_num [responseUpper])) (table.νBounds _).2
  have hsource := (hAt.ordinary T db).2 p db.val hdb hdb' hsupply D.state D.width_bound D.character
    D.modulus_ray D.modulus_base hmask D.keep_equiv D.rows D.keep D.plateau
    ⌊(73/200:ℝ)/G.ez⌋₊ table.Je table.Jν (fun z=>(D.ticket z).band) (fun z=>(D.ticket z).level)
    D.window (fun k=>totalCutoff (table.cutoff k)) D.witness tag
    (Real.logb (U^db.val) D.Y) (table.cutoff tag.2.2.1) hr0 hrR (by linarith) rfl hoccupied
    (fun z=>(D.ticket z).next) D.tShort hfreq D.theta rel σ D.v D.thetaLong σ D.vLong
    D.tShort D.tLong D.height D.height D.X hwrel hrelmesh (fun _=>le_rfl) (fun _=>le_rfl)
    D.height_nonneg D.pitch (fun _=>le_rfl) (fun _=>le_rfl) D.height_nonneg D.pitchLong D.long_positive
    (terminal_original_length_cap hAt.one hnpos D.long_cap)
    (fun z hz=>D.long_keep z (hsub hz)) hlongnorm (fun z hz=>hrow z (hsub hz))
    (table.egrid tag.2.2.1.1+loss/10) (table.egrid tag.2.2.1.1)
    (max (table.egrid tag.2.2.1.1) (table.νgrid tag.2.2.1.2)) (loss/10) price V gap (3*conductor) Cslot buffer conductor cell.upper
    hy0 hy1 hyn hn (by positivity) helo0 (table.eBounds _).2 (le_max_left _ _) hνupper hν0 hν1 le_rfl
    (by positivity) hprice (table.guard _) (table.ordinaryCap _) hc0 (table.paid _) hordinary
    hV hVd hdV (hm0 _) heps hgap hgap1 hgap le_rfl
    (fun j=>(hrelwidth j).trans_le ((D.width_mesh j).trans hmeshGap)) hwidth hCslot0 hb hrY
    (by simpa only [hrelwidth] using D.width_sum) hz hresp hheight le_rfl hconductor hcapFee
    hwitnessFee hsourceFee hbufferT hheightT hFee
  rw [hrScale] at hsource
  have heq := finiteEnergyOn_norm_congr Finset.univ (D.fiber tag) A.ηLong D.state.character
    ((TerminalProfileUniform.unitPair (L.sources.ordinary T db).S (L.sources.ordinary T db).C p).profile 0)
    ((TerminalProfileUniform.unitPair (L.sources.ordinary T db).S (L.sources.ordinary T db).C p).profile 1)
    D.tLong D.tShort D.X D.Y D.physical native
    (fun z hz j _=>(D.short_presentation z (hsub hz) j).trans (congrArg norm (hnatives z j)).symm)
  have hsource0 : finiteEnergyOn Finset.univ (D.fiber tag) A.ηLong D.state.character
      ((TerminalProfileUniform.unitPair (L.sources.ordinary T db).S (L.sources.ordinary T db).C p).profile 0)
      ((TerminalProfileUniform.unitPair (L.sources.ordinary T db).S (L.sources.ordinary T db).C p).profile 1)
      D.tLong D.tShort D.X D.Y native ≤ terminalOrdinaryCost L T db I Cslot*
        U^(V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((QRH.SourceCertificate.H:ℝ)-V)) := by
    simpa only [TerminalTicketContext.fiber,TerminalTicketContext.key,native,terminalOrdinaryCost] using hsource
  rw [←heq] at hsource0
  have hpaid := terminal_finite_unit_payment Finset.univ (D.fiber tag) A.ηLong D.state.character p
    D.tLong D.tShort D.X D.Y D.physical (L.sources.ordinary T db).S (L.sources.ordinary T db).S_zero
    (zero_lt_one.trans_le (L.sources.ordinary T db).C_one) hsource0
  convert hpaid using 1   <;> unfold terminalOrdinaryCost   <;> ring

#print axioms terminal_actual_ordinary_source_at
end
end QRH.Cycle092.RegularColoredForward
