/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The low coordinate exits use the actual bank cutoff and original source. -/
import Candidate.C092.transport.MixedOutsidePaidOrdinaryPrice
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace QRH.Cycle092.MixedOutsidePaid
open scoped Classical BigOperators
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorRawFiber HeckeDetectorWitnessRows
open QRH.Record12518109Count Cycle25ProbeFinalAssembly
open QRH.Record1252270103Return QRH.Cycle092.PacketJoinE49 QRH.Cycle092.MixedOffsetCount
open QRH.Cycle090 QRH.Cycle092.TopData QRH.Cycle092.RawTicket
open QRH.Cycle092.SelectedNonfloor QRH.Cycle092.PacketJoin QRH.Cycle092.MixedTicketTails
open Qrh.MarkedAnchor.Return (fiber_inverse_width_count)

def inverseTangentR (δ p r:ℝ):ℝ:=1-δ*(Return.aI p+Return.kI p*r)

/-- The authentic inverse rectangle supplier requires only its own coordinate.
The ordinary coordinate may already have left the central window. -/
theorem actual_inverse_tangent_count (hβ:(51/100:ℝ)≤ HeckeZeroSupremum.beta) :
    ∃mesh:ℝ→ℝ,(∀t,0<t → 0 < mesh t) ∧
    ∀(D:Cycle25.Weighted.MomentData)(S:WeightedSourceData D),
      (∀s,D.ell s ≤ mesh D.t/200) →
    ∀η:Character,∃J:ℕ,∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(d a tstar T allowance height:ℝ)(i:ℕ),
      (1/200:ℝ)≤ d → 51/100<a → 2*a-1≤ 3/4 → D.t≤ 1/10000000 →
      0≤ height → 2*Real.pi*allowance+(3*i:ℕ)*T≤ height →
    ∀(P:Presented D S η Z d a tstar T allowance i)(F:Slice P),
      (∀s,|(P.batch.external s).im|≤ height) → anchorLeft≤ F.fiber.r → F.fiber.r≤ anchorTop →
    ∀common:Finset FreeRow,common⊆F.fiber.rows →
      (common.card:ℝ)≤ 12*(1+height)*(C*(1+height)^J)*
        (Z^d)^(inverseTangentR (2*a-1) (F.fiber.q/(2*a-1)) F.fiber.r+countLoss D.ε P.batch.mesh D.t) := by
  have hs:=tangent_fiber_moments hβ
  choose mesh hm hsource using fun t:{t:ℝ//0<t}=>hs t.val t.property
  let chooseMesh:ℝ→ℝ:=fun t=>if ht:0<t then mesh ⟨t,ht⟩ else 1
  refine ⟨chooseMesh,?_,?_⟩
  · intro t ht;simpa only [chooseMesh,dif_pos ht] using hm ⟨t,ht⟩
  intro D S hfine η
  have hfi:∀s,D.ell s≤ mesh ⟨D.t,D.t_pos⟩/200:=by simpa only [chooseMesh,dif_pos D.t_pos] using hfine
  obtain ⟨J,C,hC,hsource⟩:=(hsource ⟨D.t,D.t_pos⟩ S rfl hfi) η
  refine ⟨J,C,hC,?_⟩
  filter_upwards [hsource] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro d a tstar T allowance height i hd ha hδhi ht hh hf P F him hrlo hrhi common hsub
  have hU:1<Z^d:=Real.one_lt_rpow hZ.1 (by linarith)
  have hi:=hZ.2 P.batch.rows P.lower d hd a tstar T allowance i P.batch (fun _ hu=>hu)
    P.data P.profile P.widths (fun s=>congrFun P.upper s) P.real
    F.bin F.label F.left F.right F.nonempty height hh him
  obtain ⟨hz,hz'⟩:=Return.markCap_bounds (line:=Return.line) hrlo hrhi D.t_pos ht
  have hb:=fiber_inverse_width_count F.fiber hU (by linarith) (by positivity:0≤ C*(1+height)^J) hh hf
    (markCap Return.line F.fiber.r-D.t) hz.le hz'
    (fun sel hsel hw=>hi.inverse hrlo hrhi sel hsel hw)
  have hq:(2*a-1)*(F.fiber.q/(2*a-1))=F.fiber.q:=mul_div_cancel₀ _ (by linarith:2*a-1≠0)
  have hid:1-(2*a-1)*F.fiber.r-2*F.fiber.q*(markCap Return.line F.fiber.r-D.t)=
      inverseTangentR (2*a-1) (F.fiber.q/(2*a-1)) F.fiber.r+2*F.fiber.q*D.t:=by
    unfold inverseTangentR Return.aI Return.kI markCap
    field_simp [show 2*a-1≠0 by linarith]
    <;> ring
  have hmean:=F.fiber.mean_bounds (by linarith:1/2≤ a)
  have hq1:2*F.fiber.q≤ 1:=by linarith [hmean.2]
  have hqt:=mul_le_mul_of_nonneg_right hq1 D.t_pos.le
  have hmesh:(2*a-1)*F.fiber.mesh≤ P.batch.mesh:=by
    change (2*a-1)*P.batch.mesh≤ P.batch.mesh
    exact mul_le_of_le_one_left P.batch.mesh_nonneg (by linarith)
  have he:1-(2*a-1)*F.fiber.r-2*F.fiber.q*(markCap Return.line F.fiber.r-D.t)+2*D.ε+(2*a-1)*F.fiber.mesh+D.t≤
      inverseTangentR (2*a-1) (F.fiber.q/(2*a-1)) F.fiber.r+countLoss D.ε P.batch.mesh D.t:=by
    rw [hid]
    unfold countLoss
    linarith [D.epsilon_pos,D.t_pos]
  have hcard:(common.card:ℝ)≤(F.fiber.rows.card:ℝ):=by exact_mod_cast Finset.card_le_card hsub
  exact hcard.trans (hb.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hU.le he) (by positivity)))

/-- A low inverse coordinate forces an ordinary-high exit at the same bank
cutoff, even after the whole original bank offset. -/
theorem inverse_low_forces_ordinary_high {tstar r m ε ξ t₀:ℝ}
    (hlength:tstar-r-ε≤ m) (ht:tstar=t₀-ξ)
    (htlo:tLo≤ t₀) (hξ:ξ≤ gammaMax) (hε:ε≤ 1/10000000)
    (hr:r≤ anchorLeft) : anchorTop≤ 2*m := by
  norm_num [tLo,gammaMax,anchorLeft,anchorTop] at *
  linarith only [hlength,ht,htlo,hξ,hε,hr]

variable [Geometry.Parameters]
lemma original_k_lower {r:Row} (hr:r∈rows) {δ p:ℝ} (hpbox:r.box.Contains (δ,p)) : kMin≤ Return.kI p := by
  have hp:=original_point_bounds hr hpbox
  have hg:=Qrh.TwoSlot.AnchorContinuum.Contact.tangent_coefficient_bounds
  have h0:0≤ Return.line.g1:=by have h:=hg.2.2.1;change (3799809/50000000:ℝ)<Return.line.g1 at h;linarith
  have h1:Return.line.g1≤ 379981/5000000:=hg.2.2.2.le
  have hm:=mul_le_mul hp.2.2.2 h1 h0 (by norm_num : (0:ℝ)≤ 1/2)
  unfold Return.kI kMin
  nlinarith only [hm,hp.2.2.2]

/-- Low ordinary length leaves a genuine improved inverse count saving. The
actual original bank width, rather than a centrality assumption, pays the fee. -/
theorem original_ordinary_low_price_paid {r:Row} (hr:r∈rows) {δ p d x m tstar ε ξ:ℝ}
    (hpbox:r.box.Contains (δ,p))
    (hh:hLower≤ Geometry.h) (hh':Geometry.h≤ hUpper) (hell:Geometry.ell=Physical.ell)
    (hd:originalDlow r≤ d) (hdh:d≤ Geometry.h+rowPad)
    (hlength:tstar-x-ε≤ m) (ht:tstar=Return.cutoffI δ p-ξ)
    (hξ:ξ≤ gammaMax) (hε:ε≤ 1/10000000) (hm:2*m≤ anchorLeft) :
    rowPrice δ p (inverseTangentR δ p x) d sourceCost<theta-8*oldFee+2*rowPad := by
  have hav:=original_e49_available hr hpbox
  have hc:=actual_crossing_bounds hr hpbox actual_contact_root
  rw [←actual_contact_width,←actual_contact_intercept,←actual_contact_slope,
    ←actual_cutoff_eq δ p (Return.hJ hav.1 hav.2).ne'] at hc
  have hcross:Return.crossingI δ p=2*Return.cutoffI δ p/3:=by unfold Return.crossingI Return.cutoffI;ring
  have hx:1/100≤ x-Return.crossingI δ p:=by
    rw [hcross]
    norm_num [tLo,gammaMax,anchorLeft] at *
    linarith only [hlength,ht,hξ,hε,hm,hc.1]
  have hk:=original_k_lower hr hpbox
  have hk0:0≤ Return.kI p:=(by norm_num [kMin] : (0:ℝ)≤ kMin).trans hk
  have hdist:=mul_le_mul_of_nonneg_left hx hk0
  have hid:=Return.inverse_identity δ p (Return.hJ hav.1 hav.2).ne'
  have hδp:=original_point_bounds hr hpbox
  have hmul:=mul_le_mul_of_nonneg_left hdist hδp.1
  have hpaid:=original_actual_debit_padded hr hpbox hh hh' hell
    ((by norm_num [Dmin] : (0:ℝ)<Dmin).trans_le ((every_original_band hr (originalSep r)).2.1.trans hd)) hdh
  have hdpos:0≤d:=(by norm_num [Dmin] : (0:ℝ)≤Dmin).trans ((every_original_band hr (originalSep r)).2.1.trans hd)
  have hdu:=mul_le_mul ((every_original_band hr (originalSep r)).2.1.trans hd)
    ((row_endpoint_hull hr).1.1.trans hpbox.1) (by norm_num [dLo]) hdpos
  have hdu0:0≤d*δ:=mul_nonneg hdpos hδp.1
  have hduk:=mul_le_mul hdu hk (by norm_num [kMin]) hdu0
  have hR:inverseTangentR δ p x≤ Return.valueI δ p-δ*Return.kI p/100:=by
    unfold inverseTangentR Return.aI Return.kI at *
    nlinarith only [hmul,hid]
  have hgain:=mul_le_mul_of_nonneg_left hR hdpos
  have hdebit:originalDebit r≤ oldDebitCap:=(every_original_band hr (originalSep r)).1
  unfold inverseTangentR at hgain ⊢
  unfold Return.kI at hgain hduk ⊢
  unfold rowPrice at hpaid ⊢
  norm_num [Dmin,dLo,kMin,oldDebitCap,oldFee] at hduk hdebit ⊢
  nlinarith only [hgain,hpaid,hduk,hdebit]
end QRH.Cycle092.MixedOutsidePaid
#print axioms QRH.Cycle092.MixedOutsidePaid.actual_inverse_tangent_count
#print axioms QRH.Cycle092.MixedOutsidePaid.original_ordinary_low_price_paid
