/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Construct the paid input from the actual original source CellBank and true
same-zero first-short class. Reflection and all native metadata are derived. -/
import Candidate.C092.transport.MixedMiddleReturnPaidSliceReindex
import Candidate.C092.transport.MixedUpperFinalNativeFacts
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true
namespace QRH.Cycle092.MixedMiddleReturn
noncomputable section
attribute [local reducible] QRH.Record1252270103Return.GenericPhysical.BaselineData.toMomentData
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
open HeckeDetectorWitnessRows HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition HeckeDetectorPhysicalSelection
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.ProbeAssembly QRH.Cycle092.SelectedNonfloor QRH.Cycle092.MediumWitness
open QRH.Cycle092.MixedOffsetBank QRH.Cycle092.MixedOffsetCount QRH.Cycle092.PacketJoinE49
open Cycle25.Numerator Cycle25.Weighted.Numerator
open QRH.Cycle092.MixedUpperFinal QRH.Cycle090 QRH.Cycle092.TopData QRH.Cycle092.Mixed
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]
variable {D : BaselineData} {F : BaselineSourceData D} {η : Character}
variable {Z d a : ℝ} {rows : Finset FreeRow} {z : ℂ}
variable {bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t}
variable {t₀ γ τ : ℝ} {i : ℕ}

/-- Lower adapter: its physical phase upper will be supplied internally by
the eventual selected-cell wrapper. No Layout/Presented, count or moment is
assumed; every source bank object is constructed by the native producer. -/
def actual_paid_input (B : CellBank D F η Z d a rows z bin t₀ γ τ i)
    (P : TransportParameters D) (cap : ℝ) (hcap : 0<cap)
    (hfine : ∀s,D.length s ≤ cap/200) (hZ : 1<Z) (hd : (1/100:ℝ) ≤ d) (hdhi : d ≤ 7/8)
    (ha : 51/100<a) (hahi : a ≤ 7/8)
    (hlower : ∀u∈rows,Z^(1/100:ℝ) ≤ rowNorm u)
    (hnp : ∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1)
    (hz : z.re=17/50) (him : |z.im| ≤ (3*i+1:ℕ)*Z^τ)
    (r : Row) (hr : r∈TopData.rows)
    (hp : r.box.Contains (2*a-1,classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)))
    (ht : t₀=Return.cutoffI (2*a-1)
      (classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)))
    (hg : γ=(rowGamma r.box r.B:ℝ)) (hs : D.ε ≤ 3*witnessCollar)
    (σ : Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d)))
    (hne : ((B.layoutCap P (by linarith) hdhi cap hcap hfine).common σ).Nonempty) (j : Offset)
    (first : firstShort (inverseLength (Z^d) σ)=some j)
    (central : centralLengths (inverseLength (Z^d) σ j) (ordinaryLength (Z^d) σ j))
    (narrow : widthLo ≤ ordinaryLength (Z^d) σ j ∧ ordinaryLength (Z^d) σ j ≤ widthHi)
    (h decrement epsilon xi ann loss massEps : ℝ) (J : Finset (Fin D.N))
    (hdold : MixedTicketTails.originalDlow r ≤ d) (hdmax : d ≤ h+rowPad)
    (height : 1+PacketJoin.nativeHeight Z d τ i ≤ Z^d)
    (x : ℂ) (hx : x.re=a+16*D.e)
    (upper : ∀u∈(B.layoutCap P (by linarith) hdhi cap hcap hfine).common σ,∀s : Fin D.N,
      ‖originalPhysical D F Z d (fun _=>z) u s‖ ≤
        (Z^d)^((D.length s/d)*(binValue Finset.univ ((2*a-1)/2) D.t bin s+D.t)))
    (outerFee : ℝ)
    (fee : d*((2*a-1)*(classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1))*decrement+
      D.t*(Geometry.ell/d)+(2*a-1)*(min P.mesh cap)/2+D.ε+
      (countLoss D.ε (min P.mesh cap) D.t+epsilon+loss)/2+massEps)+outerFee
        ≤ paddingDebit+(1/100000000000000:ℝ)) :
    let M:=B.middleCap P cap hcap hfine hZ (by linarith) hdhi ha hahi hlower hz him r hr hp ht hg hs σ hne j first central
    PaidSliceInput h decrement epsilon xi ann loss massEps cap (sourceWidthMin D)
      M.currentSlice.fiber.reverse D F J η Z := by
  let hd' : (1/200:ℝ) ≤ d := by linarith
  let L:=B.layoutCap P hd' hdhi cap hcap hfine
  let M:=B.middleCap P cap hcap hfine hZ hd' hdhi ha hahi hlower hz him r hr hp ht hg hs σ hne j first central
  have hsub : M.currentSlice.fiber.rows ⊆ amplitudeCell D F Z d a rows (fun _=>z) bin :=
    B.capped_rows_subset P hd' hdhi cap hcap hfine σ hne j
  have hn (u : FreeRow) (hu : u∈M.currentSlice.fiber.rows) :
      (rowCharacter F.S F.exclusions.prime u).residue≠1 := hnp u (Finset.mem_filter.mp (hsub hu)).1
  have hslots : M.currentSlice.fiber.slots=Finset.univ := rfl
  have htotal := native_original_total D F M hslots
  have ho := offset_bounds M.γ M.gamma_nonneg M.j
  have hγ : M.γ=(rowGamma r.box r.B:ℝ) := hg
  refine {
    bank:=M,r:=r,row:=hr,point:=hp,d_min:=hd,d_old:=hdold,d_max:=hdmax,d_hi:=hdhi,
    gamma:=hγ,collar:=rfl,factor:=rfl,offset_nonneg:=ho.1,offset_max:=?_,
    reverse_eq:=rfl,T_nonneg:=?_,allowance_nonneg:=?_,height_bound:=height,
    current_slots:=hslots,base_slots:=rfl,base_bin:=rfl,fine:=?_,widths:=?_,row_lower:=?_,row_upper:=?_,
    ordinary_min:=narrow.1,ordinary_max:=narrow.2,x:=x,z:=z,x_re:=hx,z_re:=hz,external_eq:=rfl,
    data:=(fun u=>Classical.choice (physical_reflection_data_exists F.S F.exclusions.prime u.val (hn u.val u.property))),
    nonprincipal:=hn,margin:=?_,slot_upper:=?_,outerFee:=outerFee,fee_paid:=?_ }
  · rw [←hγ];exact ho.2
  · change 0 ≤ Z^τ;positivity
  · change 0 ≤ (Z^d)^(τ/(2*(7/8:ℝ)));positivity
  · exact min_le_right _ _
  · intro s _
    change sourceWidthMin D ≤ D.length s/d
    exact sourceWidthMin_le_normalized D (by linarith) (by linarith) s
  · intro u hu
    exact hlower u (Finset.mem_filter.mp (hsub hu)).1
  · intro u hu
    exact B.row_upper u (hsub hu)
  · rw [hx];linarith [D.e_pos]
  · intro u hu s _
    exact upper u hu s
  · change d*((2*a-1)*(classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1))*decrement+
      D.t*(∑s∈M.currentSlice.fiber.slots,M.currentSlice.fiber.widths s)+(2*a-1)*(min P.mesh cap)/2+D.ε+
      (countLoss D.ε (min P.mesh cap) D.t+epsilon+loss)/2+massEps)+outerFee ≤ _
    rw [htotal]
    exact fee

#print axioms actual_paid_input
end
end QRH.Cycle092.MixedMiddleReturn
