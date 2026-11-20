/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal centered native count on one same-bank subclass, including j=0. -/
import Candidate.C092.transport.MixedOffsetCountNative
set_option autoImplicit false
namespace QRH.Cycle092.MixedOffsetCount
noncomputable section
open scoped Classical BigOperators
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorRawFiber HeckeDetectorWitnessRows HeckeDetectorBatch HeckeDetectorAmplitudeFirst
open HeckeDetectorPhysicalSelection
open QRH.Record12518109Count Cycle25ProbeFinalAssembly
open QRH.Cycle092.PacketJoinE49 QRH.Cycle092.MixedOffsetBank QRH.Cycle092.MixedCenteredFaces

def countLoss (ε mesh t : ℝ) : ℝ := 159*ε+mesh+8*t

def countCoefficient (labels bins : ℕ) (U height K₀ Ki C₀ Cr Ci : ℝ) (J₀ Jr Ji : ℕ) : ℝ :=
  (labels:ℝ)*(dyadicLength U:ℝ)^2*fiberConstant (C₀*(1+height)^J₀) height K₀*(bins:ℝ)+
    192*(1+height)*(Cr*(1+height)^Jr)+12*(1+height)*((Ci*(1+height)^Ji)*Ki)+1

/-- The native rectangle, original paired baseline, and amplified inverse
suppliers are called inside this theorem. Only original source metadata,
common-subclass inclusions and actual geometric gates are inputs. The final
count has one prefactor and one centered deficit on that identical subclass. -/
theorem actual_centered_bank_count (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
    ∃mesh : ℝ→ℝ,(∀t,0<t → 0< mesh t) ∧
    ∀ (D : Cycle25.Weighted.MomentData) (S : WeightedSourceData D),
      (∀s,D.ell s ≤  mesh D.t/200) → (∀s,D.ell s ≤ Cycle25.sourceMesh D.t/200) →
      D.ε ≤ 1/10000000 → D.t ≤ 1/10000000 →
    ∀κplain : ℝ,7/10 ≤ κplain → κplain ≤ 3/4 → 2*HeckeZeroSupremum.beta-1 ≤ κplain →
    ∃K₀ Ki : ℝ,0 ≤ K₀ ∧ 0 ≤ Ki ∧
    ∀η : Character,∃J₀ Jr Ji : ℕ,∃C₀ Cr Ci : ℝ,0<C₀ ∧ 0<Cr ∧ 0<Ci ∧
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀ (d a T allowance height q t₀ γ meshBank εa factor : ℝ) (i : ℕ) (j : Offset),
      (1/200:ℝ) ≤ d → 51/100<a → 2*a-1 ≤ 3/4 →
      0 ≤ height → 2*Real.pi*allowance+(3*i:ℕ)*T ≤ height →
      0 ≤ γ → 1 ≤ t₀-γ → t₀ ≤ 3/2 → 0 ≤ meshBank → 0 ≤ εa → D.ε ≤ 3*εa →
      Return.window.Available (2*a-1) (q/(2*a-1)) →
      t₀=Return.cutoffI (2*a-1) (q/(2*a-1)) →
    ∀ (P₀ : Presented D S η Z d a t₀ T allowance i)
      (P : Presented D S η Z d a (cutoff t₀ γ j) T allowance i)
      (Pprev : Presented D S η Z d a (cutoff t₀ γ (previous j)) T allowance i)
      (F : Slice P) (Fprev : Slice Pprev),
      P₀.batch.rows.Nonempty →
      (∀u∈P₀.batch.rows,rowMean P₀.batch.slots (Z^d) ((2*a-1)/2) P₀.batch.binWidth P₀.batch.widths
        (physical S.modulus ⊤ (fun u:FreeRow=>u.val) P₀.batch.profile P₀.batch.upper
          P₀.batch.widths P₀.batch.external (Z^d)) u=q) →
      (∀s,|(P₀.batch.external s).im| ≤ height) → (∀s,|(P.batch.external s).im| ≤ height) →
      (∀s,|(Pprev.batch.external s).im| ≤ height) →
      P₀.batch.mesh ≤ meshBank → F.fiber.mesh ≤ meshBank →
      F.fiber.q=q → anchorLeft ≤ F.fiber.r → F.fiber.r ≤ anchorTop →
      anchorLeft ≤ 2*F.fiber.m → 2*F.fiber.m ≤ anchorTop →
      (j.val=0 ∨ 1 ≤ Fprev.fiber.r) →
      (2*a-1)*factor ≤ 5/6-(2*a-1) →
    ∀common : Finset FreeRow,common⊆P₀.batch.rows → common⊆F.fiber.rows → common⊆Fprev.fiber.rows →
    let δ:=2*a-1
    let p:=q/δ
    let m:=t₀/3
    let h:=factor*max 0 (offset γ j-γ/65536-3*εa)
    let C:=countCoefficient (Fintype.card (Sum Bool (RayQuotient.Characters S.modulus ⊤)))
      (Fintype.card P₀.batch.Bin) (Z^d) height K₀ Ki C₀ Cr Ci J₀ Jr Ji
    (common.card:ℝ) ≤ C*(Z^d)^(Return.valueI δ p-
      δ*center (Return.kI p) F.fiber.r F.fiber.m m h+countLoss D.ε meshBank D.t) ∧
    ∀lo hi M : ℝ,0 ≤ lo → lo ≤ Return.kI p → Return.kI p ≤ hi → m ≤ M →
      QRH.Cycle090.witnessPenalty lo hi (-hi*(offset γ j+3*εa)) h M F.fiber.m  ≤ 
        Return.kI p*(F.fiber.m-m)+center (Return.kI p) F.fiber.r F.fiber.m m h ∧
      (common.card:ℝ) ≤ C*(Z^d)^(Return.valueI δ p-
        δ*(QRH.Cycle090.witnessPenalty lo hi (-hi*(offset γ j+3*εa)) h M F.fiber.m-
          Return.kI p*(F.fiber.m-m))+countLoss D.ε meshBank D.t) := by
  obtain ⟨mb,hmb,hbase⟩:=q_e49_batch_count hβ
  obtain ⟨mr,hmr,hrect⟩:=actual_rectangle_counts hβ
  let mesh : ℝ→ℝ:=fun t=>min (mb t) (mr t)
  refine ⟨mesh,fun t ht=>lt_min (hmb t ht) (hmr t ht),?_⟩
  intro D S hfine hstandard hεsmall htsmall κplain hk hk' hkβ
  have hfb : ∀s,D.ell s ≤ mb D.t/200:=fun s=>(hfine s).trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have hfr : ∀s,D.ell s ≤ mr D.t/200:=fun s=>(hfine s).trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
  obtain ⟨K₀,hK₀,hbase⟩:=hbase D S hfb hstandard hεsmall κplain hk hk' hkβ
  obtain ⟨Ki,hKi,Ji,hinverse⟩:=QRH.Cycle092.DirectCount.source_inverse_fiber_count D S
  refine ⟨K₀,Ki,hK₀,hKi,?_⟩
  intro η
  obtain ⟨J₀,C₀,hC₀,hbase⟩:=hbase η
  obtain ⟨Jr,Cr,hCr,hrect⟩:=hrect D S hfr η
  obtain ⟨Ci,hCi,hinverse⟩:=hinverse η
  refine ⟨J₀,Jr,Ji,C₀,Cr,Ci,hC₀,hCr,hCi,?_⟩
  filter_upwards [hbase,hrect,hinverse] with Z hbase hrect hinverse
  refine ⟨hbase.1,?_⟩
  intro d a T allowance height q t₀ γ meshBank εa factor i j hd ha hδhi hh hf hγ htlo hthi hmBank hεa hεaBudget hav ht₀
    P₀ P Pprev F Fprev hne₀ hmean him₀ him himprev hmesh₀ hmesh hq hrlo hrhi hmlo hmhi hlong hscale
    common hsub₀ hsub hsubprev
  dsimp only
  let δ:=2*a-1
  let p:=q/δ
  let m:=t₀/3
  let v:=5/6-δ
  let R:=Return.valueI δ p
  let h:=factor*max 0 (offset γ j-γ/65536-3*εa)
  let C:=countCoefficient (Fintype.card (Sum Bool (RayQuotient.Characters S.modulus ⊤)))
    (Fintype.card P₀.batch.Bin) (Z^d) height K₀ Ki C₀ Cr Ci J₀ Jr Ji
  let loss:=countLoss D.ε meshBank D.t
  have hU : 1<Z^d:=Real.one_lt_rpow hbase.1 (by linarith)
  have hδ : 0<δ:=by dsimp [δ];linarith
  have hv : 0 ≤ v:=by dsimp [v,δ];linarith
  have hkpos : 0<Return.kI p:=Return.hk hav.1 hav.2
  have hJ : Return.JI δ p≠0:=(Return.hJ hav.1 hav.2).ne'
  have hR : R=1-δ*(Return.aI p+Return.kI p*(2*m)) := by
    have hid:=Return.inverse_identity δ p hJ
    have hcross : Return.crossingI δ p=2*m := by
      dsimp [Return.crossingI,m];rw [ht₀];dsimp [Return.cutoffI,p,δ];ring
    rw [hcross] at hid
    exact hid.symm
  have hRlong : R=1/6+v*(3*m) := by
    have hid:=Return.long_identity δ p hJ
    rw [←ht₀] at hid
    dsimp [R,m,v];linarith only [hid]
  have hCbase : 0 ≤ (Fintype.card (Sum Bool (RayQuotient.Characters S.modulus ⊤)):ℝ)*
      (dyadicLength (Z^d):ℝ)^2*fiberConstant (C₀*(1+height)^J₀) height K₀*(Fintype.card P₀.batch.Bin:ℝ) := by
    unfold fiberConstant;positivity
  have hCr0 : 0 ≤ 192*(1+height)*(Cr*(1+height)^Jr):=by positivity
  have h12Cr : 12*(1+height)*(Cr*(1+height)^Jr) ≤ 192*(1+height)*(Cr*(1+height)^Jr) := by
    apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_right (by norm_num : (12:ℝ) ≤ 192) (by linarith only [hh])
    · positivity
  have hCi0 : 0 ≤ 12*(1+height)*((Ci*(1+height)^Ji)*Ki):=by positivity
  have hC : 0 ≤ C:=by dsimp [C,countCoefficient];positivity
  have promote (large : Finset FreeRow) (hs : common⊆large) (c₁ E₁ E₂ : ℝ)
      (hc₁ : c₁ ≤ C) (hc : (large.card:ℝ) ≤ c₁*(Z^d)^E₁) (hE : E₁ ≤ E₂) :
      (common.card:ℝ) ≤ C*(Z^d)^E₂ := by
    exact (MixedOffsetBank.common_count common large hs c₁ (Z^d) E₁ hc).trans
      ((mul_le_mul_of_nonneg_right hc₁ (Real.rpow_nonneg (zero_lt_one.trans hU).le _)).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.le hE) hC))
  have hbaseActual := hbase.2 P₀.batch.rows P₀.lower d hd a T allowance D.t height q i
    ha hδhi D.t_pos htsmall (le_refl _) hh hf hav
  rw [←ht₀] at hbaseActual
  have hb:=hbaseActual P₀.batch hne₀ (fun _ hu=>hu) P₀.data P₀.profile P₀.widths P₀.upper P₀.real him₀ hmean
  have hb' : (common.card:ℝ) ≤ C*(Z^d)^(R+loss) := by
    apply promote _ hsub₀ _ _ _ (by dsimp [C,countCoefficient];linarith only [hCr0,hCi0]) hb
    dsimp [R,loss,countLoss,δ,p];linarith
  have hr:=hrect.2 d hd a _ T allowance height i P F (by linarith) htsmall hh him hf hrlo hrhi hmlo hmhi
  rw [hq] at hr
  have hqBounds:=F.fiber.mean_bounds (by linarith : 1/2 ≤ a)
  rw [hq] at hqBounds
  have hqt : 2*q ≤ 1:=by dsimp [δ] at hδ;linarith [hqBounds.2]
  have hloss : 2*q*D.t+4*D.ε+δ*F.fiber.mesh+D.t ≤ loss := by
    have hmt:=mul_le_mul_of_nonneg_left hmesh hδ.le
    have hmt' := mul_le_mul_of_nonneg_right (show δ ≤ 1 by dsimp [δ];linarith) hmBank
    have hqt' := mul_le_mul_of_nonneg_right hqt D.t_pos.le
    dsimp [loss,countLoss];linarith only [hmt,hmt',hqt',D.epsilon_pos,D.t_pos]
  have hI : (common.card:ℝ) ≤ C*(Z^d)^(1-δ*(Return.aI p+Return.kI p*F.fiber.r)+loss) := by
    apply promote _ hsub _ _ _ (by dsimp [C,countCoefficient];linarith only [hCbase,hCi0,h12Cr]) hr.1
    dsimp [δ,p];dsimp [δ] at hloss;linarith [D.epsilon_pos]
  have hO : (common.card:ℝ) ≤ C*(Z^d)^(1-δ*(Return.aI p+2*Return.kI p*F.fiber.m)+loss) := by
    apply promote _ hsub _ _ _ (by dsimp [C,countCoefficient];linarith only [hCbase,hCi0]) hr.2
    dsimp [δ,p];dsimp [δ] at hloss;linarith
  have hprev : (common.card:ℝ) ≤ C*(Z^d)^(R-δ*h+loss) := by
    apply predecessor_count common hU.le hC hv hscale hRlong hb'
    intro hpositive
    have hj : 0<j.val := by
      rcases hlong with hj0|hl
      · have hz : offset γ j=0:=by simp [offset,hj0]
        rw [hz] at hpositive
        have hs : 0 ≤ γ/65536:=by positivity
        linarith
      · by_contra hj
        have hj0 : j.val=0:=Nat.eq_zero_of_not_pos hj
        have hz : offset γ j=0:=by simp [offset,hj0]
        rw [hz] at hpositive
        have hs : 0 ≤ γ/65536:=by positivity
        linarith
    have hrlong : 1 ≤ Fprev.fiber.r:=hlong.resolve_left (Nat.ne_of_gt hj)
    have hgeom:=Fprev.fiber.lengths hU
    have htprev := (cutoff_bounds t₀ γ hγ htlo hthi (previous j)).2
    have hr2 : Fprev.fiber.r ≤ 2:=by linarith [D.epsilon_pos,hgeom.2.1]
    have hp:=hinverse.2 d hd a D.ε _ T allowance i Pprev.batch Pprev.data Pprev.profile Pprev.upper
      Pprev.widths Pprev.real Fprev.bin Fprev.label Fprev.left Fprev.right Fprev.nonempty height hh (by linarith) hf
      (by linarith) hr2
    have hcprev : cutoff t₀ γ (previous j) ≤ 3*m-(offset γ j-γ/65536-3*εa) := by
      dsimp only [cutoff,m]
      rw [previous_offset γ hγ j]
      have hz:=le_max_right 0 (offset γ j-γ/65536)
      linarith only [hz,hεa]
    refine ⟨hcprev,?_⟩
    apply promote _ hsubprev _ _ _ (by dsimp [C,countCoefficient];linarith only [hCbase,hCr0]) hp
    have hmax : (1:ℝ) ≤ (1+5*Fprev.fiber.r)/6:=by linarith
    dsimp [HeckeInverseAmplification.sourceExponent]
    rw [max_eq_right hmax]
    have hupper:=mul_le_mul_of_nonneg_left hgeom.2.1 hv
    have hv1 : v ≤ 1:=by dsimp [v];linarith only [hδ]
    have hve:=mul_le_mul_of_nonneg_right hv1 D.epsilon_pos.le
    dsimp [v,δ,loss,countLoss] at hupper hve ⊢
    nlinarith only [hupper,hve,D.epsilon_pos,D.t_pos,hmBank]
  have hcentered:=centered_count common hU.le hδ.le hkpos.le hR hb' hI hO hprev
  refine ⟨hcentered,?_⟩
  intro lo hi M hlo hklo hkhi hmM
  have hsupport : 3*m-offset γ j-3*εa ≤ F.fiber.r+F.fiber.m := by
    have hs:=F.fiber.lengths hU
    dsimp [cutoff,m] at hs ⊢
    linarith only [hs.1,hεaBudget]
  have hpen:=directed_penalty (step:=γ/65536) (h:=h) hlo hklo hkhi hmM
    (offset_bounds γ hγ j).1 (by positivity : 0 ≤ 3*εa) hsupport
  change QRH.Cycle090.witnessPenalty lo hi (-hi*(offset γ j+3*εa)) h M F.fiber.m ≤
    Return.kI p*(F.fiber.m-m)+center (Return.kI p) F.fiber.r F.fiber.m m h at hpen
  refine ⟨hpen,?_⟩
  apply hcentered.trans
  apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.le ?_) hC
  have hmul:=mul_le_mul_of_nonneg_left hpen hδ.le
  change R-δ*center (Return.kI p) F.fiber.r F.fiber.m m h+loss ≤
    R-δ*(QRH.Cycle090.witnessPenalty lo hi (-hi*(offset γ j+3*εa)) h M F.fiber.m-
      Return.kI p*(F.fiber.m-m))+loss
  nlinarith only [hmul]

#print axioms actual_centered_bank_count
end
end QRH.Cycle092.MixedOffsetCount
