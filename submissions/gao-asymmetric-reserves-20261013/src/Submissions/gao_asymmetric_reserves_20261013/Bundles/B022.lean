/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B008
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B009
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B019
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B020
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyData
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedPhysicalRows
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceDeletedEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceFiberEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorDictionarySlots
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryUniformHeight
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainSlotProfile
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.RetainedEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.FirstProduct

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.MomentDetectorPlainSlotProfile ; sha256 03e71e4132a6213e5aa9d49e479e27c618992d7d60e697cf57cc46dbbb70b4b9 -/
section






namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
namespace SevenEighths.Cycle25CenteredMomentDetectorPlainSlotProfile
open CenteredMomentDetectorPlainSlotProfile Cycle25ProbeFinalAssembly
open HeckeFamily HeckeInverseAmplification HeckeDyadic CenteredMomentDetectorDictionary
open CenteredMomentRetainedEnergy
variable {D:Cycle25.Weighted.MomentData}

lemma weighted_conjugate_source_support (F:Cycle25ProbeFinalAssembly.WeightedSourceData D):
    Function.support (fun x=> conj (F.W x))⊆Set.Icc (1:ℝ) 2 := by
  intro x hx
  exact F.complex_support (by simpa using hx)

end SevenEighths.Cycle25CenteredMomentDetectorPlainSlotProfile

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.MomentDetectorPlainSlotProfile -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.MomentInverseMarkedReferenceFiberEnergy ; sha256 d4a2cf2d0df59d8444accd38e5df98068f96d06bb81f945792572927be7712e0 -/
section




namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.Cycle25DetectorDictionaryInverseMarkedReference
open DetectorDictionaryInverseMarkedReference Cycle25ProbeFinalAssembly
open HeckeFamily HeckeInverseAmplification HeckeDyadic HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer InverseMoment InverseInitialProfile
open ConcreteTraceCRT ConcretePrimeRowBridge CanonicalRowCompletion
open DetectorDictionaryInverseRawInitialGates DetectorDictionaryInverseMarkedPhysicalRows
open InverseInitialPhysicalSlots IdealMobiusDivisorSum
local notation "O"=> HeckeFamily.O

theorem weighted_fiber_reference_energy {D:Cycle25.Weighted.MomentData}
    (S:Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (W:ℝ→ℂ)(ao bo:ℝ)(hao:0< ao)(hab:ao ≤ bo)
    (hsW:Function.support W⊆Set.Icc ao bo)(hW:ContDiff ℝ ∞ W)
    (εm:ℝ)(hεm:0<εm)(K:ℕ):
    ∃degree:ℕ,∀data:RowData,∃C U₀:ℝ,0< C ∧ 1< U₀ ∧
    ∀U:ℝ,U₀ ≤ U →
    ∀(M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)
      {Label Slot:Type}{a ε tstar T allowance:ℝ}{i:ℕ}
      (F:Fiber M H Label Slot U a ε tstar T allowance i)(selected:Finset Slot),
      F.rowData=data → selected.card ≤ K →
      (∀s∈selected,F.profile s=S.W) → (∀s∈selected,F.upper s=2) →
      (∀s∈selected,0 ≤ F.widths s) → (∀s∈selected,(F.external s).re ≤ 1) →
      (((Finset.univ:Finset selected):Set selected).PairwiseDisjoint (fiberLists F selected)) →
      (∀s∈selected,((deletedBase data).modulus.absNorm:ℝ)< U^(F.widths s)) →
      0 ≤ F.r → F.r+2*(∑s∈selected,F.widths s)<1 →
      2*F.r+8*(∑s∈selected,F.widths s)<3 → ∀v:ℝ,
      (∑u∈F.rows,‖polynomial (F.family u F.label) true (childLogTest W v) (U^F.r) 0 0*
        F.physicalProduct selected u‖^2) ≤ C*U^(1+εm)*((1+‖v‖)^degree)^2 := by
  have hsor (b:Bool):Function.support (orientedProfile b W)⊆Set.Icc ao bo := by
    cases b
    · exact hsW
    · intro x hx
      apply hsW
      simpa [orientedProfile] using hx
  have hWor (b:Bool):ContDiff ℝ ∞ (orientedProfile b W) := by
    cases b
    · exact hW
    · exact Complex.conjCLE.contDiff.comp hW
  choose J hj using fun b:Bool=> weighted_deleted_source_energy S (orientedProfile b W) ao bo hao hab
    (hsor b) (hWor b) εm hεm K
  refine ⟨∑b:Bool,J b,?_⟩
  intro data
  choose C U₀ hC hU₀ hb using fun b:Bool=> hj b data
  let Tbad:=idealDivisors (∏P∈excluded data,P)
  let Ctotal:ℝ:=((Tbad.card:ℝ)+1)^2*(∑b:Bool,C b)
  have hCsum:0<∑b:Bool,C b:=Finset.sum_pos (fun b _=> hC b) Finset.univ_nonempty
  refine ⟨Ctotal,max (U₀ false) (U₀ true),by dsimp [Ctotal];positivity,
    lt_max_of_lt_left (hU₀ false),?_⟩
  intro U hU M neM H Label Slot a ε tstar T allowance i F selected hdata hK hprofile hupper
    hell hext hdis hlarge hr hfirst hsecond v
  have hUb (b:Bool):U₀ b ≤ U:=by cases b <;> exact le_trans (by simp) hU
  have hUone:1< U:=(hU₀ false).trans_le (hUb false)
  have hpr (s:selected):F.profile s=S.W:=hprofile s s.property
  have hup (s:selected):F.upper s=2:=hupper s s.property
  have hprof:(fun s:selected=> F.profile s)=(fun _=>(S.W:ℝ→ℂ)):=funext hpr
  have hups:(fun s:selected=> F.upper s)=(fun _=>2):=funext hup
  have hslots:∀s∈selected,∀x,F.profile s x≠0 → x∈Set.Icc (1:ℝ) (F.upper s) := by
    intro s hs x hx
    rw [hprofile s hs] at hx
    rw [hupper s hs]
    exact S.complex_support hx
  have hlarge':∀s∈selected,((deletedBase F.rowData).modulus.absNorm:ℝ)<1*U^(F.widths s):=by
    simpa only [hdata,one_mul] using hlarge
  have hphys:=fiber_child_rows_le_deleted_sources F selected W v bo (fun _=>1) hUone
    (fun x hx=>(hsW hx).2) hslots hlarge'
  rw [hdata] at hphys
  let rows:Finset O:=F.rows.image (fun u=> u.val)
  have hsum (f:O→ℝ):(∑u∈rows,f u)=∑u∈F.rows,f u.val:=
    Finset.sum_image (fun u _ w _ he=> Subtype.ext he)
  have hrows:∀u∈rows,‖eisEmbedding u‖^2 ≤ U := by
    intro u hu
    obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hu
    rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
    exact F.row_norm w hw
  have hpow (b:Bool):((1+‖orientedFrequency b v‖)^(J b))^2 ≤
      ((1+‖v‖)^(∑b:Bool,J b))^2 := by
    have hn:‖orientedFrequency b v‖=‖v‖:=by cases b <;> simp [orientedFrequency]
    rw [hn]
    apply pow_le_pow_left₀ (by positivity)
    apply pow_le_pow_right₀ (by linarith [norm_nonneg v])
    exact Finset.single_le_sum (fun b _=> Nat.zero_le _) (Finset.mem_univ b)
  have hterm (j:Ideal O)(hj:j∈Tbad):
      (∑u∈F.rows,‖deletedSelectedSource data M H
        (childLogTest (orientedProfile F.reverse W) (orientedFrequency F.reverse v))
        (fun s:selected=> F.profile s) U (shiftedExponent data U F.r j)
        0 0 bo (fun s:selected=> F.upper s) (fun s:selected=> F.widths s)
        (fun s:selected=> F.external s) u.val‖^2) ≤
      (∑b:Bool,C b)*U^(1+εm)*((1+‖v‖)^(∑b:Bool,J b))^2 := by
    rw [hprof,hups]
    have hdis':((Finset.univ:Finset selected):Set selected).PairwiseDisjoint
        (fun s:selected=> livePrimes M H S.W 2 (U^(F.widths s))) := by
      have heL:fiberLists F selected=(fun s:selected=> livePrimes M H S.W 2 (U^(F.widths s))) := by
        funext s
        dsimp only [fiberLists]
        rw [hpr s,hup s]
      rwa [heL] at hdis
    have hh:=hb F.reverse U (hUb F.reverse) (by simpa using hK)
      M H (fun s:selected=> F.widths s) (fun s:selected=> F.external s)
      (fun s=> hell s s.property) (fun s=> hext s s.property) hdis'
      (fun s=> hlarge s s.property) F.r hr
      (by simpa only [Finset.sum_coe_sort] using hfirst)
      (by simpa only [Finset.sum_coe_sort] using hsecond) j hj rows hrows (orientedFrequency F.reverse v)
    rw [hsum] at hh
    refine hh.trans ?_
    apply mul_le_mul _ (hpow F.reverse) (by positivity) (by positivity)
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
    exact Finset.single_le_sum (fun b _=>(hC b).le) (Finset.mem_univ F.reverse)
  refine hphys.trans ?_
  change (Tbad.card:ℝ)*(∑j∈Tbad,_) ≤ _
  calc
    _ ≤ (Tbad.card:ℝ)*(∑j∈Tbad,(∑b:Bool,C b)*U^(1+εm)*
        ((1+‖v‖)^(∑b:Bool,J b))^2):=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
    _=(Tbad.card:ℝ)^2*(∑b:Bool,C b)*U^(1+εm)*((1+‖v‖)^(∑b:Bool,J b))^2:=by
      simp only [Finset.sum_const,nsmul_eq_mul];ring
    _ ≤ Ctotal*U^(1+εm)*((1+‖v‖)^(∑b:Bool,J b))^2:=by
      dsimp [Ctotal]
      gcongr
      nlinarith [show 0 ≤ (Tbad.card:ℝ) by positivity]

end SevenEighths.Cycle25DetectorDictionaryInverseMarkedReference

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.MomentInverseMarkedReferenceFiberEnergy -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.Parameters ; sha256 56d3cc62a8de51e0089b351a98959a3ea4ed905db08cb426c9f7f12d751b1197 -/
section





namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.Cycle25ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst Cycle25DetectorRowCount

structure CountParameters (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (εm : ℝ) where
  c : ℝ
  k : ℝ
  c_pos : 0< c
  c_one : c≤1
  k_pos : 0< k
  balanced : ∃K₀ : ℝ,0≤ K₀ ∧ ∀ᶠU : ℝ in atTop,
      ∀(a ε T allowance κplain ν C height q : ℝ) (i : ℕ),
      1< U → 51/100< a → 2*a-1≤3/4 → 0≤ε → ε≤1/1000 →
      7/10≤κplain → κplain≤3/4 → 0<ν → 0≤ C → 0≤ height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤ height →
      ∀{Label Slot : Type} [Fintype Label] (B : Batch M H Label Slot U a ε (cutoff (2*a-1) (q/(2*a-1)) κplain) T allowance i),
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=> u.val) B.profile B.upper B.widths B.external U) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Cycle25DetectorRawFiber.Moments (B.fiber bin j J K hne) κplain c k C height εm) →
      (B.rows.card:ℝ)≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2* fiberConstant C height K₀*
        (Fintype.card B.Bin:ℝ)*
        U^(rowCount (2*a-1) (q/(2*a-1)) κplain+
          159*ε+εm+B.mesh+7*ν)

theorem exists_count_parameters
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm : ℝ) (hεm : 0<εm) :
    Nonempty (CountParameters M H εm) := by
  obtain ⟨c,k,K,hc,hc1,hk,hK,hcount⟩ := balanced_adaptive_count_from_raw_moments
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  exact ⟨⟨c,k,hc,hc1,hk,⟨K,hK,hcount⟩⟩⟩

end SevenEighths.Cycle25ProbeHighRowFamily
end
end OAI
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.Parameters -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.HighDataFine ; sha256 e760738de7c4bfd5033f9e40f5e5b48c6d730a896956e62db7b4cf68553a2b49 -/
section


noncomputable section
open scoped BigOperators

namespace Cycle25.HighParameters
open OAI.SevenEighths.Parameters

theorem exists_high_data_fine (Δ:ℝ)(hΔ:0<Δ)
    (kap : ℝ) (hkaplo : 7/10 ≤ kap) (hkaphi : kap ≤ 3/4)
    (hkapbeta : 2*OAI.SevenEighths.HeckeZeroSupremum.beta-1 ≤ kap)
    (hkapexact : kap = 2*OAI.SevenEighths.HeckeZeroSupremum.beta-1)
    (mesh:ℝ→ℝ)
    (hmesh:∀t:ℝ,0 < t→0 < mesh t):
    ∃D:HighData Δ,∀j,D.ell j ≤ mesh D.t/200:=by
  let t := min (Δ/100000) (1/100000000)
  have ht : 0 < t := lt_min (by positivity) (by norm_num)
  have htΔ : t < Δ/4 := by have hh := min_le_left (Δ/100000) (1/100000000); dsimp [t]; linarith only [hh,hΔ]
  have htgap : t ≤ Δ/100000 := min_le_left _ _
  have ht1 : t ≤ 1/100000000 := min_le_right _ _
  obtain ⟨N,hN,ell,rmin,hr,hell,hsum,hbounds,_⟩ :=
    Cycle25.HighParameters.exists_physical_slot_lengths (1/200) (7/8) (min t (mesh t)) t (by norm_num) (by norm_num)
      (lt_min ht (hmesh t ht)) ht
  let allowance := t/((N:ℝ)+2000)
  have ha : 0 < allowance := div_pos ht (by positivity)
  let small := min allowance (t/((N:ℝ)+2000))
  have hsmall : 0 < small := lt_min ha (div_pos ht (by positivity))
  have hsa : small ≤ allowance := min_le_left _ _
  have hst : small ≤ t/((N:ℝ)+2000) := min_le_right _ _
  have hst0 : small ≤ t/2000 := hst.trans
    (div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) N]))
  let ellMin := (7/8:ℝ)*rmin
  have hmin : 0 < ellMin := mul_pos (by norm_num) hr
  obtain ⟨ε,e,κ,cost,τ₀,hε,hε1,hεgap,hεa,he,he1,heell,hea,hκ,hκ1,hcost,
    hdet,hphase,_,_,_,_,_⟩ :=
    exists_detector_scales t rmin t (1/200) t ellMin small 0
      ht.le hr ht (by norm_num) ht hmin hsmall (by norm_num)
  let eps := small/2
  have heps : 0 < eps := by dsimp [eps];positivity
  have hepss : eps ≤ small := by dsimp [eps];linarith only [hsmall]
  have heps1 : eps≤1 := by linarith only [hepss, hst0, ht1]
  have heN : ((N:ℝ)+2000)*eps ≤ t := by
    have h := (le_div_iff₀ (show 0<(N:ℝ)+2000 by positivity)).mp (hepss.trans hst)
    simpa only [mul_comm] using h
  have he8 : ((N:ℝ)+8)*eps ≤ t := by nlinarith only [heN, heps.le]
  have het : 2000*e ≤ t := by linarith only [hea, hst0]
  have hεt : 2000*ε ≤ t := by linarith only [hεa,hst0]
  let sigma := min (t/2) (ellMin/4)
  have hs : 0 < sigma := lt_min (by positivity) (by positivity)
  have hst2 : sigma ≤ t/2 := min_le_left _ _
  have hsell : sigma ≤ ellMin/4 := min_le_right _ _
  refine ⟨{
    momentKappa:=kap,momentKappa_lo:=hkaplo,momentKappa_hi:=hkaphi,momentKappa_beta:=hkapbeta,
    momentKappa_exact:=hkapexact,
    t:=t,N:=N,ell:=ell,rmin:=rmin,ε:=ε,e:=e,κ:=κ,cost:=cost,eps:=eps,sigma:=sigma
    t_pos:=ht,t_delta:=htΔ,t_gap:=htgap,t_small:=ht1,slots_pos:=hN,slots_injective:=hell,slots_sum:=hsum
    slots_bounds:=fun j=>⟨(hbounds j).1,(hbounds j).2.1,(hbounds j).2.2.2⟩
    rmin_pos:=hr,epsilon_pos:=hε,epsilon_small:=hε1,epsilon_gap:=hεgap
    e_pos:=he,e_small:=he1,kappa_pos:=hκ,kappa_small:=hκ1,cost_pos:=hcost
    eps_pos:=heps,eps_small:=heps1,sigma_pos:=hs,detector_budget:=by linarith only [hdet]
    phase_budget:=hphase,central_budget:=by
      have hell := Cycle25.ell_lt_one_fifth
      have hprod := mul_le_mul_of_nonneg_left hell.le ht.le
      nlinarith only [hεt,het,he8,ht1,htgap,hprod,ht]
    geometric_budget:=by linarith only [hst2, het, ht1]
    principal_budget:=by linarith only [hst2, ht1]
    window_budget:=by
      change sigma+e ≤ Cycle25.theta*ellMin
      have hc := mul_le_mul_of_nonneg_right Cycle25.theta_gt_half.le hmin.le
      linarith only [hsell,heell,hmin,hc]
    floor_budget:=by
      have hprod := mul_le_mul_of_nonneg_left Cycle25.ell_lt_one_fifth.le ht.le
      linarith only [hst2,het,he8,ht1,hprod]
    high_saving:=by linarith only [hst2,htgap,ht]
    weighted_top:=by norm_num [Cycle25.rowExtension]; linarith only [ht1]
    height_choice:=?_ },?_⟩
  · intro J hJ
    let τ := min ((1/200:ℝ)*cost/16) (min (1/800) (t/(4*(J+7))))
    have htau : 0<τ := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
    have hτc : τ≤(1/200:ℝ)*cost/16 := min_le_left _ _
    have hτd : τ≤1/800 := (min_le_right _ _).trans (min_le_left _ _)
    have hτt : τ ≤ t/(4*(J+7)) := (min_le_right _ _).trans (min_le_right _ _)
    have hτJ : τ*(4*(J+7)) ≤ t := (le_div_iff₀ (by positivity)).mp hτt
    have hprod : 0≤τ*J := mul_nonneg htau.le hJ
    have hprodeps := mul_le_mul_of_nonneg_left heps1 htau.le
    refine ⟨τ,htau,by linarith only [hτd],by linarith only [hτc, hcost],
      by nlinarith only [hτJ, hprod, htau],by nlinarith only [hτJ, hprod, htau],
      by nlinarith only [hτJ, hprod, hprodeps, htau]⟩
  · intro j
    change ell j ≤ mesh t/200
    calc
      ell j≤(1/200:ℝ)*min t (mesh t):=(hbounds j).2.2.1
      _≤(1/200:ℝ)*mesh t:=mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
      _=mesh t/200:=by ring

theorem fine_slot_widths {Δ:ℝ}(D:HighData Δ)(mesh:ℝ→ℝ)
    (hmesh:0 < mesh D.t)(hfine:∀j,D.ell j ≤ mesh D.t/200)
    (d:ℝ)(hd:(1/200:ℝ) ≤ d)(j:Fin D.N):
    0 < D.ell j/d ∧ D.ell j/d ≤ mesh D.t:=by
  have hd0:0 < d:=by linarith
  refine ⟨div_pos (D.slots_bounds j).1 hd0,(div_le_iff₀ hd0).mpr ?_⟩
  have hh:=hfine j
  nlinarith

end Cycle25.HighParameters

end


/- Adapted from weighted numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/
end
/- END ORIGINAL MODULE Cycle25.Assembly.HighDataFine -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.ReferenceLowWindow ; sha256 85ba6c12dbbbae8de07593c8f9e04afff7bf67f23d892fa3184383e2925758a6 -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/ReferenceLowWindow.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/




namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.Cycle25CenteredMomentEnergyReferenceLowWindow
open HeckeFamily CenteredMomentEnergyBands Cycle25CenteredMomentEnergyReferenceState
open Cycle25CenteredMomentEnergyReferenceLowBranchGeometry
local notation "O"=> HeckeFamily.O

lemma reflection_window_length (Z R x:ℝ)(hZ:1< Z)(hR:0≤ R)
    (hx:x∈Set.Icc 0 (R*Real.log Z)):
    length Z (Real.exp x)≤ R ∧ Real.exp x≤ Z^R:=by
  have hlog:0< Real.log Z:=Real.log_pos hZ
  have hexp:Real.exp x≤ Z^R:=by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans hZ)]
    apply Real.exp_le_exp.mpr
    simpa [mul_comm] using hx.2
  refine ⟨?_,hexp⟩
  have hmax:max 1 (Real.exp x)≤ Z^R:=
    max_le (Real.one_le_rpow hZ.le hR) hexp
  have hl:=Real.logb_le_logb_of_le hZ
    (lt_of_lt_of_le zero_lt_one (le_max_left 1 (Real.exp x))) hmax
  simpa only [length,Real.logb_rpow (zero_lt_one.trans hZ) (ne_of_gt hZ)] using hl

theorem deleted_reference_window (Z M X₁ X₂ ell z kappa xi:ℝ)
    (hZ:1< Z)(hM:0≤ M)(hX₁:0< X₁)(hX₂:0< X₂)(hell:0≤ ell)(hz:0≤ z)(hze:z≤ ell)
    (hk:7/10≤ kappa)(hxi:0≤ xi)(hxiM:xi≤ M/16)
    (hlarge:5*M/6≤ Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*kappa-1)*ell≤ M)
    (D₁ D₂:Finset (Ideal O))(hD₁:∀I∈D₁,Prime I)(hD₂:∀I∈D₂,Prime I):
    let short:=length Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ));
    let along:=Real.logb Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ));
    (short+length Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))+z≤5*M/6 ∧
      short+length Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))+6*kappa*z≤ M) ∨
    (0< along ∧ ∀x∈Set.Icc 0 (max 0 (M-along+xi)*Real.log Z),
      length Z (Real.exp x)+short+z≤5*M/6 ∧
      length Z (Real.exp x)+short+6*kappa*z≤ M):=by
  dsimp only
  let along:=Real.logb Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))
  rcases deleted_reference_cases Z M X₁ X₂ ell z kappa xi (max 0 (M-along+xi))
    hZ hM hX₁ hX₂ hell hz hze hk hxi hlarge hcap D₁ D₂ hD₁ hD₂ le_rfl with h|h
  · exact Or.inl h
  · refine Or.inr ⟨h.1,?_⟩
    intro x hx
    have hh:=reflection_window_length Z (max 0 (M-along+xi)) x hZ (le_max_left _ _) hx
    have hb:=reflected_low_admissible M xi _ (max 0 (M-along+xi)) z kappa hxiM h.2.1 h.2.2
    constructor <;> linarith [hh.1]

end SevenEighths.Cycle25CenteredMomentEnergyReferenceLowWindow

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Energy.ReferenceLowWindow -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorPrimeExpansion ; sha256 f819b71b8d633aee7831954c636c38465f2462cbb734d9a032b318be9aab2f95 -/
section



/-! Absolute Dirichlet expansion of the actual unramified correction product. -/
noncomputable section
open scoped BigOperators NNReal Classical
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

def QuadraticCoefficients.vector (c : QuadraticCoefficients) : Fin 3 → ℂ := ![c.a,c.b,c.c]

theorem quadratic_vector_eval (c : QuadraticCoefficients) (T : ℂ) :
    (∑ j : Fin 3, c.vector j * T ^ j.val) = c.eval T := by
  simp [QuadraticCoefficients.vector, QuadraticCoefficients.eval, quadratic, Fin.sum_univ_three]

theorem quadratic_vector_mass (c : QuadraticCoefficients) (Q : ℝ≥0) (w : ℂ)
    (hQ : 0 < (Q : ℝ)) :
    (∑ j : Fin 3, ‖c.vector j * ((Q : ℂ) ^ (-w)) ^ j.val‖) =
      c.mass ((Q : ℝ) ^ (-w.re)) := by
  simp [QuadraticCoefficients.vector, QuadraticCoefficients.mass, quadraticMass,
    Fin.sum_univ_three, norm_mul, norm_pow,
    Complex.norm_cpow_eq_rpow_re_of_pos hQ, Complex.neg_re]

def primeScale (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) : ℝ≥0 := P.val.absNorm

def actualUnramifiedCoefficients (η : Character) (u : FreeRow) (x z : ℂ)
    (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) : Fin 3 → ℂ :=
  if P.val ∣ Ideal.span {u.val} then 0 else
    (unramifiedDefectCoefficients P.val.absNorm
      (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val)
      (idealRowHom u.val P.val) x z).vector

theorem actual_unramified_local_expansion (η : Character) (u : FreeRow) (x w z : ℂ)
    (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : 4 ≤ P.val.absNorm)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re) :
    unramifiedFactor η u P x w z =
      1 + ∑ j : Fin 3, localMellinTerm primeScale (actualUnramifiedCoefficients η u x z) w P j := by
  by_cases hram : P.val ∣ Ideal.span {u.val}
  · simp only [unramifiedFactor, localMellinTerm, actualUnramifiedCoefficients,
      hram, ite_true, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  · simp only [unramifiedFactor, localMellinTerm, actualUnramifiedCoefficients,
      hram, ite_false]
    have hQ : (4 : ℝ) ≤ P.val.absNorm := by exact_mod_cast hP
    obtain ⟨hR,hV,hD⟩ := unramified_denominators P.val.absNorm
      (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val)
      (idealRowHom u.val P.val) x z hQ (actualAPhase_norm_le_one η _)
      (idealCoeff_norm_le_one η _) (idealRowHom_norm u.val _) hx hz
    have he := unramified_defect_expansion P.val.absNorm
      (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val)
      (idealRowHom u.val P.val) x w z (by linarith) hR hV hD
    rw [quadratic_vector_eval]
    change idealUnramifiedCorrection η u P x w z = _
    dsimp only [idealUnramifiedCorrection]
    change _ = 1 + (unramifiedDefectCoefficients _ _ _ _ _ _).eval _
    simpa only [primeScale, NNReal.coe_natCast, Complex.ofReal_natCast] using
      (eq_add_of_sub_eq he).trans (add_comm _ _)

theorem actual_unramified_local_mass (eps : ℝ) (η : Character) (u : FreeRow) (x w z : ℂ)
    (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : 4 ≤ P.val.absNorm) (heps : 0 < eps)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re)
    (hw : -(1 / 100 : ℝ) ≤ w.re) (hxw : 1 + eps ≤ x.re + w.re) :
    localMass (localMellinTerm primeScale (actualUnramifiedCoefficients η u x z) w) P ≤
      3 * firstPrimeDefectBound eps P := by
  unfold localMass localMellinTerm actualUnramifiedCoefficients
  split_ifs
  · simp only [Pi.zero_apply, zero_mul, norm_zero, Finset.sum_const_zero]
    exact mul_nonneg (by norm_num) (firstPrimeDefectBound_nonneg eps P)
  · have hQ : (4 : ℝ) ≤ P.val.absNorm := by exact_mod_cast hP
    rw [quadratic_vector_mass _ _ _ (by change (0 : ℝ) < P.val.absNorm; linarith)]
    have hh := unramified_defect_coefficient_mass P.val.absNorm w.re eps
      (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val)
      (idealRowHom u.val P.val) x z hQ (actualAPhase_norm_le_one η _)
      (idealCoeff_norm_le_one η _) (idealRowHom_norm u.val _) heps hx hz hw hxw
    simpa only [primeScale, NNReal.coe_natCast, firstPrimeDefectBound,
      show (720 : ℝ) = 3 * 240 by norm_num, mul_assoc] using hh

theorem actual_unramified_local_mass_summable (eps : ℝ) (S : Finset (Ideal O))
    (hS : FirstTail eps S) (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re)
    (hw : -(1 / 100 : ℝ) ≤ w.re) (hxw : 1 + eps ≤ x.re + w.re) :
    Summable (localMass (localMellinTerm
      (fun P : {P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal // P.val ∉ S} => primeScale P.val)
      (fun P => actualUnramifiedCoefficients η u x z P.val) w)) := by
  apply (hS.summable.mul_left 3).of_nonneg_of_le
  · intro P
    exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  · intro P
    exact actual_unramified_local_mass eps η u x w z P.val
      (hS.norm_four P.val P.property) hS.positive hx hz hw hxw

theorem actual_unramified_expansion (eps : ℝ) (S : Finset (Ideal O))
    (hS : FirstTail eps S) (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re)
    (hw : -(1 / 100 : ℝ) ≤ w.re) (hxw : 1 + eps ≤ x.re + w.re) :
    unramifiedProduct S η u x w z =
      ∑' e : EulerIndex {P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal // P.val ∉ S} 3,
        eulerCoefficient (fun P => actualUnramifiedCoefficients η u x z P.val) e *
          (eulerScale (fun P => primeScale P.val) e : ℂ) ^ (-w) := by
  have hs := actual_unramified_local_mass_summable eps S hS η u x w z hx hz hw hxw
  have he := euler_expansion_eq_tprod _ hs
  simp only [eulerTerm_mellin] at he
  rw [← he]
  apply tprod_congr
  intro P
  exact actual_unramified_local_expansion η u x w z P.val
    (hS.norm_four P.val P.property) hx hz

theorem primeScale_one_le (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) : 1 ≤ primeScale P := by
  have hn : 0 < P.val.absNorm := Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  change (1 : ℝ≥0) ≤ (P.val.absNorm : ℝ≥0)
  exact_mod_cast (Nat.succ_le_of_lt hn)

theorem actual_unramified_coefficient_mass (eps sigma : ℝ) (S : Finset (Ideal O))
    (hS : FirstTail eps S) (η : Character) (u : FreeRow) (x z : ℂ)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re)
    (hsigma : -(1 / 100 : ℝ) ≤ sigma) (hxw : 1 + eps ≤ x.re + sigma) :
    let Q := fun P : {P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal // P.val ∉ S} => primeScale P.val
    let c := fun P : {P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal // P.val ∉ S} => actualUnramifiedCoefficients η u x z P.val
    Summable (fun e : EulerIndex {P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal // P.val ∉ S} 3 =>
      ‖eulerCoefficient c e‖ * (eulerScale Q e : ℝ) ^ (-sigma)) ∧
    (∑' e : EulerIndex {P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal // P.val ∉ S} 3,
      ‖eulerCoefficient c e‖ * (eulerScale Q e : ℝ) ^ (-sigma)) ≤ Real.exp (1 / 2) := by
  dsimp only
  let Q := fun P : {P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal // P.val ∉ S} => primeScale P.val
  let c := fun P : {P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal // P.val ∉ S} => actualUnramifiedCoefficients η u x z P.val
  let f := localMellinTerm Q c (sigma : ℂ)
  have hf := actual_unramified_local_mass_summable eps S hS η u x (sigma : ℂ) z
    hx hz hsigma hxw
  have hQ : ∀ P, 1 ≤ Q P := fun P => primeScale_one_le P.val
  refine ⟨euler_coefficients_summable_weight Q hQ c sigma hf, ?_⟩
  have hb := euler_expansion_mass_le_exp f hf
  dsimp only [f] at hb
  simp only [euler_coefficient_weight_eq Q hQ c sigma] at hb
  apply hb.trans
  apply Real.exp_le_exp.mpr
  have hm : (∑' P, localMass f P) ≤
      ∑' P : {P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal // P.val ∉ S}, 3 * firstPrimeDefectBound eps P.val := by
    apply hf.tsum_le_tsum _ (hS.summable.mul_left 3)
    intro P
    exact actual_unramified_local_mass eps η u x (sigma : ℂ) z P.val
      (hS.norm_four P.val P.property) hS.positive hx hz hsigma hxw
  rw [tsum_mul_left] at hm
  linarith [hS.small]

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorPrimeExpansion -/
