/- Copyright (c) 2026 Sil. Apache-2.0.
Actual genuine-common source shortening for the outer mixed branch.
The whole ideal norm, actual nonzero frozen coefficient and original
ordinary prefix are retained. Only the first-stage root/cutoff ledger
and the concrete selected subset remain caller-side numerical duties.
Global source and cutoff assembly remain separate obligations.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.OuterFreshSelectedWindow
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.GlobalSlotSelection
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstNonexceptionalAllocation
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondCanonicalFrequency
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstSourceConductorCaps

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.OuterFreshMixedCapacity
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge ActualEisensteinCubic
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentCommonRawScale CenteredMomentSourceLiveColumn
open CenteredMomentSourceProfileMass CenteredMomentOriginalRadialComparison
open CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedFirstLiveSource MixedLiveNormalization MixedFirstNonexceptionalAllocation
open OuterFreshSelectedWindow
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq (α⊕Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

private theorem product_log {κ : Type*} [Fintype κ]
    (P w : κ→ℝ) (Z : ℝ) (hZ : 1<Z) (hP : ∀i,P i=Z^(w i)) :
    Real.logb Z (∏i,P i)=∑i,w i := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hp : ∀i,P i≠0 := fun i=>by rw [hP];exact (Real.rpow_pos_of_pos hz _).ne'
  rw [Real.logb_prod _ _ (fun i _=>hp i)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hP,Real.logb_rpow hz hZ.ne']

private theorem effective_volume_log (s : Source ι a b) (Z : ℝ) (w : ι→ℝ)
    (hZ : 1<Z) (hP : ∀i,s.P i=Z^(w i)) :
    Real.logb Z ((s.T*(∏i,s.P i))/pairNorm s.d)=
      Real.logb Z (s.T/pairNorm s.d)+∑i,w i := by
  have hp := pairNorm_pos s.hd.1 s.hd.2
  have hprod : 0<∏i,s.P i := Finset.prod_pos (fun i _=>zero_lt_one.trans_le (s.hP i))
  rw [Real.logb_div (mul_pos s.total_pos hprod).ne' hp.ne',
    Real.logb_mul s.total_pos.ne' hprod.ne',
    Real.logb_div s.total_pos.ne' hp.ne',product_log s.P w Z hZ hP]
  ring

/-- Exact logarithmic volume identity for the actual constructed live
Source. In particular the ordinary width is T/pairNorm d, not T. -/
theorem allocated_volume_log (s : Source ι a b) (hb : 0≤b)
    (cover : OriginalEnclosure s) (G : Id)
    (B : actualAllocations (tuplePools s) G) (Z : ℝ) (w : ι→ℝ)
    (hZ : 1<Z) (hP : ∀i,s.P i=Z^(w i)) :
    let live:=allocatedLiveSource s hb cover G B
    Real.logb Z (live.T/pairNorm live.d)+(∑i : liveIndices B.val,w i.val)=
      Real.logb Z (s.T/pairNorm s.d)+(∑i,w i)-Real.logb Z (rawReduction B.val s.P) := by
  let live:=allocatedLiveSource s hb cover G B
  let hB := (allocation_data (tuplePools s) G B.val (Finset.mem_filter.mp B.property).1).1
  have hPpos : ∀i,0<s.P i := fun i=>zero_lt_one.trans_le (s.hP i)
  have hv := live_volume_ratio B.val hB s.d s.T s.P hPpos
  change (live.T*(∏i,live.P i))/pairNorm live.d=
    ((s.T*(∏i,s.P i))/pairNorm s.d)/rawReduction B.val s.P at hv
  have hp := pairNorm_pos s.hd.1 s.hd.2
  have hvol : 0<(s.T*(∏i,s.P i))/pairNorm s.d :=
    div_pos (mul_pos s.total_pos (Finset.prod_pos (fun i _=>hPpos i))) hp
  have hr := rawReduction_pos B.val hB s.P hPpos
  have hl := congrArg (Real.logb Z) hv
  rw [effective_volume_log live Z (fun i : liveIndices B.val=>w i.val) hZ
      (fun i=>hP i.val),Real.logb_div hvol.ne' hr.ne',
    effective_volume_log s Z w hZ hP] at hl
  exact hl

theorem live_width_le (B : Tuple ι) (w : ι→ℝ) (hw : ∀i,0≤w i) :
    (∑i : liveIndices B,w i.val)≤∑i,w i := by
  simpa only [Finset.sum_coe_sort] using Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ (liveIndices B)) (fun i _ _=>hw i)

/-- Full common norm pays the actual ordinary shortening and removed
marked scales. The sole enclosure loss is card*log_Z 2; there is no
epsilon or mesh charged separately for each removed slot. -/
theorem actual_common_capacity (s : Source ι a b) (hb : 0≤b)
    (cover : OriginalEnclosure s) (G : Id) (hG : G≠0)
    (B : actualAllocations (tuplePools s) G) (Z κ : ℝ) (w : ι→ℝ)
    (hZ : 1<Z) (hκ : 1≤κ) (hw : ∀i,0≤w i) (hP : ∀i,s.P i=Z^(w i))
    (hW : ∀i,Function.support (s.Wslot i)⊆Icc (1:ℝ) 2)
    (hfrozen : frozenCoefficient B.val G s.R s.ν s.Wslot s.P≠0) :
    let live:=allocatedLiveSource s hb cover G B
    Real.logb Z (live.T/pairNorm live.d)+κ*(∑i : liveIndices B.val,w i.val)≤
      Real.logb Z (s.T/pairNorm s.d)+κ*(∑i,w i)-Real.logb Z (G.absNorm:ℝ)+
        (Fintype.card ι:ℝ)*Real.logb Z (2:ℝ) := by
  let hB := (allocation_data (tuplePools s) G B.val (Finset.mem_filter.mp B.property).1).1
  have hprod := (Finset.mem_filter.mp B.property).2
  have hPpos : ∀i,0<s.P i := fun i=>zero_lt_one.trans_le (s.hP i)
  have hr := rawReduction_pos B.val hB s.P hPpos
  have hg : 0<(G.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hG)
  have hnorm := (actual_reduction_norm B.val hB G s.R hprod s.ν s.Wslot s.P hPpos
    1 2 zero_lt_one hW hfrozen).2
  rw [max_eq_right (by norm_num : (1:ℝ)≤2)] at hnorm
  have hlog := Real.logb_le_logb_of_le hZ hg hnorm
  rw [Real.logb_mul (by positivity : (0:ℝ)<2^Fintype.card ι).ne' hr.ne',
    Real.logb_pow] at hlog
  have hvolume := allocated_volume_log s hb cover G B Z w hZ hP
  have hlive := live_width_le B.val w hw
  dsimp only at hvolume ⊢
  nlinarith

/-- The same literal norm extraction pays the FIRST common loss in
the paper's 93/25 root capacity. Only the original root-domain scalar
inequality is supplied; the extracted child's capacity is proved. -/
theorem actual_first_common_root (s : Source ι a b) (hb : 0≤b)
    (cover : OriginalEnclosure s) (G : Id) (hG : G≠0)
    (B : actualAllocations (tuplePools s) G) (Z : ℝ) (w : ι→ℝ)
    (hZ : 1<Z) (hw : ∀i,0≤w i) (hP : ∀i,s.P i=Z^(w i))
    (hW : ∀i,Function.support (s.Wslot i)⊆Icc (1:ℝ) 2)
    (hfrozen : frozenCoefficient B.val G s.R s.ν s.Wslot s.P≠0)
    (Q Delta : ℝ)
    (hroot : Real.logb Z (s.T/pairNorm s.d)+(93/25:ℝ)*(∑i,w i)≤Q-Delta) :
    let live:=allocatedLiveSource s hb cover G B
    Real.logb Z (live.T/pairNorm live.d)+(93/25:ℝ)*(∑i : liveIndices B.val,w i.val)≤
      Q-Real.logb Z (G.absNorm:ℝ)-Delta+(Fintype.card ι:ℝ)*Real.logb Z (2:ℝ) := by
  have he:=actual_common_capacity s hb cover G hG B Z (93/25) w hZ
    (by norm_num) hw hP hW hfrozen
  dsimp only at he ⊢
  linarith

/-- The uniform threshold for the one fixed dimension cost precedes
the source, common ideal and actual allocation. -/
theorem common_enclosure_cost_eventually (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀n : ℕ,n≤N→(n:ℝ)*Real.logb Z (2:ℝ)≤ε := by
  have hc : ∀ᶠZ : ℝ in atTop,(2:ℝ)^N≤Z^ε :=
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) _
  filter_upwards [Filter.eventually_gt_atTop (1:ℝ),hc] with Z hZ hc
  refine ⟨hZ,?_⟩
  intro n hn
  have hl := Real.logb_le_logb_of_le hZ (by positivity : (0:ℝ)<2^N) hc
  rw [Real.logb_pow,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hl
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hn)
    (Real.logb_nonneg hZ (by norm_num : (1:ℝ)≤2))).trans hl

/-- Actual common labels, on either side: g2 is no greater than the
full common norm and t2 is nonnegative. No asserted log-width premise. -/
theorem actual_common_widths (C E : Id) (hC : Supported C) (hE : Supported E)
    (hCE : CompletedGauss.primeSupport C=CompletedGauss.primeSupport E)
    (U : Finset (CommonIndex C E)) (G : Id) (hGE : G=C ∨ G=E)
    (Z : ℝ) (hZ : 1<Z) :
    0≤Real.logb Z (G.absNorm:ℝ) ∧
    0≤Real.logb Z ((∏P∈U,P.val).absNorm:ℝ) ∧
    Real.logb Z (normValue (commonFrequencyGenerator C E))≤Real.logb Z (G.absNorm:ℝ) := by
  have hg : Supported G := by rcases hGE with rfl|rfl <;> assumption
  have hU : (∏P∈U,P.val)≠0 := Finset.prod_ne_zero_iff.mpr (fun P _=>
    (IdealMobiusDivisorSum.support_prime (Finset.mem_inter.mp P.property).1).ne_zero)
  refine ⟨Real.logb_nonneg hZ (ideal_norm_one_le hg.1),
    Real.logb_nonneg hZ (ideal_norm_one_le hU),?_⟩
  have hdiv : Ideal.span {commonFrequencyGenerator C E}∣G := by
    rcases hGE with heq|heq
    · rw [heq]
      simpa only [primary_span_supported C hC] using
        Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr
          (commonFrequencyGenerator_dvd C E hC hE hCE).1
    · rw [heq]
      simpa only [primary_span_supported E hE] using
        Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr
          (commonFrequencyGenerator_dvd C E hC hE hCE).2
  have hnorm := CenteredMomentFirstSourceConductorCaps.divisor_norm_le _ G hg.1 hdiv
  exact Real.logb_le_logb_of_le hZ
    (normValue_pos _ (commonFrequencyGenerator_ne_zero C E hC)) hnorm

/-- The complete literal allocation gate, conditional only on the
remaining first-stage ROOT/CUTOFF numerical provenance and actual
greedy scalar data. This is not claimed to construct that provenance.
Here S0=(sum remaining w)+d, exactly the supplier partition's width.
The max covers both signs of J=D0-c without discarding either case. -/
theorem actual_allocated_large_gate (s : Source ι a b) (hb : 0≤b)
    (cover : OriginalEnclosure s) (C E : Id) (hC : Supported C) (hE : Supported E)
    (hCE : CompletedGauss.primeSupport C=CompletedGauss.primeSupport E)
    (U : Finset (CommonIndex C E)) (G : Id) (hGE : G=C ∨ G=E)
    (B : actualAllocations (tuplePools s) G) (Z : ℝ) (w : ι→ℝ)
    (hZ : 1<Z) (hw : ∀i,0≤w i) (hP : ∀i,s.P i=Z^(w i))
    (hW : ∀i,Function.support (s.Wslot i)⊆Icc (1:ℝ) 2)
    (hfrozen : frozenCoefficient B.val G s.R s.ν s.Wslot s.P≠0)
    (Q c D0 d Delta mesh eDyad eDeclared Rdecl rhoMixed rhoFloor : ℝ)
    (hc : 0≤c) (heDyad : 0≤eDyad) (hD0 : -eDyad≤D0)
    (hrhoFloor : 0<rhoFloor) (hlarge : rhoFloor<(∑i,w i)+d)
    (hselectLo : (43/100:ℝ)*((∑i,w i)+d)≤d)
    (hselectHi : d≤(43/100:ℝ)*((∑i,w i)+d)+mesh)
    (hroot : Real.logb Z (s.T/pairNorm s.d)+(93/25:ℝ)*((∑i,w i)+d)≤Q-c-Delta)
    (hdeclared : Q+(D0-c)-max (D0-c) 0-2*d-
      Real.logb Z (normValue (commonFrequencyGenerator C E))+
      Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)-eDeclared≤Rdecl)
    (hreserve : rhoMixed+(Fintype.card ι:ℝ)*Real.logb Z (2:ℝ)+
      4*mesh+eDyad+eDeclared≤Delta) :
    let live:=allocatedLiveSource s hb cover G B
    Real.logb Z (live.T/pairNorm live.d)+2*(∑i : liveIndices B.val,w i.val)+4*d≤
      Rdecl-rhoMixed ∧
    rhoFloor/400<d-(3/4:ℝ)*(∑i : liveIndices B.val,w i.val) ∧
      (3/4:ℝ)*(∑i : liveIndices B.val,w i.val)<d := by
  have hg : Supported G := by rcases hGE with rfl|rfl <;> assumption
  have hcapacity := actual_common_capacity s hb cover G hg.1 B Z 2 w hZ
    (by norm_num) hw hP hW hfrozen
  have hcommon := actual_common_widths C E hC hE hCE U G hGE Z hZ
  have hmax : max (D0-c) 0≤D0+eDyad := max_le (by linarith) (by linarith)
  have hlive := live_width_le B.val w hw
  have hnative := GlobalSlotSelection.gate_after_loss (S:=(∑i,w i)+d)
    (d:=d) (s:=∑i : liveIndices B.val,w i.val) (rho:=rhoFloor) (loss:=0)
    hlarge hselectLo (by linarith)
  dsimp only at hcapacity ⊢
  refine ⟨?_,?_,?_⟩
  · linarith [hcommon.2.1,hcommon.2.2]
  · linarith
  · linarith

end
end Candidate.FourthPower.OuterFreshMixedCapacity
