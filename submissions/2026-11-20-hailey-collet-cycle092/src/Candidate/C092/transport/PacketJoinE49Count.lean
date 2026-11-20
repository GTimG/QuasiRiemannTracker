/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The original balanced old count, supplied on actual source dictionaries. -/
import Candidate.C092.transport.DirectCountFields
import Candidate.C092.transport.DirectPrices
import Candidate.C092.transport.PacketJoinE49Bridge
import Candidate.C092.transport.PacketJoinE49CountBatch
import Candidate.C092.transport.PacketJoinE49Window
import Submissions.hailey_collet_1252270103.Cycle25.Assembly.Count.Adaptive
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical BigOperators
open Filter Set
namespace QRH.Cycle092.PacketJoinE49
open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorRawFiber HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection
open HeckeDetectorFixedAmplitudeCount HeckeDetectorAmplitudeFirst
open Cycle25ProbeDetectorPlainMarkedFineField ProbeFinalAssembly
open QRH.Record12518109Count Cycle25ProbeFinalAssembly
open QRH.Record1252270103Return QRH.Cycle090 QRH.Cycle092.Direct QRH.Cycle092.DirectCount

theorem q_e49_batch_count (hβ : (51/100 : ℝ)  ≤  HeckeZeroSupremum.beta) :
    ∃ mesh : ℝ → ℝ, (∀ t, 0 < t → 0 < mesh t) ∧
    ∀ (D : Cycle25.Weighted.MomentData) (S : WeightedSourceData D),
    (∀ j, D.ell j  ≤  mesh D.t/200) →
    (∀ j, D.ell j  ≤  Cycle25.sourceMesh D.t/200) → D.ε  ≤  1/10000000 →
    ∀ κplain : ℝ, 7/10  ≤  κplain → κplain  ≤  3/4 →
    2*HeckeZeroSupremum.beta-1  ≤  κplain →
    ∃ K : ℝ, 0  ≤  K ∧ ∀ η : Character, ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ rows : Finset FreeRow, (∀ u ∈ rows, Z^(1/100 : ℝ)  ≤  rowNorm u) →
    ∀ d : ℝ, (1/200 : ℝ)  ≤  d →
    ∀ (a T allowance ν height q : ℝ) (i : ℕ), 51/100 < a → 2*a-1  ≤  3/4 →
    0 < ν → ν  ≤  1/10000000 → D.t  ≤  ν → 0  ≤  height →
    2*Real.pi*allowance+(3*i : ℕ)*T  ≤  height →
    Return.window.Available (2*a-1) (q/(2*a-1)) →
    ∀ B : HeckeDetectorBatch.Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤))
      (Fin D.N) (Z^d) a D.ε (Return.cutoffI (2*a-1) (q/(2*a-1))) T allowance i,
    B.rows.Nonempty → B.rows ⊆ rows →
    B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η →
    B.profile=(fun _ x => (S.w x : ℂ)) → B.widths=(fun s => D.ell s/d) →
    B.upper=(fun _ => 2) → (∀ s, (B.external s).re=17/50) →
    (∀ s, |(B.external s).im|  ≤  height) →
    (∀ u ∈ B.rows, rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
      (physical S.modulus ⊤ (fun u : FreeRow => u.val) B.profile B.upper B.widths B.external (Z^d)) u=q) →
    (B.rows.card : ℝ)  ≤ 
      (Fintype.card (Sum Bool (RayQuotient.Characters S.modulus ⊤)) : ℝ)*
      (dyadicLength (Z^d) : ℝ)^2*fiberConstant (C*(1+height)^J) height K*
      (Fintype.card B.Bin : ℝ)*
      (Z^d)^(Return.valueI (2*a-1) (q/(2*a-1))+159*D.ε+D.t+B.mesh+7*ν) := by
  obtain ⟨mc,hmc,hfields⟩ := q_actual_count_fields hβ
  have hs := tangent_fiber_moments hβ
  choose mi hmi hi using (fun t : {t : ℝ // 0<t} => hs t.val t.property)
  let chosen : ℝ→ℝ := fun t => if ht:0<t then mi ⟨t,ht⟩ else 1
  let mesh : ℝ→ℝ := fun t=> min (mc t) (chosen t)
  refine ⟨mesh,?_,?_⟩
  · intro t ht
    exact lt_min (hmc t ht) (by simpa only [chosen,dif_pos ht] using hmi ⟨t,ht⟩)
  intro D S hfineA hfine hεsmall κ hk hk1 hkβ
  have hfmc : ∀ j,D.ell j ≤ mc D.t/200 := by
    intro j
    exact (hfineA j).trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have hfmi : ∀ j,D.ell j ≤ mi ⟨D.t,D.t_pos⟩/200 := by
    intro j
    have hh := (hfineA j).trans (div_le_div_of_nonneg_right (min_le_right (mc D.t) (chosen D.t)) (by norm_num : (0:ℝ) ≤ 200))
    simpa only [chosen,dif_pos D.t_pos] using hh
  have himp := hi ⟨D.t,D.t_pos⟩ S rfl hfmi
  obtain ⟨c,κi,K,hc,hc1,hκi,hK,hcount⟩ := Return.fixed_amplitude_windows_count
    (line := Return.line) S.modulus ⊤ le_top S.S S.w S.smooth S.compact S.positive_support
    (fun y => (S.bounded y).1) S.nonzero 1 2 1 (by norm_num) (by norm_num)
    (by norm_num) S.support (fun y => (S.bounded y).2) D.t D.t_pos
  obtain ⟨U0,hU0⟩ := eventually_atTop.mp hcount
  have hscaled : ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, (1/200 : ℝ)  ≤  d → U0  ≤  Z^d := by
    filter_upwards [(tendsto_rpow_atTop (by norm_num : 0 < (1/200 : ℝ))).eventually
      (eventually_ge_atTop U0),eventually_ge_atTop (1 : ℝ)] with Z hZ hZone
    intro d hd
    exact hZ.trans (Real.rpow_le_rpow_of_exponent_le hZone hd)
  refine ⟨K,hK,?_⟩
  intro η
  obtain ⟨Jc,Cc,hCc,hsource⟩ := hfields D S hfmc hfine (QRH.PositiveGap.Return.naturalK/6) (by norm_num [QRH.PositiveGap.Return.naturalK]) (by norm_num [QRH.PositiveGap.Return.naturalK])
    (by norm_num [QRH.PositiveGap.Return.naturalK]; linarith [hkβ,hk1]) c κi hc hκi η
  obtain ⟨Ji,Ci,hCi,himp⟩ := himp η
  let J := Jc+Ji
  let C := Cc+Ci+1
  have hC : 0<C := by dsimp [C];linarith
  refine ⟨J,C,hC,?_⟩
  filter_upwards [hsource,himp,hscaled] with Z hsource himp hscaled
  refine ⟨hsource.1,?_⟩
  intro rows hrows d hd a T allowance ν height q i ha hδhi hν hνhi hνt hh hf hav
    B hne hB hdata hprofile hwidth hupper hreal him hq
  have hU : 1<Z^d := Real.one_lt_rpow hsource.1 (by linarith)
  have hb : 1 ≤ 1+height := by linarith
  have pc : Cc*(1+height)^Jc ≤ C*(1+height)^J :=
    mul_le_mul (by dsimp [C];linarith) (pow_le_pow_right₀ hb (by dsimp [J];omega)) (by positivity) hC.le
  have pi : Ci*(1+height)^Ji ≤ C*(1+height)^J :=
    mul_le_mul (by dsimp [C];linarith) (pow_le_pow_right₀ hb (by dsimp [J];omega)) (by positivity) hC.le
  have fields bin label left right hne := hsource.2 rows hrows d hd a _ T allowance i B hB hdata hprofile hwidth
    hupper hreal bin label left right hne height hh him
  have imp bin label left right hne := himp.2 rows hrows d hd a _ T allowance i B hB hdata hprofile hwidth
    (fun s=>congrFun hupper s) hreal bin label left right hne height hh him
  have hc' := (hU0 (Z^d) (hscaled d hd)).2 (QRH.PositiveGap.Return.naturalK/6) (by norm_num [QRH.PositiveGap.Return.naturalK]) (by norm_num [QRH.PositiveGap.Return.naturalK]) Return.window
    a D.ε T allowance ν (C*(1+height)^J) height q i hU ha hδhi D.epsilon_pos.le
    hεsmall hν hνhi (by positivity) hh hf hav B hq
  simp only [←Nat.card_eq_fintype_card] at hc' ⊢
  dsimp only [Return.window] at hc'
  apply hc'
  · intro bin label left right hne
    have m := (fields bin label left right hne).1
    refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
    · intro n hn σ hσ t ht
      exact ⟨rawMoment_mono_constant (m.original.inverse_raw n hn σ hσ t ht).1 pc,
        rawMoment_mono_constant (m.original.inverse_raw n hn σ hσ t ht).2 pc⟩
    · intro sel hsel h1 h2 n hn σ hσ t ht
      exact (m.original.inverse_marked sel hsel h1 h2 n hn σ hσ t ht).trans
        (mul_le_mul_of_nonneg_right pc (by positivity))
    · intro sel hsel hcap j k hjk σ hσ t ht
      exact (m.original.plain_marked sel hsel hcap j k hjk σ hσ t ht).trans
        (mul_le_mul_of_nonneg_right pc (by positivity))
    · intro j k hjk σ hσ t ht
      exact (m.original.plain_unmarked j k hjk σ hσ t ht).trans
        (mul_le_mul_of_nonneg_right pc (by positivity))
    · intro sel hsel hcap j k hjk σ hσ t ht
      exact (m.plain_marked sel hsel hcap j k hjk σ hσ t ht).trans
        (mul_le_mul_of_nonneg_right pc (by positivity))
  · intro bin label left right hne
    have f := (fields bin label left right hne).2
    intro hmlo hmhi sel hsel hs0 hs1 hs2 j k hjk σ hσ t ht
    have hh0 : 0 ≤ ∑s∈sel,(B.fiber bin label left right hne).widths s := hs0
    have hcst := source_contact_guards
    have hslot : (∑s∈sel,(B.fiber bin label left right hne).widths s) ≤ countFace.slotHi := by
      change (∑s∈sel,(B.fiber bin label left right hne).widths s) ≤ 3/20-1000*sourceCost/1143
      change (∑s∈sel,(B.fiber bin label left right hne).widths s) ≤ 3/20-1/10000000 at hs1
      linarith [hcst.2.1]
    have hbud : 2*(B.fiber bin label left right hne).m+countFace.lam*(∑s∈sel,(B.fiber bin label left right hne).widths s) ≤ countFace.B := by
      change 2*(B.fiber bin label left right hne).m+(2+10*sourceCost)*(∑s∈sel,(B.fiber bin label left right hne).widths s) ≤ 1-sourceCost
      change 2*(B.fiber bin label left right hne).m+(200000000001/100000000000:ℝ)*(∑s∈sel,(B.fiber bin label left right hne).widths s) ≤ 999999999999/1000000000000 at hs2
      nlinarith [mul_nonneg hh0 (show (0:ℝ) ≤ 1/100000000000-10*sourceCost by linarith [hcst.2.1])]
    exact (f hmlo hmhi sel hsel hs0 hslot hbud j k hjk σ hσ t ht).trans
      (mul_le_mul_of_nonneg_right pc (by positivity))
  · intro bin label left right hne
    have hi' := (imp bin label left right hne).mono_constant (by positivity) pi
    constructor
    · intro h1 h2 sel hsel hw
      exact hi'.inverse h1 h2 sel hsel (by linarith)
    · intro h1 h2 sel hsel hw
      exact hi'.ordinary h1 h2 sel hsel (by linarith)

end QRH.Cycle092.PacketJoinE49
#print axioms QRH.Cycle092.PacketJoinE49.q_e49_batch_count
