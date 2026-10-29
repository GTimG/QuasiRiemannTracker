/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceShortCount
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.NoSlotCount

/-! Complete source-derived actual detector count, before conversion of
logarithmic factors and arbitrarily small buffer budgets. -/
namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped Classical BigOperators ContDiff
open Set Filter OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification HeckeDyadic HeckeDetectorWitnessRows
open HeckeDetectorSupportedWitness HeckeDetectorRowwisePolynomial HeckeDetectorInverseFiberCount HeckeDetectorDyadicProfiles
open QRH.Record12518109Existence QRH.Record1252270103Source
open CenteredMomentNaturalFixedRaySource LocalMoment
local notation "O" => HeckeFamily.O

private theorem promote {count U C C' h e e' : ℝ} {J J' : ℕ}
    (hcount : count≤C*(1+h)^J*U^e) (hU : 1≤U) (hh : 0≤h)
    (hC : C≤C') (hC0 : 0≤C') (hJ : J≤J') (he : e≤e') :
    count≤C'*(1+h)^J'*U^e' := by
  apply hcount.trans
  exact mul_le_mul
    (mul_le_mul hC (pow_le_pow_right₀ (by linarith) hJ) (by positivity) hC0)
    (Real.rpow_le_rpow_of_exponent_le hU he) (Real.rpow_nonneg (by linarith) _)
    (by positivity)

theorem source_supported_count {Label Slot : Type} [Fintype Label] [Nonempty Label]
    [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (B L c mesh εm Aroot νmin : ℝ) (hL : 3/2≤L) (hεm : 0<εm) (hAr : 0≤Aroot)
    (hB0 : 0≤B) (hB : B≤1) (hc0 : 0≤c) (hc : c≤1/6) (hνmin : 0<νmin)
    (hsource : UnitFaceSource (globalFace B L c) mesh (εm/2))
    (hβglobal : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (base anchor : Label→Character) (bad : Label→Ideal O)
    (hQM : ∀j,bad j≤M) (hQ0 : ∀j,internalQ (bad j) (anchor j)≠0)
    (hQt : ∀j,internalQ (bad j) (anchor j)≠⊤)
    (hQ72 : ∀j,internalQ (bad j) (anchor j)≤Ideal.span {(72:O)})
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Icc (1:ℝ) 2)
    (K : ℕ) :
    ∃ J : ℕ,∃ C : ℝ,0<C ∧ ∀ᶠ U : ℝ in atTop,1<U ∧
    ∀ N : RootedBatch (Slot:=Slot) M H hH base anchor bad W U Aroot,
    (∀s∈N.slots,N.widths s≤mesh) → ∀χ : FreeRow→Label→Character,
    ∀(a ε tstar T allowance : ℝ)(i : ℕ),1/2≤a → 0≤ε → ε≤1/1000 → ε≤νmin/2000 →
    ∀witness : ∀u,SupportedWitness (χ u) U a ε tstar T allowance i,
    ∀reverse : Label→Bool,(∀u∈N.rows,∀j I,idealCoeff (χ u j) I=
      if reverse j then starRingEnd ℂ (idealCoeff (N.family u j) I) else idealCoeff (N.family u j) I) →
    ∀(δ β smin loss τ height : ℝ)(error : Slot→ℝ),
    0≤height → (∀s∈N.slots,|N.commonHeight+N.relativeHeight s|≤height) →
    νmin≤2*a-1 → 2*a-1≤3/4 → 0≤δ → δ≤2*a-1 → 0<τ →
    (∀s∈N.slots,0≤error s) → 0<β → 0<smin → smin≤∑s∈N.slots,N.widths s →
    (∀u∈N.rows,∀s∈N.slots,‖N.Q u s‖^2≤U^(N.widths s+error s)) →
    (∑s∈N.slots,error s)≤loss →
    (∀u∈N.rows,U^((δ+β)*(∑s∈N.slots,N.widths s)-loss)≤∏s∈N.slots,‖N.Q u s‖^2) →
    4*loss≤β*smin → 0≤mesh → 1/(β*smin/2)+1≤(K:ℝ) →
    tstar=max (crossingCut (2*a-1) (δ/(2*(2*a-1))) 2 (2*(δ/(2*(2*a-1)))*c))
      (crossingCut (2*a-1) (δ/(2*(2*a-1))) (2-4*(δ/(2*(2*a-1)))/L)
        (2*(δ/(2*(2*a-1)))*B/L)) →
    1≤tstar → tstar≤3/2 → 2*Real.pi*allowance+(3*i:ℕ)*T≤height →
    (N.rows.card:ℝ)≤C*(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2*(1+height)^J*
      U^(rawRepeatedCountRate B L c (2*a-1) δ+200*ε+δ*τ+δ*mesh+εm) := by
  obtain ⟨Js,Cs,hCs,hs⟩ := source_short_count (Slot:=Slot) M H hH B L c mesh εm Aroot hL hεm hAr
    hB0 hB hc0 hc hsource base anchor bad hQM hQ0 hQt hQ72 W hW hWs K
  obtain ⟨Jn,Cn,hCn,hn⟩ := actual_no_slot_fiber_counts base εm hεm hβglobal
  let J := Js+Jn
  let C := Cs+Cn
  have hC : 0<C := by dsimp [C]; positivity
  have hJs : Js≤J := by dsimp [J];omega
  have hJn : Jn≤J := by dsimp [J];omega
  have hCsC : Cs≤C := by dsimp [C];linarith
  have hCnC : Cn≤C := by dsimp [C];linarith
  refine ⟨J,C,hC,?_⟩
  filter_upwards [hs,hn] with U hs hn
  refine ⟨hs.1,?_⟩
  intro N hwm χ a ε tstar T allowance i ha hε hε1 hεnu witness reverse hχ
    δ β smin loss τ height error hh hv hνlow hνhi hδ hδν hτ herr hβ hsmin hsminN
    hupper herrors hlower hbudget hm hK htstar htstar0 htstar1 hfreq
  let A := N.unmarked reverse χ witness hχ
  have hν : 0<2*a-1 := hνmin.trans_le hνlow
  have hp0 : 0≤δ/(2*(2*a-1)) := div_nonneg hδ (by positivity)
  have hp : δ/(2*(2*a-1))≤1/2 := (div_le_iff₀ (by positivity : 0<2*(2*a-1))).mpr (by linarith)
  have htail : 1-(2*a-1)*B≤rawRepeatedCountRate B L c (2*a-1) δ := le_max_right _ _
  have hshort : max (crossingRate (2*a-1) (δ/(2*(2*a-1))) 2 (2*(δ/(2*(2*a-1)))*c))
      (crossingRate (2*a-1) (δ/(2*(2*a-1))) (2-4*(δ/(2*(2*a-1)))/L)
        (2*(δ/(2*(2*a-1)))*B/L))≤rawRepeatedCountRate B L c (2*a-1) δ := le_max_left _ _
  have hδτ : 0≤δ*τ := mul_nonneg hδ hτ.le
  have hδmesh : 0≤δ*mesh := mul_nonneg hδ hm
  have hfiber : ∀label left right,∀hne : (A.fiberRows label left right).Nonempty,
      ((A.fiber label left right hne).rows.card:ℝ)≤C*(1+height)^J*
        U^(rawRepeatedCountRate B L c (2*a-1) δ+200*ε+δ*τ+δ*mesh+εm) := by
    intro label left right hne
    let F := A.fiber label left right hne
    have hgeom := HeckeDetectorSupportedWitness.fiber_lengths F.rows F.nonempty F.family U a ε tstar T allowance i
      hs.1 F.witness F.left F.right F.fixed_left F.fixed_right
    change tstar-F.r-ε≤F.m ∧ F.r≤tstar+ε ∧ F.m≤1/2+75*ε ∧ tstar-1/2-76*ε≤F.r ∧ 0≤F.m at hgeom
    have hcases := hn.2 a ε tstar T allowance i ha htstar0 htstar1 hε hε1 A rfl height hh hfreq label left right hne
    change (F.rows.card:ℝ)≤Cn*(1+height)^Jn*U^(sourceExponent F.r-(2*a-1)*F.r+2*ε+εm) ∧
      (F.rows.card:ℝ)≤Cn*(1+height)^Jn*U^(max 1 (2*F.m)-2*(2*a-1)*F.m+4*ε+εm) at hcases
    by_cases hr : F.r<1
    · by_cases hmB : F.m≤B/2
      · have hrhalf : 1/2<F.r := inverse_length_above_half hνmin hνlow hνhi hp0 hp hc0 hc
          (by rw [htstar];exact le_max_left _ _) hεnu hgeom.2.2.2.1
        have hsub : F.rows⊆N.rows := Finset.filter_subset _ _
        have he := hs.2 N hwm F.rows hsub χ a ε tstar T allowance i ha hε
          (fun u=>(witness u).toWitness) label left right F.fixed_label F.fixed_left F.fixed_right
          (reverse label) (fun u hu I=>hχ u (hsub hu) label I)
          δ β smin loss τ height ε error hh hv hν hνhi hδ hδν hε hτ hrhalf hr hgeom.2.2.2.2 hmB
          herr hβ hsmin hsminN hupper herrors hlower hbudget hm hK
          (by rw [←htstar]; change tstar≤F.r+F.m+ε; linarith only [hgeom.1]) hfreq
        apply promote he hs.1.le hh hCsC hC.le hJs
        have hh := mul_nonneg (show 0≤196-(2*a-1) by linarith) hε
        nlinarith only [hh]
      · have hmB' : B/2≤F.m := le_of_not_ge hmB
        have hmax : max 1 (2*F.m)≤1+150*ε := max_le (by linarith) (by linarith [hgeom.2.2.1])
        have hprod := mul_le_mul_of_nonneg_left hmB' hν.le
        apply promote hcases.2 hs.1.le hh hCnC hC.le hJn
        nlinarith only [hmax,hprod,htail,hδτ,hδmesh,hε]
    · have hr1 : 1≤F.r := le_of_not_gt hr
      have hsource : sourceExponent F.r=(1+5*F.r)/6 := by
        unfold sourceExponent
        rw [max_eq_right (by linarith)]
      have hlong := long_at_maximum_cutoff (p:=δ/(2*(2*a-1))) (A₁:=2)
        (Z₁:=2*(δ/(2*(2*a-1)))*c) (A₂:=2-4*(δ/(2*(2*a-1)))/L)
        (Z₂:=2*(δ/(2*(2*a-1)))*B/L) (by linarith : 2*a-1≤5/6)
      rw [←htstar] at hlong
      have hgap := mul_nonneg (show 0≤(5/6:ℝ)-(2*a-1) by linarith) (sub_nonneg.mpr hgeom.2.1)
      apply promote hcases.1 hs.1.le hh hCnC hC.le hJn
      rw [hsource]
      unfold longArm at hlong
      nlinarith only [hlong,hshort,hgap,hδτ,hδmesh,hε,hν.le]
  have he := A.card_bound (C*(1+height)^J) _ (by positivity) (zero_lt_one.trans hs.1) hfiber
  convert he using 1 <;> first | rfl | ring

end
end Qrh.JointDetector.RepeatedMarks
