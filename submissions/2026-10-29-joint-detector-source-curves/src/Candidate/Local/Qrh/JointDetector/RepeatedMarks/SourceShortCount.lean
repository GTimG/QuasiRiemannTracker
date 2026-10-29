/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.ActualShortCount
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.Capacity

/-! Source-derived short counts. The only analytic source premise is the
literal previously proved GlobalSource face, at its one early mesh. -/
namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped Classical BigOperators ContDiff
open Set Filter OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification HeckeDyadic HeckeDetectorWitnessRows
open HeckeDetectorRowwisePolynomial HeckeDetectorInverseFiberCount HeckeDetectorDyadicProfiles
open QRH.Record12518109Existence QRH.Record1252270103Source
open CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O

/-- All actual finite short fibers receive the repeated count from their
proved parent source. Constants precede every live batch, bin and witness. -/
theorem source_short_count {Label Slot : Type} [Fintype Label] [Nonempty Label]
    [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (B L c mesh εm Aroot : ℝ) (hL : 3/2≤L) (hεm : 0<εm) (hAr : 0≤Aroot)
    (hB0 : 0≤B) (hB : B≤1) (hc0 : 0≤c) (hc : c≤1/6)
    (hsource : UnitFaceSource (globalFace B L c) mesh (εm/2))
    (base anchor : Label→Character) (bad : Label→Ideal O)
    (hQM : ∀j,bad j≤M) (hQ0 : ∀j,internalQ (bad j) (anchor j)≠0)
    (hQt : ∀j,internalQ (bad j) (anchor j)≠⊤)
    (hQ72 : ∀j,internalQ (bad j) (anchor j)≤Ideal.span {(72:O)})
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Icc (1:ℝ) 2)
    (K : ℕ) :
    ∃ J : ℕ,∃ C : ℝ,0<C ∧ ∀ᶠ U : ℝ in atTop,1<U ∧
    ∀ N : RootedBatch (Slot:=Slot) M H hH base anchor bad W U Aroot,
    (∀s∈N.slots,N.widths s≤mesh) →
    ∀rows : Finset FreeRow,rows⊆N.rows → ∀χ : FreeRow→Label→Character,
    ∀(a ε tstar T allowance : ℝ)(i : ℕ),1/2≤a → 0≤ε →
    ∀witness : ∀u,Witness (χ u) U a ε tstar T allowance i,
    ∀(label : Label)(Jdy Kdy : Fin (dyadicLength U)),
    (∀u∈rows,(witness u).label=label) → (∀u∈rows,(witness u).left=Jdy) →
    (∀u∈rows,(witness u).right=Kdy) →
    ∀reverse : Bool,(∀u∈rows,∀I,idealCoeff (χ u label) I=
      if reverse then starRingEnd ℂ (idealCoeff (N.family u label) I) else idealCoeff (N.family u label) I) →
    ∀(δ β smin loss τ height lengthLoss : ℝ)(error : Slot→ℝ),
    0≤height → (∀s∈N.slots,|N.commonHeight+N.relativeHeight s|≤height) →
    0<2*a-1 → 2*a-1≤3/4 → 0≤δ → δ≤2*a-1 → 0≤lengthLoss → 0<τ →
    1/2<Real.logb U ((2:ℝ)^Jdy.val) → Real.logb U ((2:ℝ)^Jdy.val)<1 →
    0≤Real.logb U ((2:ℝ)^Kdy.val) → Real.logb U ((2:ℝ)^Kdy.val)≤B/2 →
    (∀s∈N.slots,0≤error s) → 0<β → 0<smin → smin≤∑s∈N.slots,N.widths s →
    (∀u∈N.rows,∀s∈N.slots,‖N.Q u s‖^2≤U^(N.widths s+error s)) →
    (∑s∈N.slots,error s)≤loss →
    (∀u∈N.rows,U^((δ+β)*(∑s∈N.slots,N.widths s)-loss)≤∏s∈N.slots,‖N.Q u s‖^2) →
    4*loss≤β*smin → 0≤mesh → 1/(β*smin/2)+1≤(K:ℝ) →
    max (crossingCut (2*a-1) (δ/(2*(2*a-1))) 2 (2*(δ/(2*(2*a-1)))*c))
      (crossingCut (2*a-1) (δ/(2*(2*a-1))) (2-4*(δ/(2*(2*a-1)))/L)
        (2*(δ/(2*(2*a-1)))*B/L)) ≤
      Real.logb U ((2:ℝ)^Jdy.val)+Real.logb U ((2:ℝ)^Kdy.val)+lengthLoss →
    2*Real.pi*allowance+(3*i:ℕ)*T≤height →
    (rows.card:ℝ)≤C*(1+height)^J*
      U^(rawRepeatedCountRate B L c (2*a-1) δ+(2*a-1)*lengthLoss+
        (δ*τ+4*ε+δ*mesh+εm)) := by
  obtain ⟨Ji,Ci,hCi,hi⟩ := ActualCoreCount.inverse_fields (Slot:=Slot×Fin K)
    M H hH base anchor bad W Aroot εm hWs hW.continuous hεm
  obtain ⟨Jp,Cp,hCp,hp⟩ := ActualCoreCount.plain_fields (Slot:=Slot×Fin K)
    M H hH B L c mesh εm Aroot (by linarith) hεm hAr hsource base anchor bad
    hQM hQ0 hQt hQ72 W hW hWs
  let J := Ji+Jp
  let C := 192*(Fintype.card (Finset (Slot×Fin K)):ℝ)*(Ci+Cp)
  have hcard : 0<(Fintype.card (Finset (Slot×Fin K)):ℝ) := by exact_mod_cast Fintype.card_pos
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨J+1,C,hC,?_⟩
  filter_upwards [hi,hp] with U hi hp
  refine ⟨hi.1,?_⟩
  intro N hwm rows hrows χ a ε tstar T allowance i ha hε witness label Jdy Kdy hlabel hJ hKdy
    reverse hχ δ β smin loss τ height lengthLoss error hh hv hν hνhi hδ hδν hlen hτ hrhalf hr1 hm0 hmB
    herr hβ hsmin hs hupper herrors hlower hbudget hm hKI hlength hfreq
  let Craw := (Ci+Cp)*(1+height)^J
  have hCraw : 0≤Craw := by dsimp [Craw]; positivity
  have hpowI : (1+height)^Ji≤(1+height)^J := pow_le_pow_right₀ (by linarith) (by dsimp [J];omega)
  have hpowP : (1+height)^Jp≤(1+height)^J := pow_le_pow_right₀ (by linarith) (by dsimp [J];omega)
  have hcI : Ci*(1+height)^Ji≤Craw := mul_le_mul (by linarith) hpowI (by positivity) (by linarith)
  have hcP : Cp*(1+height)^Jp≤Craw := mul_le_mul (by linarith) hpowP (by positivity) (by linarith)
  have hcopymesh : ∀s∈(N.copy K).slots,(N.copy K).widths s≤mesh := by
    intro s hs
    exact hwm s.1 (Finset.mem_product.mp hs).1
  have hinvCap := inverse_capacity hrhalf hr1 hτ
  have hplainCap := plain_capacity hm0 hmB (by linarith : 0<L) hc0 (by linarith : c≤1) hτ.le
  have he := short_count_from_fields N rows hrows χ a ε tstar T allowance i hi.1 ha witness
    label Jdy Kdy hlabel hJ hKdy B L c δ β smin loss mesh τ 1 Craw εm height lengthLoss K error
    hCraw hh hε hν hνhi hδ hδν hB0 hB hL hlen hwm herr hβ hsmin hs hupper herrors hlower hbudget hm hKI
    hinvCap.2.1 hplainCap.2.1 hlength hfreq
    (by
      intro selected hselected hwidth n hn σ hσ freq hf
      have hfirst : Real.logb U ((2:ℝ)^Jdy.val)+2*(∑s∈selected,(N.copy K).widths s)<1 := by linarith [hinvCap.2.2.1]
      have hsecond : 2*Real.logb U ((2:ℝ)^Jdy.val)+8*(∑s∈selected,(N.copy K).widths s)<3 := by linarith [hinvCap.2.2.2]
      have hb := hi.2 (N.copy K) rows hrows label selected hselected (fun u=>χ u label) reverse hχ
        (Real.logb U ((2:ℝ)^Jdy.val)) (by linarith) hfirst hsecond tstar n hn σ hσ height freq hh hf
      exact hb.trans (mul_le_mul_of_nonneg_right hcI (Real.rpow_nonneg (zero_lt_one.trans hi.1).le _)))
    (by
      intro selected hselected hwidth j k hjk σ hσ freq hf
      have hcap : (∑s∈selected,(N.copy K).widths s)≤c := hwidth.trans hplainCap.2.2.1
      have hbudget' : 2*Real.logb U ((2:ℝ)^Kdy.val)+L*(∑s∈selected,(N.copy K).widths s)≤B := by
        have hh' := mul_le_mul_of_nonneg_left hwidth (show 0≤L by linarith)
        linarith [hplainCap.2.2.2]
      have hphase : ∀s∈selected,|(N.copy K).commonHeight+(N.copy K).relativeHeight s|≤height := by
        intro s hs
        exact hv s.1 (Finset.mem_product.mp (hselected hs)).1
      have hb := hp.2 (N.copy K) hcopymesh rows hrows label selected hselected (fun u=>χ u label) reverse hχ
        (Real.logb U ((2:ℝ)^Kdy.val)) height hm0 hh hphase hcap hbudget' j k hjk σ hσ freq hf
      exact hb.trans (mul_le_mul_of_nonneg_right hcP (Real.rpow_nonneg (zero_lt_one.trans hi.1).le _)))
  convert he using 1
  dsimp [C,Craw]
  rw [pow_succ]
  ring

end
end Qrh.JointDetector.RepeatedMarks
