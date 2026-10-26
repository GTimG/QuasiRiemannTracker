import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryHighPayment
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondLowLabelBudget
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
open ActualEisensteinCubic Cycle63Moment

/-- The low scalar uses the same literal first-label coordinates as the
physical normalization, before any dyadic endpoints are substituted. -/
theorem actual_low_geometry_exponent_coordinates
    {α : Type*} [Fintype α] [DecidableEq α]
    (s : Input α) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K)
    (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))
    (reflected : Bool) (A : ℝ) :
    let x := geometryExponents s R seed K Z ξ j.1.val
    lowGeometryExponent reflected Z A (geometryFirstLabel s R seed K Z ξ hK key j)=
      A-x (if reflected then 1 else 0)+x 3+x 4 := by
  intro x
  let l:=geometryFirstLabel s R seed K Z ξ hK key j
  have he : Ideal.span {primeSubsetGenerator
      (fun P : CommonIndex l.1.1 l.1.2=>P.val) l.2.val}=
      firstProjectorRadical l.1.1 l.1.2 l.2.val := by
    rw [primeSubsetGenerator,span_idealGenerator]
    rfl
  change Ideal.span {primeSubsetGenerator
    (fun P : CommonIndex j.1.val.1.val.1 j.1.val.1.val.2=>P.val) j.1.val.2.1.val}=_ at he
  cases reflected <;>
    dsimp [lowGeometryExponent,x,geometryExponents,geometryNorms,geometryIdeals,
      geometryFirstLabel,l] <;> rw [he] <;> rfl

/-- One common first-geometry bin supplies all three low-branch scalar
gates. Their combined loss is exactly four binary-bin widths, hence a
fixed factor rather than a new power of the source scale. -/
theorem actual_geometry_low_bin_scalar_gates
    {α : Type*} [Fintype α] [DecidableEq α]
    (s : Input α) (R seed : Ideal O) (K Z ξ B A : ℝ) (hK : 0<K)
    (hZ : 1<Z) (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤Z^B) (key : ℤ×(Fin 5→ℤ)) (reflected : Bool) :
    let w:=Real.logb Z 2
    let c : Fin 5:=if reflected then 1 else 0
    let p:=((key.2 2:ℝ)+1)*w
    let exponent:=A-(key.2 c:ℝ)*w+((key.2 3:ℝ)+1)*w+((key.2 4:ℝ)+1)*w
    let sideLower:=(key.2 2:ℝ)*w+A-((key.2 c:ℝ)+1)*w+
      (key.2 3:ℝ)*w+(key.2 4:ℝ)*w
    p+exponent-sideLower=4*w ∧
    ∀j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key),
      ((commonRadical
        (geometryFirstLabel s R seed K Z ξ hK key j).1.1
        (geometryFirstLabel s R seed K Z ξ hK key j).1.2).absNorm:ℝ)≤Z^p ∧
      lowGeometryExponent reflected Z A
        (geometryFirstLabel s R seed K Z ξ hK key j)≤exponent ∧
      sideLower≤geometryHighSide reflected A (geometryExponents s R seed K Z ξ j.1.val) := by
  intro w c p exponent sideLower
  refine ⟨by dsimp [p,exponent,sideLower];ring,?_⟩
  intro j
  let x:=geometryExponents s R seed K Z ξ j.1.val
  have hx (i : Fin 5) : (key.2 i:ℝ)*w≤x i ∧ x i≤((key.2 i:ℝ)+1)*w := by
    have h:=actual_geometry_fiber_range s R seed K Z ξ B hZ hs hz₁ hz₂ hsource key j.1 i
    exact ⟨h.1,h.2.le⟩
  refine ⟨?_,?_,?_⟩
  · have hn:=actual_geometry_norm_caps s R seed K Z ξ B hs hz₁ hz₂ hsource j.1.val 2
    exact (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le hn.1)).mp (hx 2).2
  · rw [actual_low_geometry_exponent_coordinates]
    change A-x c+x 3+x 4≤exponent
    dsimp only [exponent]
    linarith [(hx c).1,(hx 3).2,(hx 4).2]
  · have hbase : sideLower≤x 2+A-x c+x 3+x 4 := by
      dsimp only [sideLower]
      linarith [(hx 2).1,(hx c).2,(hx 3).1,(hx 4).1]
    have hsurplus : 0≤geometrySurplus x := actual_geometry_surplus_nonneg s R seed K Z ξ hZ j.1.val
    cases reflected <;>
      simp only [geometryHighSide,Bool.false_eq_true,ite_false,ite_true,leftExponent,rightExponent] <;>
      simp only [c,Bool.false_eq_true,ite_false,ite_true] at hbase
    all_goals change sideLower≤x 2+A-x _+x 3+x 4+max (3*x _-5*x _-x 3) 0/6+geometrySurplus x
    · linarith [le_max_right (3*x 0-5*x 1-x 3) (0:ℝ)]
    · linarith [le_max_right (3*x 1-5*x 0-x 3) (0:ℝ)]

/-- The scalar gates of one common first-geometry bin for a per-label exponent `labelExp`: a pair of exponents bounds
the common radical, the label exponent and the high side, and its combined loss is `slack` binary-bin widths. -/
def LowBinGate (labelExp : Bool → ℝ → ℝ → FirstSourceLabel → ℝ) (slack : ℝ) : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (s : Input α) (R seed : Ideal O) (K Z ξ B A : ℝ) (hK : 0<K),
    1<Z → Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤Z^B →
    ∀(key : ℤ×(Fin 5→ℤ))(reflected : Bool),
    ∃exponent sideLower : ℝ,
      ((key.2 2:ℝ)+1)*Real.logb Z 2+exponent-sideLower=slack*Real.logb Z 2 ∧
      ∀j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key),
        ((commonRadical
          (geometryFirstLabel s R seed K Z ξ hK key j).1.1
          (geometryFirstLabel s R seed K Z ξ hK key j).1.2).absNorm:ℝ)≤Z^(((key.2 2:ℝ)+1)*Real.logb Z 2) ∧
        labelExp reflected Z A (geometryFirstLabel s R seed K Z ξ hK key j)≤exponent ∧
        sideLower≤geometryHighSide reflected A (geometryExponents s R seed K Z ξ j.1.val)

/-- A gate with a smaller loss is a gate with a larger loss. -/
theorem LowBinGate.mono {labelExp : Bool → ℝ → ℝ → FirstSourceLabel → ℝ} {slack slack' : ℝ}
    (h : LowBinGate labelExp slack) (hs : slack ≤ slack') : LowBinGate labelExp slack' := by
  intro α _ _ s R seed K Z ξ B A hK hZ hsq hz₁ hz₂ hsource key reflected
  obtain ⟨exponent,sideLower,hslack,hgate⟩:=h s R seed K Z ξ B A hK hZ hsq hz₁ hz₂ hsource key reflected
  have hw : 0≤Real.logb Z 2 := Real.logb_nonneg hZ (by norm_num)
  have hextra : 0≤(slack'-slack)*Real.logb Z 2 := mul_nonneg (sub_nonneg.mpr hs) hw
  refine ⟨exponent,sideLower-(slack'-slack)*Real.logb Z 2,by linarith,fun j=>?_⟩
  obtain ⟨hrad,hexp,hside⟩:=hgate j
  exact ⟨hrad,hexp,(by linarith : sideLower-(slack'-slack)*Real.logb Z 2 ≤ sideLower).trans hside⟩

/-- The first-level gates of one common first-geometry bin, for the label exponent of the old region. -/
theorem actual_geometry_low_bin_gate : LowBinGate lowGeometryExponent 4 := by
  intro α _ _ s R seed K Z ξ B A hK hZ hs hz₁ hz₂ hsource key reflected
  have h:=actual_geometry_low_bin_scalar_gates s R seed K Z ξ B A hK hZ hs hz₁ hz₂ hsource key reflected
  exact ⟨_,_,h.1,h.2⟩

/-- The complete bin slack costs sixteen, independently of the scale. -/
theorem geometry_low_bin_slack_payment (Z : ℝ) (hZ : 1<Z) :
    Z^(4*Real.logb Z 2)=(16:ℝ) := by
  rw [mul_comm (4:ℝ),Real.rpow_mul (zero_lt_one.trans hZ).le,
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (by norm_num : (0:ℝ)<2)]
  norm_num

/-- Six binary-bin widths cost sixty-four, independently of the scale. -/
theorem geometry_low_bin_slack_six_payment (Z : ℝ) (hZ : 1<Z) :
    Z^(6*Real.logb Z 2)=(64:ℝ) := by
  rw [mul_comm (6:ℝ),Real.rpow_mul (zero_lt_one.trans hZ).le,
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (by norm_num : (0:ℝ)<2)]
  norm_num

/-- A nonempty first geometry bin has a uniformly bounded radical upper
endpoint. The extra one is only the last binary interval at Z at least two. -/
theorem actual_geometry_low_bin_radical_exponent_cap
    {α : Type*} [Fintype α] [DecidableEq α]
    (s : Input α) (R seed : Ideal O) (K Z ξ B : ℝ)
    (hZ : 2≤Z) (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤Z^B) (key : ℤ×(Fin 5→ℤ))
    (q : CommonGeometryFiber s R seed K Z ξ key) :
    ((key.2 2:ℝ)+1)*Real.logb Z 2≤B+1 := by
  have hZ1 : 1<Z := by linarith
  have hn:=actual_geometry_norm_caps s R seed K Z ξ B hs hz₁ hz₂ hsource q.val 2
  have hx:=actual_geometry_fiber_range s R seed K Z ξ B hZ1 hs hz₁ hz₂ hsource key q 2
  have hcap : geometryExponents s R seed K Z ξ q.val 2≤B :=
    (Real.logb_le_iff_le_rpow hZ1 (zero_lt_one.trans_le hn.1)).mpr hn.2
  have hw : Real.logb Z 2≤1 := by
    apply (Real.logb_le_iff_le_rpow hZ1 (by norm_num : (0:ℝ)<2)).mpr
    simpa only [Real.rpow_one] using hZ
  nlinarith

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
