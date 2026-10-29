/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.UniformCoreCount
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.BufferedRootedCount

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped Classical BigOperators ContDiff
open Set Filter OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification HeckeDyadic HeckeDetectorWitnessRows
open HeckeDetectorSupportedWitness HeckeDetectorClassBudget
open QRH.Record12518109Existence QRH.Record1252270103Source
open CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O

/-- Genuine repeated source count for actual buffered zero events. The
mesh and repetition budget precede all finite slots. Degree and constant
precede the detector height power, so its polynomial cost can be paid by
an arbitrarily small later choice of that power. -/
theorem zero_count_at_loss
    (B L c νmin dmin smin loss : ℝ) (hL : 3/2≤L) (hB0 : 0≤B) (hBmin : 9/10≤B) (hB : B≤1)
    (hc0 : 0≤c) (hc : c≤1/6) (hνmin : 0<νmin) (hdmin : 0<dmin) (hsmin : 0<smin) (hloss : 0<loss)
    (hsource : GlobalSource B L c) (hβglobal : (51/100:ℝ)≤HeckeZeroSupremum.beta) :
    ∃ meshMax β εMax : ℝ,0<meshMax ∧ 0<β ∧ β≤dmin/4 ∧ 0<εMax ∧
    ∀mesh : ℝ,0≤mesh → mesh≤meshMax →
    ∀{Label Slot : Type}[Fintype Label][Nonempty Label][Fintype Slot][DecidableEq Slot],
    ∀(M : Ideal O)[NeZero M](H : Subgroup (O⧸M)ˣ)(hH : RayOrthogonality.globalUnits M≤H)
      (Aroot : ℝ),0≤Aroot → ∀(base anchor : Label→Character)(bad : Label→Ideal O),
    (∀j,bad j≤M) → (∀j,internalQ (bad j) (anchor j)≠0) →
    (∀j,internalQ (bad j) (anchor j)≠⊤) →
    (∀j,internalQ (bad j) (anchor j)≤Ideal.span {(72:O)}) →
    ∀(W : ℝ→ℂ),ContDiff ℝ ∞ W → Function.support W⊆Icc (1:ℝ) 2 →
    ∃J : ℕ,∃C : ℝ,0<C ∧
    ∀(τ ε e κ η : ℝ)(n : ℕ),0<τ → τ<1/2 → 4*τ<η →
      0<ε → ε≤εMax → 0<e → e<1/1000 → 0<κ → κ≤1 → 0≤η →
      12*e*((22:ℝ)+2)+8*κ+2*η≤ε/2 → 0<n → (49/100:ℝ)≤(n:ℝ)*e →
    ∀ᶠU : ℝ in atTop,1<U ∧
    ∀N : RootedBatch (Slot:=Slot) M H hH base anchor bad W U Aroot,
    (∀s∈N.slots,N.widths s≤mesh) →
    ∀(a₀ v height : ℝ),51/100<a₀ → νmin≤2*a₀-1 → 2*a₀-1≤3/4 →
      dmin≤v → v≤2*a₀-1 → 0≤height →
    (∀s∈N.slots,|N.commonHeight+N.relativeHeight s|≤height) →
    smin≤∑s∈N.slots,N.widths s →
    (∀u∈N.rows,U^(v*(∑s∈N.slots,N.widths s))≤∏s∈N.slots,‖N.Q u s‖^2) →
    ∀hχ : ∀u : N.rows,∀j,(N.family u.val j).residue≠1,
    (∀u : N.rows,∀j,(N.family u.val j).modulus.absNorm≤U) →
    (∀u : N.rows,a₀+e≤HeckeDetectorZeros.zeroMaximum (N.family u.val) (hχ u) (U^τ)) →
    2*Real.pi*U^(τ/2)+(3*n:ℕ)*U^τ≤height →
    (N.rows.card:ℝ)≤((n+1:ℕ):ℝ)*(⌈1/e⌉₊+2:ℕ)*C*(1+height)^J*
      U^(rawRepeatedCountRate B L c (2*a₀-1) v+loss) := by
  obtain ⟨meshMax,β,εMax,hm,hβ,hβd,hεMax,hsourceCount⟩ := supported_count_at_loss
    B L c νmin dmin smin loss hL hB0 hB hc0 hc hνmin hdmin hsmin hloss hsource hβglobal
  refine ⟨meshMax,β,εMax,hm,hβ,hβd,hεMax,?_⟩
  intro mesh hmesh0 hmesh Label Slot _ _ _ _ M _ H hH Aroot hAr base anchor bad
    hQM hQ0 hQt hQ72 W hW hWs
  obtain ⟨J,C,hC,hcount⟩ := hsourceCount mesh hmesh0 hmesh (Label:=Label) (Slot:=Slot) M H hH Aroot hAr base anchor bad
    hQM hQ0 hQt hQ72 W hW hWs
  refine ⟨J,C,hC,?_⟩
  intro τ ε e κ η n hτ hτsmall hτη hε hεsmall he heSmall hκ hκSmall hη hbudget hn hwidth
  obtain ⟨U₀,hzeroCount⟩ := actual_buffered_rooted_count 1 1 τ ε e κ η n
    (by norm_num) le_rfl hτ hτsmall (by simpa using hτη) hε he heSmall hκ hκSmall hη hbudget
  have hT : ∀ᶠU : ℝ in atTop,2<U^τ :=
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop 2)
  filter_upwards [hcount,eventually_ge_atTop U₀,hT] with U hcount hU₀ hT
  refine ⟨hcount.1,?_⟩
  intro N hwm a₀ v height ha₀ hνlow hνhi hvmin hv hh hphase hS hresponse hχ hconductor hzero hfreq
  let tstar := max
    (crossingCut (2*a₀-1) ((v-β)/(2*(2*a₀-1))) 2 (2*((v-β)/(2*(2*a₀-1)))*c))
    (crossingCut (2*a₀-1) ((v-β)/(2*(2*a₀-1))) (2-4*((v-β)/(2*(2*a₀-1)))/L)
      (2*((v-β)/(2*(2*a₀-1)))*B/L))
  have hν : 0<2*a₀-1 := hνmin.trans_le hνlow
  have hvβ : 0≤v-β := by linarith
  have hvβν : v-β≤2*a₀-1 := by linarith
  have hp0 : 0≤(v-β)/(2*(2*a₀-1)) := div_nonneg hvβ (by positivity)
  have hp : (v-β)/(2*(2*a₀-1))≤1/2 := (div_le_iff₀ (by positivity)).2 (by linarith)
  have htCap := cap_cutoff_bounds hν hνhi hp0 hp hc0 hc
  have htBudget := budget_cutoff_bounds hBmin hB hL hν hνhi hp0 hp
  have ht0 : 1≤tstar := (htCap.1.le).trans (le_max_left _ _)
  have ht1 : tstar≤3/2 := max_le htCap.2.le htBudget.2.le
  have hz := hzeroCount U hU₀ 1 le_rfl le_rfl (Label:=Label) (Slot:=Slot) (M:=M) (H:=H) (hH:=hH) (base:=base) (anchor:=anchor) (bad:=bad) (W:=W) (Aroot:=Aroot)
  rw [Real.rpow_one] at hz
  rw [mul_one] at hz
  have hUp : 0<U := zero_lt_one.trans hcount.1
  have hcard := hz N a₀ tstar (C*(1+height)^J*U^(rawRepeatedCountRate B L c (2*a₀-1) v+loss))
    hcount.1 hT hn hwidth ha₀ ht0 ht1 (by positivity) hχ hconductor hzero ?_
  · convert hcard using 1 <;> ring
  intro F hF i hi χ hχ' witness
  let NF := N.restrict F hF
  apply hcount.2 NF hwm χ a₀ ε tstar (U^τ) (U^(τ/2)) i
    (by linarith) hε.le hεsmall witness (fun _=>false) ?_ v height
    hνlow hνhi hvmin hv hh hphase hS ?_ rfl ht0 ht1 ?_
  · intro u hu j I
    rw [hχ' u hu]
    rfl
  · intro u hu
    exact hresponse u (hF hu)
  · have hi' : (3*i:ℕ)≤3*n := Nat.mul_le_mul_left 3 hi
    have hiR : ((3*i:ℕ):ℝ)≤(3*n:ℕ) := by exact_mod_cast hi'
    have hp := mul_le_mul_of_nonneg_right hiR (Real.rpow_nonneg (zero_lt_one.trans hcount.1).le τ)
    linarith only [hp,hfreq]

end
end Qrh.JointDetector.RepeatedMarks

#print axioms Qrh.JointDetector.RepeatedMarks.zero_count_at_loss
