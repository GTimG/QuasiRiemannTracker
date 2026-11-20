/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual first-short inverse continuation outside the central anchor window. -/
import Candidate.C092.transport.MixedOffsetCountBankFacts
import Candidate.C092.transport.DirectCountMarkedInverse
import Candidate.C092.transport.MixedTicketTailsRawPrice
set_option autoImplicit false
namespace QRH.Cycle092.MixedOutsidePaid
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorRawFiber
open QRH.Record12518109Count Cycle25ProbeFinalAssembly

open QRH.Cycle092.MixedOffsetCount
open QRH.Cycle092.PacketJoinE49

def inverseHighR (δ p:ℝ) : ℝ := 1-δ*(p+(1-p)*anchorTop)

/-- Two actual native continuation sources on the identical retained subset.
The original inverse field supplies both counts; no moment/count is assumed. -/
theorem actual_inverse_high_count (D:Cycle25.Weighted.MomentData) (S:WeightedSourceData D) :
    ∃J:ℕ,∀η:Character,∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(d a tstar T allowance height:ℝ) (i:ℕ),
      (1/200:ℝ)≤d → 51/100<a → 2*a-1≤3/4 → D.t≤1/10000000 →
      0≤height → 2*Real.pi*allowance+(3*i:ℕ)*T≤height →
    ∀(P:Presented D S η Z d a tstar T allowance i) (F:Slice P),
      anchorTop≤F.fiber.r → F.fiber.r<1 →
    ∀common:Finset FreeRow,common⊆F.fiber.rows →
      (common.card:ℝ)≤(12*(1+height)*(C*(1+height)^J))*
        (Z^d)^(inverseHighR (2*a-1) (F.fiber.q/(2*a-1))+countLoss D.ε P.batch.mesh D.t) := by
  obtain ⟨Jm,hmarked⟩:=QRH.Cycle092.DirectCount.source_marked_inverse_fiber_count D S
  obtain ⟨Ki,hKi,Ji,hinverse⟩:=QRH.Cycle092.DirectCount.source_inverse_fiber_count D S
  refine ⟨Jm+Ji,?_⟩
  intro η
  obtain ⟨Cm,hCm,hm⟩:=hmarked η
  obtain ⟨Ci,hCi,hi⟩:=hinverse η
  let C:=Cm+Ci*Ki+1
  have hC:0<C:=by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [hm,hi] with Z hm hi
  refine ⟨hm.1,?_⟩
  intro d a tstar T allowance height i hd ha hδhi ht hh hf P F hr hr1 common hsub
  have hU:1<Z^d:=Real.one_lt_rpow hm.1 (by linarith)
  have hδ:0<2*a-1:=by linarith
  have hgeom:=F.fiber.lengths hU
  obtain ⟨hq,hqhi⟩:=F.fiber.mean_bounds (by linarith:1/2≤a)
  have hp:0≤F.fiber.q/(2*a-1):=div_nonneg hq hδ.le
  have hp1:F.fiber.q/(2*a-1)≤1/2:=(div_le_iff₀ hδ).mpr (by linarith)
  have hqp:(2*a-1)*(F.fiber.q/(2*a-1))=F.fiber.q:=mul_div_cancel₀ _ hδ.ne'
  have hH:1≤1+height:=by linarith
  have pm:Cm*(1+height)^Jm ≤ C*(1+height)^(Jm+Ji):=
    mul_le_mul (by dsimp [C];nlinarith [mul_nonneg hCi.le hKi])
      (pow_le_pow_right₀ hH (by omega)) (by positivity) hC.le
  have pi:(Ci*(1+height)^Ji)*Ki ≤ C*(1+height)^(Jm+Ji):=by
    calc
      _ = (Ci*Ki)*(1+height)^Ji:=by ring
      _ ≤ C*(1+height)^(Jm+Ji):=mul_le_mul (by dsimp [C];linarith)
        (pow_le_pow_right₀ hH (by omega)) (by positivity) hC.le
  have hconst:0≤12*(1+height)*(C*(1+height)^(Jm+Ji)):=by positivity
  have hsCard:(common.card:ℝ)≤(F.fiber.rows.card:ℝ):=by exact_mod_cast Finset.card_le_card hsub
  have hbound:(F.fiber.rows.card:ℝ)≤(12*(1+height)*(C*(1+height)^(Jm+Ji)))*
      (Z^d)^(inverseHighR (2*a-1) (F.fiber.q/(2*a-1))+countLoss D.ε P.batch.mesh D.t):=by
    by_cases hr9:F.fiber.r≤9/10
    · let z:ℝ:=(1-F.fiber.r)/2-D.t
      have hz:0≤z:=by dsimp [z];linarith [D.t_pos]
      have hzmax:z≤7/37:=by norm_num [anchorTop] at hr;dsimp [z];linarith [D.t_pos]
      have hcap1:F.fiber.r+2*z<1:=by dsimp [z];linarith [D.t_pos]
      have hcap2:2*F.fiber.r+8*z<3:=by norm_num [anchorTop] at hr;dsimp [z];linarith [D.t_pos]
      have hb:=hm.2 d hd a D.ε tstar T allowance i P.batch P.data P.profile P.upper P.widths P.real
        F.bin F.label F.left F.right F.nonempty height z hh (by linarith) hf hz hzmax hcap1 hcap2
      have hprod:(1-F.fiber.q/(2*a-1))*anchorTop ≤ (1-F.fiber.q/(2*a-1))*F.fiber.r:=
        mul_le_mul_of_nonneg_left hr (by linarith)
      have hE:1-(2*a-1)*F.fiber.r-2*F.fiber.q*z+2*D.ε+(2*a-1)*F.fiber.mesh+D.t ≤
          inverseHighR (2*a-1) (F.fiber.q/(2*a-1))+countLoss D.ε P.batch.mesh D.t:=by
        have hmsh: (2*a-1)*F.fiber.mesh≤P.batch.mesh:=by
          change (2*a-1)*P.batch.mesh≤P.batch.mesh
          exact mul_le_of_le_one_left P.batch.mesh_nonneg (by linarith)
        have hmul:=mul_le_mul_of_nonneg_left hprod hδ.le
        have hq1:2*F.fiber.q≤1:=by linarith
        have hqDt:=mul_le_mul_of_nonneg_right hq1 D.t_pos.le
        have hid:1-(2*a-1)*F.fiber.r-2*F.fiber.q*z =
            1-(2*a-1)*(F.fiber.q/(2*a-1)+(1-F.fiber.q/(2*a-1))*F.fiber.r)+2*F.fiber.q*D.t:=by
          dsimp only [z]
          have hrqp:=congrArg (fun x:ℝ=>x*F.fiber.r) hqp
          nlinarith only [hqp,hrqp]
        rw [hid]
        unfold inverseHighR countLoss
        nlinarith only [hmul,hqDt,hmsh,D.epsilon_pos,D.t_pos]
      exact hb.trans ((mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left pm (by positivity:0≤12*(1+height)))
          (Real.rpow_nonneg (zero_lt_one.trans hU).le _)).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.le hE) hconst))
    · have hrr:(9/10:ℝ)≤F.fiber.r:=le_of_lt (lt_of_not_ge hr9)
      have hb:=hi.2 d hd a D.ε tstar T allowance i P.batch P.data P.profile P.upper P.widths P.real
        F.bin F.label F.left F.right F.nonempty height hh (by linarith) hf (by linarith) (by linarith)
      have hbr:F.fiber.q/(2*a-1)+(1-F.fiber.q/(2*a-1))*anchorTop≤9/10:=by
        norm_num [anchorTop]
        linarith
      have hE:sourceExponent F.fiber.r-(2*a-1)*F.fiber.r+2*D.ε+D.t ≤
          inverseHighR (2*a-1) (F.fiber.q/(2*a-1))+countLoss D.ε P.batch.mesh D.t:=by
        unfold sourceExponent
        rw [max_eq_left (by linarith only [hr1] : (1+5*F.fiber.r)/6≤(1:ℝ))]
        have hh0:=mul_le_mul_of_nonneg_left (hbr.trans hrr) hδ.le
        unfold inverseHighR countLoss
        nlinarith only [hh0,D.epsilon_pos,D.t_pos,P.batch.mesh_nonneg]
      exact hb.trans ((mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left pi (by positivity:0≤12*(1+height)))
          (Real.rpow_nonneg (zero_lt_one.trans hU).le _)).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.le hE) hconst))
  exact hsCard.trans hbound

#print axioms actual_inverse_high_count
end
end QRH.Cycle092.MixedOutsidePaid
