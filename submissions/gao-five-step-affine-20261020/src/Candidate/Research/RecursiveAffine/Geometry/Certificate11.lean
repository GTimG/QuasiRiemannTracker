import Candidate.Research.RecursiveAffine.Geometry.Constraints
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153Geometry
noncomputable section
open scoped BigOperators

namespace Certificate11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- stage_1_U; exact fixed-price input. -/
def objective : Affine 14 := ![(112107264619002524652637939772382352119898600442266630799970071840751813459555476751008924290126756132548599049997156750911419586421345660795093803782270936322222558836734187026837201613599566473887705868583331937623065049461659998335730190189320487457259105416630595732548867607638772454640224236773862400307649126793289881586501025472389576373412001022608652837526780981965545946243708547060953137 / 98915411193238710949752739142409074645338399489735276869715911282846994576276999133331994971118384818255034153519941364721535193967355885919237728104270009432407328158785398882719867723811779828703728018553154953738332339560453984890392037860388698207738936879386732553947458099652958258669650600505801770008308079129599448721238887292162274889569384857822895821599146261668298365282298265600000000), (-136410301700604760261767533404598043949337886370045118152255848744652459119976518020631916242635383674957222366157930 / 29397392789312960882578709234168016747099711891573401930173224526792653335728037697923015688799521699772526341867829), -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def weights : Fin 1 → ℚ := ![1]

def rows : Fin 1 → Affine 14 := ![Model.constraint08]

def selected : Fin 1 → Fin 48 := ![8]

def margin : ℚ := (397 / 1000)

theorem coordinate_identity : ∀ i : Fin 15, objective i = constant margin i + ∑ j, weights j * rows j i := by
  intro i
  fin_cases i <;> norm_num [objective, weights, rows, margin, constant, Fin.sum_univ_succ, Model.constraint08]

theorem weights_nonneg : ∀ j, 0 ≤ weights j := by
  intro j
  fin_cases j <;> norm_num [weights]

theorem margin_gt : (157 / 100000000000 : ℚ) < margin := by
  norm_num [margin]

theorem mass_lt : (∑ j, weights j) < 1489 := by
  norm_num [weights, Fin.sum_univ_succ]

theorem rows_selected : ∀ j, rows j = Model.constraint (selected j) := by
  intro j
  fin_cases j <;> rfl

theorem prefix_admissible : ∀ j, (selected j).val < 14 ∨ 35 ≤ (selected j).val := by
  intro j
  fin_cases j <;> norm_num [selected]

def certificate : Certificate 14 1 where
  objective := objective
  rows := rows
  weights := weights
  margin := margin
  weights_nonneg := weights_nonneg
  coordinate_identity := coordinate_identity
  margin_gt := margin_gt
  mass_lt := mass_lt

theorem positive (x : Fin 14 → ℝ) (E : ℝ) (hE : E ≤ 1 / 1000000000000000)
    (hc : ∀ j, -E ≤ eval (Model.constraint (selected j)) x) :
    0 < eval objective x := by
  apply certificate.positive_of_constraint_error x E hE
  intro j
  change -E ≤ eval (rows j) x
  rw [rows_selected]
  exact hc j

theorem robust_lower (x : Fin 14 → ℝ) (E : ℝ) (hE : E ≤ 1 / 1000000000000000)
    (hc : ∀ j, -E ≤ eval (Model.constraint (selected j)) x) :
    (1568511 / 1000000000000000 : ℝ) < eval objective x := by
  apply certificate.uniform_robust_lower x E hE
  intro j
  change -E ≤ eval (rows j) x
  rw [rows_selected]
  exact hc j

end Certificate11

end
end OAI.SevenEighths.Cycle153Geometry

#print axioms OAI.SevenEighths.Cycle153Geometry.Certificate11.robust_lower
