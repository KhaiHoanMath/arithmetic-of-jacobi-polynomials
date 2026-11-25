module

import ArithmeticOfJacobiPolynomials
public meta import Lean.Util.CollectAxioms
public meta import Lean.Elab.Command

/-! Check logical axioms of declarations exported by the project modules.
Literature assumptions and unformalized computations are parameters in theorem statements. -/

set_option maxHeartbeats 0 in
-- The audit traverses every declaration exported by every project module.
open Lean in
run_cmd do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  let mut modules : Nat := 0
  for mod in env.header.modules, data in env.header.moduleData do
    unless (`ArithmeticOfJacobiPolynomials).isPrefixOf mod.module do continue
    modules := modules + 1
    for decl in data.constNames do
      for ax in ← collectAxioms decl do
        unless allowed.contains ax do
          throwError "{decl} depends on the unexpected axiom {ax}"
      count := count + 1
  if count == 0 then throwError "No declarations from the project were found"
  logInfo m!"Checked the logical axioms of {count} exported declarations \
    in {modules} project modules."

open ArithmeticOfJacobiPolynomials in
-- These applications check the complete list of hypotheses in the two revised statements.
example (hw : HoltWahabLegendreIrreducibility) (hh : HansonLcmBound) (hz : JacobiSimpleRealZeros) :
    LegendreAndDerivativesStatement ∧ CommonRootsStatement :=
  ⟨legendreAndDerivatives_verified hw hh hz, commonRoots_verified hw hh hz⟩
