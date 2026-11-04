import KroneckerManuscriptDimensions
import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let modules := #[`KroneckerManuscriptDimensions]
  let mut count : ℕ := 0
  for (n, _) in env.constants.toList do
    if let some i := env.getModuleIdxFor? n then
      if modules.contains env.header.moduleNames[i.toNat]! then
        let axioms ← Lean.collectAxioms n
        for a in axioms do
          unless #[`propext, `Classical.choice, `Quot.sound].contains a do
            throwError "Unexpected axiom {a} in {n}"
        logInfo m!"PROFILE {n}: {axioms}"
        count := count + 1
  logInfo m!"AUDITED {count} declarations"
