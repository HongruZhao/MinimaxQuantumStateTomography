import MainResults
import Lean.Util.CollectAxioms

open Lean Elab Command
set_option maxHeartbeats 0
set_option pp.fullNames true

run_cmd do
  let standard := #[`propext, `Classical.choice, `Quot.sound]
  let targets : Array Name := #[`TomographyOracleCore.PaperMatch.ExactMain.theorem3, `TomographyOracleCore.PaperMatch.ExactMain.theorem3_solver_fit, `TomographyOracleCore.PaperMatch.ExactMain.theorem3_mw_record, `TomographyOracleCore.PaperMatch.ExactMain.corollary4, `TomographyOracleCore.PaperMatch.ExactMain.corollary4_omd_record, `TomographyOracleCore.PaperMatch.ExactMain.corollary4_mw]
  let mut rows : Array Json := #[]
  for name in targets do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun n => !standard.contains n
    unless bad.isEmpty do throwError "Unexpected axioms for {name}: {bad}"
    let info ← getConstInfo name
    let statement ← liftTermElabM do return (← Meta.ppExpr info.type).pretty
    rows := rows.push (Json.mkObj [
      ("name", toJson name.toString), ("type", toJson statement),
      ("axioms", toJson (axioms.map Name.toString))])
  IO.FS.createDirAll "verification/rerun"
  IO.FS.writeFile "verification/rerun/main_endpoints.json" ((toJson rows).pretty ++ "\n")
  logInfo m!"MAIN_AXIOM_AUDIT: {targets.size} endpoints; only standard Lean foundations"
