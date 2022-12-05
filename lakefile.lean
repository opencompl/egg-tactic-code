import Lake
open Lake DSL

package «egg-tactic»

lean_lib EggTactic

@[defaultTarget]
lean_exe «EggTacticExe» {
  root := `EggTactic
  supportInterpreter := true
}

-- require «egg-tactic» from git  "https://github.com/opencompl/egg-tactic-code" @ "499ef2d"
