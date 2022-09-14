import Lake
open Lake DSL

package «egg-tactic» {
  supportInterpreter := true,
  libRoots := #[`EggTactic]
  libName := "EggTactic"
  binRoot := `Main

  -- add configuration options here

}

--require «aesop» from git  "https://github.com/JLimperg/aesop" @ "3fb480b3d7b1e70e488e479e94875bb94d7c8ade"
