import Lake
open Lake DSL

package «egg-tactic» {
  supportInterpreter := true,
  libRoots := #[`EggTactic]
  libName := "EggTactic"
  binRoot := `Main

  -- add configuration options here
}
