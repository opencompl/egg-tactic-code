import Lake
open Lake DSL

package «egg-tactic» {

}

def compileCargo (name : String) (manifestFile : FilePath)
 (cargo : FilePath := "cargo") : LogIO Unit := do
  logInfo s!"Creating {name}"
  proc {
    cmd := cargo.toString
    args := #["build", "--release", "--manifest-path", manifestFile.toString]
  }

def buildCargo (targetFile : FilePath) (manifestFile : FilePath)
(oFileJobs : Array (BuildJob FilePath)) : SchedulerM (BuildJob FilePath) :=
  let name := targetFile.fileName.getD targetFile.toString
  buildFileAfterDepArray targetFile oFileJobs fun _ => do
    compileCargo name manifestFile

@[defaultTarget]
target «egg-herbie» (pkg : Package) : FilePath := do
  let buildDir := pkg.dir / "json-egg"
  let binFile := buildDir / "target" / "release" / "egg-herbie"
  let manifestFile := buildDir / "Cargo.toml"
  buildCargo binFile manifestFile #[]

lean_lib EggTactic{
  roots := #[`EggTactic]
}
  -- add configuration options here

--require «aesop» from git  "https://github.com/JLimperg/aesop" @ "3fb480b3d7b1e70e488e479e94875bb94d7c8ade"
