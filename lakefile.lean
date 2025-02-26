import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"f0957a7575317490107578ebaee9efaf8e62a4ab"

require FastMemset from git
  "https://github.com/NethermindEth/Lean4UtilMemset.git"

package «evmyul» {
  moreLeanArgs := #["-DautoImplicit=false"]
  moreServerOptions := #[⟨`DautoImplicit, false⟩]
}

target cloneSha2 pkg : GitRepo := do
  let repoDir : GitRepo := ⟨pkg.dir / "sha2"⟩
  if !(← repoDir.dir.pathExists) then
    GitRepo.clone "https://github.com/amosnier/sha-2.git" repoDir
  return pure repoDir

def inputTextFile (path : FilePath) : SpawnM (BuildJob FilePath) :=
  Job.async <| (path, ·) <$> computeTrace (TextFilePath.mk path)

def hash256CDir (hash256repo : GitRepo) : System.FilePath :=
  hash256repo.dir

abbrev compiler := "cc"

-- def buildSha256Obj (pkg : Package) (fileName : String) := do
--   let (repo, _)   ← (←clonesha2.fetch).await
--   let cDir        := hash256CDir repo
--   let srcJob      ← inputTextFile $ cDir / fileName |>.addExtension "cpp"
--   let oFile       := pkg.buildDir / fileName |>.addExtension "o"
--   let includeArgs := #["-I", cDir.toString]
--   buildO oFile srcJob includeArgs #["-fPIC"] compiler getLeanTrace

-- target ffi.o pkg : System.FilePath := do
--   let (repo, _)  ← (←clonesha2.fetch).await
--   let oFile      := pkg.buildDir / "ffi.o"
--   let srcJob     ← inputFile $ pkg.dir / "ffi.cpp"
--   let includeDir ← getLeanIncludeDir
--   let cDir       := hash256CDir repo
--   let weakArgs   := #["-I", includeDir.toString, "-I", cDir.toString]
--   buildO oFile srcJob weakArgs #["-fPIC"] compiler getLeanTrace

-- extern_lib ffi pkg := do
--   let sha256O ← buildSha256Obj pkg "sha"
--   let ffiO    ← ffi.o.fetch
--   let name    := nameToStaticLib "ffi"
--   buildStaticLib (pkg.nativeLibDir / name) #[sha256O, ffiO]

target ffi.o pkg : FilePath := do
  let (sha2, _) ← (←cloneSha2.fetch).await
  let oFile := pkg.buildDir / "ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "EvmYul" / "FFI" / "ffi.c"
  let weakArgs := #[
    "-I", (← getLeanIncludeDir).toString,
    "-I", sha2.dir.toString
  ]
  buildO oFile srcJob weakArgs #["-fPIC"] compiler getLeanTrace

def buildSha256Obj (pkg : Package) (fileName : String) := do
  let (sha2, _) ← (←cloneSha2.fetch).await
  let srcJob ← inputTextFile $ sha2.dir / fileName |>.addExtension "c"
  let oFile := pkg.buildDir / fileName |>.addExtension "o"
  let includeArgs := #["-I", sha2.dir.toString]
  let weakArgs := includeArgs
  buildO oFile srcJob weakArgs #[] compiler getLeanTrace

extern_lib libleanffi pkg := do
  -- In the static lib we include:
  -- the `sha-256` library itself
  let sha256O ← buildSha256Obj pkg "sha-256"
  -- our own `ffi.c`
  let ffiO ← ffi.o.fetch
  let name := nameToStaticLib "leanffi"
  buildStaticLib (pkg.nativeLibDir / name) #[sha256O, ffiO]

lean_lib «Conform»
  
lean_lib «sha2»

@[default_target]
lean_lib «EvmYul»

lean_exe «conform» where
  root := `Conform.Main
