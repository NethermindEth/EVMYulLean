import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"f0957a7575317490107578ebaee9efaf8e62a4ab"

package «evmyul» {
  moreLeanArgs := #["-DautoImplicit=false"]
  moreServerOptions := #[⟨`DautoImplicit, false⟩]
}

def cloneWithCache (pkg : NPackage _package.name) (dirname url : String) : FetchM (BuildJob GitRepo) := do
  let repoDir : GitRepo := ⟨pkg.dir / dirname⟩
  if !(← repoDir.dir.pathExists) then dbg_trace s!"Cloning: {url}"; GitRepo.clone url repoDir
  return pure repoDir

target cloneSha2 pkg : GitRepo := cloneWithCache pkg "sha2" "https://github.com/amosnier/sha-2.git"

target cloneKeccak256 pkg : GitRepo := cloneWithCache pkg "keccak256" "https://github.com/brainhub/SHA3IUF.git"

def inputTextFile (path : FilePath) : SpawnM (BuildJob FilePath) :=
  Job.async <| (path, ·) <$> computeTrace (TextFilePath.mk path)

def hash256CDir (hash256repo : GitRepo) : System.FilePath :=
  hash256repo.dir

abbrev compiler := "cc"

target ffi.o pkg : FilePath := do
  let (sha2, _) ← (←cloneSha2.fetch).await
  let (keccak256, _) ← (←cloneKeccak256.fetch).await
  let oFile := pkg.buildDir / "ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "EvmYul" / "FFI" / "ffi.c"
  let weakArgs := #[
    "-I", (← getLeanIncludeDir).toString,
    "-I", sha2.dir.toString,
    "-I", keccak256.dir.toString
  ]
  buildO oFile srcJob weakArgs #["-fPIC"] compiler getLeanTrace

def buildFFILib (pkg : Package) (repo : GitRepo) (fileName : String) : FetchM (BuildJob FilePath) := do
  let srcJob ← inputTextFile $ repo.dir / fileName |>.addExtension "c"
  let oFile := pkg.buildDir / fileName |>.addExtension "o"
  let includeArgs := #["-I", repo.dir.toString]
  let weakArgs := includeArgs
  buildO oFile srcJob weakArgs #["-fPIC"] compiler getLeanTrace

def buildSha256Obj (pkg : Package) (fileName : String) := do
  buildFFILib pkg (← (←cloneSha2.fetch).await).1 fileName

def buildKeccak256Obj (pkg : Package) (fileName : String) := do
  buildFFILib pkg (← (←cloneKeccak256.fetch).await).1 fileName

extern_lib libleanffi pkg := do
  -- In the static lib we include:
  -- the `sha-256` library itself
  let sha256O ← buildSha256Obj pkg "sha-256"
  let keccak256 ← buildKeccak256Obj pkg "sha3"
  -- our own `ffi.c`
  let ffiO ← ffi.o.fetch

  if !(←System.FilePath.pathExists "EthereumTests") then
    dbg_trace s!"Cloning EthereumTests into a submodule." 
    discard <| IO.Process.run {cmd := "git submodule init"}

  let name := nameToStaticLib "leanffi"
  buildStaticLib (pkg.nativeLibDir / name) #[sha256O, keccak256, ffiO]

lean_lib «Conform»

@[default_target]
lean_lib «EvmYul»

lean_exe «conform» where
  root := `Conform.Main
