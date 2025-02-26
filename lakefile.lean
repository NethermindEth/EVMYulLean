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

def cloneWithCache (pkg : NPackage _package.name) (dirname url : String) : FetchM (BuildJob GitRepo) := do
  let repoDir : GitRepo := ⟨pkg.dir / dirname⟩
  if !(← repoDir.dir.pathExists) then dbg_trace s!"Cloning: {url}"; GitRepo.clone url repoDir
  return pure repoDir

target cloneSha2 pkg : GitRepo := cloneWithCache pkg "sha2" "https://github.com/amosnier/sha-2.git"
  -- let repoDir : GitRepo := ⟨pkg.dir / "sha2"⟩
  -- if !(← repoDir.dir.pathExists) then
  --   GitRepo.clone "https://github.com/amosnier/sha-2.git" repoDir
  -- return pure repoDir

-- target cloneBlake2 pkg : GitRepo := cloneWithCache pkg "blake2" "https://github.com/Ferinko/BLAKE2_compress_any"

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
  -- let (blake2, _) ← (←cloneBlake2.fetch).await
  let oFile := pkg.buildDir / "ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "EvmYul" / "FFI" / "ffi.c"
  let weakArgs := #[
    "-I", (← getLeanIncludeDir).toString,
    "-I", sha2.dir.toString
    -- "-I", blake2.dir.toString
  ]
  buildO oFile srcJob weakArgs #["-fPIC"] compiler getLeanTrace

def buildFFILib (pkg : Package) (repo : GitRepo) (fileName : String) : FetchM (BuildJob FilePath) := do
  let srcJob ← inputTextFile $ repo.dir / fileName |>.addExtension "c"
  let oFile := pkg.buildDir / fileName |>.addExtension "o"
  let includeArgs := #["-I", repo.dir.toString]
  let weakArgs := includeArgs
  buildO oFile srcJob weakArgs #[] compiler getLeanTrace

def buildSha256Obj (pkg : Package) (fileName : String) := do
  buildFFILib pkg (← (←cloneSha2.fetch).await).1 fileName

-- def buildBlake2Obj (pkg : Package) (fileName : String) := do
--   buildFFILib pkg (← (←cloneBlake2.fetch).await).1 fileName

extern_lib libleanffi pkg := do
  -- In the static lib we include:
  -- the `sha-256` library itself
  let sha256O ← buildSha256Obj pkg "sha-256"
  -- the `blake2` library itself, the file being in `ref/`
  -- let blake2O ← buildBlake2Obj pkg "ref/blake2b-ref"
  -- our own `ffi.c`
  let ffiO ← ffi.o.fetch
  let name := nameToStaticLib "leanffi"
  buildStaticLib (pkg.nativeLibDir / name) #[sha256O, /- blake2O -/ ffiO]

lean_lib «Conform»
  
lean_lib «sha2»

@[default_target]
lean_lib «EvmYul»

lean_exe «conform» where
  root := `Conform.Main
