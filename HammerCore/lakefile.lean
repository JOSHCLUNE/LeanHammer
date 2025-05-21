import Lake
open Lake DSL

require «aesop» from git "https://github.com/leanprover-community/aesop" @ "v4.20.0-rc2"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "7179853dbd9b66e18258c438626e0704833923cf"

package HammerCore {
  precompileModules := true
}

@[default_target]
lean_lib HammerCore
