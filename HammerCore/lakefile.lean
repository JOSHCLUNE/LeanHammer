import Lake
open Lake DSL

require «aesop» from git "https://github.com/leanprover-community/aesop" @ "v4.20.0-rc2"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "9c9e3d2c2b4711c66b19b7e8791fe0e537c7c765"

package HammerCore {
  precompileModules := true
}

@[default_target]
lean_lib HammerCore
