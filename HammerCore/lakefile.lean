import Lake
open Lake DSL

require «aesop» from git "https://github.com/leanprover-community/aesop" @ "v4.18.0"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "e28c4e11389116ccb6a48ff0fe9c3d1a9d7642e4"

package HammerCore {
  precompileModules := true
}

@[default_target]
lean_lib HammerCore
