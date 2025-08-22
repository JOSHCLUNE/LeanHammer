import Lake
open Lake DSL

require «aesop» from git "https://github.com/leanprover-community/aesop" @ "v4.22.0"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "18d7f15b17d9b3071d74ec8d5e56f2f954ceec0a"

package HammerCore {
  precompileModules := true
}

@[default_target]
lean_lib HammerCore
