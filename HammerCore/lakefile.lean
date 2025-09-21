import Lake
open Lake DSL

require «aesop» from git "https://github.com/leanprover-community/aesop" @ "v4.23.0"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "aaad53c0a0d216321fcaa1f77db164e726baa512"

package HammerCore {
  precompileModules := true
}

@[default_target]
lean_lib HammerCore
