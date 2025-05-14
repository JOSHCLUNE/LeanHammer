import Lake
open Lake DSL

require «aesop» from git "https://github.com/leanprover-community/aesop" @ "v4.20.0-rc2"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "7acf7e0d4afef7bee340380078fd69736f91cf88"

package HammerCore {
  precompileModules := true
}

@[default_target]
lean_lib HammerCore
