import Lake
open Lake DSL

require «aesop» from git "https://github.com/leanprover-community/aesop" @ "v4.20.0-rc2"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "08f45c9b00960ee97351ba43cde133933803ab22"

package HammerCore {
  precompileModules := true
}

@[default_target]
lean_lib HammerCore
