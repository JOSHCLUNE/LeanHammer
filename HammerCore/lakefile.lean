import Lake
open Lake DSL

require «aesop» from git "https://github.com/leanprover-community/aesop" @ "v4.18.0"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "055689b9ca7d2efe339c8f8a4563ae3e697fa435"

package HammerCore {
  precompileModules := true
}

@[default_target]
lean_lib HammerCore
