import Lake
open Lake DSL

require «aesop» from git "https://github.com/leanprover-community/aesop" @ "v4.18.0"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "7b2d2a989944b6e65df7194954de732a5357de42"

package HammerCore {
  precompileModules := true
}

@[default_target]
lean_lib HammerCore
