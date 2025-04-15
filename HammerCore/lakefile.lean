import Lake
open Lake DSL

require «aesop» from git "https://github.com/leanprover-community/aesop" @ "v4.18.0"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "65737400c80dcff0c205e79717fd0389ee8132ae"

package HammerCore {
  precompileModules := true
}

@[default_target]
lean_lib HammerCore
