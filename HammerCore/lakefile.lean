import Lake
open Lake DSL

require «aesop» from git "https://github.com/leanprover-community/aesop" @ "v4.20.0-rc2"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "5ba6bd2c3693b45b5e8da9cadbab416c2bdff2e8"

package HammerCore {
  precompileModules := true
}

@[default_target]
lean_lib HammerCore
