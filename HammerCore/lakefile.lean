import Lake
open Lake DSL

require «aesop» from git "https://github.com/leanprover-community/aesop" @ "v4.20.0-rc2"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "8b40ddbea14dc992f085c568923a58ca1438c5ca"

package HammerCore {
  precompileModules := true
}

@[default_target]
lean_lib HammerCore
