import Lake
open Lake DSL

require «premise-selection» from git "https://github.com/hanwenzhu/premise-selection" @ "v4.25.1"

require «Qq» from git "https://github.com/leanprover-community/quote4.git" @ "v4.25.1"

require «HammerCore» from "./HammerCore"

package Hammer {
  precompileModules := true
  preferReleaseBuild := true
}

@[default_target]
lean_lib Hammer
