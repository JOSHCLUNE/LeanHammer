import Lake
open Lake DSL

require «premise-selection» from git "https://github.com/hanwenzhu/premise-selection" @ "v4.18.0"

require «HammerCore» from "./HammerCore"

package Hammer 

@[default_target]
lean_lib Hammer
