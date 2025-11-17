# LeanHammer

LeanHammer is an automated reasoning tool for Lean that brings together multiple proof search and reconstruction techniques and combines them into one tool. The `hammer` tactic provided by LeanHammer uses a variety of techniques to search for a proof of the current goal, then constructs a suggestion for a tactic script which can replace the `hammer` invocation.

LeanHammer is in an early stage of its development and is therefore subject to breaking changes. There are currently versions of the hammer that are compatible with the stable versions of Lean from `v4.20.0` through `v4.25.0` (and the corresponding versions of Mathlib).

Pull requests and issues are welcome.

## Adding LeanHammer to Your Project

To add LeanHammer for v4.25.0 to an existing project with a `lakefile.toml` file, replace the Mathlib dependency in `lakefile.toml` with the following:

```toml
[[require]]
name = "Hammer"
git = "https://github.com/JOSHCLUNE/LeanHammer"
rev = "v4.25.0"

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.25.0"
```
The file `lean-toolchain` should contain the following:
```
leanprover/lean4:v4.25.0
```

If you have a project with a `lakefile.lean` instead of `lakefile.toml`, you can use this instead:

```lean
require Hammer from git "https://github.com/JOSHCLUNE/LeanHammer" @ "v4.25.0"

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.25.0"
```

Then use `lake update` to fetch the hammer and the corresponding versions of Lean and Mathlib. This also retrieves the Zipperposition executable that comes with LeanHammer. (This executable will be stored in the existing project's `.lake` directory.) The following example should then compile without any warnings or errors:

```lean
import Hammer

example : True := by
  hammer
```

The first time you `import Hammer`, Lake has to build the hammer component, which takes a few minutes, but after that, you can start hammering away.

If you use a version of Mathlib that differs from the most recent one, the premise selection server may have to calculate embeddings for the theorems it doesn't have. This can take a little while, but the server can use cached embeddings after that. You can test the hammer without premise selection by replacing `hammer` by `hammer {aesopPremises := 0, autoPremises := 0}` in the example above.

You are free to try to use a version of the hammer with a nearby version of Lean and Mathlib, but there are no guarantees it will work. As explained below, the hammer has several dependencies, and they break often as Lean changes. If you add the Hammer to an existing project and don't use `lake update`, you should use `lake update Hammer` to fetch the hammer and Zipperposition. You should also put the `Hammer` dependency before the `mathlib` dependency in `lakefile.toml` or `lakefil.lean`: Mathlib and LeanHammer share a dependency on `batteries`, and unless you favor Mathlib's version, you will end up recompiling Mathlib.

### Note for Macs

If you are using a Mac with an Apple silicon chip, Zipperposition may not work out of the box. To test this, try this from the top folder of your project:
```
.lake/packages/auto/.lake/build/zipperposition-bin-macos-big-sur.exe --version
```
If it doesn't successfully return the version,
```
softwareupdate --install-rosetta
```
should fix it.

## Components

Currently, LeanHammer consists of/depends on the following components:

- **Premise selection**
  - A [cloud-based premise selector](https://github.com/hanwenzhu/premise-selection) developed specifically for LeanHammer
  - [MePo](https://www.sciencedirect.com/science/article/pii/S1570868307000626) which has been widely used in Isabelle's Sledgehammer and was implemented in Lean by Kim Morrison
- **Translation procedure**
  - [Lean-auto](https://github.com/leanprover-community/lean-auto) which serves as an interface to translate from Lean into TPTP and SMT
- **Automatic theorem provers**
  - [Zipperposition](https://github.com/sneeuwballen/zipperposition) which is retrieved automatically via [this post_update script](https://github.com/leanprover-community/lean-auto/blob/hammer/lakefile.lean#L53)
  - [cvc5](https://github.com/cvc5/cvc5) via the [Lean cvc5 FFI](https://github.com/abdoo8080/lean-cvc5) (Not yet integrated)
- **Proof search and proof reconstruction tools native to Lean**
  - [Aesop](https://github.com/leanprover-community/aesop)
  - [Duper](https://github.com/leanprover-community/duper)
  - [Lean-SMT](https://github.com/ufmg-smite/lean-smt/tree/main) (Not yet integrated)

The above list only consists of components that LeanHammer currently consists of/depends on. As additional components are added and integrated, they will be added to the above list.

For more details about the premise selection component of LeanHammer, please refer to our paper [*Premise Selection for a Lean Hammer*](https://arxiv.org/abs/2506.07477) (Thomas Zhu, Joshua Clune, Jeremy Avigad, Albert Jiang, Sean Welleck).

## Usage

The syntax for invoking the `hammer` tactic is `by hammer [lemmas] {options}`. The `lemmas` and `options` arguments are both optional, with the former being used to tell `hammer` to use the supplied list of lemmas (in addition to any lemmas recommended by premise selection), and the latter being used to set LeanHammer's various configuration options.

### Options

Each of the `options` supplied to `hammer` have the form `option := value` and are separated by commas. Options that can be used to customize a LeanHammer call include:

- `disableAesop`: Can be set to `true` or `false` (default `false`). This option is used to remove Aesop from the LeanHammer call.
- `disableAuto`: Can be set to `true` or `false` (default `false`). This option is used to remove Lean-auto, Zipperposition, and Duper from the LeanHammer call (each of these tools are part of a single pipeline)
- `preprocessing`: Can be set to `aesop`, `simp_target`, `simp_all`, or `no_preprocessing` (default `aesop`). This option determines whether the initial goal is first processed by `aesop`, `simp`, `simp_all`, or none of these. This option can only be set to a value other than `aesop` if `disableAesop` is set to `true`, and must be set to `aesop` if `disableAesop` is set to `false`.
- `aesopPremises`: Can be set to any Nat (default 32). This option determines the number of lemmas from premise selection that are passed to Aesop as unsafe rules.
- `autoPremises`: Can be set to any Nat (default 16). This option determines the number of lemmas from premises selection that are passed to Lean-auto, Zipperposition, and Duper.
- `aesopPremisePriority`: Can be set to any Nat between 0 and 100 (default 20). This option determines the Aesop success priority assigned to each of the lemmas from premise selection when passed to Aesop as unsafe rules. See [Aesop's README](https://github.com/leanprover-community/aesop) for additional details on the meaning of this success priority.
- `aesopAutoPriority`: Can be set to any Nat between 0 and 100 (default 10). This option determines the Aesop success priority assigned to the unsafe rule that attempts to use Lean-auto, Zipperposition, and Duper to solve the current goal.
- `solver`: Can be set to `zipperposition_exe` or `zipperposition` (default `zipperposition_exe`). This option determines the external automatic theorem prover that Lean-auto sends its translated problem to. Currently, the only options are `zipperposition_exe` (which uses the Zipperposition executable that LeanHammer's post_update script retrieves) and `zipperposition` (which allows the user to use their own preinstalled version of Zipperposition).

Each of these options' defaults can be changed with `set_option hammer.<option_name>Default <new default>`. For example, the command that changes the default number of premises passed to Lean-auto from 16 to 32 is `set_option hammer.autoPremisesDefault 32`.

### Examples

You can use:
- `hammer` to run the full pipeline
- `hammer {disableAuto := true}` to try Aesop with premise selection
- `hammer {disableAesop := true, preprocessing := no_preprocessing}` to try Zipperposition and Duper with premise selection

### Premise Selection

In addition to the above options, LeanHammer has a premise selection component, based on the `Lean.PremiseSelection` API introduced in Lean 4 core. You may also use the premise selection component individually by:

```lean
import PremiseSelection

example : True := by
  premises
```

The premise selector can be modified with the command `set_premise_selector <myPremiseSelector>`. If no premise selector is specified by the user via this API, then LeanHammer uses the default selector `Cloud.premiseSelector <|> mepoSelector (useRarity := false) (p := 0.6) (c := 0.9)`. For more information on the interpretation of this selector, as well as information on `Cloud.premiseSelector`'s caching behavior, see the [premise-selection](https://github.com/hanwenzhu/premise-selection) repository.

The default premise selection server used by `Cloud.premiseSelector` hosted at `http://leanpremise.net` is intended for individual use. For heavy use cases, (e.g. performing an evaluation of `hammer` on a large number of theorems), we encourage users to use [this code](https://github.com/hanwenzhu/lean-premise-server) to host their own server which can be accessed following the instructions in [this README](https://github.com/hanwenzhu/premise-selection).

To view the set of premises that are passed to LeanHammer via premise selection, use the command `set_option trace.hammer.premises true`.

### Debugging

You can use the following to get more information:

- `set_option trace.hammer.premises true` to display the list of premises retrieved
- `set_option trace.hammer.debug true` to display what is passed to Zipperposition and the minimized set sent to Duper if it succeeds
- `set_option trace.auto.tptp.printQuery true` to display the query sent to Zipperposition
- `set_option trace.auto.tptp.result true` to display the response from Zipperposition
- `set_option trace.aesop true` to display the Aesop search tree
