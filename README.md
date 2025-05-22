# LeanHammer

LeanHammer is an automated reasoning tool for Lean which aims to bring together multiple proof search and reconstruction techniques and combine them into one tool. The `hammer` tactic provided by LeanHammer utilizes this variety of techniques to search for a proof of the current goal, then constructs a suggestion for a tactic script which can replace the `hammer` invocation.

LeanHammer is in an early stage of its development and therefore may be subject to breaking changes.

Pull requests and issues are welcome.


## Adding LeanHammer to Your Project

To use LeanHammer in an existing project with a `lakefile.toml` file, add the following lines to your list of dependencies in `lakefile.toml`:

```toml
[[require]]
name = "Hammer"
git = "https://github.com/JOSHCLUNE/LeanHammer"
rev = "main"
```

To use LeanHammer in an existing project with a `lakefile.lean` file, add the following line to your list of dependencies in `lakefile.lean`:

```lean
require hammer from git "https://github.com/JOSHCLUNE/LeanHammer" @ "main"
```

After LeanHammer has been added as a dependency to your project, run `lake update` or `lake update hammer` to retrieve the Zipperposition executable that comes with LeanHammer (this executable will be stored in the existing project's `.lake` directory). Then, the following example should compile without any warnings or errors:

```lean
import Hammer

-- Setting `aesopPremises` and `autoPremises` to 0 to bypass premise selection
-- which is slow on its first uncached invocation
example : True := by
  hammer {aesopPremises := 0, autoPremises := 0}
```

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

### Premise Selection

In addition to the above options, LeanHammer uses the `Lean.PremiseSelection` API introduced in Lean 4 core, and therefore can have its premise selection modified with the command `set_premise_selector <myPremiseSelector>`. If no premise selector is specified by the user via this API, then LeanHammer uses the default selector `Cloud.premiseSelector <|> mepoSelector (useRarity := true) (p := 0.6) (c := 0.9)`. For more information on the interpretation of this selector, as well as information on `Cloud.premiseSelector`'s caching behavior, see [this](https://github.com/hanwenzhu/premise-selection) README.

The default premise selection server used by `Cloud.premiseSelector` hosted at `http://leanpremise.net` is intended for individual use. For heavy use cases, (e.g. performing an evaluation of `hammer` on a large number of theorems), we encourage users to use [this](https://github.com/hanwenzhu/lean-premise-server) code to host their own server which can be accessed following the instructions in [this](https://github.com/hanwenzhu/premise-selection) README.

To view the set of premises that are passed to LeanHammer via premise selection, use the command `set_option trace.hammer.premises true`.